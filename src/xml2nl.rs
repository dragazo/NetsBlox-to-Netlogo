use std::io::Read;
use std::fmt::{self, Display};
use std::collections::BTreeMap;

use xml::reader::{EventReader, XmlEvent};
use xml::name::OwnedName;
use xml::attribute::OwnedAttribute;
use xml::common::Position;

/// Possible errors for the NetsBlox to Netlogo conversion.
#[derive(Debug)]
pub enum ParseError {
    /// The input was not valid xml.
    /// Impossible for a valid NetsBlox xml file.
    InvalidXML,
    /// The input lacked a `stage` element.
    /// Impossible for a valid NetsBlox xml file.
    NoStage,
    /// The input had an invalid root `script` element.
    /// Impossible for a valid NetsBlox xml file.
    InvalidRootScript,
    /// The input had an incorrectly-formatted block.
    /// Impossible for a valid NetsBlox xml file.
    InvalidBlock,
    /// The input had a sprite which had no `name` attribute.
    /// Impossible for a valid NetsBlox xml file.
    UnnamedSprite,

    /// The given block type was not recognized or not supported.
    UnknownBlockType(String),
    /// The stage had multiple setup scripts, which is currently not supported.
    MultipleSetup,
    /// A entity (sprite) had multiple go scripts, which is currently not supported.
    EntityHadMultiGo(String),
    /// Reference to an entity (sprite) which was not defined by a `define` (custom) block.
    UndefinedEntity(String),
    /// A previously-defined entity (sprite) was redefined.
    EntityAlreadyDefined(String),
    /// An entity's properties list was not a literal list, which is currently not supported.
    EntityPropsNotList,
    /// An entity's properties list had a non-string-literal, which is currently not supported.
    EntityPropNotString,
    /// A general operator block contained a non-constant operator name, which is currently not supported.
    NonConstantOperator,
}

#[derive(Debug)]
struct XMLAttr {
    name: String,
    value: String,
}
#[derive(Debug)]
struct XML {
    name: String,
    attrs: Vec<XMLAttr>,
    children: Vec<XML>,
    text: String,
}
impl XML {
    fn get(&self, path: &[&str]) -> Option<&XML> {
        match path {
            [] => Some(self),
            [first, rest @ ..] => self.children.iter().find(|x| x.name == *first).map(|x| x.get(rest)).flatten(),
        }
    }
    fn attr(&self, name: &str) -> Option<&XMLAttr> {
        self.attrs.iter().find(|a| a.name == name)
    }
}
fn parse_xml_root<R: Read>(xml: &mut EventReader<R>, root_name: OwnedName, root_attrs: Vec<OwnedAttribute>) -> Result<XML, ParseError> {
    let mut text = String::new();
    let mut children = vec![];
    loop {
        match xml.next() {
            Ok(XmlEvent::StartElement { name, attributes, .. }) => {
                children.push(parse_xml_root(xml, name, attributes)?);
            }
            Ok(XmlEvent::EndElement { name }) => {
                assert_eq!(name, root_name);
                let attrs = root_attrs.into_iter().map(|a| XMLAttr {
                    name: a.name.local_name,
                    value: a.value,
                }).collect();
                return Ok(XML { name: root_name.local_name, attrs, children, text });
            }
            Ok(XmlEvent::Characters(s)) | Ok(XmlEvent::CData(s)) => text += &s,
            Ok(XmlEvent::Comment(_)) | Ok(XmlEvent::Whitespace(_)) | Ok(XmlEvent::ProcessingInstruction { .. }) => (),
            Ok(x @ XmlEvent::StartDocument { .. }) | Ok(x @ XmlEvent::EndDocument) => panic!("{:?} at pos {:?}", x, xml.position()),
            Err(_) => return Err(ParseError::InvalidXML),
        }
    }
}

enum HatType {
    Init, Go,
}
impl HatType {
    fn classify_root(script: &XML) -> Result<Option<HatType>, ParseError> {
        if script.name != "script" || script.attr("x").is_none() || script.attr("y").is_none() || script.children.is_empty() {
            return Err(ParseError::InvalidRootScript);
        }

        let first = &script.children[0];
        if first.name != "block" { return Ok(None) }

        let block_type = match first.attr("s") {
            Some(x) => x.value.as_str(),
            None => return Ok(None),
        };

        Ok(match block_type {
            "receiveGo" => {
                Some(HatType::Init)
            }
            "receiveMessage" => match first.get(&["l"]) {
                Some(x) => if x.text == "go" { Some(HatType::Go) } else { None }
                None => return Err(ParseError::InvalidBlock),
            }
            _ => None,
        })
    }
}

#[derive(Default, Debug, Clone)]
struct Entity {
    fields: Vec<String>,
    go: Option<String>,
}
/// Holds information about translated Netlogo code.
/// 
/// The main use of this type is the [`Netlogo::parse_xml`] function, which translates a NetsBlox project into Netlogo source.
/// Currently, no access is given to the internals, but the `Display` impl can be used to get the Netlogo source as a string.
#[derive(Default, Debug, Clone)]
pub struct Netlogo {
    entities: BTreeMap<String, Entity>,
    setup: Option<String>,
}
impl Netlogo {
    fn indent(code: &str) -> String {
        code.lines().map(|s| format!("    {}", s)).collect::<Vec<_>>().join("\n")
    }
    fn parse_bin_op_recursive(&mut self, op: &str, parent: &XML, my_name: &str) -> Result<String, ParseError> {
        if parent.children.len() != 2 { return Err(ParseError::InvalidBlock); }
        let a = self.parse_script_recursive(&parent.children[0], my_name)?;
        let b = self.parse_script_recursive(&parent.children[1], my_name)?;
        Ok(format!("({} {} {})", a, op, b))
    }
    fn parse_unary_op_recursive(&mut self, op: &str, parent: &XML, my_name: &str) -> Result<String, ParseError> {
        if parent.children.len() != 1 { return Err(ParseError::InvalidBlock); }
        let val = self.parse_script_recursive(&parent.children[0], my_name)?;
        Ok(format!("({} {})", op, val))
    }
    fn define_breed(&mut self, script: &XML, breed_name: String) -> Result<(), ParseError> {
        let mut fields = vec![];
        match script.attr("s") {
            None => return Err(ParseError::InvalidBlock),
            Some(x) => if x.value != "reportNewList" { return Err(ParseError::EntityPropsNotList); },
        }
        match script.get(&["list"]) {
            None => return Err(ParseError::InvalidBlock),
            Some(list) => for prop in list.children.iter() {
                if prop.name != "l" { return Err(ParseError::EntityPropNotString); }
                fields.push(prop.text.clone());
            }
        }
        if self.entities.contains_key(&breed_name) { return Err(ParseError::EntityAlreadyDefined(breed_name)); }
        let breed = Entity { fields, go: None };
        assert!(self.entities.insert(breed_name, breed).is_none());
        Ok(())
    }
    fn parse_script_recursive(&mut self, script: &XML, my_name: &str) -> Result<String, ParseError> {
        match script.name.as_str() {
            "script" => {
                let mut res = vec![];
                for block in script.children.iter() {
                    let item = self.parse_script_recursive(block, my_name)?;
                    if !item.is_empty() { res.push(item) }
                }
                Ok(res.join("\n"))
            }
            "block" | "custom-block" => match script.attr("s") {
                None => {
                    if let Some(var) = script.attr("var") {
                        Ok(var.value.clone())
                    }
                    else { return Err(ParseError::InvalidBlock); }
                }
                Some(block_type) => match block_type.value.as_str() {
                    "receiveMessage" => Ok(String::new()),
                    "patch at %l" => Ok(String::new()),
                    "clear all" => Ok("clear-all".into()),
                    "kill self %l" => Ok("die".into()),
                    "xPosition" => Ok("xcor".into()),
                    "yPosition" => Ok("ycor".into()),
                    "direction" => Ok("heading".into()),
                    "reportMouseDown" => Ok("mouse-down?".into()),
                    "reportMouseX" => Ok("mouse-xcor".into()),
                    "reportMouseY" => Ok("mouse-ycor".into()),
                    "quoted %txt" => {
                        if script.children.len() != 1 { return Err(ParseError::InvalidBlock); }
                        let content = self.parse_script_recursive(&script.children[0], my_name)?;
                        Ok(format!("\"{}\"", content))
                    }
                    "doDeclareVariables" => match script.get(&["list"]) {
                        None => return Err(ParseError::InvalidBlock),
                        Some(list) => {
                            let mut vars = vec![];
                            for item in list.children.iter() {
                                let name = self.parse_script_recursive(item, my_name)?;
                                if !name.is_empty() {
                                    vars.push(format!("let {} 0", name));
                                }
                            }
                            Ok(vars.join("\n"))
                        }
                    }
                    "reportGet" => match script.get(&["l", "option"]) {
                        None => return Err(ParseError::InvalidBlock),
                        Some(prop) => match prop.text.as_str() {
                            "name" => Ok(my_name.into()),
                            x => return Err(ParseError::UnknownBlockType(format!("reportGet <{}>", x))),
                        }
                    }
                    "get %s nearby %l" => {
                        if script.children.len() != 2 { return Err(ParseError::InvalidBlock); }
                        let type_name = self.parse_script_recursive(&script.children[0], my_name)?;
                        Ok(format!("{}-here", type_name))
                    }
                    "doSetVar" => {
                        if script.children.len() != 2 { return Err(ParseError::InvalidBlock); }
                        let var_name = self.parse_script_recursive(&script.children[0], my_name)?;
                        let value = self.parse_script_recursive(&script.children[1], my_name)?;
                        Ok(if !var_name.is_empty() && !value.is_empty() { format!("set {} {}", var_name, value) } else { String::new() })
                    }
                    "ask %s %upvar to do %cs" => {
                        if script.children.len() != 3 { return Err(ParseError::InvalidBlock); }
                        let type_name = self.parse_script_recursive(&script.children[0], my_name)?;
                        let command = self.parse_script_recursive(&script.children[2], my_name)?;
                        Ok(format!("ask {} [\n{}\n]", type_name, Self::indent(&command)))
                    }
                    "create %n %txt and for each %upvar do %cs" => {
                        if script.children.len() != 4 { return Err(ParseError::InvalidBlock); }
                        let count = self.parse_script_recursive(&script.children[0], my_name)?;
                        let type_name = self.parse_script_recursive(&script.children[1], my_name)?;
                        let command = self.parse_script_recursive(&script.children[3], my_name)?;
                        Ok(format!("create-{} {} [\n{}\n]", type_name, count, Self::indent(&command)))
                    }
                    "hatch %n from %l and for each %upvar do %cs" => {
                        if script.children.len() != 4 { return Err(ParseError::InvalidBlock); }
                        let count = &self.parse_script_recursive(&script.children[0], my_name)?;
                        let command = self.parse_script_recursive(&script.children[3], my_name)?;
                        Ok(format!("hatch {} [\n{}\n]", count, Self::indent(&command)))
                    }
                    "set value of %txt in %l to %s" => {
                        if script.children.len() != 3 { return Err(ParseError::InvalidBlock); }
                        let field_name = &self.parse_script_recursive(&script.children[0], my_name)?;
                        let value = self.parse_script_recursive(&script.children[2], my_name)?;
                        Ok(format!("set {} {}", field_name, value))
                    }
                    "value %txt in %l" => {
                        if script.children.len() != 2 { return Err(ParseError::InvalidBlock); }
                        let field_name = self.parse_script_recursive(&script.children[0], my_name)?;
                        Ok(field_name)
                    }
                    "random item of %l" => {
                        if script.children.len() != 1 { return Err(ParseError::InvalidBlock); }
                        let vals = self.parse_script_recursive(&script.children[0], my_name)?;
                        Ok(format!("one-of {}", vals))
                    }
                    "rotate %l left %n degrees" => {
                        if script.children.len() != 2 { return Err(ParseError::InvalidBlock); }
                        let ang = self.parse_script_recursive(&script.children[1], my_name)?;
                        Ok(format!("lt {}", ang))
                    }
                    "rotate %l right %n degrees" => {
                        if script.children.len() != 2 { return Err(ParseError::InvalidBlock); }
                        let ang = self.parse_script_recursive(&script.children[1], my_name)?;
                        Ok(format!("rt {}", ang))
                    }
                    "turn" => {
                        if script.children.len() != 1 { return Err(ParseError::InvalidBlock); }
                        let ang = self.parse_script_recursive(&script.children[0], my_name)?;
                        Ok(format!("rt {}", ang))
                    }
                    "turnLeft" => {
                        if script.children.len() != 1 { return Err(ParseError::InvalidBlock); }
                        let ang = self.parse_script_recursive(&script.children[0], my_name)?;
                        Ok(format!("lt {}", ang))
                    }
                    "setHeading" => {
                        if script.children.len() != 1 { return Err(ParseError::InvalidBlock); }
                        match script.get(&["l", "option"]) {
                            Some(opt) => match opt.text.as_str() {
                                "random" => Ok("set heading (random-float 360)".to_string()),
                                x => return Err(ParseError::UnknownBlockType(format!("setHeading <{}>", x))),
                            }
                            None => {
                                let val = self.parse_script_recursive(&script.children[0], my_name)?;
                                Ok(format!("set heading {}", val))
                            }
                        }
                    }
                    "doFaceTowards" => {
                        if script.children.len() != 1 { return Err(ParseError::InvalidBlock); }
                        match script.get(&["l", "option"]) {
                            Some(opt) => match opt.text.as_str() {
                                "center" => Ok("facexy 0 0".to_string()),
                                "mouse-pointer" => Ok("facexy mouse-xcor mouse-ycor".to_string()),
                                "random position" => Ok("set heading (random-float 360)".to_string()),
                                x => return Err(ParseError::UnknownBlockType(format!("doFaceTowards <{}>", x))),
                            }
                            None => {
                                let target = self.parse_script_recursive(&script.children[0], my_name)?;
                                Ok(format!("face {}", target))
                            }
                        }
                    }
                    "wrapping move %l %n steps" => {
                        if script.children.len() != 2 { return Err(ParseError::InvalidBlock); }
                        let dist = self.parse_script_recursive(&script.children[1], my_name)?;
                        Ok(format!("fd {}", dist))
                    }
                    "forward" => {
                        if script.children.len() != 1 { return Err(ParseError::InvalidBlock); }
                        let dist = self.parse_script_recursive(&script.children[0], my_name)?;
                        Ok(format!("fd {}", dist))
                    }
                    "gotoXY" => {
                        if script.children.len() != 2 { return Err(ParseError::InvalidBlock); }
                        let x = self.parse_script_recursive(&script.children[0], my_name)?;
                        let y = self.parse_script_recursive(&script.children[1], my_name)?;
                        Ok(format!("setxy {} {}", x, y))
                    }
                    "changeXPosition" => {
                        if script.children.len() != 1 { return Err(ParseError::InvalidBlock); }
                        let delta = self.parse_script_recursive(&script.children[0], my_name)?;
                        Ok(format!("set xcor (xcor + {})", delta))
                    }
                    "setXPosition" => {
                        if script.children.len() != 1 { return Err(ParseError::InvalidBlock); }
                        let val = self.parse_script_recursive(&script.children[0], my_name)?;
                        Ok(format!("set xcor {}", val))
                    }
                    "changeYPosition" => {
                        if script.children.len() != 1 { return Err(ParseError::InvalidBlock); }
                        let delta = self.parse_script_recursive(&script.children[0], my_name)?;
                        Ok(format!("set ycor (ycor + {})", delta))
                    }
                    "setYPosition" => {
                        if script.children.len() != 1 { return Err(ParseError::InvalidBlock); }
                        let val = self.parse_script_recursive(&script.children[0], my_name)?;
                        Ok(format!("set ycor {}", val))
                    }
                    "reportNewList" => {
                        if script.children.len() != 1 { return Err(ParseError::InvalidBlock); }
                        let mut res = String::from("[ ");
                        for item in script.children[0].children.iter() {
                            res += &self.parse_script_recursive(item, my_name)?;
                            res.push(' ');
                        }
                        res.push(']');
                        Ok(res)
                    }
                    "reportNumbers" => {
                        if script.children.len() != 2 { return Err(ParseError::InvalidBlock); }
                        let low = self.parse_script_recursive(&script.children[0], my_name)?;
                        let high = self.parse_script_recursive(&script.children[1], my_name)?;
                        Ok(format!("(range {} ({} + 1))", low, high))
                    }
                    "reportListIsEmpty" => {
                        if script.children.len() != 1 { return Err(ParseError::InvalidBlock); }
                        let src = self.parse_script_recursive(&script.children[0], my_name)?;
                        Ok(format!("(empty? {})", src))
                    }
                    "doIfElse" => {
                        if script.children.len() != 3 { return Err(ParseError::InvalidBlock); }
                        let condition = self.parse_script_recursive(&script.children[0], my_name)?;
                        let case_1 = self.parse_script_recursive(&script.children[1], my_name)?;
                        let case_2 = self.parse_script_recursive(&script.children[2], my_name)?;
                        Ok(format!("ifelse {} [\n{}\n] [\n{}\n]", condition, Self::indent(&case_1), Self::indent(&case_2)))
                    }
                    "reportIfElse" => {
                        if script.children.len() != 3 { return Err(ParseError::InvalidBlock); }
                        let condition = self.parse_script_recursive(&script.children[0], my_name)?;
                        let case_1 = self.parse_script_recursive(&script.children[1], my_name)?;
                        let case_2 = self.parse_script_recursive(&script.children[2], my_name)?;
                        Ok(format!("(ifelse-value {} [ {} ] [ {} ])", condition, case_1, case_2))
                    }
                    "doRepeat" => {
                        if script.children.len() != 2 { return Err(ParseError::InvalidBlock); }
                        let count = self.parse_script_recursive(&script.children[0], my_name)?;
                        let action = self.parse_script_recursive(&script.children[1], my_name)?;
                        Ok(format!("repeat {} [\n{}\n]", count, Self::indent(&action)))
                    }
                    "reportMonadic" => {
                        if script.children.len() != 2 { return Err(ParseError::InvalidBlock); }
                        let arg = self.parse_script_recursive(&script.children[1], my_name)?;
                        let op = match script.get(&["l", "option"]) {
                            None => return Err(ParseError::NonConstantOperator),
                            Some(x) => x.text.as_str(),
                        };
                        Ok(match op {
                            "abs" | "ceiling" | "floor" | "sqrt" | "sin" | "cos" | "tan" | "asin" | "acos" | "ln" => format!("({} {})", op, arg),
                            "neg" => format!("(- {})", arg),
                            "atan" => format!("(atan 1 {})", arg),
                            "log" => format!("(log {} 10)", arg),
                            "lg" => format!("(log {} 2)", arg),
                            "e^" => format!("(exp {})", arg),
                            "10^" => format!("(10 ^ {})", arg),
                            "2^" => format!("(2 ^ {})", arg),
                            "id" => arg,
                            _ => return Err(ParseError::UnknownBlockType(format!("monadic <{}>", op))),
                        })
                    }
                    "reportListItem" | "reportLetter" => {
                        if script.children.len() != 2 { return Err(ParseError::InvalidBlock); }
                        let src = self.parse_script_recursive(&script.children[1], my_name)?;
                        match script.get(&["l", "option"]) {
                            None => {
                                let index = self.parse_script_recursive(&script.children[0], my_name)?;
                                Ok(format!("(item ({}-1) {})", index, src))
                            }
                            Some(opt) => match opt.text.as_str() {
                                "last" => Ok(format!("(last {})", src)),
                                "any" => Ok(format!("(one-of {})", src)),
                                x => return Err(ParseError::UnknownBlockType(format!("get item <{}>", x))),
                            }
                        }
                    }
                    "reportListContainsItem" => {
                        if script.children.len() != 2 { return Err(ParseError::InvalidBlock); }
                        let list = self.parse_script_recursive(&script.children[0], my_name)?;
                        let val = self.parse_script_recursive(&script.children[1], my_name)?;
                        Ok(format!("(member? {} {})", val, list))
                    }
                    "reportConcatenatedLists" => {
                        if script.children.len() != 1 { return Err(ParseError::InvalidBlock); }
                        let list = &script.children[0];
                        if list.name != "list" { return Err(ParseError::InvalidBlock); }

                        let mut res = "(sentence".to_string();
                        for item in list.children.iter() {
                            res.push(' ');
                            res += &self.parse_script_recursive(item, my_name)?;
                        }
                        res.push(')');
                        Ok(res)
                    }
                    "doIf" => {
                        if script.children.len() != 2 { return Err(ParseError::InvalidBlock); }
                        let condition = self.parse_script_recursive(&script.children[0], my_name)?;
                        let then = self.parse_script_recursive(&script.children[1], my_name)?;
                        Ok(format!("if {} [\n{}\n]", condition, Self::indent(&then)))
                    }
                    "reportRandom" => {
                        if script.children.len() != 2 { return Err(ParseError::InvalidBlock); }
                        let low = self.parse_script_recursive(&script.children[0], my_name)?;
                        let high = self.parse_script_recursive(&script.children[1], my_name)?;

                        if low == "0" { Ok(format!("(random {})", high)) }
                        else { Ok(format!("((floor {}) + random ({} - {}))", low, high, low)) }
                    }
                    "random float %s %s" => {
                        if script.children.len() != 2 { return Err(ParseError::InvalidBlock); }
                        let low = self.parse_script_recursive(&script.children[0], my_name)?;
                        let high = self.parse_script_recursive(&script.children[1], my_name)?;

                        if low == "0" { Ok(format!("(random-float {})", high)) }
                        else { Ok(format!("({} + random-float ({} - {}))", low, high, low)) }
                    }
                    "reportListLength" | "reportStringSize" => {
                        if script.children.len() != 1 { return Err(ParseError::InvalidBlock); }
                        let src = self.parse_script_recursive(&script.children[0], my_name)?;
                        Ok(format!("(length {})", src))
                    }
                    "define breed %txt with properties %l" => {
                        if script.children.len() != 2 { return Err(ParseError::InvalidBlock); }
                        let type_name = self.parse_script_recursive(&script.children[0], my_name)?;
                        self.define_breed(&script.children[1], type_name)?;
                        Ok("".to_string())
                    }
                    "define patches with properties %l" => {
                        if script.children.len() != 1 { return Err(ParseError::InvalidBlock); }
                        self.define_breed(&script.children[0], "patches".to_string())?;
                        Ok("".to_string())
                    }
                    "reportRound" => {
                        if script.children.len() != 1 { return Err(ParseError::InvalidBlock); }
                        let val = self.parse_script_recursive(&script.children[0], my_name)?;
                        Ok(format!("(round {})", val))
                    }
                    "reportBoolean" => {
                        if script.children.len() != 1 { return Err(ParseError::InvalidBlock); }
                        match script.get(&["l", "bool"]) {
                            None => return Err(ParseError::NonConstantOperator),
                            Some(x) => Ok(x.text.clone()),
                        }
                    }
                    "doFor" => {
                        if script.children.len() != 4 { return Err(ParseError::InvalidBlock); }
                        let var = self.parse_script_recursive(&script.children[0], my_name)?;
                        let low = self.parse_script_recursive(&script.children[1], my_name)?;
                        let high = self.parse_script_recursive(&script.children[2], my_name)?;
                        let action = self.parse_script_recursive(&script.children[3], my_name)?;
                        Ok(format!("foreach (range {} ({} + 1)) [ {} ->\n{}\n]", low, high, var, Self::indent(&action)))
                    }
                    "doForEach" => {
                        if script.children.len() != 3 { return Err(ParseError::InvalidBlock); }
                        let var = self.parse_script_recursive(&script.children[0], my_name)?;
                        let range = self.parse_script_recursive(&script.children[1], my_name)?;
                        let action = self.parse_script_recursive(&script.children[2], my_name)?;
                        Ok(format!("foreach {} [ {} ->\n{}\n]", range, var, Self::indent(&action)))
                    }
                    "doForever" => {
                        if script.children.len() != 1 { return Err(ParseError::InvalidBlock); }
                        let action = self.parse_script_recursive(&script.children[0], my_name)?;
                        Ok(format!("loop [\n{}\n]", Self::indent(&action)))
                    }
                    "reportEquals" => self.parse_bin_op_recursive("=", script, my_name),
                    "reportLessThan" => self.parse_bin_op_recursive("<", script, my_name),
                    "reportGreaterThan" => self.parse_bin_op_recursive(">", script, my_name),
                    "reportAnd" => self.parse_bin_op_recursive("and", script, my_name),
                    "reportOr" => self.parse_bin_op_recursive("or", script, my_name),
                    "reportSum" => self.parse_bin_op_recursive("+", script, my_name),
                    "reportDifference" => self.parse_bin_op_recursive("-", script, my_name),
                    "reportProduct" => self.parse_bin_op_recursive("*", script, my_name),
                    "reportQuotient" => self.parse_bin_op_recursive("/", script, my_name),
                    "reportModulus" => self.parse_bin_op_recursive("mod", script, my_name),
                    "reportPower" => self.parse_bin_op_recursive("^", script, my_name),
                    "reportNot" => self.parse_unary_op_recursive("not", script, my_name),
                    "random-xcor" => Ok("random-xcor".to_string()),
                    "random-ycor" => Ok("random-ycor".to_string()),
                    "reset ticks" => Ok("reset-ticks".to_string()),
                    x => return Err(ParseError::UnknownBlockType(x.to_string())),
                }
            }
            "l" => Ok(script.text.clone()),
            x => return Err(ParseError::UnknownBlockType(x.to_string())),
        }
    }
    fn parse_root_script(&mut self, script: &XML, sprite: &str) -> Result<(), ParseError> {
        Ok(match HatType::classify_root(script)? {
            Some(HatType::Init) => for block in script.children.iter().filter(|s| s.name == "custom-block") {
                match block.attr("s") {
                    None => return Err(ParseError::InvalidBlock),
                    Some(x) => match x.value.as_str() {
                        "definitions %cs" => match block.get(&["script"]) {
                            None => return Err(ParseError::InvalidBlock),
                            Some(defs) => {
                                self.parse_script_recursive(defs, sprite)?;
                            }
                        }
                        "setup %cs" => match block.get(&["script"]) {
                            None => return Err(ParseError::InvalidBlock),
                            Some(setup) => {
                                let parsed = self.parse_script_recursive(setup, sprite)?;
                                if self.setup.is_some() { return Err(ParseError::MultipleSetup); }
                                self.setup = Some(format!("to setup\n{}\nend", Self::indent(&parsed)));
                            }
                        }
                        _ => (),
                    }
                }
            }
            Some(HatType::Go) => {
                let parsed = self.parse_script_recursive(script, sprite)?;
                match self.entities.get_mut(sprite) {
                    None => return Err(ParseError::UndefinedEntity(sprite.to_string())),
                    Some(breed) => {
                        if breed.go.is_some() { return Err(ParseError::EntityHadMultiGo(sprite.to_string())); }
                        breed.go = Some(parsed);
                    }
                }                
            }
            None => (),
        })
    }

    /// Parses a NetsBlox project xml file into Netlogo source.
    pub fn parse_xml<R: Read>(xml: R) -> Result<Self, ParseError> {
        let mut xml = EventReader::new(xml);
        while let Ok(e) = xml.next() {
            if let XmlEvent::StartElement { name, attributes, .. } = e {
                if name.local_name != "stage" { continue }

                let stage = parse_xml_root(&mut xml, name, attributes)?;
                let mut gen = Netlogo::default();

                for stage_script in stage.get(&["scripts"]).into_iter().flat_map(|s| &s.children) {
                    gen.parse_root_script(stage_script, "patches")?;
                }
                for sprite in stage.get(&["sprites"]).into_iter().flat_map(|s| &s.children).filter(|c| c.name == "sprite") {
                    let sprite_name = match sprite.attr("name") {
                        Some(x) => &x.value,
                        None => return Err(ParseError::UnnamedSprite),
                    };
                    for sprite_script in sprite.get(&["scripts"]).into_iter().flat_map(|s| &s.children) {
                        gen.parse_root_script(sprite_script, sprite_name)?;
                    }
                }

                return Ok(gen);
            }
        }
        Err(ParseError::NoStage)
    }
}
impl Display for Netlogo {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        for breed in self.entities.keys() {
            if breed == "patches" { continue }
            writeln!(f, "breed [ {0} single-{0} ]", breed)?;
        }
        writeln!(f)?;

        for (breed_name, breed) in self.entities.iter() {
            if breed.fields.is_empty() { continue }
            writeln!(f, "{}-own [ {} ]", breed_name, breed.fields.join(" "))?;
        }
        writeln!(f)?;

        if let Some(setup) = self.setup.as_ref() {
            writeln!(f, "{}\n", setup)?;
        }

        let mut go_scripts = vec![];
        for (breed_name, breed) in self.entities.iter() {
            if let Some(script) = breed.go.as_ref() {
                go_scripts.push((breed_name.as_str(), script.as_str()));
            }
        }
        if !go_scripts.is_empty() {
            writeln!(f, "to go")?;
            for script in go_scripts.iter() {
                writeln!(f, "    go-{}", script.0)?;
            }
            writeln!(f, "    tick\nend\n")?;

            for script in go_scripts.iter() {
                writeln!(f, "to go-{}\n{}\nend\n", script.0, Self::indent(script.1))?;
            }
        }

        Ok(())
    }
}