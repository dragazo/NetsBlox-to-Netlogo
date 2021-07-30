use std::io::Read;
use std::fmt::{self, Display};
use std::collections::HashSet;

use linked_hash_map::LinkedHashMap;

use xml::reader::{EventReader, XmlEvent};
use xml::name::OwnedName;
use xml::attribute::OwnedAttribute;
use xml::common::Position;

use regex::Regex;

use crate::common::*;
use crate::util::*;

lazy_static! {
    static ref BUILTIN_BLOCKS: HashSet<&'static str> = {
        let mut res = HashSet::new();
        for line in include_str!("builtin_blocks.txt").lines().map(|s| s.trim()) {
            if line.is_empty() || line.starts_with('#') { continue }
            assert!(res.insert(line));
        }
        res
    };
    static ref NUMBER_REGEX: Regex = Regex::new(r"^-?[0-9]+(\.[0-9]*)?([eE][+-]?[0-9]+)?$").unwrap();
    static ref PARAM_FINDER: Regex = Regex::new(r"%'([^']+)'").unwrap();
}

fn rename_patch_prop(name: &str) -> &str {
    NB2NL_PATCH_PROP_RENAMES.get(name).copied().unwrap_or(name)
}

/// Possible errors for the NetsBlox to Netlogo conversion.
#[derive(Debug)]
pub enum Error {
    /// The input was not valid xml.
    /// Impossible for a valid NetsBlox xml file.
    InvalidXml,
    /// The input was not a valid NetsBlox project.
    /// Impossible for a valid NetsBlox xml file.
    InvalidProject,

    /// The input project had multiple roles defined, which is not currently supported.
    MultipleRoles,
    /// The project had two or more sprites that share a single (case insensitive) name.
    SpritesWithSameName(String),
    /// The project had a block that created turtles outside of a tell block (not supported).
    CreateOutsideOfTell,
    /// The project used a block which was only intended for core behavior (not user-level code).
    UseOfInternalBlock(String),
    
    /// The project refered to a breed name indirectly, which is not currently supported.
    NonConstantBreedName,
    /// The project had a code block which was non-constant or non-inlined (e.g. a lambda function).
    NonConstantCodeBlock,
    /// The project refered to a patch prop indirectly (not by-name)
    NonConstantPatchProp,
    /// The project refered to a color indirectly (not by-name)
    NonConstantColor,

    /// A set block was used to set the builtin ticks variable to a non-zero value (not allowed).
    SetTicksToNonZero,
    /// A change block was used to change the builtin ticks variable by a non-one amount (not allowed).
    ChangeTicksByNonOne,

    /// The given block type was not recognized or not supported.
    UnknownBlockType(String),
    /// A general operator block contained a non-constant operator name, which is currently not supported.
    NonConstantOperator,

    /// A ringified reporter was empty.
    EmptyReportRing,
}

fn surely<T>(val: Option<T>) -> Result<T, Error> {
    match val {
        Some(x) => Ok(x),
        None => Err(Error::InvalidProject),
    }
}
fn clean_name(name: &str) -> Result<String, Error> {
    if name.is_empty() { return Err(Error::InvalidProject); }

    let mut res = String::with_capacity(name.len());
    if name.chars().next().unwrap().is_digit(10) { res.push('_') }
    for ch in name.chars() {
        res.push(if ch.is_whitespace() { '-' } else { ch });
    }
    Ok(res)
}

#[derive(Debug)]
struct XmlAttr {
    name: String,
    value: String,
}
#[derive(Debug)]
struct Xml {
    name: String,
    attrs: Vec<XmlAttr>,
    children: Vec<Xml>,
    text: String,
}
impl Xml {
    fn get(&self, path: &[&str]) -> Option<&Xml> {
        match path {
            [] => Some(self),
            [first, rest @ ..] => self.children.iter().find(|x| x.name == *first).map(|x| x.get(rest)).flatten(),
        }
    }
    fn attr(&self, name: &str) -> Option<&XmlAttr> {
        self.attrs.iter().find(|a| a.name == name)
    }
}
fn parse_xml_root<R: Read>(xml: &mut EventReader<R>, root_name: OwnedName, root_attrs: Vec<OwnedAttribute>) -> Result<Xml, Error> {
    let mut text = String::new();
    let mut children = vec![];
    loop {
        match xml.next() {
            Ok(XmlEvent::StartElement { name, attributes, .. }) => {
                children.push(parse_xml_root(xml, name, attributes)?);
            }
            Ok(XmlEvent::EndElement { name }) => {
                assert_eq!(name, root_name);
                let attrs = root_attrs.into_iter().map(|a| XmlAttr {
                    name: a.name.local_name,
                    value: a.value,
                }).collect();
                return Ok(Xml { name: root_name.local_name, attrs, children, text });
            }
            Ok(XmlEvent::Characters(s)) | Ok(XmlEvent::CData(s)) => text += &s,
            Ok(XmlEvent::Comment(_)) | Ok(XmlEvent::Whitespace(_)) | Ok(XmlEvent::ProcessingInstruction { .. }) => (),
            Ok(x @ XmlEvent::StartDocument { .. }) | Ok(x @ XmlEvent::EndDocument) => panic!("{:?} at pos {:?}", x, xml.position()),
            Err(_) => return Err(Error::InvalidXml),
        }
    }
}

#[derive(Debug)]
struct Entity {
    plural: String,
    props: LinkedHashMap<String, ()>,
}
#[derive(Debug)]
struct Function {
    name: String,
    params: Vec<String>,
    reports: bool,
    formatted: Option<String>, // this should be Some(_) by the end of parsing all functions
}

#[derive(Default, Debug)]
struct Program {
    globals: Vec<String>,
    entities: LinkedHashMap<String, Entity>,
    functions: LinkedHashMap<String, Function>,

    metadata: MetaData,
}
impl Program {
    fn parse_bin_op_recursive(&mut self, op: &str, parent: &Xml) -> Result<String, Error> {
        if parent.children.len() != 2 { return Err(Error::InvalidProject); }
        let a = self.parse_script_recursive(&parent.children[0])?;
        let b = self.parse_script_recursive(&parent.children[1])?;
        Ok(format!("({} {} {})", a, op, b))
    }
    fn parse_unary_op_recursive(&mut self, op: &str, parent: &Xml) -> Result<String, Error> {
        if parent.children.len() != 1 { return Err(Error::InvalidProject); }
        let val = self.parse_script_recursive(&parent.children[0])?;
        Ok(format!("({} {})", op, val))
    }
    
    fn parse_script_recursive(&mut self, script: &Xml) -> Result<String, Error> {
        match script.name.as_str() {
            "script" => {
                let mut res = vec![];
                for block in script.children.iter() {
                    let item = self.parse_script_recursive(block)?;
                    if !item.is_empty() { res.push(item) }
                }
                Ok(res.join("\n"))
            }
            "autolambda" => {
                if script.children.len() > 1 { return Err(Error::InvalidProject); }
                if script.children.is_empty() { return Err(Error::EmptyReportRing); }
                self.parse_script_recursive(&script.children[0])
            }
            "block" | "custom-block" => match script.attr("s") {
                None => match script.attr("var") {
                    Some(var) => Ok(var.value.clone()),
                    None => Err(Error::InvalidProject),
                }
                Some(block_type) => match block_type.value.as_str() {
                    x @ "is %obj alive?" => Err(Error::UseOfInternalBlock(x.to_string())),
                    "%n clones" | "%n new %s" | "%n new %s (ordered)" => Err(Error::CreateOutsideOfTell),

                    "update background" => Ok(String::new()), // this is done automatically in netlogo, so it can compile into nothing

                    "delete all clones" => Ok("clear-turtles".into()),
                    "reset patches" => Ok("clear-patches".into()),
                    "reset global variables" => Ok("clear-globals".into()),
                    "reset everything" => Ok("clear-all".into()),
                    "random x position" => Ok("random-xcor".into()),
                    "random y position" => Ok("random-ycor".into()),
                    "dx of 1 step" => Ok("dx".into()),
                    "dy of 1 step" => Ok("dy".into()),
                    "self" => Ok("self".into()),
                    "asker" => Ok("myself".into()),
                    "pick random 0 up to %n" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let max = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("(random {})", max))
                    }
                    "pick random float %n" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let max = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("(random-float {})", max))
                    }
                    "tell %l to %cs" => {
                        if script.children.len() != 2 { return Err(Error::InvalidProject); }

                        let action = self.parse_script_recursive(&script.children[1])?;

                        let agents = &script.children[0];
                        let (is_create, is_ordered, is_hatch) = if agents.name != "custom-block" { (false, false, false) } else {
                            let t = surely(agents.attr("s"))?.value.as_str();
                            if t == "%n new %s" || t == "%n new %s (ordered)" { (true, t.ends_with("(ordered)"), false) }
                            else if t == "%n clones" { (false, false, true) }
                            else { (false, false, false) }
                        };
                        debug_assert!(!is_create || !is_hatch);

                        if is_create {
                            if agents.children.len() != 2 { return Err(Error::InvalidProject); }
                            let count = self.parse_script_recursive(&agents.children[0])?;
                            let breed = match agents.children[1].name.as_str() {
                                "l" => clean_name(&agents.children[1].text)?,
                                _ => return Err(Error::NonConstantBreedName),
                            };
                            Ok(format!("{}{} {} [\n{}\n]", if is_ordered { "create-ordered-" } else { "create-" }, breed, count, indent(&action)))
                        }
                        else if is_hatch {
                            if agents.children.len() != 1 { return Err(Error::InvalidProject); }
                            let count = self.parse_script_recursive(&agents.children[0])?;
                            Ok(format!("hatch {} [\n{}\n]", count, indent(&action)))
                        }
                        else {
                            let target = self.parse_script_recursive(agents)?;
                            Ok(format!("ask {} [\n{}\n]", target, indent(&action)))
                        }
                    }
                    "ask %obj for its %repRing" => {
                        if script.children.len() != 2 { return Err(Error::InvalidProject); }
                        if script.children[1].name != "block" || surely(script.children[1].attr("s"))?.value != "reifyReporter" {
                            return Err(Error::NonConstantCodeBlock);
                        }
                    
                        let target = self.parse_script_recursive(&script.children[0])?;
                        let expr = self.parse_script_recursive(surely(script.children[1].get(&["autolambda"]))?)?;
                        Ok(format!("([{}] of {})", expr, target))
                    }
                    "set pen color to %l" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let color = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("set color {}", color))
                    }
                    "setColor" => {
                        let vals: Vec<_> = surely(script.get(&["color"]))?.text.split(',').collect();
                        if vals.len() != 3 && vals.len() != 4 { return Err(Error::InvalidProject); }
                        Ok(format!("set color (list {} {} {})", vals[0], vals[1], vals[2]))
                    } 
                    "pen color" => Ok("color".into()),
                    "set scale to %n x" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let scale = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("set size {}", scale))
                    }
                    "scale" => Ok("size".into()),
                    "distance from x: %n y: %n" => {
                        if script.children.len() != 2 { return Err(Error::InvalidProject); }
                        let x = self.parse_script_recursive(&script.children[0])?;
                        let y = self.parse_script_recursive(&script.children[1])?;
                        Ok(format!("(distancexy {} {})", x, y))
                    }
                    "distance from %obj" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let obj = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("(distance {})", obj))
                    }
                    "direction towards x: %n y: %n" => {
                        if script.children.len() != 2 { return Err(Error::InvalidProject); }
                        let x = self.parse_script_recursive(&script.children[0])?;
                        let y = self.parse_script_recursive(&script.children[1])?;
                        Ok(format!("(towardsxy {} {})", x, y))
                    }
                    "direction towards %obj" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let obj = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("(towards {})", obj))
                    }
                    "angle change from %n to %n" => {
                        if script.children.len() != 2 { return Err(Error::InvalidProject); }
                        let from = self.parse_script_recursive(&script.children[0])?;
                        let to = self.parse_script_recursive(&script.children[1])?;
                        Ok(format!("(subtract-headings {} {})", to, from)) // yes, these should be backwards
                    }

                    "removeClone" => Ok("die".into()),
                    "xPosition" | "x position" => Ok("xcor".into()),
                    "yPosition" | "y position" => Ok("ycor".into()),
                    "direction" => Ok("heading".into()),
                    "reportMouseDown" => Ok("mouse-down?".into()),
                    "reportMouseX" => Ok("mouse-xcor".into()),
                    "reportMouseY" => Ok("mouse-ycor".into()),
                    "doDeclareVariables" => match script.get(&["list"]) {
                        None => Err(Error::InvalidProject),
                        Some(list) => {
                            let mut vars = vec![];
                            for item in list.children.iter() {
                                if item.name != "l" { return Err(Error::InvalidProject); }
                                let name = clean_name(&item.text)?;
                                vars.push(format!("let {} 0", name));
                            }
                            Ok(vars.join("\n"))
                        }
                    }
                    "script variable %upvar = %s" => {
                        if script.children.len() != 2 { return Err(Error::InvalidProject); }
                        if script.children[0].name != "l" { return Err(Error::InvalidProject); }
                        let name = clean_name(&script.children[0].text)?;
                        let value = self.parse_script_recursive(&script.children[1])?;
                        Ok(format!(r#"let {} {}"#, name, value))
                    }
                    x @ ("doSetVar" | "doChangeVar") => {
                        let is_set = x == "doSetVar";

                        if script.children.len() != 2 { return Err(Error::InvalidProject); }
                        
                        let var_name = match script.children[0].name.as_str() {
                            "l" => clean_name(&script.children[0].text)?,
                            _ => return Err(Error::InvalidProject),
                        };
                        let value = self.parse_script_recursive(&script.children[1])?;

                        if !var_name.is_empty() && !value.is_empty() {
                            match (var_name.as_str(), is_set) {
                                ("ticks", true) => match value.as_str() {
                                    "0" => Ok("reset-ticks".into()),
                                    _ => Err(Error::SetTicksToNonZero),
                                }
                                ("ticks", false) => match value.as_str() {
                                    "1" => Ok("tick".into()),
                                    _ => Err(Error::ChangeTicksByNonOne),
                                }

                                (_, true) => Ok(format!("set {} {}", var_name, value)),
                                (_, false) => Ok(format!("set {} ({} + {})", var_name, var_name, value)),
                            }
                        }
                        else { Ok(String::new()) }
                    }
                    x @ ("set patch %s to %s" | "change patch %s by %s") => {
                        let is_set = x.starts_with("set");

                        if script.children.len() != 2 { return Err(Error::InvalidProject); }

                        let var_name = match script.children[0].name.as_str() {
                            "l" => clean_name(&script.children[0].text)?,
                            _ => return Err(Error::InvalidProject),
                        };
                        let value = self.parse_script_recursive(&script.children[1])?;

                        if !var_name.is_empty() && !value.is_empty() {
                            match is_set {
                                true => Ok(format!("set {var} {val}", var = rename_patch_prop(&var_name), val = value)),
                                false => Ok(format!("set {var} ({var} + {val})", var = rename_patch_prop(&var_name), val = value)),
                            }
                        }
                        else { Ok(String::new()) }
                    }
                    "get patch %s" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        match script.children[0].name.as_str() {
                            "l" => Ok(rename_patch_prop(&clean_name(&script.children[0].text)?).into()),
                            _ => Err(Error::NonConstantPatchProp),
                        }
                    }
                    "color %s" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        match script.children[0].name.as_str() {
                            "l" => Ok(clean_name(&script.children[0].text)?),
                            _ => Err(Error::NonConstantColor),
                        }
                    }

                    "doReport" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let value = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("report {}", value))
                    }
                    "setHeading" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        match script.get(&["l", "option"]) {
                            Some(opt) => match opt.text.as_str() {
                                "random" => Ok("set heading (random-float 360)".to_string()),
                                x => return Err(Error::UnknownBlockType(format!("setHeading <{}>", x))),
                            }
                            None => {
                                let val = self.parse_script_recursive(&script.children[0])?;
                                Ok(format!("set heading {}", val))
                            }
                        }
                    }
                    "doFaceTowards" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        match script.get(&["l", "option"]) {
                            Some(opt) => match opt.text.as_str() {
                                "center" => Ok("(facexy 0 0)".to_string()),
                                "mouse-pointer" => Ok("(facexy mouse-xcor mouse-ycor)".to_string()),
                                "random position" => Ok("set heading (random-float 360)".to_string()),
                                x => return Err(Error::UnknownBlockType(format!("doFaceTowards <{}>", x))),
                            }
                            None => {
                                let target = self.parse_script_recursive(&script.children[0])?;
                                Ok(format!("(face {})", target))
                            }
                        }
                    }
                    "forward" | "move %n steps" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let dist = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("(fd {})", dist))
                    }
                    "turn" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let ang = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("(rt {})", ang))
                    }
                    "turnLeft" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let ang = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("(lt {})", ang))
                    }
                    "gotoXY" | "go to x: %n y: %n" => {
                        if script.children.len() != 2 { return Err(Error::InvalidProject); }
                        let x = self.parse_script_recursive(&script.children[0])?;
                        let y = self.parse_script_recursive(&script.children[1])?;
                        Ok(format!("(setxy {} {})", x, y))
                    }
                    "changeXPosition" | "change x by %n" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let delta = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("set xcor (xcor + {})", delta))
                    }
                    "setXPosition" | "set x to %n" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let val = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("set xcor {}", val))
                    }
                    "changeYPosition" | "change y by %n" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let delta = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("set ycor (ycor + {})", delta))
                    }
                    "setYPosition" | "set y to %n" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let val = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("set ycor {}", val))
                    }
                    "reportNewList" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let mut res = String::from("(list");
                        for item in script.children[0].children.iter() {
                            res.push(' ');
                            res += &self.parse_script_recursive(item)?;
                        }
                        res.push(')');
                        Ok(res)
                    }
                    "turtle set %mult%obj" => {
                        let list = surely(script.get(&["list"]))?;
                        match list.children.len() {
                            0 => Ok("no-turtles".into()),
                            _ => {
                                let mut items = Vec::with_capacity(list.children.len());
                                for item in list.children.iter() {
                                    items.push(self.parse_script_recursive(item)?);
                                }
                                Ok(format!("(turtle-set {})", Punctuated(items.iter(), " ")))
                            }
                        }
                    }
                    "nobody" => Ok("nobody".into()),
                    "reportNumbers" => {
                        if script.children.len() != 2 { return Err(Error::InvalidProject); }
                        let low = self.parse_script_recursive(&script.children[0])?;
                        let high = self.parse_script_recursive(&script.children[1])?;
                        Ok(format!("(range {} ({} + 1))", low, high))
                    }
                    "reportListIsEmpty" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let src = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("(empty? {})", src))
                    }
                    "is %l empty? (turtle set)" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let src = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("(not (any? {}))", src))
                    }
                    "random item %l (turtle set)" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let src = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("(one-of {})", src))
                    }
                    "turtles %l within distance %n" => {
                        if script.children.len() != 2 { return Err(Error::InvalidProject); }
                        let agents = self.parse_script_recursive(&script.children[0])?;
                        let distance = self.parse_script_recursive(&script.children[1])?;
                        Ok(format!("({} in-radius {})", agents, distance))
                    }
                    "exclude myself %l" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let src = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("(other {})", src))
                    }
                    x @ ("min %l" | "max %l") => {
                        let is_min = x.starts_with("min");

                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let src = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("({} {})", if is_min { "min" } else { "max" }, src))
                    }
                    x @ ("get one %l with min %repRing" | "get one %l with max %repRing") => {
                        let is_min = x.contains("min");

                        if script.children.len() != 2 { return Err(Error::InvalidProject); }
                        if script.children[1].name != "block" || surely(script.children[1].attr("s"))?.value != "reifyReporter" {
                            return Err(Error::NonConstantCodeBlock);
                        }
                    
                        let agents = self.parse_script_recursive(&script.children[0])?;
                        let expr = self.parse_script_recursive(surely(script.children[1].get(&["autolambda"]))?)?;
                        Ok(format!("({}-one-of {} [{}])", if is_min { "min" } else { "max" }, agents, expr))
                    }
                    "sum %l" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let src = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("(sum {})", src))
                    }
                    "average %l" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let src = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("(mean {})", src))
                    }
                    "doIfElse" => {
                        if script.children.len() != 3 { return Err(Error::InvalidProject); }
                        let condition = self.parse_script_recursive(&script.children[0])?;
                        let case_1 = self.parse_script_recursive(&script.children[1])?;
                        let case_2 = self.parse_script_recursive(&script.children[2])?;
                        Ok(format!("ifelse {} [\n{}\n] [\n{}\n]", condition, indent(&case_1), indent(&case_2)))
                    }
                    "reportIfElse" => {
                        if script.children.len() != 3 { return Err(Error::InvalidProject); }
                        let condition = self.parse_script_recursive(&script.children[0])?;
                        let case_1 = self.parse_script_recursive(&script.children[1])?;
                        let case_2 = self.parse_script_recursive(&script.children[2])?;
                        Ok(format!("(ifelse-value {} [ {} ] [ {} ])", condition, case_1, case_2))
                    }
                    "doForever" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let action = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("loop [\n{}\n]", indent(&action)))
                    }
                    "doRepeat" => {
                        if script.children.len() != 2 { return Err(Error::InvalidProject); }
                        let count = self.parse_script_recursive(&script.children[0])?;
                        let action = self.parse_script_recursive(&script.children[1])?;
                        Ok(format!("repeat {} [\n{}\n]", count, indent(&action)))
                    }
                    "doUntil" => {
                        if script.children.len() != 2 { return Err(Error::InvalidProject); }
                        let condition = self.parse_script_recursive(&script.children[0])?;
                        let action = self.parse_script_recursive(&script.children[1])?;
                        Ok(format!("while [not {}] [\n{}\n]", condition, indent(&action)))
                    }
                    "reportMonadic" => {
                        if script.children.len() != 2 { return Err(Error::InvalidProject); }
                        let arg = self.parse_script_recursive(&script.children[1])?;
                        let op = match script.get(&["l", "option"]) {
                            None => return Err(Error::NonConstantOperator),
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
                            _ => return Err(Error::UnknownBlockType(format!("monadic <{}>", op))),
                        })
                    }
                    "atan x: %n y: %n" => {
                        if script.children.len() != 2 { return Err(Error::InvalidProject); }
                        let x = self.parse_script_recursive(&script.children[0])?;
                        let y = self.parse_script_recursive(&script.children[1])?;
                        Ok(format!("(atan {} {})", x, y))
                    }
                    "reportListItem" | "reportLetter" => {
                        if script.children.len() != 2 { return Err(Error::InvalidProject); }
                        let src = self.parse_script_recursive(&script.children[1])?;
                        match script.get(&["l", "option"]) {
                            None => {
                                let index = self.parse_script_recursive(&script.children[0])?;
                                Ok(format!("(item ({}-1) {})", index, src))
                            }
                            Some(opt) => match opt.text.as_str() {
                                "last" => Ok(format!("(last {})", src)),
                                "any" => Ok(format!("(one-of {})", src)),
                                x => return Err(Error::UnknownBlockType(format!("get item <{}>", x))),
                            }
                        }
                    }
                    "reportListContainsItem" => {
                        if script.children.len() != 2 { return Err(Error::InvalidProject); }
                        let list = self.parse_script_recursive(&script.children[0])?;
                        let val = self.parse_script_recursive(&script.children[1])?;
                        Ok(format!("(member? {} {})", val, list))
                    }
                    "reportConcatenatedLists" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let list = &script.children[0];
                        if list.name != "list" { return Err(Error::InvalidProject); }

                        let mut res = "(sentence".to_string();
                        for item in list.children.iter() {
                            res.push(' ');
                            res += &self.parse_script_recursive(item)?;
                        }
                        res.push(')');
                        Ok(res)
                    }
                    "doIf" => {
                        if script.children.len() != 2 { return Err(Error::InvalidProject); }
                        let condition = self.parse_script_recursive(&script.children[0])?;
                        let then = self.parse_script_recursive(&script.children[1])?;
                        Ok(format!("if {} [\n{}\n]", condition, indent(&then)))
                    }
                    "reportRandom" => {
                        if script.children.len() != 2 { return Err(Error::InvalidProject); }
                        let low = self.parse_script_recursive(&script.children[0])?;
                        let high = self.parse_script_recursive(&script.children[1])?;

                        if low == "0" { Ok(format!("(random {})", high)) }
                        else { Ok(format!("((floor {}) + random ({} - {}))", low, high, low)) }
                    }
                    "random float %s %s" => {
                        if script.children.len() != 2 { return Err(Error::InvalidProject); }
                        let low = self.parse_script_recursive(&script.children[0])?;
                        let high = self.parse_script_recursive(&script.children[1])?;

                        if low == "0" { Ok(format!("(random-float {})", high)) }
                        else { Ok(format!("({} + random-float ({} - {}))", low, high, low)) }
                    }
                    "reportListLength" | "reportStringSize" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let src = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("(length {})", src))
                    }
                    "reportRound" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        let val = self.parse_script_recursive(&script.children[0])?;
                        Ok(format!("(round {})", val))
                    }
                    "reportBoolean" => {
                        if script.children.len() != 1 { return Err(Error::InvalidProject); }
                        match script.get(&["l", "bool"]) {
                            None => Err(Error::NonConstantOperator),
                            Some(x) => Ok(x.text.clone()),
                        }
                    }
                    "reportEquals" => self.parse_bin_op_recursive("=", script),
                    "reportLessThan" => self.parse_bin_op_recursive("<", script),
                    "reportGreaterThan" => self.parse_bin_op_recursive(">", script),
                    "reportAnd" => self.parse_bin_op_recursive("and", script),
                    "reportOr" => self.parse_bin_op_recursive("or", script),
                    "%b xor %b" => self.parse_bin_op_recursive("xor", script),
                    "reportSum" => self.parse_bin_op_recursive("+", script),
                    "reportDifference" => self.parse_bin_op_recursive("-", script),
                    "reportProduct" => self.parse_bin_op_recursive("*", script),
                    "reportQuotient" => self.parse_bin_op_recursive("/", script),
                    "reportModulus" => self.parse_bin_op_recursive("mod", script),
                    "reportPower" => self.parse_bin_op_recursive("^", script),
                    "reportNot" => self.parse_unary_op_recursive("not", script),
                    
                    x => match self.functions.get(x) {
                        None => Err(Error::UnknownBlockType(x.to_string())),
                        Some(func) => {
                            let mut items = vec![func.name.clone()];
                            for param in script.children.iter() {
                                let val = self.parse_script_recursive(param)?;
                                items.push(val);
                            }

                            Ok(if items.len() == 1 { items.into_iter().next().unwrap() } else { format!("({})", Punctuated(items.iter(), " ")) })
                        }
                    }
                }
            }
            "l" => Ok(if NUMBER_REGEX.is_match(&script.text) { script.text.clone() } else { format!("\"{}\"", script.text) }),
            x => Err(Error::UnknownBlockType(x.to_string())),
        }
    }
}
impl Display for Program {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let true_globals: Vec<_> = self.globals.iter().filter(|g| !self.metadata.gui_vars.contains(g.as_str())).collect();
        if !true_globals.is_empty() {
            writeln!(f, "globals [ {} ]\n", Punctuated(true_globals.iter(), ", "))?;
        }

        for breed in self.entities.values() {
            if breed.plural == "patches" { continue }
            let singular = self.metadata.breed_singulars.get(breed.plural.as_str());
            writeln!(f, "breed [ {} {} ]", breed.plural, singular.unwrap_or(&format!("a-{}", breed.plural)))?;
        }
        writeln!(f)?;

        let breeds = self.entities.values().filter(|s| s.plural != "patches");
        let all_breed_props: HashSet<&str> = breeds.clone().flat_map(|s| s.props.keys().map(|s| s.as_str())).collect();
        let common_props: LinkedHashMap<&str, ()> = all_breed_props.iter().copied().filter(|&s| breeds.clone().all(|b| b.props.contains_key(s))).map(|s| (s, ())).collect();

        if !common_props.is_empty() {
            writeln!(f, "turtles-own [ {} ]", Punctuated(common_props.keys(), " "))?;
        }

        let mut patches = None;
        for (breed_name, breed) in self.entities.iter() {
            if breed.props.is_empty() { continue } // must happen before patches check, since we want to ignore empty patch props
            if breed_name == "patches" { patches = Some(breed); continue }

            let props: Vec<_> = breed.props.keys().filter(|p| !common_props.contains_key(p.as_str())).collect();
            if !props.is_empty() { writeln!(f, "{}-own [ {} ]", breed_name, Punctuated(props.iter(), " "))?; }
        }
        writeln!(f)?;

        if let Some(patches) = patches {
            writeln!(f, "patches-own [ {} ]\n", Punctuated(patches.props.keys(), " "))?;
        }

        for func in self.functions.values() {
            writeln!(f, "{}\n", func.formatted.as_ref().expect("should have formatted all functions by now"))?;
        }

        Ok(())
    }
}

fn parse_function_header(program: &mut Program, block: &Xml) -> Result<(), Error> {
    let t = surely(block.attr("s"))?.value.as_str();
    assert!(!t.starts_with('%'));
    
    let meta_name = PARAM_FINDER.replace_all(t, "%s").into_owned();

    let stop_pos = t.find('%').unwrap_or(t.len());
    let name = clean_name(t[..stop_pos].trim())?;

    let reports = match surely(block.attr("type"))?.value.as_str() {
        "command" => false,
        "reporter" | "predicate" => true,
        _ => return Err(Error::InvalidProject),
    };

    let mut params: Vec<String> = vec![];
    for cap in PARAM_FINDER.captures_iter(t) {
        params.push(clean_name(&cap[1])?);
    }

    program.functions.insert(meta_name, Function { name, params, reports, formatted: None });
    Ok(())
}
fn parse_function_body(program: &mut Program, block: &Xml) -> Result<(), Error> {
    let t = surely(block.attr("s"))?.value.as_str();
    assert!(!t.starts_with('%'));
    let meta_name = PARAM_FINDER.replace_all(t, "%s").into_owned();

    let action = match block.get(&["script"]) {
        None => String::new(),
        Some(script) => indent(&program.parse_script_recursive(script)?),
    };

    let body = {
        let info = program.functions.get(&meta_name).expect("should have already parsed the header");
        match info.params.is_empty() {
            true => format!("{} {}\n{}\nend", if info.reports { "to-report" } else { "to" }, info.name, action),
            false => format!("{} {} [{}]\n{}\nend", if info.reports { "to-report" } else { "to" }, info.name, Punctuated(info.params.iter(), " "), action),
        }
    };

    program.functions.get_mut(&meta_name).unwrap().formatted = Some(body);
    Ok(())
}
fn parse_sprite(program: &mut Program, sprite: &Xml) -> Result<(), Error> {
    let plural = clean_name(&surely(sprite.attr("name"))?.value)?;

    let mut props = LinkedHashMap::new();
    for var in surely(sprite.get(&["variables"]))?.children.iter() {
        let name = clean_name(&surely(var.attr("name"))?.value)?;
        if props.insert(name, ()).is_some() { return Err(Error::InvalidProject); }
    }

    let entity = Entity { plural: plural.clone(), props };
    if program.entities.insert(plural.clone(), entity).is_some() {
        return Err(Error::SpritesWithSameName(plural));
    }

    Ok(())
}
fn parse_project(room: &Xml) -> Result<String, Error> {
    let mut program = Program::default();

    // make sure we have a valid room setup (multiple rooms is for networking, which we don't support)
    match room.children.iter().filter(|x| x.name == "role").count() {
        0 => return Err(Error::InvalidProject),
        1 => (),
        _ => return Err(Error::MultipleRoles),
    }

    let sprites = surely(room.get(&["role", "project", "stage", "sprites"]))?;
    for sprite in sprites.children.iter() {
        parse_sprite(&mut program, sprite)?;
    }

    // vars must be done after sprites so that sprite names aren't made into globals
    let vars = surely(room.get(&["role", "project", "variables"]))?;
    for var in vars.children.iter() {
        let name = clean_name(&surely(var.attr("name"))?.value)?;
        if !GLOBAL_SCOPE.contains(name.as_str()) && !FALSE_GLOBAL_SCOPE.contains(name.as_str()) && !program.entities.contains_key(&name) {
            program.globals.push(name);
        }
    }

    let blocks = surely(room.get(&["role", "project", "blocks"]))?;
    for block in blocks.children.iter() {
        let t = surely(block.attr("s"))?.value.as_str();
        if t == "__meta" {
            let js = surely(block.get(&["script", "block", "block", "block", "l"]))?.text.trim();
            if !js.starts_with("return") || !js.ends_with(';') { return Err(Error::InvalidProject) }
            program.metadata = match serde_json::from_str(&js[6..js.len()-1]) {
                Ok(v) => v,
                Err(_) => return Err(Error::InvalidProject),
            };
            continue
        }
        else if BUILTIN_BLOCKS.contains(t) { continue }
        parse_function_header(&mut program, block)?;
    }
    for block in blocks.children.iter() {
        let t = surely(block.attr("s"))?.value.as_str();
        if t == "__meta" || BUILTIN_BLOCKS.contains(t) { continue }
        parse_function_body(&mut program, block)?;
    }

    Ok(program.to_string())
}

/// Parses a NetsBlox project xml file into Netlogo source.
pub fn parse<R: Read>(xml: R) -> Result<String, Error> {
    let mut xml = EventReader::new(xml);
    while let Ok(e) = xml.next() {
        if let XmlEvent::StartElement { name, attributes, .. } = e {
            if name.local_name != "room" { continue }

            let room = parse_xml_root(&mut xml, name, attributes)?;
            return parse_project(&room);
        }
    }
    Err(Error::InvalidProject)
}