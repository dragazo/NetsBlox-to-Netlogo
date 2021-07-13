mod ast;

use std::collections::{BTreeSet, BTreeMap, HashSet, HashMap};
use linked_hash_map::LinkedHashMap;

use std::cell::RefCell;
use std::rc::Rc;
use std::fmt::Write;
use std::f32::consts as f32c;
use std::f64::consts as f64c;
use std::iter;

use crate::common::*;
use crate::util::*;
use ast::*;
pub use ast::{Ident, Span};

use lalrpop_util::{ParseError, lexer::Token};

use xml::escape::escape_str_attribute as escape_xml;

const BASE_SPRITE_SCALE: f64 = 0.5;

lazy_static! {
    static ref GLOBAL_SCOPE_IDENTS: Vec<Ident> = GLOBAL_SCOPE.iter().map(|&s| Ident { id: s.into(), raw_span: Span(0, 0) }).collect();
    static ref SUGGESTIONS: HashMap<&'static str, &'static str> = parse_ws_pairs(include_str!("suggestions.txt"));
    static ref READONLY_BUILTINS: HashMap<&'static str, &'static str> = parse_ws_rest(include_str!("readonly-builtins.txt"));
    static ref BUILTIN_PATCH_PROPS: HashSet<&'static str> = parse_idents(include_str!("builtin-patch-props.txt"));
}

fn rename_patch_prop(prop: &str) -> &str {
    NL2NB_PATCH_PROP_RENAMES.get(prop).copied().unwrap_or(prop)
}

fn get_func_def_name<'b>(func: &Function) -> Result<String, Error<'b>> {
    if let Some(bad) = iter::once(&func.name).chain(&func.params).find(|s| s.id.contains('\'')) {
        return Err(Error::FuncHeaderHadApos { func: func.name.clone(), name: bad.clone() });
    }

    let mut res = func.name.id.clone();
    for param in func.params.iter() {
        write!(res, " %'{}'", param.id).unwrap();
    }
    Ok(escape_xml(&res).into_owned())
}
fn get_func_name(func: &Function) -> String {
    let mut res = String::with_capacity(func.name.id.len() + 3 * func.params.len());
    res.clone_from(&func.name.id);
    for _ in 0..func.params.len() {
        res += " %s";
    }
    escape_xml(&res).into_owned()
}

#[derive(Debug)]
pub enum Error<'a> {
    Parse(ParseError<usize, Token<'a>, &'a str>),
    FuncHeaderHadApos { func: Ident, name: Ident },

    Redefine { name: Ident, previous: Ident },
    RedefineBuiltin { name: Ident },

    ExpectedSingular { name: Ident },
    ExpectedPlural { name: Ident },
    BreedNotDefined { name: Ident },
    VariableNoTDefined { name: Ident },
    FunctionNotDefined { name: Ident, suggested: Option<&'static str> },

    AssignToReadonlyVar { name: Ident },
    
    InvalidColor { color_span: Span },

    FunctionArgCount { func: Ident, invoke_span: Span, got: usize, expected: usize, is_builtin: bool },
    NonReporterInExpr { func: Ident, invoke_span: Span, is_builtin: bool },
    ReporterValueDiscarded { func: Ident, invoke_span: Span, is_builtin: bool },

    ReportInNonReporter { func: Ident, report_span: Span },
    UnreachableCode { func: Ident, unreachable_span: Span },

    MissingRequiredFunc { name: &'static str, reports: bool, params: &'static [&'static str] },
}
impl<'a> From<ParseError<usize, Token<'a>, &'a str>> for Error<'a> {
    fn from(e: ParseError<usize, Token<'a>, &'a str>) -> Self {
        Error::Parse(e)
    }
}

enum StorageLocation {
    Builtin { get: &'static str, set: Option<(&'static str, &'static str)> },
    Lexical, Property, PatchesProp,

    BuiltinColor,
}

#[derive(Default)]
struct EntityInfo<'a> { props: BTreeMap<&'a str, &'a Ident> } // btree so we get sorted order

struct GlobalSymbol<'a> { ident: &'a Ident }
struct BreedSymbol<'a> { ident: &'a Ident, is_plural: bool, info: Rc<RefCell<EntityInfo<'a>>> }

#[derive(Default)]
pub struct Program<'a> {
    globals: LinkedHashMap<&'a str, GlobalSymbol<'a>>,
    breeds: LinkedHashMap<&'a str, BreedSymbol<'a>>,
    funcs: LinkedHashMap<&'a str, &'a Function>,
    patches: EntityInfo<'a>,

    all_breed_props: HashMap<&'a str, &'a Ident>,
}
impl<'a> Program<'a> {
    // checks for validity in (only) the global scope
    fn validate_define_global<'b>(&self, ident: &Ident) -> Result<(), Error<'b>> {
        let id = ident.id.as_str();
        let prev = self.globals.get(id).map(|s| s.ident)
            .or(self.breeds.get(id).map(|s| s.ident))
            .or(self.funcs.get(id).map(|s| &s.name))
            .or(self.patches.props.get(id).copied())
            .or(self.all_breed_props.get(id).copied());
        if let Some(prev) = prev {
            return Err(Error::Redefine { name: ident.clone(), previous: prev.clone() });
        }
        if RESERVED_WORDS.contains(id) {
            return Err(Error::RedefineBuiltin { name: ident.clone() });
        }
        Ok(())
    }
    fn validate_define_lexical<'b>(&self, ident: &Ident, scopes: &[LinkedHashMap<&str, &Ident>]) -> Result<(), Error<'b>> {
        for scope in scopes.iter().rev() {
            if let Some(&prev) = scope.get(ident.id.as_str()) {
                return Err(Error::Redefine { name: ident.clone(), previous: prev.clone() });
            }
        }
        self.validate_define_global(ident)
    }
    fn find_var<'b>(&self, scopes: &[LinkedHashMap<&str, &Ident>], ident: &Ident) -> Result<StorageLocation, Error<'b>> {
        let id = ident.id.as_str();
        for scope in scopes.iter().rev() {
            if scope.contains_key(id) { return Ok(StorageLocation::Lexical) }
        }
        if self.globals.contains_key(id) { return Ok(StorageLocation::Lexical) }
        if self.all_breed_props.contains_key(id) { return Ok(StorageLocation::Property) }
        if BUILTIN_PATCH_PROPS.contains(id) || self.patches.props.contains_key(id) { return Ok(StorageLocation::PatchesProp) }
        if let Some(get) = READONLY_BUILTINS.get(id) { return Ok(StorageLocation::Builtin { get, set: None }) }

        // the rest are more annoying to do as standard files
        Ok(match id {
            "heading" => StorageLocation::Builtin { get: r#"<block s="direction"></block>"#, set: Some((r#"<block s="setHeading">"#, "</block>")) },
            "size" => StorageLocation::Builtin { get: r#"<custom-block s="scale"></custom-block>"#, set: Some((r#"<custom-block s="set scale to %n x">"#, "</custom-block>")) },
            "color" => StorageLocation::BuiltinColor,
            _ => return Err(Error::VariableNoTDefined { name: ident.clone() }),
        })
    }
    fn ensure_breed_defined<'b>(&self, ident: &Ident, should_be_plural: Option<bool>) -> Result<(), Error<'b>> {
        let breed = match self.breeds.get(ident.id.as_str()) {
            None => return Err(Error::BreedNotDefined { name: ident.clone() }),
            Some(b) => b,
        };
        if let Some(should_be_plural) = should_be_plural {
            match (breed.is_plural, should_be_plural) {
                (true, true) | (false, false) => (),
                (true, false) => return Err(Error::ExpectedSingular { name: ident.clone() }),
                (false, true) => return Err(Error::ExpectedPlural { name: ident.clone() }),
            }
        }
        Ok(())
    }
    fn format_func_call<'b>(&self, script: &mut String, scopes: &mut Vec<LinkedHashMap<&str, &Ident>>, call: &FnCall, in_expr: bool) -> Result<(), Error<'b>> {
        fn check_usage<'b>(call: &FnCall, func: Option<&Function>, reports: bool, in_expr: bool, expected_args: Option<usize>) -> Result<(), Error<'b>> {
            debug_assert!(func.is_none() || func.unwrap().reports == reports);
            debug_assert!(func.is_none() || expected_args.is_none() || func.unwrap().params.len() == expected_args.unwrap());
            let target = func.map(|f| &f.name).unwrap_or(&call.name);
            let is_builtin = func.is_none();

            match (reports, in_expr) {
                (true, true) | (false, false) => (),
                (true, false) => return Err(Error::ReporterValueDiscarded { func: target.clone(), invoke_span: call.span(), is_builtin }),
                (false, true) => return Err(Error::NonReporterInExpr { func: target.clone(), invoke_span: call.span(), is_builtin }),
            }
            if let Some(expected) = expected_args {
                if call.args.len() != expected { return Err(Error::FunctionArgCount { func: target.clone(), invoke_span: call.span(), got: call.args.len(), expected, is_builtin }) }
            }
            Ok(())
        }
        match call.name.id.as_str() {
            "tick" => {
                check_usage(call, None, false, in_expr, Some(0))?;
                *script += r#"<block s="doChangeVar"><l>ticks</l><l>1</l></block>"#;
            }
            "reset-ticks" | "clear-ticks" => {
                check_usage(call, None, false, in_expr, Some(0))?;
                *script += r#"<block s="doSetVar"><l>ticks</l><l>0</l></block>"#;
            }
            "clear-turtles" => {
                check_usage(call, None, false, in_expr, Some(0))?;
                *script += r#"<custom-block s="delete all clones"></custom-block>"#;
            }
            "clear-patches" => {
                check_usage(call, None, false, in_expr, Some(0))?;
                *script += r#"<custom-block s="reset patches"></custom-block>"#;
            }
            "clear-globals" => {
                check_usage(call, None, false, in_expr, Some(0))?;
                *script += r#"<custom-block s="reset global variables"></custom-block>"#;
            }
            "clear-all" => {
                check_usage(call, None, false, in_expr, Some(0))?;
                *script += r#"<custom-block s="reset everything"></custom-block>"#;
            }
            "die" => {
                check_usage(call, None, false, in_expr, Some(0))?;
                *script += r#"<block s="removeClone"></block>"#;
            }
            "forward" | "fd" => {
                check_usage(call, None, false, in_expr, Some(1))?;
                *script += r#"<custom-block s="move %n steps">"#;
                self.generate_expr_script(script, scopes, &call.args[0])?;
                *script += "</custom-block>";
            }
            x @ ("right" | "rt" | "left" | "lt") => {
                check_usage(call, None, false, in_expr, Some(1))?;
                *script += if x.starts_with("r") { r#"<block s="turn">"# } else { r#"<block s="turnLeft">"# };
                self.generate_expr_script(script, scopes, &call.args[0])?;
                *script += "</block>";
            }
            "random" => {
                check_usage(call, None, true, in_expr, Some(1))?;
                *script += r#"<custom-block s="pick random 0 up to %n">"#;
                self.generate_expr_script(script, scopes, &call.args[0])?;
                *script += "</custom-block>";
            }
            "random-float" => {
                check_usage(call, None, true, in_expr, Some(1))?;
                *script += r#"<custom-block s="pick random float %n">"#;
                self.generate_expr_script(script, scopes, &call.args[0])?;
                *script += "</custom-block>";
            }
            "setxy" => {
                check_usage(call, None, false, in_expr, Some(2))?;
                *script += r#"<block s="gotoXY">"#;
                self.generate_expr_script(script, scopes, &call.args[0])?;
                self.generate_expr_script(script, scopes, &call.args[1])?;
                *script += "</block>";
            }
            x => match self.funcs.get(x) {
                None => return Err(Error::FunctionNotDefined { name: call.name.clone(), suggested: SUGGESTIONS.get(x).copied() }),
                Some(func) => {
                    check_usage(call, Some(func), func.reports, in_expr, Some(func.params.len()))?;

                    write!(script, r#"<custom-block s="{}">"#, get_func_name(func)).unwrap();
                    for arg in call.args.iter() {
                        self.generate_expr_script(script, scopes, arg)?;
                    }
                    *script += "</custom-block>";
                }
            }
        }
        Ok(())
    }
    fn generate_expr_script<'b>(&self, script: &mut String, scopes: &mut Vec<LinkedHashMap<&str, &Ident>>, expr: &Expr) -> Result<(), Error<'b>> {
        match expr {
            Expr::Choice { condition, a, b, .. } => { *script += r#"<block s="reportIfElse">"#; self.generate_expr_script(script, scopes, condition)?; self.generate_expr_script(script, scopes, a)?; self.generate_expr_script(script, scopes, b)?; *script += "</block>" }

            Expr::And { a, b, .. } => { *script += r#"<block s="reportAnd">"#; self.generate_expr_script(script, scopes, a)?; self.generate_expr_script(script, scopes, b)?; *script += "</block>"; }
            Expr::Or { a, b, .. } => { *script += r#"<block s="reportOr">"#; self.generate_expr_script(script, scopes, a)?; self.generate_expr_script(script, scopes, b)?; *script += "</block>"; }
            Expr::Xor { a, b, .. } => { *script += r#"<custom-block s="%b xor %b">"#; self.generate_expr_script(script, scopes, a)?; self.generate_expr_script(script, scopes, b)?; *script += "</custom-block>"; }

            Expr::Equ { a, b, .. } => { *script += r#"<block s="reportEquals">"#; self.generate_expr_script(script, scopes, a)?; self.generate_expr_script(script, scopes, b)?; *script += "</block>"; }
            Expr::Neq { a, b, .. } => { *script += r#"<block s="reportNot"><block s="reportEquals">"#; self.generate_expr_script(script, scopes, a)?; self.generate_expr_script(script, scopes, b)?; *script += "</block></block>"; }
            
            Expr::Less { a, b, .. } => { *script += r#"<block s="reportLessThan">"#; self.generate_expr_script(script, scopes, a)?; self.generate_expr_script(script, scopes, b)?; *script += "</block>"; }
            Expr::LessEq { a, b, .. } => { *script += r#"<block s="reportNot"><block s="reportGreaterThan">"#; self.generate_expr_script(script, scopes, a)?; self.generate_expr_script(script, scopes, b)?; *script += "</block></block>"; }
            Expr::Great { a, b, .. } => { *script += r#"<block s="reportGreaterThan">"#; self.generate_expr_script(script, scopes, a)?; self.generate_expr_script(script, scopes, b)?; *script += "</block>"; }
            Expr::GreatEq { a, b, .. } => { *script += r#"<block s="reportNot"><block s="reportLessThan">"#; self.generate_expr_script(script, scopes, a)?; self.generate_expr_script(script, scopes, b)?; *script += "</block></block>"; }

            Expr::Add { a, b, .. } => { *script += r#"<block s="reportSum">"#; self.generate_expr_script(script, scopes, a)?; self.generate_expr_script(script, scopes, b)?; *script += "</block>"; }
            Expr::Sub { a, b, .. } => { *script += r#"<block s="reportDifference">"#; self.generate_expr_script(script, scopes, a)?; self.generate_expr_script(script, scopes, b)?; *script += "</block>"; }
            
            Expr::Mul { a, b, .. } => { *script += r#"<block s="reportProduct">"#; self.generate_expr_script(script, scopes, a)?; self.generate_expr_script(script, scopes, b)?; *script += "</block>"; }
            Expr::Div { a, b, .. } => { *script += r#"<block s="reportQuotient">"#; self.generate_expr_script(script, scopes, a)?; self.generate_expr_script(script, scopes, b)?; *script += "</block>"; }
            Expr::Mod { a, b, .. } => { *script += r#"<block s="reportModulus">"#; self.generate_expr_script(script, scopes, a)?; self.generate_expr_script(script, scopes, b)?; *script += "</block>"; }
            
            Expr::Pow { a, b, .. } => { *script += r#"<block s="reportPower">"#; self.generate_expr_script(script, scopes, a)?; self.generate_expr_script(script, scopes, b)?; *script += "</block>"; }
            
            Expr::Not { val, .. } => { *script += r#"<block s="reportNot">"#; self.generate_expr_script(script, scopes, val)?; *script += "</block>"; }
            Expr::Neg { val, .. } => { *script += r#"<block s="reportMonadic"><l><option>neg</option></l>"#; self.generate_expr_script(script, scopes, val)?; *script += "</block>"; }

            Expr::FnCall(call) => self.format_func_call(script, scopes, call, true)?,

            Expr::Value(Value::Number(num)) => write!(script, "<l>{}</l>", escape_xml(&num.value)).unwrap(),
            Expr::Value(Value::Text(text)) => write!(script, "<l>{}</l>", escape_xml(&text.content)).unwrap(),
            Expr::Value(Value::List(list)) => {
                *script += r#"<block s="reportNewList"><list>"#;
                for value in &list.values {
                    self.generate_expr_script(script, scopes, value)?;
                }
                *script += "</list></block>";
            }
            Expr::Value(Value::Ident(ident)) => match ident.id.as_str() {
                x @ ("true" | "false") => write!(script, r#"<block s="reportBoolean"><l><bool>{}</bool></l></block>"#, x).unwrap(),
                _ => match self.find_var(&*scopes, ident)? {
                    StorageLocation::Lexical | StorageLocation::Property => write!(script, r#"<block var="{}"/>"#, escape_xml(&ident.id)).unwrap(),
                    StorageLocation::PatchesProp => write!(script, r#"<custom-block s="get patch %s"><l>{}</l></custom-block>"#, escape_xml(rename_patch_prop(&ident.id))).unwrap(),
                    StorageLocation::Builtin { get, .. } => *script += get,
                    StorageLocation::BuiltinColor => *script += r#"<custom-block s="pen color"></custom-block>"#,
                }
            }
        }
        Ok(())
    }
    fn generate_script<'b>(&self, script: &mut String, scopes: &mut Vec<LinkedHashMap<&'a str, &'a Ident>>, stmts: &'a [Stmt], func: &Function) -> Result<(), Error<'b>> {
        scopes.push(Default::default()); // generate a new scope for this script

        let mut has_terminated = false;

        for stmt in stmts {
            if has_terminated { return Err(Error::UnreachableCode { func: func.name.clone(), unreachable_span: stmt.span() }) }
            match stmt {
                Stmt::Report(report) => {
                    if !func.reports { return Err(Error::ReportInNonReporter { func: func.name.clone(), report_span: report.span() }) }

                    *script += r#"<block s="doReport">"#;
                    self.generate_expr_script(script, scopes, &report.value)?;
                    *script += "</block>";

                    has_terminated = true;
                }
                Stmt::IfElse(ifelse) => {
                    *script += if ifelse.otherwise.is_none() { r#"<block s="doIf">"# } else { r#"<block s="doIfElse">"# };
                    self.generate_expr_script(script, scopes, &ifelse.condition)?;
                    *script += "<script>";
                    self.generate_script(script, scopes, &ifelse.then, func)?;
                    if let Some(otherwise) = &ifelse.otherwise {
                        *script += "</script><script>";
                        self.generate_script(script, scopes, otherwise, func)?;
                    }
                    *script += "</script></block>";
                }
                Stmt::FnCall(call) => self.format_func_call(script, scopes, call, false)?,
                Stmt::VarDecl(vardecl) => {
                    self.validate_define_lexical(&vardecl.name, scopes)?; // check if the name is valid before we do anything else
                    
                    write!(script, r#"<custom-block s="script variable %upvar = %s"><l>{}</l>"#, escape_xml(&vardecl.name.id)).unwrap();
                    self.generate_expr_script(script, scopes, &vardecl.value)?;
                    *script += "</custom-block>";

                    scopes.last_mut().unwrap().insert(&vardecl.name.id, &vardecl.name); // add the symbol after evaluating to prevent self-dependency
                }
                Stmt::Assign(assign) => match self.find_var(scopes, &assign.name)? {
                    StorageLocation::Lexical | StorageLocation::Property => {
                        write!(script, r#"<block s="doSetVar"><l>{}</l>"#, escape_xml(&assign.name.id)).unwrap();
                        self.generate_expr_script(script, scopes, &assign.value)?;
                        *script += "</block>";
                    }
                    StorageLocation::PatchesProp => {
                        write!(script, r#"<custom-block s="set patch %s to %s"><l>{}</l>"#, escape_xml(rename_patch_prop(&assign.name.id))).unwrap();
                        self.generate_expr_script(script, scopes, &assign.value)?;
                        *script += "</custom-block>";
                    }
                    StorageLocation::Builtin { set, .. } => match set {
                        Some(set) => {
                            *script += set.0;
                            self.generate_expr_script(script, scopes, &assign.value)?;
                            *script += set.1;
                        }
                        None => return Err(Error::AssignToReadonlyVar { name: assign.name.clone() }),
                    }
                    StorageLocation::BuiltinColor => {
                        let is_general = match &assign.value {
                            Expr::Value(Value::List(list)) => match list.values.as_slice() {
                                [Expr::Value(Value::Number(r)), Expr::Value(Value::Number(g)), Expr::Value(Value::Number(b))] => {
                                    write!(script, r#"<block s="setColor"><color>{},{},{},1</color></block>"#, r.value, g.value, b.value).unwrap();
                                    false
                                }
                                [_, _, _] => true,
                                _ => return Err(Error::InvalidColor { color_span: assign.value.span() }), // not three values
                            }
                            _ => true,
                        };
                        if is_general {
                            *script += r#"<custom-block s="set pen color to %l">"#;
                            self.generate_expr_script(script, scopes, &assign.value)?;
                            *script += "</custom-block>";
                        }
                    }
                }
                Stmt::Repeat(repeat) => {
                    *script += r#"<block s="doRepeat">"#;
                    self.generate_expr_script(script, scopes, &repeat.count)?;
                    *script += "<script>";
                    self.generate_script(script, scopes, &repeat.stmts, func)?;
                    *script += "</script></block>";
                }
                Stmt::Create(create) => {
                    self.ensure_breed_defined(&create.breed_plural, Some(true))?;
                    *script += r#"<custom-block s="tell %l to %cs">"#;
                    *script += if create.ordered { r#"<custom-block s="%n new %s (ordered)">"# } else { r#"<custom-block s="%n new %s">"# };
                    self.generate_expr_script(script, scopes, &create.count)?;
                    write!(script, r#"<l>{}</l></custom-block><script>"#, escape_xml(&create.breed_plural.id)).unwrap();
                    self.generate_script(script, scopes, &create.stmts, func)?;
                    *script += "</script></custom-block>";
                }
                Stmt::Ask(ask) => {
                    *script += r#"<custom-block s="tell %l to %cs">"#;
                    self.generate_expr_script(script, scopes, &ask.agents)?;
                    *script += r#"<script>"#;
                    self.generate_script(script, scopes, &ask.stmts, func)?;
                    *script += "</script></custom-block>";
                }
                Stmt::Hatch(hatch) => {
                    *script += r#"<custom-block s="tell %l to %cs"><custom-block s="%n clones">"#;
                    self.generate_expr_script(script, scopes, &hatch.count)?;
                    *script += r#"</custom-block><script>"#;
                    self.generate_script(script, scopes, &hatch.stmts, func)?;
                    *script += "</script></custom-block>";
                }
            }
        }

        scopes.pop(); // remove the scope we created
        Ok(())
    }
    fn init_global<'b>(items: &[Item]) -> Result<Program, Error<'b>> {
        let mut program = Program::default();
        let mut owns: Vec<&Own> = Vec::with_capacity(16);

        // initial pass - collect all the globals, breeds, and functions (names at global scope)
        for item in items {
            match item {
                Item::Globals(Globals { idents, .. }) => for ident in idents {
                    program.validate_define_global(ident)?;
                    assert!(program.globals.insert(&ident.id, GlobalSymbol { ident }).is_none());
                }
                Item::Breed(Breed { plural, singular, .. }) => {
                    let info = Rc::new(RefCell::new(EntityInfo::default()));
                    for (ident, is_plural) in [(plural, true), (singular, false)] {
                        program.validate_define_global(&ident)?;
                        assert!(program.breeds.insert(&ident.id, BreedSymbol { ident, is_plural, info: info.clone() }).is_none());
                    }
                }
                Item::Function(func) => {
                    program.validate_define_global(&func.name)?;
                    assert!(program.funcs.insert(&func.name.id, func).is_none());
                }
                Item::Own(own) => match own.plural_owner.id.as_str() {
                    "patches" => owns.insert(0, own), // patches-own needs to come first for breed prop name conflict deduction
                    _ => owns.push(own), // just gather these up for after the first pass
                }
            }
        }
        // process all the own drectives we stored
        for own in owns {
            fn add_props<'a, 'b>(target: &mut BTreeMap<&'a str, &'a Ident>, props: &'a [Ident]) -> Result<(), Error<'b>> {
                for prop in props {
                    if let Some(prev) = target.insert(&prop.id, prop) {
                        return Err(Error::Redefine { name: prop.clone(), previous: prev.clone() })
                    }
                }
                Ok(())
            }
            
            for prop in own.props.iter() {
                program.validate_define_global(prop)?; // validate the names once up-front
            }
            match own.plural_owner.id.as_str() {
                "turtles" => for target in program.breeds.values().filter(|s| s.is_plural) {
                    add_props(&mut target.info.borrow_mut().props, &own.props)?;
                },
                "patches" => add_props(&mut program.patches.props, &own.props)?,
                "turtle" | "patch" => return Err(Error::ExpectedPlural { name: own.plural_owner.clone() }),
                x => match program.breeds.get(x) {
                    None => return Err(Error::BreedNotDefined { name: own.plural_owner.clone() }),
                    Some(target) => {
                        if !target.is_plural { return Err(Error::ExpectedPlural { name: own.plural_owner.clone() }) }
                        add_props(&mut target.info.borrow_mut().props, &own.props)?;
                    }
                }
            }
        }
        // gather up all the owns into one set for storage location resolution
        for breed in program.breeds.values() {
            program.all_breed_props.extend(breed.info.borrow().props.iter());
        }

        Ok(program) // we're now in a semi-valid state (at least at the global scope)
    }
}

fn parse_breed_sprite<'b>(breed_sprites: &mut String, breed: &BreedSymbol, index: (usize, usize)) -> Result<(), Error<'b>> {
    assert!(breed.is_plural);
    let ang = 2.0 * f64c::PI * (index.0 as f64 / index.1 as f64);
    let radius = if index.1 >= 2 { 100.0 } else { 0.0 };
    let color = HSV::new(ang as f32 * 180.0 / f32c::PI, 0.5, 0.9).to_rgb().to_inner();

    let escaped_name = escape_xml(&breed.ident.id);
    write!(breed_sprites, r#"<sprite name="{name}" x="{x}" y="{y}" heading="{heading}" hidden="true" color="{color}" pen="middle" scale="{scale}"><blocks></blocks><variables>"#,
        name = escaped_name,
        x = ang.sin() * radius,
        y = ang.cos() * radius,
        heading = ang * 180.0 / f64c::PI,
        scale = BASE_SPRITE_SCALE,
        color = Punctuated([color.0, color.1, color.2].iter(), ",")).unwrap();
    for var in breed.info.borrow().props.keys() {
        write!(breed_sprites, r#"<variable name="{}"><l>0</l></variable>"#, escape_xml(var)).unwrap();
    }

    *breed_sprites += "</variables><scripts>";
    
    *breed_sprites += r#"<script x="20" y="20"><block s="receiveMessage"><l>delete</l></block><block s="removeClone"></block></script>"#;

    *breed_sprites += "</scripts></sprite>";

    Ok(())
}
fn parse_function<'a, 'b>(custom_blocks: &mut String, program: &Program<'a>, scopes: &mut Vec<LinkedHashMap<&'a str, &'a Ident>>, func: &'a Function) -> Result<(), Error<'b>> {
    assert_eq!(scopes.len(), 1); // should just have the global scope
    scopes.push(Default::default()); // add a new scope for the function parameters

    write!(custom_blocks, r#"<block-definition s="{}" type="{}" category="custom"><inputs>{}</inputs>"#,
        get_func_def_name(func)?, if func.reports { "reporter" } else { "command" },
        r#"<input type="%s"></input>"#.repeat(func.params.len())).unwrap();

    for param in func.params.iter() {
        program.validate_define_lexical(param, &scopes)?;
        assert!(scopes.last_mut().unwrap().insert(&param.id, param).is_none());
    }
    let mut script = String::new();
    program.generate_script(&mut script, scopes, &func.stmts, &func)?;
    if !script.is_empty() { // if we generate an empty <script> tag here, it makes the block uneditable in NetsBlox
        write!(custom_blocks, "<script>{}</script>", script).unwrap();
    }

    write!(custom_blocks, "</block-definition>").unwrap();

    scopes.pop(); // remove the scope we added
    Ok(())
}
fn ensure_has_required_func<'b>(program: &Program, name: &'static str, reports: bool, params: &'static [&'static str]) -> Result<(), Error<'b>> {
    if let Some(&func) = program.funcs.get(name) {
        if func.reports == reports && func.params.len() == params.len() && func.params.iter().zip(params).all(|(a, &b)| a.id == b) {
            return Ok(())
        }
    }
    Err(Error::MissingRequiredFunc { name, reports, params })
}
pub fn parse<'b>(project_name: &str, input: &'b str) -> Result<String, Error<'b>> {
    let items = ast::parse(input)?;
    let program = Program::init_global(&items)?;

    let mut custom_blocks = String::new();
    let mut scopes = Vec::with_capacity(16);

    let mut variables = String::new();
    let mut root_scope: LinkedHashMap<&str, &Ident> = GLOBAL_SCOPE_IDENTS.iter().map(|s| (s.id.as_str(), s)).collect();
    for breed in program.breeds.values().filter(|s| s.is_plural) {
        assert!(root_scope.insert(breed.ident.id.as_str(), &breed.ident).is_none());
        write!(variables, r#"<variable name="{}"><list struct="atomic"></list></variable>"#, breed.ident.id.as_str()).unwrap();
    }
    for global in program.globals.values() {
        write!(variables, r#"<variable name="{}"><l>0</l></variable>"#, global.ident.id).unwrap();
    }
    scopes.push(root_scope);

    for func in program.funcs.values() {
        parse_function(&mut custom_blocks, &program, &mut scopes, func)?;
    }

    // do this after all other parsing because there are more important errors to catch
    ensure_has_required_func(&program, "setup", false, &[])?;
    ensure_has_required_func(&program, "go", false, &[])?;

    let mut breed_sprites = String::new();
    let mut plural_breed_names: BTreeSet<&str> = Default::default(); // btree so we get sorted order
    for (i, breed) in program.breeds.values().filter(|s| s.is_plural).enumerate() {
        plural_breed_names.insert(breed.ident.id.as_str());
        parse_breed_sprite(&mut breed_sprites, breed, (i, program.breeds.len() / 2))?;
    }

    let mut patches_props = String::new();
    for prop in program.patches.props.keys() {
        write!(patches_props, r#"<variable name="{}"><l>0</l></variable>"#, prop).unwrap();
    }

    let stage_size = 495;    // both width and height
    let patches_radius = 16; // patches range from [-r, r] for both axes
    let patches_dim = patches_radius * 2 + 1;
    assert_eq!(stage_size % patches_dim, 0);

    Ok(format!(include_str!("template.xml"),
        project_name = project_name,
        stage_size = stage_size,
        patches_radius = patches_radius,
        patches_dim = patches_dim,
        patches_scale = stage_size / patches_dim,
        custom_blocks = custom_blocks,
        breed_sprites = breed_sprites,
        base_sprite_scale = BASE_SPRITE_SCALE,
        variables = variables,
        patches_props = patches_props,
        plural_breed_names = escape_xml(&Punctuated(program.breeds.values().filter(|b| b.is_plural).map(|b| &b.ident.id), "\r").to_string()),
        patch_props = escape_xml(&Punctuated(["color"].iter().chain(program.patches.props.keys()), "\r").to_string()),
    ))
}

#[test] fn test_prog_header() {
    let items = ast::parse(r#"
    breed [goats goat]
    breed [merps merp]
    turtles-own [ mtdews ]
    merps-own [ kfcs ]
    patches-own [ duck-count ]

    to-report commIt-sudoku
        report "rosebud"
    end
    "#).unwrap();
    let res = Program::init_global(&items).unwrap();

    assert_eq!(res.breeds.len(), 4);
    
    let goats = res.breeds.get("goats").unwrap();
    let goat = res.breeds.get("goat").unwrap();
    assert!(goats.is_plural && !goat.is_plural);
    assert!(std::ptr::eq(goats.info.as_ref(), goat.info.as_ref()));

    let merps = res.breeds.get("merps").unwrap();
    let merp = res.breeds.get("merp").unwrap();
    assert!(merps.is_plural && !merp.is_plural);
    assert!(std::ptr::eq(merps.info.as_ref(), merp.info.as_ref()));

    assert!(!std::ptr::eq(goats.info.as_ref(), merps.info.as_ref()));

    let goats_info = goats.info.borrow();
    let merps_info = merps.info.borrow();

    assert_eq!(goats_info.props.len(), 1);
    assert!(goats_info.props.contains_key("mtdews"));

    assert_eq!(merps_info.props.len(), 2);
    assert!(merps_info.props.contains_key("mtdews"));
    assert!(merps_info.props.contains_key("kfcs"));

    assert_eq!(res.patches.props.len(), 1);
    assert!(res.patches.props.contains_key("duck-count"));

    assert_eq!(res.funcs.len(), 1);
    assert!(res.funcs.contains_key("commit-sudoku"));
}

#[test] fn test_disjoint_owns() {
    if let Err(x) = parse("test", r#"
    breed [dogs dog]
    breed [cats cat]
    breed [pups pup]
    dogs-own [water]
    cats-own [water]
    pups-own [water]

    to setup end
    to go end
    "#) { panic!("{:?}", x) }
    if let Err(x) = parse("test", r#"
    breed [dogs dog]
    breed [cats cat]
    breed [pups pup]
    turtles-own [water]

    to setup end
    to go end
    "#) { panic!("{:?}", x) }
}
#[test] fn test_redundant_owns() {
    match parse("test", r#"
    breed [dogs dog]
    breed [cats cat]
    breed [pups pup]
    turtles-own [water]
    cats-own [water]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "water"); assert_eq!(previous.id, "water") }, x => panic!("{:?}", x) }
}

// types of conflict sources: breed, func, global, lexical, patches prop, breed prop
// we'll do symmetric tests for all pairs of types, including same type

#[test] fn test_name_overlap_same_type() {
    match parse("test", r#"
    breed [cats cat]
    breed [x catS]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "cats"); assert_eq!(previous.id, "cats") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    breed [cats cat]
    breed [x cAt]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    to foo end
    to Foo end
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "foo"); assert_eq!(previous.id, "foo") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    globals [ merp Merp ]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "merp"); assert_eq!(previous.id, "merp") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    to thing[x]
        let x 4
    end
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "x"); assert_eq!(previous.id, "x") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    to thing
        let x 4
        if x [
            let x 6
        ]
    end
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "x"); assert_eq!(previous.id, "x") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    patches-own [energy energy]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "energy"); assert_eq!(previous.id, "energy") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    breed [dogs dog]
    turtles-own [a]
    dogs-own [a]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "a"); assert_eq!(previous.id, "a") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    breed [dogs dog]
    dogs-own [a]
    turtles-own [a]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "a"); assert_eq!(previous.id, "a") }, x => panic!("{:?}", x) }
}
#[test] fn test_name_overlap_breed_other() {
    match parse("test", r#"
    breed [cats cat]
    to cats end
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "cats"); assert_eq!(previous.id, "cats") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    breed [cats cat]
    to cat end
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    to cats end
    breed [cats cat]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "cats"); assert_eq!(previous.id, "cats") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    to cat end
    breed [cats cat]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    breed [cats cat]
    globals [cats]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "cats"); assert_eq!(previous.id, "cats") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    breed [cats cat]
    globals [cat]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    globals [caTS]
    breed [cats cAt]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "cats"); assert_eq!(previous.id, "cats") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    globals [cat]
    breed [cats cat]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    breed [cats cat]
    to go let cAts 0 end
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "cats"); assert_eq!(previous.id, "cats") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    breed [cats cat]
    to go let cat 0 end
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    to go let cats 0 end
    breed [cats cat]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "cats"); assert_eq!(previous.id, "cats") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    to go let cat 0 end
    breed [cats cat]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    breed [cats cat]
    cats-own [cats]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "cats"); assert_eq!(previous.id, "cats") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    breed [caTs cAt]
    breed [dogs dog]
    dogs-own [Cat]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    cats-own [cats]
    breed [cats cat]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "cats"); assert_eq!(previous.id, "cats") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    dogs-own [cAt]
    breed [cats cat]
    breed [dogs dog]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    breed [cats cat]
    patches-own [cat]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    patches-own [cat]
    breed [cats caT]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
}
#[test] fn test_name_overlap_func_other() {
    match parse("test", r#"
    globals [Foo]
    to foo end
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "foo"); assert_eq!(previous.id, "foo") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    to foo end
    globals [Foo]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "foo"); assert_eq!(previous.id, "foo") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    to foo let Foo 4 end
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "foo"); assert_eq!(previous.id, "foo") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    to foo end
    to bar let Foo 54 end
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "foo"); assert_eq!(previous.id, "foo") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    to foo end
    patches-own [FOO]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "foo"); assert_eq!(previous.id, "foo") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    patches-own [FOO]
    to foo end
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "foo"); assert_eq!(previous.id, "foo") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    breed [birds bird]
    birds-own [FoO]
    to foo end
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "foo"); assert_eq!(previous.id, "foo") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    breed [birds bird]
    to foo end
    birds-own [FoO]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "foo"); assert_eq!(previous.id, "foo") }, x => panic!("{:?}", x) }
}
#[test] fn test_name_overlap_global_other() {
    match parse("test", r#"
    globals [derp]
    to foo let Derp 5 end
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "derp"); assert_eq!(previous.id, "derp") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    to foo let Derp 5 end
    globals [derp]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "derp"); assert_eq!(previous.id, "derp") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    globals [derp]
    breed [ducks duck]
    ducks-own [derP]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "derp"); assert_eq!(previous.id, "derp") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    breed [ducks duck]
    ducks-own [derP]
    globals [derp]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "derp"); assert_eq!(previous.id, "derp") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    globals [derp]
    patches-own [DERP]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "derp"); assert_eq!(previous.id, "derp") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    patches-own [DERP]
    globals [derp]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "derp"); assert_eq!(previous.id, "derp") }, x => panic!("{:?}", x) }
}
#[test] fn test_name_overlap_lexical_other() {
    match parse("test", r#"
    patches-own [shells]
    to foo let sheLLs 3 end
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "shells"); assert_eq!(previous.id, "shells") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    to foo let sheLLs 3 end
    patches-own [shells]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "shells"); assert_eq!(previous.id, "shells") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    to foo let sheLLs 3 end
    breed [geese goose]
    geese-own [shells]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "shells"); assert_eq!(previous.id, "shells") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    breed [geese goose]
    geese-own [shells]
    to foo let sheLLs 3 end
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "shells"); assert_eq!(previous.id, "shells") }, x => panic!("{:?}", x) }
}
#[test] fn test_name_overlap_patchprop_other() {
    match parse("test", r#"
    patches-own [tic-tAcs]
    breed [dogs dog]
    dogs-own [Tic-TACs]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "tic-tacs"); assert_eq!(previous.id, "tic-tacs") }, x => panic!("{:?}", x) }
    match parse("test", r#"
    breed [dogs dog]
    dogs-own [Tic-TACs]
    patches-own [tic-tAcs]
    "#).unwrap_err() { Error::Redefine { name, previous } => { assert_eq!(name.id, "tic-tacs"); assert_eq!(previous.id, "tic-tacs") }, x => panic!("{:?}", x) }
}
