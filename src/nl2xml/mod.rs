mod ast;

use std::collections::{BTreeSet, BTreeMap, HashSet, HashMap};
use linked_hash_map::LinkedHashMap;

use std::cell::RefCell;
use std::rc::Rc;
use std::fmt::{self, Write, Debug, Display};
use std::f32::consts as f32c;
use std::f64::consts as f64c;
use std::iter;

use crate::common::*;
use crate::util::*;
use ast::*;
pub use ast::{Ident, Span};

use lalrpop_util::{ParseError, lexer::Token};
use xml::escape::escape_str_attribute as escape_xml;
use ordslice::Ext;

const BASE_SPRITE_SCALE: f64 = 0.25;

lazy_static! {
    static ref GLOBAL_SCOPE_IDENTS: Vec<Ident> = GLOBAL_SCOPE.iter().map(|&s| Ident { id: s.into(), raw_span: Span(0, 0) }).collect();
    static ref SUGGESTIONS: HashMap<&'static str, &'static str> = parse_ws_pairs(include_str!("suggestions.txt"));
    static ref READONLY_BUILTINS: HashMap<&'static str, &'static str> = parse_ws_rest(include_str!("readonly-builtins.txt"));
    static ref BUILTIN_PATCH_PROPS: HashSet<&'static str> = parse_idents(include_str!("builtin-patch-props.txt"));
}

fn rename_patch_prop(prop: &str) -> &str {
    NL2NB_PATCH_PROP_RENAMES.get(prop).copied().unwrap_or(prop)
}

fn get_func_def_name<'b>(func: &Function) -> Result<String, ErrorKind<'b>> {
    if let Some(bad) = iter::once(&func.name).chain(&func.params).find(|s| s.id.contains('\'')) {
        return Err(ErrorKind::FuncHeaderHadApos { func: func.name.clone(), name: bad.clone() });
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
enum ErrorKind<'a> {
    Parse(ParseError<usize, Token<'a>, AstError>),
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
    AssignToFunc { func: Ident, invoke_span: Span, is_builtin: bool },

    ReportInNonReporter { func: Ident, report_span: Span },
    UnreachableCode { func: Ident, unreachable_span: Span },

    MissingRequiredFunc { name: &'static str, reports: bool, params: &'static [&'static str] },

    NotConstexpr { expr_span: Span },

    // annotation errors (meta language)

    UnknownAnnotationForItem { annotation_span: Span, allowed: &'static [&'static str] },
}
impl<'a> From<ParseError<usize, Token<'a>, AstError>> for ErrorKind<'a> {
    fn from(e: ParseError<usize, Token<'a>, AstError>) -> Self {
        ErrorKind::Parse(e)
    }
}

pub struct Error<'a> {
    kind: ErrorKind<'a>,
    src: &'a str,
    line_starts: Vec<usize>, // sorted
}
impl Error<'_> {
    fn get_line_num(&self, pos: usize) -> usize {
        self.line_starts.upper_bound(&pos)
    }
    fn write_error(&self, f: &mut fmt::Formatter, msg: &str, span: Option<Span>, extra_msg: Option<&str>) -> fmt::Result {
        writeln!(f, "{}", msg)?;
        
        if let Some(span) = span {
            writeln!(f)?;

            let start_index = self.line_starts.upper_bound(&span.0).saturating_sub(1);
            let end_index = self.line_starts.lower_bound(&span.1);
            
            // grab all the referenced lines
            let mut lines = Vec::with_capacity(end_index - start_index);
            for i in start_index..end_index {
                let a = self.line_starts[i];
                let b = self.line_starts.get(i + 1).copied().unwrap_or(self.src.len());
                let line = self.src[a..b].trim_end();
                lines.push(if line.is_empty() { None } else { Some(line) });
            }

            // chop off any common leading space among the lines
            let mut chop_len = 0;
            while let Some(c) = lines.iter().flatten().filter_map(|s| s.chars().next()).next() {
                if !c.is_whitespace() || !lines.iter().flatten().all(|s| s.starts_with(c)) { break }
                let len = c.len_utf8();
                for line in lines.iter_mut().flatten() {
                    *line = &line[len..];
                    chop_len += 1;
                }
            }

            let pos_prefix = format!("line {}: ", start_index + 1);
            let space_prefix = " ".repeat(pos_prefix.len());
            
            if !lines.is_empty() {
                writeln!(f, "| {}{}", pos_prefix, lines[0].unwrap_or(""))?;
                for line in &lines[1..] {
                    writeln!(f, "| {}{}", space_prefix, line.unwrap_or(""))?;
                }
            }
            if lines.len() == 1 {
                let underline = "^".repeat(self.src[span.0..span.1].chars().count());
                let prefix = " ".repeat(span.0 - self.line_starts[start_index] - chop_len + space_prefix.len());
                writeln!(f, "  {}{}", prefix, underline)?;
            }
        }

        if let Some(extra) = extra_msg { writeln!(f, "\n{}", extra)? }
        
        Ok(())
    }
}
impl Debug for Error<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{:?}", self.kind)
    }
}
impl Display for Error<'_> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match &self.kind {
            ErrorKind::Parse(e) => match e {
                ParseError::InvalidToken { location } => self.write_error(f, "invalid token", Some(Span(*location, location + 1)), None)?,
                ParseError::UnrecognizedEOF { location, .. } => self.write_error(f, "unexpected end of file", Some(Span(*location, location + 1)), None)?,
                ParseError::UnrecognizedToken { token, .. } => self.write_error(f, "unexpected token", Some(Span(token.0, token.2)), None)?,
                ParseError::ExtraToken { token } => self.write_error(f, "found extra token", Some(Span(token.0, token.2)), None)?,
                ParseError::User { error } => match error {
                    AstError::ParseFloat { problem_span } => self.write_error(f, "failed to parse float", Some(*problem_span), None)?,
                }
            }
            ErrorKind::FuncHeaderHadApos { name, .. } => self.write_error(f, &format!("function header had invalid symbol: {}", name.id), Some(name.span()), Some("function names and parameters may not contain apostrophes"))?,
            
            ErrorKind::Redefine { name, previous } => self.write_error(f, &format!("redefined symbol: {}", name.id), Some(name.span()), Some(&format!("previously defined on line {}", self.get_line_num(previous.span().0))))?,
            ErrorKind::RedefineBuiltin { name } => self.write_error(f, &format!("redefined symbol: {}", name.id), Some(name.span()), Some("this is a built-in or reserved name"))?,

            ErrorKind::ExpectedSingular { name } => self.write_error(f, &format!("expected singular breed name, got: {}", name.id), Some(name.span()), None)?,
            ErrorKind::ExpectedPlural { name } => self.write_error(f, &format!("expected plural breed name, got: {}", name.id), Some(name.span()), None)?,
            ErrorKind::BreedNotDefined { name } => self.write_error(f, &format!("breed does not exist: {}", name.id), Some(name.span()), Some("you can define breeds with 'breed [ plural singular ]'"))?,
            ErrorKind::VariableNoTDefined { name } => self.write_error(f, &format!("undefined variable: {}", name.id), Some(name.span()), Some("if this was meant to be a netlogo gui input, these are not currently supported"))?,
            ErrorKind::FunctionNotDefined { name, suggested } => {
                let m = suggested.map(|s| format!("suggestion: {}", s));
                self.write_error(f, &format!("undefined function: {}", name.id), Some(name.span()), m.as_deref())?
            }

            ErrorKind::AssignToReadonlyVar { name } => self.write_error(f, &format!("assign to readonly variable: {}", name.id), Some(name.span()), None)?,

            ErrorKind::InvalidColor { color_span } => self.write_error(f, "invalid color", Some(*color_span), Some("custom colors must be a list of three numbers denoting rbg"))?,

            ErrorKind::FunctionArgCount { func, invoke_span, got, expected, is_builtin } => {
                let m = match is_builtin {
                    false => format!("{} (defined on line {}) expected {} {}, but got {}", func.id, self.get_line_num(func.span().0), expected, if *expected == 1 { "argument" } else { "arguments" }, got),
                    true => format!("{} (built-in) expected {} arguments, but got {}", func.id, expected, got),
                };
                self.write_error(f, "incorrect number of arguments", Some(*invoke_span), Some(&m))?
            }
            ErrorKind::NonReporterInExpr { func, invoke_span, is_builtin } => {
                let m = match is_builtin {
                    false => format!("{} (defined on line {}) does not report a value", func.id, self.get_line_num(func.span().0)),
                    true => format!("{} (built-in) does not report a value", func.id),
                };
                self.write_error(f, "non-reporter used in expression", Some(*invoke_span), Some(&m))?
            }
            ErrorKind::ReporterValueDiscarded { func, invoke_span, is_builtin } => {
                let m = match is_builtin {
                    false => format!("{} (defined on line {}) reports a value, but the result is discarded", func.id, self.get_line_num(func.span().0)),
                    true => format!("{} (built-in) reports a value, but the result is discarded", func.id),
                };
                self.write_error(f, "reporter value discarded", Some(*invoke_span), Some(&m))?
            }
            ErrorKind::AssignToFunc { func, invoke_span, is_builtin } => {
                let m = match is_builtin {
                    false => format!("{} (defined on line {}) is not a variable", func.id, self.get_line_num(func.span().0)),
                    true => format!("{} (built-in) is not a variable", func.id),
                };
                self.write_error(f, "assign to function", Some(*invoke_span), Some(&m))?
            }

            ErrorKind::ReportInNonReporter { report_span, .. } => self.write_error(f, "report statement in non-reporter", Some(*report_span), Some("the enclosing function does not report a value.\ndid you mean to use 'to-report' instead of 'to'?"))?,
            ErrorKind::UnreachableCode { unreachable_span, .. } => self.write_error(f, "unreachable code", Some(*unreachable_span), Some("a previous instruction already exited the function or started an infinite loop"))?,

            ErrorKind::MissingRequiredFunc { name, reports, params } => {
                self.write_error(f, "missing required function", None, Some(&format!("expected a function with signature '{} {} [ {} ] end", if *reports { "to-report" } else { "to" }, name, Punctuated(params.iter(), " "))))?
            }

            ErrorKind::NotConstexpr { expr_span } => self.write_error(f, "expected a constant expression", Some(*expr_span), Some("constant expressions are numbers, strings, or lists of constant expressions"))?,

            // annotation errors (meta language)

            ErrorKind::UnknownAnnotationForItem { annotation_span, allowed } => self.write_error(f, "unknown annotation for this item", Some(*annotation_span), Some(&format!("allowed annotations: {}", Punctuated(allowed.iter(), " "))))?,
        }
        Ok(())
    }
}

enum StorageLocation<'a> {
    Builtin { get: &'static str, set: Option<(&'static str, &'static str)> },
    Lexical, Property, PatchesProp,

    BuiltinColor,

    // in an expression, func calls with no args will at first be parsed as variables to avoid ambiguity in the grammar
    FunctionName { func: &'a Function, is_builtin: bool },
}

struct EntityInfo<'a> {
    props: BTreeMap<&'a str, &'a Ident>, // btree so we get sorted order
    placeins: Vec<(&'a Function, &'a PlaceIn)>,
    singular: &'a str,
    plural: &'a str,
}

struct GlobalSymbol<'a> { ident: &'a Ident, gui_var_value: Option<&'a Expr> } // gui_var_value is None iff not gui var
struct BreedSymbol<'a> { ident: &'a Ident, is_plural: bool, info: Rc<RefCell<EntityInfo<'a>>> }

pub struct Program<'a> {
    globals: LinkedHashMap<&'a str, GlobalSymbol<'a>>,
    breeds: LinkedHashMap<&'a str, BreedSymbol<'a>>,
    funcs: LinkedHashMap<&'a str, &'a Function>,
    patches: EntityInfo<'a>,

    all_breed_props: HashMap<&'a str, &'a Ident>,
}
impl<'a> Program<'a> {
    fn new() -> Self {
        Program {
            globals: Default::default(),
            breeds: Default::default(),
            funcs: Default::default(),
            patches: EntityInfo { props: Default::default(), placeins: Default::default(), plural: "patches", singular: "patch" },

            all_breed_props: Default::default(),
        }
    }

    // checks for validity in (only) the global scope
    fn validate_define_global<'b>(&self, ident: &Ident) -> Result<(), ErrorKind<'b>> {
        let id = ident.id.as_str();
        let prev = self.globals.get(id).map(|s| s.ident)
            .or_else(|| self.breeds.get(id).map(|s| s.ident))
            .or_else(|| self.funcs.get(id).map(|s| &s.name))
            .or_else(|| self.patches.props.get(id).copied())
            .or_else(|| self.all_breed_props.get(id).copied());
        if let Some(prev) = prev {
            return Err(ErrorKind::Redefine { name: ident.clone(), previous: prev.clone() });
        }
        if RESERVED_WORDS.contains(id) {
            return Err(ErrorKind::RedefineBuiltin { name: ident.clone() });
        }
        Ok(())
    }
    fn validate_define_lexical<'b>(&self, ident: &Ident, scopes: &[LinkedHashMap<&str, &Ident>]) -> Result<(), ErrorKind<'b>> {
        for scope in scopes.iter().rev() {
            if let Some(&prev) = scope.get(ident.id.as_str()) {
                return Err(ErrorKind::Redefine { name: ident.clone(), previous: prev.clone() });
            }
        }
        self.validate_define_global(ident)
    }
    fn find_var<'b>(&self, scopes: &[LinkedHashMap<&str, &Ident>], ident: &Ident) -> Result<StorageLocation, ErrorKind<'b>> {
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
            "xcor" => StorageLocation::Builtin { get: r#"<custom-block s="x position"></custom-block>"#, set: Some((r#"<custom-block s="set x to %n">"#, "</custom-block>")) },
            "ycor" => StorageLocation::Builtin { get: r#"<custom-block s="y position"></custom-block>"#, set: Some((r#"<custom-block s="set y to %n">"#, "</custom-block>")) },
            "color" => StorageLocation::BuiltinColor,
            _ => match self.funcs.get(id) {
                Some(&func) => StorageLocation::FunctionName { func, is_builtin: false },
                None => return Err(ErrorKind::VariableNoTDefined { name: ident.clone() }),
            }
        })
    }
    fn ensure_breed_defined<'b>(&self, ident: &Ident, should_be_plural: Option<bool>) -> Result<(), ErrorKind<'b>> {
        let breed = match self.breeds.get(ident.id.as_str()) {
            None => return Err(ErrorKind::BreedNotDefined { name: ident.clone() }),
            Some(b) => b,
        };
        if let Some(should_be_plural) = should_be_plural {
            match (breed.is_plural, should_be_plural) {
                (true, true) | (false, false) => (),
                (true, false) => return Err(ErrorKind::ExpectedSingular { name: ident.clone() }),
                (false, true) => return Err(ErrorKind::ExpectedPlural { name: ident.clone() }),
            }
        }
        Ok(())
    }
    fn format_func_call<'b>(&self, script: &mut String, scopes: &mut Vec<LinkedHashMap<&str, &Ident>>, call: &FnCall, in_expr: bool) -> Result<(), ErrorKind<'b>> {
        fn check_usage<'b>(call: &FnCall, func: Option<&Function>, reports: bool, in_expr: bool, expected_args: Option<usize>) -> Result<(), ErrorKind<'b>> {
            debug_assert!(func.is_none() || func.unwrap().reports == reports);
            debug_assert!(func.is_none() || expected_args.is_none() || func.unwrap().params.len() == expected_args.unwrap());
            let target = func.map(|f| &f.name).unwrap_or(&call.name);
            let is_builtin = func.is_none();

            match (reports, in_expr) {
                (true, true) | (false, false) => (),
                (true, false) => return Err(ErrorKind::ReporterValueDiscarded { func: target.clone(), invoke_span: call.span(), is_builtin }),
                (false, true) => return Err(ErrorKind::NonReporterInExpr { func: target.clone(), invoke_span: call.span(), is_builtin }),
            }
            if let Some(expected) = expected_args {
                if call.args.len() != expected { return Err(ErrorKind::FunctionArgCount { func: target.clone(), invoke_span: call.span(), got: call.args.len(), expected, is_builtin }) }
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
                *script += if x.starts_with('r') { r#"<block s="turn">"# } else { r#"<block s="turnLeft">"# };
                self.generate_expr_script(script, scopes, &call.args[0])?;
                *script += "</block>";
            }
            "setxy" => {
                check_usage(call, None, false, in_expr, Some(2))?;
                *script += r#"<custom-block s="go to x: %n y: %n">"#;
                self.generate_expr_script(script, scopes, &call.args[0])?;
                self.generate_expr_script(script, scopes, &call.args[1])?;
                *script += "</custom-block>";
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
            "atan" => {
                check_usage(call, None, true, in_expr, Some(2))?;
                *script += r#"<custom-block s="atan x: %n y: %n">"#;
                self.generate_expr_script(script, scopes, &call.args[0])?;
                self.generate_expr_script(script, scopes, &call.args[1])?;
                *script += "</custom-block>";
            }
            "any?" => {
                check_usage(call, None, true, in_expr, Some(1))?;
                *script += r#"<block s="reportNot"><custom-block s="is %l empty? (turtle set)">"#;
                self.generate_expr_script(script, scopes, &call.args[0])?;
                *script += "</custom-block></block>";
            }
            "one-of" => {
                check_usage(call, None, true, in_expr, Some(1))?;
                *script += r#"<custom-block s="random item %l (turtle set)">"#;
                self.generate_expr_script(script, scopes, &call.args[0])?;
                *script += "</custom-block>";
            }
            x @ ("min" | "max") => {
                check_usage(call, None, true, in_expr, Some(1))?;
                write!(script, r#"<custom-block s="{} %l">"#, x).unwrap();
                self.generate_expr_script(script, scopes, &call.args[0])?;
                *script += "</custom-block>";
            }
            "sum" => {
                check_usage(call, None, true, in_expr, Some(1))?;
                *script += r#"<custom-block s="sum %l">"#;
                self.generate_expr_script(script, scopes, &call.args[0])?;
                *script += "</custom-block>";
            }
            "mean" => {
                check_usage(call, None, true, in_expr, Some(1))?;
                *script += r#"<custom-block s="average %l">"#;
                self.generate_expr_script(script, scopes, &call.args[0])?;
                *script += "</custom-block>";
            }
            x @ ("abs" | "sin" | "cos" | "tan" | "asin" | "acos" | "sqrt" | "ln" | "log" | "floor" | "ceiling") => {
                check_usage(call, None, true, in_expr, Some(1))?;
                write!(script, r#"<block s="reportMonadic"><l><option>{}</option></l>"#, x).unwrap();
                self.generate_expr_script(script, scopes, &call.args[0])?;
                *script += "</block>";
            }
            "other" => {
                check_usage(call, None, true, in_expr, Some(1))?;
                *script += r#"<custom-block s="exclude myself %l">"#;
                self.generate_expr_script(script, scopes, &call.args[0])?;
                *script += "</custom-block>";
            }
            "distancexy" => {
                check_usage(call, None, true, in_expr, Some(2))?;
                *script += r#"<custom-block s="distance from x: %n y: %n">"#;
                self.generate_expr_script(script, scopes, &call.args[0])?;
                self.generate_expr_script(script, scopes, &call.args[1])?;
                *script += "</custom-block>";
            }
            "distance" => {
                check_usage(call, None, true, in_expr, Some(1))?;
                *script += r#"<custom-block s="distance from %obj">"#;
                self.generate_expr_script(script, scopes, &call.args[0])?;
                *script += "</custom-block>";
            }
            "towardsxy" => {
                check_usage(call, None, true, in_expr, Some(2))?;
                *script += r#"<custom-block s="direction towards x: %n y: %n">"#;
                self.generate_expr_script(script, scopes, &call.args[0])?;
                self.generate_expr_script(script, scopes, &call.args[1])?;
                *script += "</custom-block>";
            }
            "towards" => {
                check_usage(call, None, true, in_expr, Some(1))?;
                *script += r#"<custom-block s="direction towards %obj">"#;
                self.generate_expr_script(script, scopes, &call.args[0])?;
                *script += "</custom-block>";
            }
            "subtract-headings" => {
                check_usage(call, None, true, in_expr, Some(2))?;
                *script += r#"<custom-block s="angle change from %n to %n">"#;
                self.generate_expr_script(script, scopes, &call.args[1])?;
                self.generate_expr_script(script, scopes, &call.args[0])?;
                *script += "</custom-block>";
            }
            x => match self.funcs.get(x) {
                None => return Err(ErrorKind::FunctionNotDefined { name: call.name.clone(), suggested: SUGGESTIONS.get(x).copied() }),
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
    fn generate_constexpr_script<'b>(&self, script: &mut String, expr: &Expr) -> Result<(), ErrorKind<'b>> {
        match expr {
            Expr::Value(Value::Number(x)) => write!(script, "<l>{}</l>", x.value).unwrap(),
            Expr::Value(Value::Text(x)) => write!(script, "<l>{}</l>", x.content).unwrap(),
            Expr::Value(Value::List(x)) => {
                *script += r#"<list>"#;
                for value in x.values.iter() {
                    *script += "<item>";
                    self.generate_constexpr_script(script, value)?;
                    *script += "</item>";
                }
                *script += "</list>";
            }
            _ => return Err(ErrorKind::NotConstexpr { expr_span: expr.span() }),
        }
        Ok(())
    }
    fn generate_expr_script<'b>(&self, script: &mut String, scopes: &mut Vec<LinkedHashMap<&str, &Ident>>, expr: &Expr) -> Result<(), ErrorKind<'b>> {
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

            Expr::Fetch { target, expr, .. } => {
                *script += r#"<custom-block s="ask %obj for its %repRing">"#;
                self.generate_expr_script(script, scopes, target)?;
                *script += r#"<block s="reifyReporter"><autolambda>"#;
                self.generate_expr_script(script, scopes, expr)?;
                *script += "</autolambda><list></list></block></custom-block>";
            }
            Expr::InRadius { agents, radius } => {
                *script += r#"<custom-block s="turtles %l within distance %n">"#;
                self.generate_expr_script(script, scopes, agents)?;
                self.generate_expr_script(script, scopes, radius)?;
                *script += "</custom-block>";
            }
            Expr::MinMaxOneOf { agents, expr, is_max, .. } => {
                write!(script, r#"<custom-block s="get one %l with {} %repRing">"#, if *is_max { "max" } else { "min" }).unwrap();
                self.generate_expr_script(script, scopes, agents)?;
                *script += r#"<block s="reifyReporter"><autolambda>"#;
                self.generate_expr_script(script, scopes, expr)?;
                *script += "</autolambda><list></list></block></custom-block>";
            }

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
                    StorageLocation::FunctionName { .. } => self.format_func_call(script, scopes, &FnCall { name: ident.clone(), args: vec![] }, true)?,
                }
            }
        }
        Ok(())
    }
    fn generate_script<'b>(&self, script: &mut String, scopes: &mut Vec<LinkedHashMap<&'a str, &'a Ident>>, stmts: &'a [Stmt], func: &Function) -> Result<(), ErrorKind<'b>> {
        scopes.push(Default::default()); // generate a new scope for this script

        let mut has_terminated = false;

        for stmt in stmts {
            if has_terminated { return Err(ErrorKind::UnreachableCode { func: func.name.clone(), unreachable_span: stmt.span() }) }
            match stmt {
                Stmt::Report(report) => {
                    if !func.reports { return Err(ErrorKind::ReportInNonReporter { func: func.name.clone(), report_span: report.span() }) }

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
                        None => return Err(ErrorKind::AssignToReadonlyVar { name: assign.name.clone() }),
                    }
                    StorageLocation::BuiltinColor => {
                        let is_general = match &assign.value {
                            Expr::Value(Value::List(list)) => match list.values.as_slice() {
                                [Expr::Value(Value::Number(r)), Expr::Value(Value::Number(g)), Expr::Value(Value::Number(b))] => {
                                    write!(script, r#"<block s="setColor"><color>{},{},{},1</color></block>"#, r.value, g.value, b.value).unwrap();
                                    false
                                }
                                [_, _, _] => true,
                                _ => return Err(ErrorKind::InvalidColor { color_span: assign.value.span() }), // not three values
                            }
                            _ => true,
                        };
                        if is_general {
                            *script += r#"<custom-block s="set pen color to %l">"#;
                            self.generate_expr_script(script, scopes, &assign.value)?;
                            *script += "</custom-block>";
                        }
                    }
                    StorageLocation::FunctionName { func, is_builtin } => return Err(ErrorKind::AssignToFunc { func: func.name.clone(), invoke_span: assign.name.span(), is_builtin }),
                }
                Stmt::Loop(repeat) => {
                    *script += r#"<block s="doForever"><script>"#;
                    self.generate_script(script, scopes, &repeat.stmts, func)?;
                    *script += "</script></block>";

                    has_terminated = true;
                }
                Stmt::Repeat(repeat) => {
                    *script += r#"<block s="doRepeat">"#;
                    self.generate_expr_script(script, scopes, &repeat.count)?;
                    *script += "<script>";
                    self.generate_script(script, scopes, &repeat.stmts, func)?;
                    *script += "</script></block>";
                }
                Stmt::While(repeat) => {
                    *script += r#"<block s="doUntil"><block s="reportNot">"#;
                    self.generate_expr_script(script, scopes, &repeat.condition)?;
                    *script += "</block><script>";
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
    fn init_global<'b>(items: &[Item]) -> Result<Program, ErrorKind<'b>> {
        let mut program = Program::new();
        let mut owns: Vec<&Own> = Vec::with_capacity(16);
        let mut placeins: Vec<(&Function, &PlaceIn)> = Vec::with_capacity(16);

        // initial pass - collect all the globals, breeds, and functions (names at global scope)
        for item in items {
            match item {
                Item::Globals(Globals { annotations, idents, .. }) => {
                    for annotation in annotations {
                        match annotation {
                            Annotation::GuiVar(GuiVar { ident, value, .. }) => {
                                program.validate_define_global(ident)?;
                                assert!(program.globals.insert(&ident.id, GlobalSymbol { ident, gui_var_value: Some(value) }).is_none());
                            }
                            _ => return Err(ErrorKind::UnknownAnnotationForItem { annotation_span: annotation.span(), allowed: &["guivar"] })
                        }
                    }
                    for ident in idents {
                        program.validate_define_global(ident)?;
                        assert!(program.globals.insert(&ident.id, GlobalSymbol { ident, gui_var_value: None }).is_none());
                    }
                }
                Item::Breed(Breed { plural, singular, .. }) => {
                    let info = Rc::new(RefCell::new(EntityInfo { props: Default::default(), placeins: Default::default(), plural: &plural.id, singular: &singular.id }));
                    for (ident, is_plural) in [(plural, true), (singular, false)] {
                        program.validate_define_global(ident)?;
                        assert!(program.breeds.insert(&ident.id, BreedSymbol { ident, is_plural, info: info.clone() }).is_none());
                    }
                }
                Item::Function(func) => {
                    program.validate_define_global(&func.name)?;
                    for annotation in func.annotations.iter() {
                        match annotation {
                            Annotation::PlaceIn(x) => placeins.push((func, x)), // gather them up for later when all breeds have been defined
                            _ => return Err(ErrorKind::UnknownAnnotationForItem { annotation_span: annotation.span(), allowed: &["placein"] })
                        }
                    }
                    assert!(program.funcs.insert(&func.name.id, func).is_none());
                }
                Item::Own(own) => match own.plural_owner.id.as_str() {
                    "patches" => owns.insert(0, own), // patches-own needs to come first for breed prop name conflict deduction
                    _ => owns.push(own), // just gather these up for after the first pass
                }
            }
        }

        fn apply_to_breeds<'a, 'b, F: Fn(&mut EntityInfo<'a>) -> Result<(), ErrorKind<'b>>>(program: &mut Program<'a>, target: &Ident, apply: F) -> Result<(), ErrorKind<'b>> {
            match target.id.as_str() {
                "turtles" => for breed in program.breeds.values().filter(|s| s.is_plural) {
                    apply(&mut *breed.info.borrow_mut())?
                },
                "patches" => apply(&mut program.patches)?,
                "turtle" | "patch" => return Err(ErrorKind::ExpectedPlural { name: target.clone() }),
                x => match program.breeds.get(x) {
                    None => return Err(ErrorKind::BreedNotDefined { name: target.clone() }),
                    Some(breed) => {
                        if !breed.is_plural { return Err(ErrorKind::ExpectedPlural { name: target.clone() }) }
                        apply(&mut *breed.info.borrow_mut())?;
                    }
                }
            }
            Ok(())
        }

        // process all the own drectives we stored
        for own in owns {
            for prop in own.props.iter() {
                program.validate_define_global(prop)?; // validate the names once up-front
            }
            apply_to_breeds(&mut program, &own.plural_owner, |target| {
                for prop in &own.props {
                    if let Some(prev) = target.props.insert(&prop.id, prop) {
                        return Err(ErrorKind::Redefine { name: prop.clone(), previous: prev.clone() })
                    }
                }
                Ok(())
            })?;
        }
        // gather up all the owns into one set for storage location resolution
        for breed in program.breeds.values() {
            program.all_breed_props.extend(breed.info.borrow().props.iter());
        }
        // go through all of the placein annotations we stored
        for (func, placein) in placeins {
            apply_to_breeds(&mut program, &placein.sprite, |target| {
                target.placeins.push((func, placein)); // just toss these over there, and it'll format them for us later
                Ok(())
            })?;
        }

        Ok(program) // we're now in a semi-valid state (at least at the global scope)
    }
}

fn parse_breed_sprite<'b>(breed_sprites: &mut String, breed: &BreedSymbol, index: (usize, usize)) -> Result<(), ErrorKind<'b>> {
    assert!(breed.is_plural);
    let ang = 2.0 * f64c::PI * (index.0 as f64 / index.1 as f64);
    let radius = if index.1 >= 2 { 100.0 } else { 0.0 };
    let color = Hsv::new(ang as f32 * 180.0 / f32c::PI, 0.5, 0.9).to_rgb().to_inner();

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
    write!(breed_sprites, r#"<script x="20" y="100"><custom-block s="tell %l to %cs"><block var="{}"/><script></script></custom-block><custom-block s="update background"></custom-block></script>"#, escaped_name).unwrap();
    for (func, placein) in breed.info.borrow().placeins.iter() {
        write!(breed_sprites, r#"<script x="{x}" y="{y}"><custom-block s="{block_name}">{params}{comment}</custom-block></script>"#,
            x = placein.x, y = placein.y,
            block_name = get_func_name(func),
            params = Punctuated(iter::once("<l></l>").cycle().take(func.params.len()), ""), // pass nothing by default
            comment = placein.comment.as_ref().map(|c| format!(r#"<comment w="200" collapsed="false">{}</comment>"#, escape_xml(&c.content))).unwrap_or_default(),
        ).unwrap();
    }
    *breed_sprites += "</scripts></sprite>";

    Ok(())
}
fn parse_function<'a, 'b>(custom_blocks: &mut String, program: &Program<'a>, scopes: &mut Vec<LinkedHashMap<&'a str, &'a Ident>>, func: &'a Function) -> Result<(), ErrorKind<'b>> {
    assert_eq!(scopes.len(), 1); // should just have the global scope
    scopes.push(Default::default()); // add a new scope for the function parameters

    write!(custom_blocks, r#"<block-definition s="{}" type="{}" category="custom"><inputs>{}</inputs>"#,
        get_func_def_name(func)?, if func.reports { "reporter" } else { "command" },
        r#"<input type="%s"></input>"#.repeat(func.params.len())).unwrap();

    for param in func.params.iter() {
        program.validate_define_lexical(param, scopes)?;
        assert!(scopes.last_mut().unwrap().insert(&param.id, param).is_none());
    }
    let mut script = String::new();
    program.generate_script(&mut script, scopes, &func.stmts, func)?;
    if !script.is_empty() { // if we generate an empty <script> tag here, it makes the block uneditable in NetsBlox
        write!(custom_blocks, "<script>{}</script>", script).unwrap();
    }

    write!(custom_blocks, "</block-definition>").unwrap();

    scopes.pop(); // remove the scope we added
    Ok(())
}
fn ensure_has_required_func<'b>(program: &Program, name: &'static str, reports: bool, params: &'static [&'static str]) -> Result<(), ErrorKind<'b>> {
    if let Some(&func) = program.funcs.get(name) {
        if func.reports == reports && func.params.len() == params.len() && func.params.iter().zip(params).all(|(a, &b)| a.id == b) {
            return Ok(())
        }
    }
    Err(ErrorKind::MissingRequiredFunc { name, reports, params })
}
fn parse_private<'b>(project_name: &str, input: &'b str) -> Result<String, ErrorKind<'b>> {
    let items = ast::parse(input)?;
    let program = Program::init_global(&items)?;

    let mut custom_blocks = String::new();
    let mut scopes = Vec::with_capacity(16);

    let mut variables = String::new();
    let mut root_scope: LinkedHashMap<&str, &Ident> = GLOBAL_SCOPE_IDENTS.iter().map(|s| (s.id.as_str(), s)).collect();
    for breed in program.breeds.values().filter(|s| s.is_plural) {
        assert!(root_scope.insert(breed.ident.id.as_str(), breed.ident).is_none());
        write!(variables, r#"<variable name="{}"><list struct="atomic"></list></variable>"#, breed.ident.id.as_str()).unwrap();
    }
    for global in program.globals.values() {
        match global.gui_var_value {
            None => write!(variables, r#"<variable name="{}"><l>0</l></variable>"#, global.ident.id).unwrap(),
            Some(value) => {
                write!(variables, r#"<variable name="{}">"#, global.ident.id).unwrap();
                program.generate_constexpr_script(&mut variables, value)?;
                variables += "</variable>";
            }
        }
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

    let breed_singulars: HashMap<_, _> = program.breeds.values().filter(|b| b.is_plural).map(|b| {
        let info = b.info.borrow();
        (info.plural.to_owned(), info.singular.to_owned())
    }).collect();
    let gui_vars: HashSet<_> = program.globals.values().filter(|g| g.gui_var_value.is_some()).map(|v| v.ident.id.clone()).collect();
    let metadata = MetaData { breed_singulars, gui_vars };

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
        plural_breed_names = escape_xml(&Punctuated(plural_breed_names.iter(), "\r").to_string()),
        patch_props = escape_xml(&Punctuated(["color"].iter().chain(program.patches.props.keys()), "\r").to_string()),
        metadata_json = serde_json::to_string_pretty(&metadata).unwrap(),
    ))
}
pub fn parse<'b>(project_name: &str, input: &'b str) -> Result<String, Error<'b>> {
    parse_private(project_name, input).map_err(|kind| Error { kind, src: input, line_starts: get_line_starts(input) })
}

#[test] fn test_prog_header() {
    let items = ast::parse(r#"
    ;@guivar num 40
    ;@guivar str "hello world"
    ;@guivar lst (list 1 2 3)
    globals [grd]

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

    assert_eq!(res.globals.len(), 4);
    assert!(res.globals.get("grd").unwrap().gui_var_value.is_none());
    match res.globals.get("num").unwrap().gui_var_value.as_ref().unwrap() {
        Expr::Value(Value::Number(x)) => assert_eq!(x.value, "40"),
        x => panic!("{:?}", x),
    }
    match res.globals.get("str").unwrap().gui_var_value.as_ref().unwrap() {
        Expr::Value(Value::Text(x)) => assert_eq!(x.content, "hello world"),
        x => panic!("{:?}", x),
    }
    match res.globals.get("lst").unwrap().gui_var_value.as_ref().unwrap() {
        Expr::Value(Value::List(x)) => assert_eq!(x.values.len(), 3),
        x => panic!("{:?}", x),
    }

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
    if let Err(x) = parse_private("test", r#"
    breed [dogs dog]
    breed [cats cat]
    breed [pups pup]
    dogs-own [water]
    cats-own [water]
    pups-own [water]

    to setup end
    to go end
    "#) { panic!("{:?}", x) }
    if let Err(x) = parse_private("test", r#"
    breed [dogs dog]
    breed [cats cat]
    breed [pups pup]
    turtles-own [water]

    to setup end
    to go end
    "#) { panic!("{:?}", x) }
}
#[test] fn test_redundant_owns() {
    match parse_private("test", r#"
    breed [dogs dog]
    breed [cats cat]
    breed [pups pup]
    turtles-own [water]
    cats-own [water]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "water"); assert_eq!(previous.id, "water") }, x => panic!("{:?}", x) }
}

// types of conflict sources: breed, func, global, lexical, patches prop, breed prop
// we'll do symmetric tests for all pairs of types, including same type

#[test] fn test_name_overlap_same_type() {
    match parse_private("test", r#"
    breed [cats cat]
    breed [x catS]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "cats"); assert_eq!(previous.id, "cats") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    breed [cats cat]
    breed [x cAt]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    to foo end
    to Foo end
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "foo"); assert_eq!(previous.id, "foo") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    globals [ merp Merp ]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "merp"); assert_eq!(previous.id, "merp") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    to thing[x]
        let x 4
    end
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "x"); assert_eq!(previous.id, "x") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    to thing
        let x 4
        if x [
            let x 6
        ]
    end
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "x"); assert_eq!(previous.id, "x") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    patches-own [energy energy]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "energy"); assert_eq!(previous.id, "energy") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    breed [dogs dog]
    turtles-own [a]
    dogs-own [a]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "a"); assert_eq!(previous.id, "a") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    breed [dogs dog]
    dogs-own [a]
    turtles-own [a]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "a"); assert_eq!(previous.id, "a") }, x => panic!("{:?}", x) }
}
#[test] fn test_name_overlap_breed_other() {
    match parse_private("test", r#"
    breed [cats cat]
    to cats end
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "cats"); assert_eq!(previous.id, "cats") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    breed [cats cat]
    to cat end
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    to cats end
    breed [cats cat]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "cats"); assert_eq!(previous.id, "cats") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    to cat end
    breed [cats cat]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    breed [cats cat]
    globals [cats]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "cats"); assert_eq!(previous.id, "cats") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    breed [cats cat]
    globals [cat]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    globals [caTS]
    breed [cats cAt]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "cats"); assert_eq!(previous.id, "cats") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    globals [cat]
    breed [cats cat]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    breed [cats cat]
    to go let cAts 0 end
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "cats"); assert_eq!(previous.id, "cats") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    breed [cats cat]
    to go let cat 0 end
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    to go let cats 0 end
    breed [cats cat]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "cats"); assert_eq!(previous.id, "cats") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    to go let cat 0 end
    breed [cats cat]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    breed [cats cat]
    cats-own [cats]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "cats"); assert_eq!(previous.id, "cats") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    breed [caTs cAt]
    breed [dogs dog]
    dogs-own [Cat]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    cats-own [cats]
    breed [cats cat]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "cats"); assert_eq!(previous.id, "cats") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    dogs-own [cAt]
    breed [cats cat]
    breed [dogs dog]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    breed [cats cat]
    patches-own [cat]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    patches-own [cat]
    breed [cats caT]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "cat"); assert_eq!(previous.id, "cat") }, x => panic!("{:?}", x) }
}
#[test] fn test_name_overlap_func_other() {
    match parse_private("test", r#"
    globals [Foo]
    to foo end
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "foo"); assert_eq!(previous.id, "foo") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    to foo end
    globals [Foo]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "foo"); assert_eq!(previous.id, "foo") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    to foo let Foo 4 end
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "foo"); assert_eq!(previous.id, "foo") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    to foo end
    to bar let Foo 54 end
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "foo"); assert_eq!(previous.id, "foo") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    to foo end
    patches-own [FOO]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "foo"); assert_eq!(previous.id, "foo") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    patches-own [FOO]
    to foo end
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "foo"); assert_eq!(previous.id, "foo") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    breed [birds bird]
    birds-own [FoO]
    to foo end
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "foo"); assert_eq!(previous.id, "foo") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    breed [birds bird]
    to foo end
    birds-own [FoO]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "foo"); assert_eq!(previous.id, "foo") }, x => panic!("{:?}", x) }
}
#[test] fn test_name_overlap_global_other() {
    match parse_private("test", r#"
    globals [derp]
    to foo let Derp 5 end
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "derp"); assert_eq!(previous.id, "derp") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    to foo let Derp 5 end
    globals [derp]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "derp"); assert_eq!(previous.id, "derp") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    globals [derp]
    breed [ducks duck]
    ducks-own [derP]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "derp"); assert_eq!(previous.id, "derp") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    breed [ducks duck]
    ducks-own [derP]
    globals [derp]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "derp"); assert_eq!(previous.id, "derp") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    globals [derp]
    patches-own [DERP]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "derp"); assert_eq!(previous.id, "derp") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    patches-own [DERP]
    globals [derp]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "derp"); assert_eq!(previous.id, "derp") }, x => panic!("{:?}", x) }
}
#[test] fn test_name_overlap_lexical_other() {
    match parse_private("test", r#"
    patches-own [shells]
    to foo let sheLLs 3 end
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "shells"); assert_eq!(previous.id, "shells") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    to foo let sheLLs 3 end
    patches-own [shells]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "shells"); assert_eq!(previous.id, "shells") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    to foo let sheLLs 3 end
    breed [geese goose]
    geese-own [shells]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "shells"); assert_eq!(previous.id, "shells") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    breed [geese goose]
    geese-own [shells]
    to foo let sheLLs 3 end
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "shells"); assert_eq!(previous.id, "shells") }, x => panic!("{:?}", x) }
}
#[test] fn test_name_overlap_patchprop_other() {
    match parse_private("test", r#"
    patches-own [tic-tAcs]
    breed [dogs dog]
    dogs-own [Tic-TACs]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "tic-tacs"); assert_eq!(previous.id, "tic-tacs") }, x => panic!("{:?}", x) }
    match parse_private("test", r#"
    breed [dogs dog]
    dogs-own [Tic-TACs]
    patches-own [tic-tAcs]
    "#).unwrap_err() { ErrorKind::Redefine { name, previous } => { assert_eq!(name.id, "tic-tacs"); assert_eq!(previous.id, "tic-tacs") }, x => panic!("{:?}", x) }
}
