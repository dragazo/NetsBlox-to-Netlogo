mod ast;

use std::collections::{BTreeSet, BTreeMap, HashSet};
use linked_hash_map::LinkedHashMap;

use std::cell::RefCell;
use std::rc::Rc;
use std::fmt::Write;
use std::f32::consts as f32c;
use std::f64::consts as f64c;

use crate::util::*;
use ast::*;
pub use ast::{Ident, Span};

use lalrpop_util::{ParseError, lexer::Token};

use xml::escape::escape_str_attribute as escape_xml;

lazy_static! {
    static ref BUILTIN_NAMES: HashSet<&'static str> = {
        let mut s = HashSet::new();
        for line in include_str!("builtins.txt").lines() {
            for name in line.split_whitespace() {
                if name.starts_with("#") { break } // comment
                assert_eq!(name, name.to_lowercase());
                s.insert(name);
            }
        }
        s
    };
}

fn get_func_def_name(func: &Function) -> String {
    let mut res = func.name.id.clone();
    for param in func.params.iter() {
        write!(res, " %'{}'", param.id).unwrap();
    }
    escape_xml(&res).into_owned()
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

    Redefine { name: Ident, previous: Ident },
    RedefineBuiltin { name: Ident },

    ExpectedPlural { name: Ident },
    BreedNotDefined { name: Ident },
    VariableNoTDefined { name: Ident },
    FunctionNotDefined { name: Ident },

    FunctionArgCount { func: Ident, invoke_span: Span, got: usize, expected: usize },
    NonReporterInExpr { func: Ident, invoke_span: Span },
    
    ReportInNonReporter { func: Ident, report_span: Span },
    UnreachableCode { func: Ident, unreachable_span: Span },
}
impl<'a> From<ParseError<usize, Token<'a>, &'a str>> for Error<'a> {
    fn from(e: ParseError<usize, Token<'a>, &'a str>) -> Self {
        Error::Parse(e)
    }
}

#[derive(Default)]
struct EntityInfo<'a> { props: BTreeMap<&'a str, &'a Ident> }

struct GlobalSymbol<'a> { ident: &'a Ident }
struct BreedSymbol<'a> { ident: &'a Ident, is_plural: bool, info: Rc<RefCell<EntityInfo<'a>>> }

#[derive(Default)]
pub struct Program<'a> {
    globals: LinkedHashMap<&'a str, GlobalSymbol<'a>>,
    breeds: LinkedHashMap<&'a str, BreedSymbol<'a>>,
    funcs: LinkedHashMap<&'a str, &'a Function>,
    patches: EntityInfo<'a>,
}
impl<'a> Program<'a> {
    // checks for validity in (only) the global scope
    fn validate_define_global<'b>(&self, ident: &Ident) -> Result<(), Error<'b>> {
        let prev = self.globals.get(ident.id.as_str()).map(|s| s.ident)
            .or(self.breeds.get(ident.id.as_str()).map(|s| s.ident))
            .or(self.funcs.get(ident.id.as_str()).map(|s| &s.name));
        if let Some(prev) = prev {
            return Err(Error::Redefine { name: ident.clone(), previous: prev.clone() });
        }
        if BUILTIN_NAMES.contains(ident.id.as_str()) {
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
    fn ensure_var_defined<'b>(&self, scopes: &[LinkedHashMap<&str, &Ident>], ident: &Ident) -> Result<(), Error<'b>> {
        for scope in scopes.iter().rev() {
            if scope.contains_key(ident.id.as_str()) { return Ok(()) }
        }
        if self.globals.contains_key(ident.id.as_str()) { return Ok(()) }
        Err(Error::VariableNoTDefined { name: ident.clone() })
    }
    fn format_func_call<'b>(&self, scopes: &mut Vec<LinkedHashMap<&str, &Ident>>, func: &Function, args: &[Expr], invoke_span: Span) -> Result<String, Error<'b>> {
        if func.params.len() != args.len() {
            return Err(Error::FunctionArgCount { func: func.name.clone(), invoke_span, got: args.len(), expected: func.params.len() });
        }

        let mut res = format!(r#"<custom-block s="{}">"#, get_func_name(func));
        for arg in args.iter() {
            res += &self.generate_expr_script(scopes, arg)?;
        }
        res += "</custom-block>";
        Ok(res)
    }
    fn generate_expr_script<'b>(&self, scopes: &mut Vec<LinkedHashMap<&str, &Ident>>, expr: &Expr) -> Result<String, Error<'b>> {
        Ok(match expr {
            Expr::Choice { condition, a, b, .. } => format!(r#"<block s="reportIfElse">{}{}{}</block>"#, self.generate_expr_script(scopes, condition)?, self.generate_expr_script(scopes, a)?, self.generate_expr_script(scopes, b)?),

            Expr::And { a, b, .. } => format!(r#"<block s="reportAnd">{}{}</block>"#, self.generate_expr_script(scopes, a)?, self.generate_expr_script(scopes, b)?),
            Expr::Or { a, b, .. } => format!(r#"<block s="reportOr">{}{}</block>"#, self.generate_expr_script(scopes, a)?, self.generate_expr_script(scopes, b)?),
            Expr::Xor { a, b, .. } | Expr::Neq { a, b, .. } => format!(r#"<block s="reportNot"><block s="reportEquals">{}{}</block></block>"#, self.generate_expr_script(scopes, a)?, self.generate_expr_script(scopes, b)?),
            Expr::Equ { a, b, .. } => format!(r#"<block s="reportEquals">{}{}</block>"#, self.generate_expr_script(scopes, a)?, self.generate_expr_script(scopes, b)?),
            
            Expr::Less { a, b, .. } => format!(r#"<block s="reportLessThan">{}{}</block>"#, self.generate_expr_script(scopes, a)?, self.generate_expr_script(scopes, b)?),
            Expr::LessEq { a, b, .. } => format!(r#"<block s="reportNot"><block s="reportGreaterThan">{}{}</block></block>"#, self.generate_expr_script(scopes, a)?, self.generate_expr_script(scopes, b)?),
            Expr::Great { a, b, .. } => format!(r#"<block s="reportGreaterThan">{}{}</block>"#, self.generate_expr_script(scopes, a)?, self.generate_expr_script(scopes, b)?),
            Expr::GreatEq { a, b, .. } => format!(r#"<block s="reportNot"><block s="reportLessThan">{}{}</block></block>"#, self.generate_expr_script(scopes, a)?, self.generate_expr_script(scopes, b)?),

            Expr::Add { a, b, .. } => format!(r#"<block s="reportSum">{}{}</block>"#, self.generate_expr_script(scopes, a)?, self.generate_expr_script(scopes, b)?),
            Expr::Sub { a, b, .. } => format!(r#"<block s="reportDifference">{}{}</block>"#, self.generate_expr_script(scopes, a)?, self.generate_expr_script(scopes, b)?),
            
            Expr::Mul { a, b, .. } => format!(r#"<block s="reportProduct">{}{}</block>"#, self.generate_expr_script(scopes, a)?, self.generate_expr_script(scopes, b)?),
            Expr::Div { a, b, .. } => format!(r#"<block s="reportQuotient">{}{}</block>"#, self.generate_expr_script(scopes, a)?, self.generate_expr_script(scopes, b)?),
            Expr::Mod { a, b, .. } => format!(r#"<block s="reportModulus">{}{}</block>"#, self.generate_expr_script(scopes, a)?, self.generate_expr_script(scopes, b)?),
            
            Expr::Pow { a, b, .. } => format!(r#"<block s="reportPower">{}{}</block>"#, self.generate_expr_script(scopes, a)?, self.generate_expr_script(scopes, b)?),
            
            Expr::Not { val, .. } => format!(r#"<block s="reportNot">{}</block>"#, self.generate_expr_script(scopes, val)?),
            Expr::Neg { val, .. } => format!(r#"<block s="reportMonadic"><l><option>neg</option></l>{}</block>"#, self.generate_expr_script(scopes, val)?),

            Expr::FnCall(call) => match self.funcs.get(call.name.id.as_str()) {
                None => return Err(Error::FunctionNotDefined { name: call.name.clone() }),
                Some(func) => {
                    if !func.reports { return Err(Error::NonReporterInExpr { func: func.name.clone(), invoke_span: call.span() }) }
                    self.format_func_call(scopes, func, &call.args, call.span())?
                }
            }

            Expr::Value(Value::Number(num)) => format!("<l>{}</l>", escape_xml(&num.value)),
            Expr::Value(Value::Text(text)) => format!("<l>{}</l>", escape_xml(&text.content)),
            Expr::Value(Value::List(list)) => {
                let mut res = r#"<block s="reportNewList"><list>"#.to_string();
                for value in &list.values {
                    res += &self.generate_expr_script(scopes, value)?;
                }
                res += "</list></block>";
                res
            }
            Expr::Value(Value::Ident(ident)) => match ident.id.as_str() {
                x @ ("true" | "false") => format!(r#"<block s="reportBoolean"><l><bool>{}</bool></l></block>"#, x),
                _ => {
                    self.ensure_var_defined(&*scopes, ident)?;
                    format!(r#"<block var="{}"/>"#, escape_xml(&ident.id))
                }
            }
        })
    }
    fn generate_script<'b>(&self, scopes: &mut Vec<LinkedHashMap<&'a str, &'a Ident>>, stmts: &'a [Stmt], func: &Function) -> Result<String, Error<'b>> {
        scopes.push(Default::default()); // generate a new scope for this script

        let mut script = String::new();
        let mut has_terminated = false;

        for stmt in stmts {
            if has_terminated { return Err(Error::UnreachableCode { func: func.name.clone(), unreachable_span: stmt.span() }) }
            match stmt {
                Stmt::Report(report) => {
                    if !func.reports { return Err(Error::ReportInNonReporter { func: func.name.clone(), report_span: report.span() }) }
                    write!(script, r#"<block s="doReport">{}</block>"#, self.generate_expr_script(scopes, &report.value)?).unwrap();
                    has_terminated = true;
                }
                Stmt::IfElse(ifelse) => match &ifelse.otherwise {
                    None => write!(script, r#"<block s="doIf">{}<script>{}</script></block>"#,
                        self.generate_expr_script(scopes, &ifelse.condition)?, self.generate_script(scopes, &ifelse.then, func)?).unwrap(),
                    Some(otherwise) => write!(script, r#"<block s="doIfElse">{}<script>{}</script><script>{}</script></block>"#,
                        self.generate_expr_script(scopes, &ifelse.condition)?, self.generate_script(scopes, &ifelse.then, func)?, self.generate_script(scopes, otherwise, func)?).unwrap(),
                }
                Stmt::FnCall(call) => match self.funcs.get(call.name.id.as_str()) {
                    None => return Err(Error::FunctionNotDefined { name: call.name.clone() }),
                    Some(func) => match (func.reports, self.format_func_call(scopes, func, &call.args, call.span())?) {
                        (true, x) => write!(script, r#"<block s="doRun"><block s="reifyReporter"><autolambda>{}</autolambda></block></block>"#, x).unwrap(),
                        (false, x) => script += &x,
                    }
                }
                Stmt::VarDecl(vardecl) => {
                    let value_script = self.generate_expr_script(scopes, &vardecl.value)?; // must evaluate before defining the symbol

                    self.validate_define_lexical(&vardecl.name, scopes)?;
                    scopes.last_mut().unwrap().insert(&vardecl.name.id, &vardecl.name);

                    write!(script, r#"<block s="doDeclareVariables"><list><l>{name}</l></list></block><block s="doSetVar"><l>{name}</l>{value}</block>"#,
                        name = escape_xml(&vardecl.name.id), value = value_script).unwrap();
                }
                Stmt::Assign(assign) => {
                    self.ensure_var_defined(scopes, &assign.name)?;
                    write!(script, r#"<block s="doSetVar"><l>{}</l>{}</block>"#, escape_xml(&assign.name.id), self.generate_expr_script(scopes, &assign.value)?).unwrap();
                }
                x => panic!("unimplemented stmt: {:?}", x),
            }
        }

        scopes.pop(); // remove the scope we created
        Ok(script)
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
                Item::Own(own) => owns.push(own), // just gather these up for after the first pass
            }
        }
        // process all the own drectives we stored
        for own in owns {
            fn add_props<'a>(target: &mut BTreeMap<&'a str, &'a Ident>, props: &'a [Ident]) {
                for prop in props {
                    target.insert(&prop.id, prop);
                }
            }
            
            for prop in own.props.iter() {
                program.validate_define_global(prop)?; // validate the names once up-front
            }
            match own.plural_owner.id.as_str() {
                "turtles" => for target in program.breeds.values() {
                    add_props(&mut target.info.borrow_mut().props, &own.props);
                },
                "patches" => add_props(&mut program.patches.props, &own.props),
                "turtle" | "patch" => return Err(Error::ExpectedPlural { name: own.plural_owner.clone() }),
                x => match program.breeds.get(x) {
                    None => return Err(Error::BreedNotDefined { name: own.plural_owner.clone() }),
                    Some(target) => {
                        if !target.is_plural { return Err(Error::ExpectedPlural { name: own.plural_owner.clone() }) }
                        add_props(&mut target.info.borrow_mut().props, &own.props);
                    }
                }
            }
        }

        Ok(program) // we're now in a semi-valid state (at least at the global scope)
    }
}

fn parse_breed_sprite<'b>(breed_sprites: &mut String, breed: &BreedSymbol, index: (usize, usize)) -> Result<(), Error<'b>> {
    assert!(breed.is_plural);
    let ang = 2.0 * f64c::PI * (index.0 as f64 / index.1 as f64);
    let radius = if index.1 >= 2 { 100.0 } else { 0.0 };
    let color = HSV::new(ang as f32 * 180.0 / f32c::PI, 0.5, 0.9).to_rgb().to_inner();

    write!(breed_sprites, r#"<sprite name="{name}" x="{x}" y="{y}" heading="{heading}" color="{color}"  pen="middle"><blocks></blocks><variables>"#,
        name = escape_xml(&breed.ident.id),
        x = ang.sin() * radius,
        y = ang.cos() * radius,
        heading = ang * 180.0 / f64c::PI,
        color = Punctuated(&[color.0, color.1, color.2], ",")).unwrap();
    for var in breed.info.borrow().props.keys() {
        write!(breed_sprites, r#"<variable name="{}"><l>0</l></variable>"#, escape_xml(var)).unwrap();
    }
    write!(breed_sprites, r#"</variables><scripts></scripts></sprite>"#).unwrap();

    Ok(())
}
fn parse_function<'a, 'b>(custom_blocks: &mut String, program: &Program<'a>, scopes: &mut Vec<LinkedHashMap<&'a str, &'a Ident>>, func: &'a Function) -> Result<(), Error<'b>> {
    assert!(scopes.is_empty());
    scopes.push(Default::default()); // add a new scope for the function parameters

    write!(custom_blocks, r#"<block-definition s="{}" type="{}" category="custom"><inputs>{}</inputs>"#,
        get_func_def_name(func), if func.reports { "reporter" } else { "command" },
        r#"<input type="%s"></input>"#.repeat(func.params.len())).unwrap();

    for param in func.params.iter() {
        program.validate_define_lexical(param, &scopes)?;
        assert!(scopes.last_mut().unwrap().insert(&param.id, param).is_none());
    }
    let script = program.generate_script(scopes, &func.stmts, &func)?;
    if !script.is_empty() { // if we generate an empty <script> tag it makes it uneditable in NetsBlox
        write!(custom_blocks, "<script>{}</script>", script).unwrap();
    }

    write!(custom_blocks, "</block-definition>").unwrap();

    scopes.pop(); // remove the scope we added
    Ok(())
}
pub fn parse<'b>(project_name: &str, input: &'b str) -> Result<String, Error<'b>> {
    let items = ast::parse(input)?;
    let program = Program::init_global(&items)?;
    
    let mut custom_blocks = String::new();
    let mut scopes = Vec::with_capacity(16);
    for func in program.funcs.values() {
        parse_function(&mut custom_blocks, &program, &mut scopes, func)?;
    }

    let mut breed_sprites = String::new();
    let mut all_breed_vars: BTreeSet<&str> = Default::default();
    for (i, breed) in program.breeds.values().filter(|s| s.is_plural).enumerate() {
        all_breed_vars.extend(breed.info.borrow().props.keys()); // accumulate breed vars (sorted order)
        parse_breed_sprite(&mut breed_sprites, breed, (i, program.breeds.len() / 2))?;
    }

    Ok(format!(include_str!("template.xml"),
        project_name = project_name,
        custom_blocks = custom_blocks,
        breed_sprites = breed_sprites,
        all_breed_vars = escape_xml(&Punctuated(&all_breed_vars, "\r").to_string()),
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