mod ast;

use std::collections::HashSet;
use linked_hash_map::LinkedHashMap;

use std::cell::RefCell;
use std::rc::Rc;
use std::fmt::Write;

use ast::*;
pub use ast::{Ident, Span};

use lalrpop_util::{ParseError, lexer::Token};

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

#[derive(Debug)]
pub enum Error<'a> {
    Parse(ParseError<usize, Token<'a>, &'a str>),
    Redefine { name: Ident, previous: Ident },
    RedefineBuiltin { name: Ident },
    BreedNotDefined { name: Ident },
    ExpectedPlural { name: Ident },
}
impl<'a> From<ParseError<usize, Token<'a>, &'a str>> for Error<'a> {
    fn from(e: ParseError<usize, Token<'a>, &'a str>) -> Self {
        Error::Parse(e)
    }
}

#[derive(Default)]
struct EntityInfo { props: LinkedHashMap<String, Ident> }

struct GlobalSymbol { ident: Ident }
struct BreedSymbol { ident: Ident, is_plural: bool, info: Rc<RefCell<EntityInfo>> }

#[derive(Default)]
pub struct Program {
    globals: LinkedHashMap<String, GlobalSymbol>,
    breeds: LinkedHashMap<String, BreedSymbol>,
    funcs: LinkedHashMap<String, Function>,
    patches: EntityInfo,
}
impl Program {
    // checks for validity in (only) the global scope
    fn validate_define_global<'a>(&self, ident: &Ident) -> Result<(), Error<'a>> {
        let prev = self.globals.get(&ident.id).map(|s| &s.ident)
            .or(self.breeds.get(&ident.id).map(|s| &s.ident))
            .or(self.funcs.get(&ident.id).map(|s| &s.name));
        if let Some(prev) = prev {
            return Err(Error::Redefine { name: ident.clone(), previous: prev.clone() });
        }
        if BUILTIN_NAMES.contains(ident.id.as_str()) {
            return Err(Error::RedefineBuiltin { name: ident.clone() });
        }
        Ok(())
    }
    fn validate_define_lexical<'a>(&self, ident: &Ident, scopes: &[LinkedHashMap<&str, &Ident>]) -> Result<(), Error<'a>> {
        for scope in scopes.iter().rev() {
            if let Some(&prev) = scope.get(ident.id.as_str()) {
                return Err(Error::Redefine { name: ident.clone(), previous: prev.clone() });
            }
        }
        self.validate_define_global(ident)
    }

    // fn validate_expr_recursive<'a>(&self, scopes: &Vec<HashMap<&str, &Ident>>, expr: &Expr) -> Result<(), Error<'a>> {
    //     match expr {
    //         Expr::Value(Value::List(list)) => for item in list {
    //             self.validate_expr_recursive(scopes, item)?;
    //         },
    //         Expr::Value(Value::Text(_) | Value::Number(_)) => Ok(()),
    //     }
    // }
    // fn validate_func_recursive<'a>(&self, scopes: &mut Vec<HashMap<&str, &Ident>>, stmts: &[Stmt]) -> Result<(), Error<'a>> {
    //     for stmt in stmts {
    //         match stmt {
    //             Stmt::VarDecl(VarDecl { name, value, lspan: _ }) => {

    //             }
    //         }
    //     }
    //     Ok(())
    // }
    fn parse(input: &str) -> Result<Program, Error> {
        let mut program = Program::default();
        let mut owns: Vec<Own> = Vec::with_capacity(16);
    
        // initial pass - collect all the globals, breeds, and functions (names at global scope)
        for item in ast::parse(input)? {
            match item {
                Item::Globals(Globals { idents, .. }) => for ident in idents {
                    program.validate_define_global(&ident)?;
                    assert!(program.globals.insert(ident.id.clone(), GlobalSymbol { ident }).is_none());
                }
                Item::Breed(Breed { plural, singular, .. }) => {
                    let info = Rc::new(RefCell::new(EntityInfo::default()));
                    for (ident, is_plural) in [(plural, true), (singular, false)] {
                        program.validate_define_global(&ident)?;
                        assert!(program.breeds.insert(ident.id.clone(), BreedSymbol { ident, is_plural, info: info.clone() }).is_none());
                    }
                }
                Item::Function(func) => {
                    program.validate_define_global(&func.name)?;
                    assert!(program.funcs.insert(func.name.id.clone(), func).is_none());
                }
                Item::Own(own) => owns.push(own), // just gather these up for after the first pass
            }
        }
        // process all the own drectives we stored
        for own in owns {
            fn add_props(target: &mut LinkedHashMap<String, Ident>, props: Vec<Ident>) {
                for prop in props {
                    target.insert(prop.id.clone(), prop);
                }
            }
            
            for prop in own.props.iter() {
                program.validate_define_global(prop)?; // validate the names once up-front
            }
            match own.plural_owner.id.as_str() {
                "turtles" => for target in program.breeds.values() {
                    add_props(&mut target.info.borrow_mut().props, own.props.clone());
                },
                "patches" => add_props(&mut program.patches.props, own.props),
                "turtle" | "patch" => return Err(Error::ExpectedPlural { name: own.plural_owner }),
                x => match program.breeds.get(x) {
                    None => return Err(Error::BreedNotDefined { name: own.plural_owner }),
                    Some(target) => {
                        if !target.is_plural { return Err(Error::ExpectedPlural { name: own.plural_owner }) }
                        add_props(&mut target.info.borrow_mut().props, own.props.clone());
                    }
                }
            }
        }

        Ok(program) // we're now in a semi-valid state (at least at the global scope)
    }
}

pub fn parse<'a>(project_name: &str, input: &'a str) -> Result<String, Error<'a>> {
    let program = Program::parse(input)?;
    let mut custom_blocks = String::new();

    let mut scopes = Vec::with_capacity(16);
    for func in program.funcs.values() {
        assert!(scopes.is_empty());
        scopes.push(LinkedHashMap::with_capacity(16));

    // <block-definition s="this-reports" type="reporter" category="operators">
    //     <code></code>
    //     <inputs></inputs>
    // </block-definition>

        let block_name = format!("{} {}", func.name.id,
            func.params.iter().map(|p| format!("%&apos;{}&apos;", p.id)).collect::<Vec<_>>().join(" "));
        write!(custom_blocks, r#"<block-definition s="{}" type="{}" category="custom"><code>"#,
            block_name.trim_end(), if func.reports { "reporter" } else { "command" }).unwrap();

        for param in func.params.iter() {
            program.validate_define_lexical(param, &scopes)?;
            assert!(scopes.last_mut().unwrap().insert(&param.id, param).is_none());
        }
        //program.validate_func_recursive(&mut scopes, &func.stmts)?;

        write!(custom_blocks, "</code><inputs>{}</inputs></block-definition>",
            r#"<input type="%s"></input>"#.repeat(func.params.len()).as_str()).unwrap();

        scopes.pop();
    }

    Ok(format!(include_str!("template.xml"),
        project_name = project_name,
        custom_blocks = custom_blocks,
    ))
}

#[test] fn test_prog_header() {
    let res = Program::parse(r#"
    breed [goats goat]
    breed [merps merp]
    turtles-own [ mtdews ]
    merps-own [ kfcs ]
    patches-own [ duck-count ]

    to-report commIt-sudoku
        report "rosebud"
    end
    "#).unwrap();

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