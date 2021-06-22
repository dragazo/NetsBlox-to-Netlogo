use std::ops::Range;

lalrpop_mod!(grammar);

use lalrpop_util::ParseError;
use lalrpop_util::lexer::Token;

pub type Error<'a> = ParseError<usize, Token<'a>, &'a str>;

fn clean_string(s: &str) -> String {
    assert!(s.len() >= 2);
    assert!({ let c = s.chars().next().unwrap(); c == '"' || c == '\'' });
    assert_eq!(s.chars().next().unwrap(), s.chars().rev().next().unwrap());

    let mut res = String::new();
    let mut chars = s[1..s.len()-1].chars().peekable();
    while let Some(c) = chars.next() {
        if c != '\\' {
            res.push(c);
            continue;
        }

        let escaped = match chars.next().unwrap() {
            '\\' => '\\',
            '"' => '"',
            '\'' => '\'',
            't' => '\t',
            'n' => '\n',
            x => panic!("unknown escape sequence: \\{}", x),
        };
        res.push(escaped);
    }
    res
}
fn quote_string(s: &str) -> String {
    let mut res = String::new();
    res.push('"');
    for c in s.chars() {
        match c {
            '"' => { res.push('\\'); res.push('"'); }
            '\r' => { res.push('\\'); res.push('r'); }
            '\n' => { res.push('\\'); res.push('n'); }
            '\t' => { res.push('\\'); res.push('t'); }
            _ => res.push(c),
        }
    }
    res.push('"');
    res
}
fn indent(s: &str) -> String {
    s.lines().map(|x| format!("    {}", x)).collect::<Vec<_>>().join("\n")
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub struct Span(usize, usize);
impl Span {
    pub fn to_range(&self) -> Range<usize> { self.0..self.1 }
}

pub trait Spanned {
    fn span(&self) -> Span;
}
macro_rules! raw_span_impl {
    ($($t:ty),+) => {$(
        impl Spanned for $t { fn span(&self) -> Span { self.raw_span } }
    )+}
}

#[derive(Debug, Clone)]
pub enum Item {
    Globals(Globals),
    Breed(Breed),
    Own(Own),
    Function(Function),
}
impl Spanned for Item {
    fn span(&self) -> Span {
        match self {
            Item::Globals(x) => x.span(),
            Item::Breed(x) => x.span(),
            Item::Own(x) => x.span(),
            Item::Function(x) => x.span(),
        }
    }
}

#[derive(Debug, Clone)] pub struct Globals { idents: Vec<Ident>, raw_span: Span }
#[derive(Debug, Clone)] pub struct Breed { plural: Ident, singular: Ident, raw_span: Span }
#[derive(Debug, Clone)] pub struct Own { plural_owner: Ident, props: Vec<Ident>, raw_span: Span }
#[derive(Debug, Clone)] pub struct Function { name: Ident, params: Vec<Ident>, reports: bool, stmts: Vec<Stmt>, raw_span: Span }

raw_span_impl! { Globals, Breed, Own, Function }

#[derive(Debug, Clone)]
pub enum Stmt {
    Report(Report),
    IfElse(IfElse),
    FnCall(FnCall),
    VarDecl(VarDecl),
    Assign(Assign),
    Repeat(Repeat),
}
impl Spanned for Stmt {
    fn span(&self) -> Span {
        match self {
            Stmt::Report(x) => x.span(),
            Stmt::IfElse(x) => x.span(),
            Stmt::FnCall(x) => x.span(),
            Stmt::VarDecl(x) => x.span(),
            Stmt::Assign(x) => x.span(),
            Stmt::Repeat(x) => x.span(),
        }
    }
}

#[derive(Debug, Clone)] pub struct Report { value: Expr, lspan: usize }
#[derive(Debug, Clone)] pub struct IfElse { condition: Expr, then: Vec<Stmt>, otherwise: Option<Vec<Stmt>>, raw_span: Span }
#[derive(Debug, Clone)] pub struct VarDecl { name: Ident, value: Expr, lspan: usize }
#[derive(Debug, Clone)] pub struct Assign { name: Ident, value: Expr, lspan: usize }
#[derive(Debug, Clone)] pub struct Repeat { count: Expr, stmts: Vec<Stmt>, raw_span: Span }

raw_span_impl! { IfElse, Repeat }
impl Spanned for Report { fn span(&self) -> Span { Span(self.lspan, self.value.span().1) } }
impl Spanned for VarDecl { fn span(&self) -> Span { Span(self.lspan, self.value.span().1) } }
impl Spanned for Assign { fn span(&self) -> Span { Span(self.lspan, self.value.span().1) } }

#[derive(Debug, Clone)]
pub enum Expr {
    Choice { condition: Box<Expr>, a: Box<Expr>, b: Box<Expr>, raw_span: Span },

    And { a: Box<Expr>, b: Box<Expr> },
    Or { a: Box<Expr>, b: Box<Expr> },
    Xor { a: Box<Expr>, b: Box<Expr> },

    Equ { a: Box<Expr>, b: Box<Expr> },
    Neq { a: Box<Expr>, b: Box<Expr> },

    Less { a: Box<Expr>, b: Box<Expr> },
    LessEq { a: Box<Expr>, b: Box<Expr> },
    Great { a: Box<Expr>, b: Box<Expr> },
    GreatEq { a: Box<Expr>, b: Box<Expr> },

    Add { a: Box<Expr>, b: Box<Expr> },
    Sub { a: Box<Expr>, b: Box<Expr> },

    Mul { a: Box<Expr>, b: Box<Expr> },
    Div { a: Box<Expr>, b: Box<Expr> },
    Mod { a: Box<Expr>, b: Box<Expr> },

    Pow { a: Box<Expr>, b: Box<Expr> },

    Not { val: Box<Expr>, lspan: usize },

    FnCall(FnCall),
    Value(Value),
}
impl Spanned for Expr {
    fn span(&self) -> Span {
        match self {
            Expr::Choice { raw_span, .. } => *raw_span,

            Expr::And { a, b } => Span(a.span().0, b.span().1),
            Expr::Or { a, b } => Span(a.span().0, b.span().1),
            Expr::Xor { a, b } => Span(a.span().0, b.span().1),

            Expr::Equ { a, b } => Span(a.span().0, b.span().1),
            Expr::Neq { a, b } => Span(a.span().0, b.span().1),

            Expr::Less { a, b } => Span(a.span().0, b.span().1),
            Expr::LessEq { a, b } => Span(a.span().0, b.span().1),
            Expr::Great { a, b } => Span(a.span().0, b.span().1),
            Expr::GreatEq { a, b } => Span(a.span().0, b.span().1),

            Expr::Add { a, b } => Span(a.span().0, b.span().1),
            Expr::Sub { a, b } => Span(a.span().0, b.span().1),

            Expr::Mul { a, b } => Span(a.span().0, b.span().1),
            Expr::Div { a, b } => Span(a.span().0, b.span().1),
            Expr::Mod { a, b } => Span(a.span().0, b.span().1),

            Expr::Pow { a, b } => Span(a.span().0, b.span().1),

            Expr::Not { val, lspan } => Span(*lspan, val.span().1),

            Expr::FnCall(x) => x.span(),
            Expr::Value(x) => x.span(),
        }
    }
}

#[derive(Debug, Clone)] pub struct FnCall { name: Ident, args: Vec<Expr> }
impl Spanned for FnCall {
    fn span(&self) -> Span {
        let s = self.name.span();
        Span(s.0, self.args.last().map(|s| s.span().1).unwrap_or(s.1))
    }
}

#[derive(Debug, Clone)]
pub enum Value {
    Ident(Ident),
    Number(Number),
    Text(Text),
    List(List),
}
impl Spanned for Value {
    fn span(&self) -> Span {
        match self {
            Value::Ident(x) => x.span(),
            Value::Number(x) => x.span(),
            Value::Text(x) => x.span(),
            Value::List(x) => x.span(),
        }
    }
}

#[derive(Debug, Clone)] pub struct Ident { id: String, raw_span: Span }
#[derive(Debug, Clone)] pub struct Number { value: String, raw_span: Span }
#[derive(Debug, Clone)] pub struct Text { content: String, raw_span: Span }
#[derive(Debug, Clone)] pub struct List { values: Vec<Expr>, raw_span: Span }

raw_span_impl! { Ident, Number, Text, List }

pub fn parse(program: &str) -> Result<Vec<Item>, Error> {
    grammar::ProgramParser::new().parse(program)
}

#[test] fn test_own() {
    let prog = r#"
    patches-own [ mud sticks mud-sticks ]
    turtles-own [ 경험치 ]
    dogs-own [ bones ]"#;
    let res = parse(prog).unwrap();
    assert_eq!(res.len(), 3);
    match &res[0] {
        Item::Own(own) => {
            assert_eq!(own.plural_owner.id, "patches");
            assert_eq!(own.props.len(), 3);
        }
        x => panic!("{:?}", x),
    }
    match &res[1] {
        Item::Own(own) => {
            assert_eq!(own.plural_owner.id, "turtles");
            assert_eq!(&prog[own.plural_owner.raw_span.to_range()], "turtles");
            assert_eq!(own.props.len(), 1);
            assert_eq!(own.props[0].id, "경험치");
            assert_eq!(&prog[own.props[0].raw_span.to_range()], "경험치");
        }
        x => panic!("{:?}", x),
    }
    match &res[2] {
        Item::Own(own) => assert_eq!(own.plural_owner.id, "dogs"),
        x => panic!("{:?}", x),
    }
}
#[test] fn test_fn_call() {
    let res = parse(r#"
    to-report go [x]
        report (list x 1.23 2+3 energy-vals 경험치 "hello world" (list 1 2))
        report (list)
        report (go x - 1)
        clear-all
        merp ; call a function taking no args
        die
        (muk-duk 6) ; call a function with one arg
    end"#).unwrap();
    assert_eq!(res.len(), 1);
    let go = match &res[0] {
        Item::Function(f) => f,
        x => panic!("{:?}", x),
    };
    assert_eq!(go.name.id, "go");
    assert_eq!(go.params.len(), 1);
    assert_eq!(go.params[0].id, "x");
    assert_eq!(go.reports, true);
    assert_eq!(go.stmts.len(), 7);

    match &go.stmts[0] {
        Stmt::Report(Report { value: Expr::Value(Value::List(x)), .. }) => assert_eq!(x.values.len(), 7),
        x => panic!("{:?}", x),
    }
    match &go.stmts[1] {
        Stmt::Report(Report { value: Expr::Value(Value::List(x)), .. }) => assert_eq!(x.values.len(), 0),
        x => panic!("{:?}", x),
    }
    match &go.stmts[2] {
        Stmt::Report(Report { value: Expr::FnCall(FnCall { name, args }), .. }) => {
            assert_eq!(name.id, "go");
            assert_eq!(args.len(), 1);
            match &args[0] {
                Expr::Sub { .. } => (),
                x => panic!("{:?}", x),
            }
        }
        x => panic!("{:?}", x),
    }
    match &go.stmts[3] {
        Stmt::FnCall(FnCall { name, args }) => {
            assert_eq!(name.id, "clear-all");
            assert_eq!(args.len(), 0);
        }
        x => panic!("{:?}", x),
    }
    match &go.stmts[4] {
        Stmt::FnCall(FnCall { name, args }) => {
            assert_eq!(name.id, "merp");
            assert_eq!(args.len(), 0);
        }
        x => panic!("{:?}", x),
    }
    match &go.stmts[5] {
        Stmt::FnCall(FnCall { name, args }) => {
            assert_eq!(name.id, "die");
            assert_eq!(args.len(), 0);
        }
        x => panic!("{:?}", x),
    }
    match &go.stmts[6] {
        Stmt::FnCall(FnCall { name, args }) => {
            assert_eq!(name.id, "muk-duk");
            assert_eq!(args.len(), 1);
        }
        x => panic!("{:?}", x),
    }
}
#[test] fn test_vars() {
    let res = parse(r#"
    to go ;func with no args
        let foo [1 2 3 4]
        set foo foo + 1
    end"#).unwrap();
    assert_eq!(res.len(), 1);
    let go = match &res[0] {
        Item::Function(f) => f,
        x => panic!("{:?}", x),
    };
    assert_eq!(go.name.id, "go");
    assert_eq!(go.params.len(), 0);
    assert_eq!(go.reports, false);
    assert_eq!(go.stmts.len(), 2);

    match &go.stmts[0] {
        Stmt::VarDecl(VarDecl { name, value, .. }) => {
            assert_eq!(name.id, "foo");
            match value {
                Expr::Value(Value::List(list)) => assert_eq!(list.values.len(), 4),
                x => panic!("{:?}", x),
            }
        }
        x => panic!("{:?}", x),
    }
    match &go.stmts[1] {
        Stmt::Assign(Assign { name, value, .. }) => {
            assert_eq!(name.id, "foo");
            match value {
                Expr::Add { a, .. } => match &**a {
                    Expr::Value(Value::Ident(ident)) => assert_eq!(ident.id, "foo"),
                    x => panic!("{:?}", x),
                }
                x => panic!("{:?}", x),
            }
        }
        x => panic!("{:?}", x),
    }
}
#[test] fn test_loops() {
    let res = parse(r#"
    to-report go-circle
        let merp 10
        repeat 36 [ (fd 1) (rt merp) ]
    end"#).unwrap();
    assert_eq!(res.len(), 1);
    let go = match &res[0] {
        Item::Function(f) => f,
        x => panic!("{:?}", x),
    };
    assert_eq!(go.name.id, "go-circle");
    assert_eq!(go.params.len(), 0);
    assert_eq!(go.reports, true);
    assert_eq!(go.stmts.len(), 2);

    match &go.stmts[1] {
        Stmt::Repeat(Repeat { count, stmts, .. }) => {
            match count {
                Expr::Value(Value::Number(s)) => assert_eq!(s.value, "36"),
                x => panic!("{:?}", x),
            }
            assert_eq!(stmts.len(), 2);
            match &stmts[0] {
                Stmt::FnCall(FnCall { name, args, .. }) => {
                    assert_eq!(name.id, "fd");
                    assert_eq!(args.len(), 1);
                }
                x => panic!("{:?}", x),
            }
            match &stmts[1] {
                Stmt::FnCall(FnCall { name, args, .. }) => {
                    assert_eq!(name.id, "rt");
                    assert_eq!(args.len(), 1);
                    match &args[0] {
                        Expr::Value(Value::Ident(ident)) => assert_eq!(ident.id, "merp"),
                        x => panic!("{:?}", x),
                    }
                }
                x => panic!("{:?}", x),
            }
        }
        x => panic!("{:?}", x),
    }
}