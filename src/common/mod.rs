use std::collections::BTreeSet;

fn parse_idents(input: &str) -> BTreeSet<&str> {
    let mut s = BTreeSet::new();
    for line in input.lines() {
        for name in line.split_whitespace() {
            if name.starts_with("#") { break } // comment
            debug_assert_eq!(name, name.to_lowercase());
            s.insert(name);
        }
    }
    s
}

lazy_static! {
    pub static ref GLOBAL_SCOPE: BTreeSet<&'static str> = parse_idents(include_str!("globals.txt"));
    pub static ref RESERVED_WORDS: BTreeSet<&'static str> = parse_idents(include_str!("reserved.txt"));
}