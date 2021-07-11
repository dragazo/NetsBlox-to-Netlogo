use std::collections::{HashSet, HashMap};

pub fn parse_idents(input: &str) -> HashSet<&str> {
    let mut s = HashSet::new();
    for line in input.lines() {
        for name in line.split_whitespace() {
            if name.starts_with("#") { break }
            debug_assert_eq!(name, name.to_lowercase());
            s.insert(name);
        }
    }
    s
}
pub fn parse_ws_pairs(input: &str) -> HashMap<&str, &str> {
    let mut s = HashMap::new();
    for line in input.lines() {
        let mut items = line.split_whitespace();
        if let Some(a) = items.next() {
            if a.starts_with("#") { continue }
            let b = items.next().unwrap();
            debug_assert!(!b.starts_with("#"));
            let c = items.next();
            debug_assert!(c.is_none() || c.unwrap().starts_with("#"));
            debug_assert_eq!(s.insert(a, b), None);
        }
    }
    s
}
pub fn parse_ws_rest(input: &str) -> HashMap<&str, &str> {
    let mut s = HashMap::new();
    for line in input.lines() {
        if let Some(ident) = line.split_whitespace().next() {
            if ident.starts_with('#') { continue }
            let res = line[ident.len()..].trim();
            debug_assert!(!res.is_empty());
            debug_assert_eq!(s.insert(ident, res), None);
        }
    }
    s
}
pub fn reverse_mapping<'a, 'b>(src: &HashMap<&'a str, &'b str>) -> HashMap<&'b str, &'a str> {
    let mut s = HashMap::with_capacity(src.len());
    for (&a, &b) in src.iter() {
        debug_assert_eq!(s.insert(b, a), None); // src must be injective
    }
    s
}

lazy_static! {
    pub static ref GLOBAL_SCOPE: HashSet<&'static str> = parse_idents(include_str!("globals.txt"));
    pub static ref FALSE_GLOBAL_SCOPE: HashSet<&'static str> = parse_idents(include_str!("false-globals.txt"));
    pub static ref RESERVED_WORDS: HashSet<&'static str> = parse_idents(include_str!("reserved.txt"));
    pub static ref NL2NB_PATCH_PROP_RENAMES: HashMap<&'static str, &'static str> = parse_ws_rest(include_str!("patch-prop-renames.txt"));
    pub static ref NB2NL_PATCH_PROP_RENAMES: HashMap<&'static str, &'static str> = reverse_mapping(&NL2NB_PATCH_PROP_RENAMES);
}
