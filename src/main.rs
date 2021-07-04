use std::fs::File;
use std::io::BufReader;

use nb2nl::{xml2nl::Netlogo, nl2xml};

fn main() {
    let args: Vec<_> = std::env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: {} [input]", args[0]);
        std::process::exit(1);
    }

    let input = &args[1];
    if input.ends_with(".xml") {
        let xml = BufReader::new(File::open(input).expect("failed to open file"));
        let netlogo = Netlogo::parse_xml(xml).expect("failed to translate");
        println!("{}", netlogo);
    }
    else if input.ends_with(".nlogo") {
        let content = std::fs::read_to_string(input).expect("failed to open file");
        let prog_stop = content.find("@#$#@#$#@").unwrap_or(content.len());
        let program = &content[..prog_stop];

        let xml = nl2xml::parse(&input[..input.len()-6], program).expect("failed to translate");
        println!("{}", xml);
    }
    else {
        eprintln!("unknown input file type");
        std::process::exit(1);
    }
}
