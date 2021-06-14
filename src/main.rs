use std::fs::File;
use std::io::BufReader;

use nb2nl::Netlogo;

fn main() {
    let args: Vec<_> = std::env::args().collect();
    if args.len() != 2 {
        eprintln!("usage: {} [NetsBlox project xml]", args[0]);
        std::process::exit(1);
    }

    let xml = BufReader::new(File::open(&args[1]).expect("failed to open file"));
    let netlogo = Netlogo::parse_xml(xml).expect("failed to translate");
    println!("{}", netlogo);
}
