use std::{env, fs, process};

use clap::{App, Arg};

use loz_compiler::inferencer;
use loz_compiler::interpreter;
use loz_compiler::parser;

const VERSION: &'static str = env!("CARGO_PKG_VERSION");

fn main() {
    let matches = App::new("Loz Compiler")
        .version(VERSION)
        .author("Haye Böhm <haye.bohm@gmail.com>")
        .about("The Loz compiler!")
        .arg(Arg::with_name("file")
            .index(1)
            .required(true)
            .help("The file to compile"))

        .arg(Arg::with_name("print_ast")
            .short("p")
            .long("print-ast")
            .help("Toggles whether to print the AST as parsed  by the parser"))

        .arg(Arg::with_name("print_inferred_types")
            .short("t")
            .long("print-inferred-types")
            .help("Toggles wether to print the inferred types of functions without a type declaration")
        )

        .get_matches();

    let filename = matches.value_of("file").unwrap();

    let contents = fs::read_to_string(filename)
        .expect(&format!("Error reading from file: {}", filename));

    let ast = parser::parse(&filename.to_string(), &contents[..]);

    if let Err(err) = ast {
        eprintln!("{} {}", filename, err);
        process::exit(1);
    }

    let ast = ast.unwrap();

    if matches.is_present("print_ast") {
        println!("Parsed AST: {:#?}", ast);
    }
    let inference_result = inferencer::infer(&ast, matches.is_present("print_inferred_types"));
    if let Err(err) = inference_result {
        err.into_iter().for_each(|e| eprintln!("{}", e));
        process::exit(1);
    }

    let result = interpreter::interpret(&inference_result.unwrap());
    if let Err(e) = result {
        eprintln!("Runtime error: {:?}", e)
    }
}
