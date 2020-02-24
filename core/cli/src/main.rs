use std::{fs, env, process};

use loz_compiler::parser;
use loz_compiler::inferencer;
use loz_compiler::interpreter;

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() < 2 {
        eprintln!("Usage: loz <file>");
        process::exit(2);
    }

    let filename = &args[1];

    let contents = fs::read_to_string(filename)
        .expect(&format!("Error reading from file: {}", filename));

    let ast = parser::parse(filename, &contents[..]);

    //println!("AST: {:#?}", ast);

    if let Err(err) = ast {
        eprintln!("{} {}", filename, err);
        process::exit(1);
    }

    let ast = ast.unwrap();
    let inference_result = inferencer::infer(&ast);
    if let Err(err) = inference_result {
        err.into_iter().for_each(|e| eprintln!("{}", e));
        process::exit(1);
    }

    let result = interpreter::interpret(&inference_result.unwrap());
    if let Err(e) = result {
        eprintln!("Runtime error: {:?}",e)
    }
}
