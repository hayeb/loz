use std::{fs, env, process};

mod parser;
mod typer;
mod interpreter;

#[macro_use]
extern crate pest_derive;

#[macro_use]
extern crate lazy_static;

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
    let typer_result = typer::_type(&ast);
    if let Err(err) = typer_result {
        err.into_iter().for_each(|e| eprintln!("{}", e));
        process::exit(1);
    }

    let result = interpreter::interpret(&typer_result.unwrap());
    if let Err(e) = result {
        eprintln!("Runtime error: {:?}",e)
    }
}
