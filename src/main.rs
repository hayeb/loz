use std::{fs, env, process};

mod parser;
mod typer;

#[macro_use]
extern crate pest_derive;

#[macro_use]
extern crate lazy_static;

fn main() {
    let args: Vec<String> = env::args().collect();

    let filename = &args[1];

    let contents = fs::read_to_string(filename)
        .expect("Error reading from file: test/test.loz");

    let ast = parser::parse(&contents[..]);

    if let Err(err) = ast {
        eprintln!("{} {}", filename, err);
        process::exit(1);
    }

    let ast = ast.unwrap();
    println!("Parse result: {:#?}", ast);
    let typer_result = typer::_type(ast);
    if let Err(err) = typer_result {
        eprintln!("{:?}", err);
        process::exit(1);
    }
    let typer_result = typer_result.unwrap();
    println!("Typer result: {:?}", typer_result)
}
