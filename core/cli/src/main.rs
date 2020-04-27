use std::{env, fs, process};

use clap::{App, Arg};

use loz_compiler::inferencer::InferencerOptions;
use loz_compiler::interpreter;
use loz_compiler::module_system;
use loz_compiler::module_system::compile_modules;
use std::path::PathBuf;

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
            .help("Toggles whether to print the inferred types of functions without a type declaration"))

         .arg(Arg::with_name("working_directory")
             .short("d")
             .long("working-directory")
             .help("The working directory")
             .takes_value(true))

        .get_matches();

    let filename = matches.value_of("file").unwrap();
    let working_directory = matches.value_of("working_directory")
            .map(|wd| {
                let pb = PathBuf::from(wd);
                if pb.is_relative() {
                    let mut cwd = env::current_dir().unwrap();
                    cwd.push(pb);
                    return cwd;
                }
                return pb;
            })
            .unwrap_or_else(|| env::current_dir().unwrap());
    let infer_options = InferencerOptions {
        print_types: matches.is_present("print_inferred_types"),
        is_main_module: true,
    };
    let result = compile_modules(filename, &working_directory, &infer_options);
    println!("Result: {:?}", result);

    // let contents =
    //     fs::read_to_string(filename).expect(&format!("Error reading from file: {}", filename));
    //
    // let ast = parser::parse(&filename.to_string(), &contents[..]);
    //
    // if let Err(err) = ast {
    //     eprintln!("{} {}", filename, err);
    //     process::exit(1);
    // }
    //
    // let ast = ast.unwrap();
    //
    // if matches.is_present("print_ast") {
    //     println!("Parsed AST: {:#?}", ast);
    // }
    // let inference_result = inferencer::infer(
    //     &ast,
    //     filename.to_string(),
    //     InferencerOptions {
    //         print_types: matches.is_present("print_inferred_types"),
    //         is_main_module: true,
    //     },
    // );
    // if let Err(err) = inference_result {
    //     err.into_iter().for_each(|e| eprintln!("{}", e));
    //     process::exit(1);
    // }

    // let result = interpreter::interpret(&inference_result.unwrap());
    // if let Err(e) = result {
    //     eprintln!("Runtime error: {:?}", e)
    // } else {
    //     println!("{}", result.unwrap());
    // }
}
