use std::env;

use clap::{App, Arg};

use loz_compiler::inferencer::InferencerOptions;
use loz_compiler::interpreter::{interpret, InterpreterError, Value};
use loz_compiler::module_system::compile_modules;
use loz_compiler::rewriter::rewrite;
use std::rc::Rc;

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
    let infer_options = InferencerOptions {
        print_types: matches.is_present("print_inferred_types"),
        is_main_module: true,
    };

    let (typed_main_module, typed_modules) =
        match compile_modules(filename.to_string(), &infer_options) {
            Ok((typed_module, _inferred_modules_by_name)) => {
                (typed_module, _inferred_modules_by_name)
            }
            Err(error) => {
                println!("{}", error);
                return;
            }
        };

    let runtime_module = rewrite(typed_main_module, typed_modules);

    match interpret(runtime_module) {
        Ok(v) => println!("{}", v),
        Err(e) => eprintln!("Runtime error: {}", e),
    }
}
