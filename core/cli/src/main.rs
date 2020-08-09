use std::env;
use std::path::{Path, PathBuf};

use clap::{App, Arg};

use loz_compiler::generator::generate;
use loz_compiler::module_system::{compile_modules, CompilerOptions};
use loz_compiler::rewriter::rewrite;
use std::process::{exit};

const VERSION: &'static str = env!("CARGO_PKG_VERSION");

static ENV_LOZ_HOME: &str = "LOZ_HOME";

#[cfg(windows)]
static DEFAULT_LOZ_HOME: &str = "%APPDATA%\\loz";
#[cfg(not(windows))]
static DEFAULT_LOZ_HOME: &str = "/usr/lib/loz";

fn main() {
    let matches = App::new("Loz Compiler")
        .version(VERSION)
        .author("Haye Böhm <haye.bohm@gmail.com>")
        .about("The Loz compiler!")

        // Arguments
        .arg(Arg::with_name("file")
            .index(1)
            .required(true)
            .help("The file to compile"))

        // Options with values
        .arg(Arg::with_name("working_directory")
            .short("d")
            .long("working-directory")
            .help("Working directory of the compiler")
            .takes_value(true))
        .arg(Arg::with_name("library_path")
            .short("l")
            .long("library-path")
            .help("Directory to include in the library path")
            .takes_value(true)
            .multiple(true)
            .number_of_values(1))

        // Options
        .arg(Arg::with_name("print_ast")
            .short("p")
            .long("print-ast")
            .help("Toggles whether to print the AST as parsed by the parser"))
        .arg(Arg::with_name("print_inferred_types")
            .short("t")
            .long("print-inferred-types")
            .help("Toggles whether to print the inferred types of functions without a type declaration"))

        .arg(Arg::with_name("execute")
             .short("x")
             .long("execute")
             .help("Whether to execute the module"))

        .get_matches();

    let filename = matches.value_of("file").unwrap();
    let mut module_search_path = matches
        .values_of("library_path")
        .map_or_else(|| Vec::new(), |v| v.map(|s| PathBuf::from(s)).collect());

    let loz_home_directory = match env::var(ENV_LOZ_HOME) {
        Ok(loz_home_dir) => {
            let pb = PathBuf::from(loz_home_dir.clone());
            if !pb.is_dir() {
                println!("Value for $LOZ_HOME '{}' does not point to a directory. Unable to find StdLib.", loz_home_dir.clone());
                exit(3)
            }
            pb
        }
        Err(_) => {
            let pb = PathBuf::from(DEFAULT_LOZ_HOME);
            if !pb.is_dir() {
                println!("Default for does $LOZ_HOME '{}' does not point to a directory. Unable to find StdLib.", DEFAULT_LOZ_HOME);
                exit(3)
            }
            pb
        }
    };
    module_search_path.insert(0, loz_home_directory);

    let compiler_options = CompilerOptions {
        current_directory: env::current_dir().unwrap(),
        loz_home: Default::default(),
        extra_module_search_path: module_search_path,
        print_ast: matches.is_present("print_ast"),
        print_types: matches.is_present("print_inferred_types"),
        execute: matches.is_present("execute"),
    };

    let (typed_main_module, typed_modules) =
        match compile_modules(filename.to_string(), &compiler_options) {
            Ok((typed_module, inferred_modules_by_name)) => {
                (typed_module, inferred_modules_by_name)
            }
            Err(error) => {
                println!("{}", error);
                exit(1)
            }
        };

    let runtime_module = rewrite(typed_main_module, typed_modules);
    match generate(runtime_module, &Path::new("target/")) {
        Ok(_) => return,
        Err(msg) => eprintln!("Error during code generation: {}", msg)
    }


}
