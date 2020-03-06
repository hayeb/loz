use std::{fs, io};
use loz_compiler::parser;
use loz_compiler::inferencer;
use loz_compiler::inferencer::{TypedAST, InferenceError};
use std::path::PathBuf;

#[test]
fn test_ok_files() -> Result<(), io::Error> {
    compile_files("tests/programs/ok", |res| res.is_ok())
}

#[test]
fn test_err_files() -> Result<(), io::Error> {
    compile_files("tests/programs/err", |res| res.is_err())
}

fn compile_files(dir: &str, f: impl Fn (Result<TypedAST, Vec<InferenceError>>) -> bool) -> Result<(), io::Error>{
    let r = fs::read_dir(dir)?;
    for entry in r {
        let entry = entry?;
        let path = entry.path();
        if path.is_dir() {
            continue;
        }

        let res = compile_file(path.clone());
        println!("{}: Result {:?}", path.clone().to_str().unwrap(), res);
        assert!(f(res))
    }
    Ok(())
}

fn compile_file(path: PathBuf) -> Result<TypedAST, Vec<InferenceError>>  {
    let file_contents = fs::read_to_string(&path).unwrap();

    // For now, assume parsing succeeds..
    let ast = parser::parse(&path.to_str().unwrap().to_string(), &file_contents).unwrap();

    inferencer::infer(&ast)
}