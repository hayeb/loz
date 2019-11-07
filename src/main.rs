use std::{fs, env};
use std::rc::Rc;

mod tokenizer;

fn main() {
    let args: Vec<String> = env::args().collect();

    let filename = &args[1];

    let contents = fs::read_to_string(filename)
        .expect("Error reading from file: test/test.loz");
    let res = tokenizer::tokenize(contents, Rc::new(String::from(filename)));

    match res {
        Ok(tokens) => println!("{:?}", tokens),
        Err(err) => println!("{}", err)
    }
}
