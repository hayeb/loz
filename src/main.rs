use std::{fs, env};
use std::rc::Rc;

mod parser;

#[macro_use]
extern crate pest_derive;

fn main() {
    let args: Vec<String> = env::args().collect();

    let filename = &args[1];

    let contents = fs::read_to_string(filename)
        .expect("Error reading from file: test/test.loz");

   println!("{:?}", parser::parse(&contents[..]));
}
