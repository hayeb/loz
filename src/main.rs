mod tokenizer;

use crate::tokenizer::tokenizer::tokenize;

fn main() {
    println!("{:?}", tokenize(String::from("1234 'c' 4321\n'r'\t\t\n\t5"), String::from("test.loz")));
}
