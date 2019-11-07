use std::fmt::{Display, Error, Formatter};
use std::rc::Rc;
use crate::tokenizer::TokenType::{Symbol, Identifier, StringLiteral, CharacterLiteral, Number};
use crate::tokenizer::TokenizerErrorType::{UnterminatedString, UnexpectedCharacter, UnexpectedEOF};

#[derive(Debug)]
pub enum TokenType {
    CharacterLiteral,
    StringLiteral,
    Identifier,
    Symbol,
    Number,
}

#[derive(Debug)]
pub enum TokenizerErrorType {
    UnexpectedEOF,
    UnexpectedCharacter(char),
    UnterminatedString,
}

#[derive(Debug)]
pub struct TokenizerError {
    file: Rc<String>,
    line: u16,
    col: u16,
    error: TokenizerErrorType,
}

#[derive(Debug)]
pub struct TokenLocation {
    line: u16,
    column: u16,
}

#[derive(Debug)]
pub struct Token {
    data: String,
    token_type: TokenType,
    token_location: TokenLocation,
}

impl Display for TokenizerError {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        write!(f, "[{}:{}:{}]: {}", self.file, self.line, self.col, self.error)
    }
}

impl Display for TokenizerErrorType {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), Error> {
        let err = match self {
            UnexpectedEOF => String::from("Unexpected EOF"),
            UnexpectedCharacter(c) => format!("Unexpected character '{}'", c),
            UnterminatedString => String::from("String literal not terminated")
        };
        write!(f, "{}", err)
    }
}

struct Tokenizer {
    input: String,
    line: u16,
    col: u16,
    file_name: Rc<String>,
}

impl Tokenizer {
    fn tokenize(&mut self) -> Result<Vec<Token>, TokenizerError> {
        let mut tokens = Vec::new();
        loop {
            match self.peek(0) {
                None => {
                    return Ok(tokens);
                }
                Some(c) => {
                    match self.read_token(c) {
                        Ok(None) => continue,
                        Ok(Some(token)) => tokens.push(token),
                        Err(e) => return Err(e)
                    }
                }
            }
        }
    }

    fn read_token(&mut self, c: char) -> Result<Option<Token>, TokenizerError> {
        if c == '\r' && self.peek(1).filter(|cr| *cr == '\n').is_some() {
            self.consume();
            self.consume();
            self.col = 1;
            return Ok(None);
        }
        if c == ' ' || c == '\t' || c == '\n' {
            self.consume();
            return Ok(None);
        }
        match Tokenizer::guess_token_type(c) {
            Number => self.read_number(c),
            CharacterLiteral => self.read_character_literal(c),
            StringLiteral => self.read_string_literal(c),
            Identifier => self.read_identifier(c),
            Symbol => self.read_symbol(c)
        }
    }

    fn read_number(&mut self, start: char) -> Result<Option<Token>, TokenizerError> {
        let mut num = String::new();
        num.push(start);

        let column = self.col;
        self.consume();
        while let Some(c) = self.peek(0) {
            if c.is_digit(10) {
                self.consume();
                num.push(c)
            } else if c.is_alphabetic() {
                return Err(self.error(UnexpectedCharacter(c)));
            } else if num.len() > 0 {
                return Ok(Some(Token { data: num, token_type: Number, token_location: TokenLocation { line: self.line, column } }));
            } else {
                return Err(self.error(UnexpectedCharacter(c)));
            }
        }
        if num.len() > 0 {
            return Ok(Some(Token { data: num, token_type: Number, token_location: TokenLocation { line: self.line, column } }));
        }
        Err(self.error(UnexpectedEOF))
    }

    fn read_character_literal(&mut self, _start: char) -> Result<Option<Token>, TokenizerError> {
        let column = self.col;

        self.consume();
        let c = self.consume();

        if let None = c {
            return Err(self.error(UnexpectedEOF));
        }
        let c = c.unwrap();

        // Consume ', hopefully
        let end = self.consume();
        match end {
            None => return Err(self.error(UnexpectedEOF)),
            Some('\'') => (),
            Some(c) => return Err(self.error(UnexpectedCharacter(c)))
        }

        let mut data = String::new();
        data.push(c);

        Ok(Some(Token { data, token_type: CharacterLiteral, token_location: TokenLocation { line: self.line, column } }))
    }

    fn read_string_literal(&mut self, _c: char) -> Result<Option<Token>, TokenizerError> {
        let column = self.col;

        // Consume "
        self.consume();

        let mut data = String::new();
        while let Some(c) = self.consume() {
            if c == '"' {
                return Ok(Some(Token { data, token_type: StringLiteral, token_location: TokenLocation { line: self.line, column } }));
            }
            data.push(c);
        }
        return Err(self.error(UnterminatedString));
    }

    fn read_identifier(&mut self, c: char) -> Result<Option<Token>, TokenizerError> {
        let column = self.col;

        self.consume();

        let mut data = String::new();
        data.push(c);

        while let Some(c) = self.peek(0) {
            if c.is_alphabetic() || c.is_numeric() || c == '_' {
                data.push(c);
                self.consume();
            } else {
                return Ok(Some(Token { data, token_type: Identifier, token_location: TokenLocation { line: self.line, column } }));
            }
        }

        Ok(Some(Token { data, token_type: Identifier, token_location: TokenLocation { line: self.line, column } }))
    }

    fn read_symbol(&mut self, c: char) -> Result<Option<Token>, TokenizerError> {
        let column = self.col;
        let mut data = String::new();
        self.consume();
        data.push(c);
        Ok(Some(Token { data, token_type: Symbol, token_location: TokenLocation { line: self.line, column } }))
    }

    fn guess_token_type(c: char) -> TokenType {
        if c.is_digit(10) {
            return Number;
        } else if c == '\'' {
            return CharacterLiteral;
        } else if c == '"' {
            return StringLiteral;
        } else if Tokenizer::is_identifier(c) {
            return Identifier;
        } else if c.is_ascii_punctuation() {
            return Symbol;
        }
        panic!("Could not determine token type: {:?}", c)
    }

    fn is_identifier(c: char) -> bool {
        c == '_' || c.is_alphabetic()
    }

    fn consume(&mut self) -> Option<char> {
        let c = self.input.chars().nth(0)?;
        self.input = self.input[1..].to_string();

        if '\n' == c {
            self.line += 1;
            self.col = 1;
        } else if '\t' == c {
            self.col += 4
        } else {
            if c != '\n' {
                self.col += 1
            }
        }
        Some(c)
    }
    fn peek(&self, offset: usize) -> Option<char> {
        self.input.chars().nth(offset)
    }

    fn error(&self, e: TokenizerErrorType) -> TokenizerError {
        TokenizerError {
            file: Rc::clone(&self.file_name),
            line: self.line,
            col: self.col,
            error: e,
        }
    }
}

pub fn tokenize(input: String, file_name: Rc<String>) -> Result<Vec<Token>, TokenizerError> {
    Tokenizer { input, line: 1, col: 1, file_name }.tokenize()
}