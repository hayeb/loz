pub mod tokenizer {
    use crate::tokenizer::tokenizer::TokenType::{CharacterLiteral, Identifier, Number, StringLiteral, Symbol};

    #[derive(Debug)]
    pub enum TokenType {
        CharacterLiteral,
        StringLiteral,
        Identifier,
        Symbol,
        Number,
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

    struct Tokenizer {
        input: String,
        tokens: Vec<Token>,
        line: u16,
        col: u16,
        file_name: String,
    }

    impl Tokenizer {
        fn tokenize(&mut self) -> Result<Vec<Token>, String> {
            let mut tokens = Vec::new();
            loop {
                match self.consume() {
                    None => {
                        println!("End of tokens at {}:{}", self.line, self.col);
                        return Ok(tokens);
                    }
                    Some(c) => {
                        println!("Token {:?}", c);
                        match self.read_token(c) {
                            Ok(None) => continue,
                            Ok(Some(token)) => tokens.push(token),
                            Err(e) => return Err(e)
                        }
                    }
                }
            }
        }

        fn read_token(&mut self, c: char) -> Result<Option<Token>, String> {
            println!("read_token {}", c);
            if c == ' ' || c == '\t' || c == '\n' {
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

        fn read_number(&mut self, start: char) -> Result<Option<Token>, String> {
            println!("read_number");
            let mut num = String::new();
            num.push(start);

            let column = self.col;
            let mut mc = self.peek();
            while let Some(c) = mc {
                println!("Read number {}", c);
                if c.is_digit(10) {
                    self.consume();
                    mc = self.peek();
                    num.push(c)
                } else if num.len() > 0 {
                    return Ok(Some(Token { data: num, token_type: Number, token_location: TokenLocation { line: self.line, column} }));
                } else {
                    return Err(format!("[{}][{}]: Unexpected character {}", self.line, self.col, c));
                }
            }
            if num.len() > 0 {
                return Ok(Some(Token { data: num, token_type: Number, token_location: TokenLocation { line: self.line, column} }));
            }
            Err(format!("[{}][{}]: Unexpected EOF", self.line, self.col))
        }

        fn read_character_literal(&mut self, start: char) -> Result<Option<Token>, String> {
            println!("read_character_literal {}", start);
            let col = self.col;

            let c = self.consume();

            if let None = c {
                return Err(format!("[{}][{}]: Expected char literal content", self.line, self.col));
            }

            // Consume ', hopefully
            let end = self.consume();
            println!("{:?} {:?}", c, end);
            match end {
                None => return Err(format!("[{}][{}]: Expected char literal end '", self.line, self.col)),
                Some('\'') => (),
                Some(c) => return Err(format!("[{}][{}]: Expected char literal end ', got {}", self.line, self.col, c))
            }

            let mut data = String::new();
            data.push(c.expect("easd"));

            Ok(Some(Token { data, token_type: CharacterLiteral, token_location: TokenLocation { line: self.line, column: self.col } }))
        }

        fn read_string_literal(&self, c: char) -> Result<Option<Token>, String> { Err(String::from("read_string_literal Not implemented")) }

        fn read_identifier(&self, c: char) -> Result<Option<Token>, String> { Err(String::from("read_identifier Not implemented")) }

        fn read_symbol(&self, c: char) -> Result<Option<Token>, String> { Err(String::from("read_symbol Not implemented")) }

        fn guess_token_type(c: char) -> TokenType {
            if c.is_digit(10) {
                return Number;
            } else if c == '\'' {
                return CharacterLiteral;
            } else if c == '"' {
                return StringLiteral;
            } else if Tokenizer::is_identifier(c) {
                return Identifier;
            }
            Number
        }

        fn is_identifier(c: char) -> bool {
            c == '_' || c.is_alphabetic()
        }

        fn consume(&mut self) -> Option<char> {
            let c = self.input.chars().nth(0);

            if let None = c {
                return None
            }
            self.input = self.input[1..].to_string();

            if let Some('\n') = c {
                self.line += 1
            }
            if let Some(' ') = c {
                self.col += 1
            }
            if let Some('\t') = c {
                self.col += 4
            }
            return c;
        }

        fn peek(&self) -> Option<char> {
            self.input.chars().nth(0)
        }
    }

    pub fn tokenize(input: String, file_name: String) -> Result<Vec<Token>, String> {
        println!("Reading tokens from {}", file_name);

        let mut tokenizer = Tokenizer { input, tokens: Vec::new(), line: 1, col: 1, file_name };
        tokenizer.tokenize()
    }
}