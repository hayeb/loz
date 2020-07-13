/* Type mapping for LOZ Types to LLVM types:
   LOZ Type         | C-Type (for refence)  | LLVM Type |
   -----------------|-----------------------|-----------|
   Bool             | bool                  | i1        |
   Char             | ????                  | u32       |
   String           | *char                 | *i8           |
   Int              | int_64_t              | i64
   Float            | float                 | float

   Things to do in no particular order:
   1. Extract compile time string constants
        Keep generator state and add them all into a "header" at the start of the file.
   2. Design tuple representation
        A tuple is a pointer on the stack , where elements
   3. Design list representation
   4. Design record representation
   5. Design lambda representation

   Right now we only support true polymorphism without things like class restrictions, so we do not (yet)
   need to do monomorphisation.
*/

use std::borrow::Borrow;
use std::collections::HashMap;
use std::rc::Rc;

use crate::ast::{Expression, FunctionBody, FunctionDefinition, FunctionRule, Type};
use crate::rewriter::RuntimeModule;

const C_NEWLINE : &'static str = "\\0A";
const C_NEWLINE_NAME: &'static str = "@c_newline";
const C_NEWLINE_LENGTH: usize = 2; // Includes NULL byte.

const C_INT_FORMAT_STRING: &'static str = "%d";
const C_INT_FORMAT_STRING_NAME: &'static str = "@c_int_format_string";

const C_FLOAT_FORMAT_STRING: &'static str = "%f";
const C_FLOAT_FORMAT_STRING_NAME: &'static str = "@c_float_format_string";

const C_CHAR_FORMAT_STRING: &'static str = "%c";
const C_CHAR_FORMAT_STRING_NAME: &'static str = "@c_char_format_string";

const C_BOOL_FORMAT_STRING_TRUE: &'static str = "True";
const C_BOOL_FORMAT_STRING_TRUE_NAME: &'static str = "@c_bool_false_format_string";

const C_BOOL_FORMAT_STRING_FALSE: &'static str = "False";
const C_BOOL_FORMAT_STRING_FALSE_NAME: &'static str = "@c_bool_true_format_string";

const C_STRING_FORMAT_STRING: &'static str = "\\22%s\\22";
const C_STRING_FORMAT_STRING_NAME: &'static str = "@c_string_format_string";
const C_STRING_FORMAT_STRING_LENGTH: usize = 5; // Includes NULL byte.

const FORMAT_BOOL: &'static str = "
define i8* @format_bool(i1 %bool) {
    br i1 %bool, label %False, label %True
True:
    %ts = getelementptr [6 x i8],[6 x i8]* @c_bool_true_format_string, i64 0, i64 0
    ret i8* %ts
False:
    %fs = getelementptr [5 x i8],[5 x i8]* @c_bool_false_format_string, i64 0, i64 0
    ret i8* %fs
}";


// The variable name of the result of a expression
type SSAVar = String;

pub fn generate(runtime_module: Rc<RuntimeModule>) -> String {
    GeneratorState::new().generate(&runtime_module)
}

struct GeneratorState {
    new_var: usize,
    string_constants: HashMap<String, String>,

    vars: Vec<HashMap<String, String>>,
}

fn to_llvm_type(loz_type: &Rc<Type>) -> String {
    match loz_type.borrow() {
        Type::Bool => "i1".to_string(),
        Type::String => "i8*".to_string(),
        Type::Int => "i64".to_string(),
        Type::Float => "double".to_string(),
        Type::Char => "i8".to_string(),
        _ => unimplemented!()
    }
}

fn return_type(loz_type: &Rc<Type>) -> Rc<Type> {
    match loz_type.borrow() {
        Type::Function(_, to) => Rc::clone(to),
        _ => Rc::clone(loz_type)
    }
}

fn to_string_constant(name: &str, constant: &str) -> String {
    format!("{} = private unnamed_addr constant [{} x i8] c\"{}\\00\"", name, constant.len()+1, constant)
}

fn to_string_constant_with_length(name: &str, constant: &str, length: usize) -> String {
    format!("{} = private unnamed_addr constant [{} x i8] c\"{}\\00\"", name, length, constant)
}

fn resolve_string_constant(result: &str, name: &str, len: usize) -> String {
    format!("{} = getelementptr [{} x i8],[{} x i8]* {}, i64 0, i64 0", result, len+1, len+1, name)
}

fn resolve_string_constant_len(result: &str, name: &str, len: usize) -> String {
    format!("{} = getelementptr [{} x i8],[{} x i8]* {}, i64 0, i64 0", result, len, len, name)
}

impl GeneratorState {
    fn new() -> Self {
        return GeneratorState {
            new_var: 0,
            string_constants: HashMap::new(),

            vars: Vec::new(),
        };
    }

    fn open_scope(&mut self) {
        self.vars.push(HashMap::new())
    }

    fn close_scope(&mut self) {
        self.vars.pop();
    }

    fn put(&mut self, var: String, value: String) {
        self.vars.last_mut().unwrap().insert(var, value);
    }

    fn get(&self, var: &str) -> Option<String> {
        self.vars.last().unwrap().get(var).cloned()
    }

    fn var(&mut self) -> SSAVar {
        self.new_var += 1;
        return format!("%v{}", self.new_var);
    }

    fn generate(&mut self, runtime_module: &Rc<RuntimeModule>) -> String {
        let mut definitions_code = String::new();
        for (_name, function_definition) in &runtime_module.functions {
            definitions_code.push_str(&self.generate_function_definition(function_definition));
            definitions_code.push_str("\n\n");
        }

        let main_result_ssa = self.var();
        let main_result_type = to_llvm_type(&runtime_module.main_function_type);
        let qualified_main_name = format!("@{}_{}()", runtime_module.name, runtime_module.main_function_name);

        let print_code = self.generate_print_code(&runtime_module.main_function_type, main_result_type.clone());
        definitions_code.push_str(&print_code);

        definitions_code.push_str(&format!(
            "define i32 @main() {{
    {} = call {} {}
    call void @print_result({} {})
    ret i32 0
}}", main_result_ssa, main_result_type.clone(), qualified_main_name, main_result_type, main_result_ssa));
        definitions_code
    }


    fn generate_print_code(&mut self, loz_type: &Rc<Type>, llvm_type: String) -> String {
        let c_newline = to_string_constant_with_length(C_NEWLINE_NAME, C_NEWLINE, C_NEWLINE_LENGTH);
        let c_int_format = to_string_constant(C_INT_FORMAT_STRING_NAME, C_INT_FORMAT_STRING);
        let c_float_format = to_string_constant(C_FLOAT_FORMAT_STRING_NAME, C_FLOAT_FORMAT_STRING);
        let c_char_format = to_string_constant(C_CHAR_FORMAT_STRING_NAME, C_CHAR_FORMAT_STRING);
        let c_string_format = to_string_constant_with_length(C_STRING_FORMAT_STRING_NAME, C_STRING_FORMAT_STRING, C_STRING_FORMAT_STRING_LENGTH);
        let c_bool_false_format = to_string_constant(C_BOOL_FORMAT_STRING_FALSE_NAME, C_BOOL_FORMAT_STRING_FALSE);
        let c_bool_true_format = to_string_constant(C_BOOL_FORMAT_STRING_TRUE_NAME, C_BOOL_FORMAT_STRING_TRUE);

        let printf_external_definition = "declare i32 @printf(i8* noalias nocapture, ...)";

        let mut print_code = String::new();
        // Push different format strings
        print_code.push_str(&c_newline);
        print_code.push_str("\n");
        print_code.push_str(&c_int_format);
        print_code.push_str("\n");
        print_code.push_str(&c_float_format);
        print_code.push_str("\n");
        print_code.push_str(&c_char_format);
        print_code.push_str("\n");
        print_code.push_str(&c_string_format);
        print_code.push_str("\n");
        print_code.push_str(&c_bool_false_format);
        print_code.push_str("\n");
        print_code.push_str(&c_bool_true_format);
        print_code.push_str("\n\n");

        // Push misc formatting routings;
        print_code.push_str(FORMAT_BOOL);
        print_code.push_str("\n");

        // External printf definition
        print_code.push_str(printf_external_definition);
        print_code.push_str("\n");

        let function_header = format!("define void @print_result({} %to_print) {{", llvm_type);
        print_code.push_str(&function_header);
        print_code.push_str("\n");

        for line in self.generate_print_code_value(loz_type, "%to_print".to_string()) {
            print_code.push_str("\t");
            print_code.push_str(&line);
            print_code.push_str("\n")
        }

        let function_footer = "}";
        print_code.push_str(function_footer);
        print_code.push_str("\n");
        print_code
    }

    fn generate_print_code_value(&mut self, loz_type: &Rc<Type>, to_print: String) -> Vec<String> {
        let mut lines = match loz_type.borrow() {
            Type::Int => {
                let var = self.var();
                vec![
                    resolve_string_constant(&var, C_INT_FORMAT_STRING_NAME, C_INT_FORMAT_STRING.len()),
                    format!("call i32 (i8*, ...) @printf(i8* {}, {} {})", var, to_llvm_type(loz_type), to_print)
                ]
            }
            Type::Bool => {
                let var = self.var();
                vec![format!("{} = call i8* @format_bool(i1 {})", var , to_print),
                    format!("call i32 (i8*, ...) @printf(i8* {})", var)
                ]

            },
            Type::String => {
                let var = self.var();
                vec![
                    resolve_string_constant_len(&var, C_STRING_FORMAT_STRING_NAME, C_STRING_FORMAT_STRING_LENGTH),
                    format!("call i32 (i8*, ...) @printf(i8* {}, {} {})", var, to_llvm_type(loz_type), to_print)
                ]
            },
            Type::Float => {
                let var = self.var();
                vec![
                    resolve_string_constant(&var, C_FLOAT_FORMAT_STRING_NAME, C_FLOAT_FORMAT_STRING.len()),
                    format!("call i32 (i8*, ...) @printf(i8* {}, {} {})", var, to_llvm_type(loz_type), to_print)
                ]
            }
            _ => unimplemented!()
        };


        let r = self.var();
        lines.push(resolve_string_constant_len(&r, C_NEWLINE_NAME, C_NEWLINE_LENGTH));
        lines.push(format!("call i32 (i8*, ...) @printf(i8* {})", r));
        lines.push("ret void".to_string());
        lines
    }

    fn generate_function_definition(&mut self, definition: &Rc<FunctionDefinition>) -> String {
        self.open_scope();
        let mut bodies: Vec<String> = Vec::new();
        let mut result = None;
        for body in &definition.function_bodies {
            let (r, b) = self.generate_function_body(body);
            result = Some(r);
            bodies.extend(b);
        }

        let mut bodies_code = String::new();
        for (v, sc) in &self.string_constants {
            let mut string_constant_code = String::new();
            string_constant_code.push_str(&to_string_constant(v, sc));
            string_constant_code.push_str("\n");
            bodies_code.push_str(&string_constant_code);
        }
        self.string_constants.clear();
        let function_return_type = return_type(&definition.function_type.as_ref().unwrap().enclosed_type);
        let llvm_function_return_type = to_llvm_type(&function_return_type);

        bodies_code.push_str(&format!("define {} @{}({}) {{\n", llvm_function_return_type, definition.name.replace("::", "_"), ""));

        for b in bodies {
            bodies_code.push_str("\t");
            bodies_code.push_str(&b);
            bodies_code.push_str("\n");
        }

        let result_var = result.unwrap();
        bodies_code.push_str(&format!("\tret {} {}\n", llvm_function_return_type, self.get(&result_var).unwrap_or(result_var.clone())));

        bodies_code.push_str("}");
        self.close_scope();
        bodies_code
    }

    fn generate_function_body(&mut self, body: &Rc<FunctionBody>) -> (SSAVar, Vec<String>) {
        let mut rules: Vec<String> = Vec::new();
        let mut result = None;
        for rule in &body.rules {
            let (r, rule_code) = self.generate_function_rule(rule);
            result = Some(r);
            rules.extend(rule_code);
        }

        (result.unwrap(), rules)
    }

    fn generate_function_rule(&mut self, rule: &Rc<FunctionRule>) -> (SSAVar, Vec<String>) {
        match rule.borrow() {
            FunctionRule::ConditionalRule(_, _, _) => unimplemented!(),
            FunctionRule::ExpressionRule(_, e) => self.generate_expr(e),
            FunctionRule::LetRule(_, _, _) => unimplemented!(),
        }
    }

    fn generate_expr(&mut self, e: &Rc<Expression>) -> (SSAVar, Vec<String>) {
        let result = self.var();
        let e_code = match e.borrow() {
            Expression::BoolLiteral(_, true) => {
                self.put(result.clone(), "true".to_string());
                None
            }

            Expression::BoolLiteral(_, false) => {
                self.put(result.clone(), "false".to_string());
                None
            }
            Expression::IntegerLiteral(_, i) => {
                self.put(result.clone(), i.to_string());
                None
            }
            Expression::StringLiteral(_, string) => {
                let global_var = self.var().replace("%", "@");
                self.string_constants.insert(global_var.clone(), string.to_string());
                Some(format!("getelementptr [{} x i8],[{} x i8]* {}, i64 0, i64 0", string.len() + 1, string.len() + 1, global_var))
            }
            Expression::CharacterLiteral(_, _) => unimplemented!(),

            Expression::FloatLiteral(_, f) => {
                self.put(result.clone(), f.to_string());
                None
            }
            Expression::TupleLiteral(_, _) => unimplemented!(),
            Expression::EmptyListLiteral(_) => unimplemented!(),
            Expression::ShorthandListLiteral(_, _) => unimplemented!(),
            Expression::LonghandListLiteral(_, _, _) => unimplemented!(),
            Expression::ADTTypeConstructor(_, _, _) => unimplemented!(),
            Expression::Record(_, _, _) => unimplemented!(),
            Expression::Case(_, _, _) => unimplemented!(),
            Expression::Call(_, _, _) => unimplemented!(),
            Expression::Variable(_, _) => unimplemented!(),
            Expression::Negation(_, _) => unimplemented!(),
            Expression::Minus(_, _) => unimplemented!(),
            Expression::Times(_, _, _) => unimplemented!(),
            Expression::Divide(_, _, _) => unimplemented!(),
            Expression::Modulo(_, _, _) => unimplemented!(),
            Expression::Add(_, _, _) => unimplemented!(),
            Expression::Subtract(_, _, _) => unimplemented!(),
            Expression::ShiftLeft(_, _, _) => unimplemented!(),
            Expression::ShiftRight(_, _, _) => unimplemented!(),
            Expression::Greater(_, _, _) => unimplemented!(),
            Expression::Greq(_, _, _) => unimplemented!(),
            Expression::Leq(_, _, _) => unimplemented!(),
            Expression::Lesser(_, _, _) => unimplemented!(),
            Expression::Eq(_, _, _) => unimplemented!(),
            Expression::Neq(_, _, _) => unimplemented!(),
            Expression::And(_, _, _) => unimplemented!(),
            Expression::Or(_, _, _) => unimplemented!(),
            Expression::RecordFieldAccess(_, _, _) => unimplemented!(),
            Expression::Lambda(_, _, _) => unimplemented!(),
        };

        if let None = e_code {
            return (result.clone(), vec![]);
        }

        let mut line = String::new();
        line.push_str(&result);
        line.push_str(" = ");
        line.push_str(&e_code.unwrap());

        return (result, vec![line]);

    }
}
