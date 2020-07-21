/* Type mapping for LOZ Types to LLVM types:
   LOZ Type         | C-Type (for refence)  | LLVM Type |
   -----------------|-----------------------|-----------|
   Bool             | bool                  | i1        |
   Char             | ????                  | i32       |
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

use crate::ast::{Expression, FunctionBody, FunctionDefinition, FunctionRule, MatchExpression, Type};
use crate::rewriter::RuntimeModule;

const ED_C_EXIT : &'static str = "declare void @exit(i32) cold noreturn nounwind";
const ED_C_PRINTF : &'static str = "declare i32 @printf(i8* noalias nocapture, ...)";

const C_NEWLINE: &'static str = "\\0A";
const C_NEWLINE_NAME: &'static str = "@c_newline";
const C_NEWLINE_LENGTH: usize = 2; // Includes NULL byte.

const C_INT_FORMAT_STRING: &'static str = "%d";
const C_INT_FORMAT_STRING_NAME: &'static str = "@c_int_format_string";

const C_FLOAT_FORMAT_STRING: &'static str = "%f";
const C_FLOAT_FORMAT_STRING_NAME: &'static str = "@c_float_format_string";

const C_CHAR_FORMAT_STRING: &'static str = "'%s'";
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
    GeneratorState::new(&runtime_module).generate(&runtime_module)
}

struct GeneratorState {
    new_var: usize,
    string_constants: HashMap<String, String>,

    vars: Vec<HashMap<String, String>>,
    var_to_type: Vec<HashMap<Rc<String>, Rc<Type>>>,

    function_name_to_type: HashMap<Rc<String>, Rc<Type>>,
}

fn to_llvm_type(loz_type: &Rc<Type>) -> String {
    match loz_type.borrow() {
        Type::Bool => "i1".to_string(),
        Type::String => "i8*".to_string(),
        Type::Int => "i64".to_string(),
        Type::Float => "double".to_string(),
        Type::Char => "i8*".to_string(),
        _ => unimplemented!(),
    }
}

fn return_type(loz_type: &Rc<Type>) -> Rc<Type> {
    match loz_type.borrow() {
        Type::Function(_, to) => Rc::clone(to),
        _ => Rc::clone(loz_type),
    }
}

fn to_string_constant(name: &str, constant: &str) -> String {
    format!(
        "{} = private unnamed_addr constant [{} x i8] c\"{}\\00\"",
        name,
        constant.len() + 1,
        constant
    )
}

fn to_string_constant_with_length(name: &str, constant: &str, length: usize) -> String {
    format!(
        "{} = private unnamed_addr constant [{} x i8] c\"{}\\00\"",
        name, length, constant
    )
}

fn resolve_string_constant(result: &str, name: &str, len: usize) -> String {
    format!(
        "{} = getelementptr [{} x i8],[{} x i8]* {}, i64 0, i64 0",
        result,
        len + 1,
        len + 1,
        name
    )
}

fn resolve_string_constant_len(result: &str, name: &str, len: usize) -> String {
    format!(
        "{} = getelementptr [{} x i8],[{} x i8]* {}, i64 0, i64 0",
        result, len, len, name
    )
}

impl GeneratorState {
    fn new(runtime_module: &Rc<RuntimeModule>) -> Self {
        return GeneratorState {
            new_var: 0,
            string_constants: HashMap::new(),

            vars: Vec::new(),
            var_to_type: Vec::new(),

            function_name_to_type: runtime_module.functions.iter()
                .map(|(n, d)| (Rc::clone(n), Rc::clone(&d.function_type.as_ref().unwrap().enclosed_type)))
                .collect(),
        };
    }

    fn open_scope(&mut self) {
        self.vars.push(HashMap::new());
        self.var_to_type.push(HashMap::new());
    }

    fn close_scope(&mut self) {
        self.vars.pop();
        self.var_to_type.pop();
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

    fn resolve(&mut self, v: SSAVar) -> String {
        match self.get(&v) {
            None => v,
            Some(value) => value,
        }
    }

    fn derive_type(&self, e: &Rc<Expression>) -> Rc<Type> {
        match e.borrow() {
            Expression::FloatLiteral(_, _) => Rc::new(Type::Float),
            Expression::IntegerLiteral(_, _) => Rc::new(Type::Int),
            Expression::Call(_, f, _) => {
                let f_type = self.function_name_to_type.get(f).unwrap();
                return_type(f_type)
            }
            _ => unimplemented!("derive_type at {}", e.locate()),
        }
    }

    fn generate(&mut self, runtime_module: &Rc<RuntimeModule>) -> String {
        let mut definitions_code = String::new();

        definitions_code.push_str(ED_C_EXIT);
        definitions_code.push_str("\n");
        definitions_code.push_str(ED_C_PRINTF);
        definitions_code.push_str("\n");

        for (_name, function_definition) in &runtime_module.functions {
            definitions_code.push_str(&self.generate_function_definition(function_definition));
            definitions_code.push_str("\n\n");
        }

        let main_result_ssa = self.var();
        let main_result_type = to_llvm_type(&runtime_module.main_function_type);
        let qualified_main_name = format!(
            "@{}_{}()",
            runtime_module.name, runtime_module.main_function_name
        );

        let print_code =
            self.generate_print_code(&runtime_module.main_function_type, main_result_type.clone());
        definitions_code.push_str(&print_code);

        definitions_code.push_str(&format!(
            "define i32 @main() {{
    {} = call {} {}
    call void @print_result({} {})
    ret i32 0
}}",
            main_result_ssa,
            main_result_type.clone(),
            qualified_main_name,
            main_result_type,
            main_result_ssa
        ));
        definitions_code
    }

    fn generate_print_code(&mut self, loz_type: &Rc<Type>, llvm_type: String) -> String {
        let c_newline = to_string_constant_with_length(C_NEWLINE_NAME, C_NEWLINE, C_NEWLINE_LENGTH);
        let c_int_format = to_string_constant(C_INT_FORMAT_STRING_NAME, C_INT_FORMAT_STRING);
        let c_float_format = to_string_constant(C_FLOAT_FORMAT_STRING_NAME, C_FLOAT_FORMAT_STRING);
        let c_char_format = to_string_constant(C_CHAR_FORMAT_STRING_NAME, C_CHAR_FORMAT_STRING);
        let c_string_format = to_string_constant_with_length(
            C_STRING_FORMAT_STRING_NAME,
            C_STRING_FORMAT_STRING,
            C_STRING_FORMAT_STRING_LENGTH,
        );
        let c_bool_false_format =
            to_string_constant(C_BOOL_FORMAT_STRING_FALSE_NAME, C_BOOL_FORMAT_STRING_FALSE);
        let c_bool_true_format =
            to_string_constant(C_BOOL_FORMAT_STRING_TRUE_NAME, C_BOOL_FORMAT_STRING_TRUE);

        let mut print_code = String::new();
        // Push different format strings
        print_code.push_str(&c_newline);
        print_code.push_str("\n\n");
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
        print_code.push_str("\n");

        // Push misc formatting routings;
        print_code.push_str(FORMAT_BOOL);
        print_code.push_str("\n\n");

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
        print_code.push_str("\n\n");
        print_code
    }

    fn generate_print_code_value(&mut self, loz_type: &Rc<Type>, to_print: String) -> Vec<String> {
        let mut lines = match loz_type.borrow() {
            Type::Int => {
                let var = self.var();
                vec![
                    resolve_string_constant(
                        &var,
                        C_INT_FORMAT_STRING_NAME,
                        C_INT_FORMAT_STRING.len(),
                    ),
                    format!(
                        "call i32 (i8*, ...) @printf(i8* {}, {} {})",
                        var,
                        to_llvm_type(loz_type),
                        to_print
                    ),
                ]
            }
            Type::Char => {
                let var = self.var();
                vec![
                    resolve_string_constant(
                        &var,
                        C_CHAR_FORMAT_STRING_NAME,
                        C_CHAR_FORMAT_STRING.len(),
                    ),
                    format!(
                        "call i32 (i8*, ...) @printf(i8* {}, {} {})",
                        var,
                        to_llvm_type(loz_type),
                        to_print
                    ),
                ]
            }
            Type::Bool => {
                let var = self.var();
                vec![
                    format!("{} = call i8* @format_bool(i1 {})", var, to_print),
                    format!("call i32 (i8*, ...) @printf(i8* {})", var),
                ]
            }
            Type::String => {
                let var = self.var();
                vec![
                    resolve_string_constant_len(
                        &var,
                        C_STRING_FORMAT_STRING_NAME,
                        C_STRING_FORMAT_STRING_LENGTH,
                    ),
                    format!(
                        "call i32 (i8*, ...) @printf(i8* {}, {} {})",
                        var,
                        to_llvm_type(loz_type),
                        to_print
                    ),
                ]
            }
            Type::Float => {
                let var = self.var();
                vec![
                    resolve_string_constant(
                        &var,
                        C_FLOAT_FORMAT_STRING_NAME,
                        C_FLOAT_FORMAT_STRING.len(),
                    ),
                    format!(
                        "call i32 (i8*, ...) @printf(i8* {}, {} {})",
                        var,
                        to_llvm_type(loz_type),
                        to_print
                    ),
                ]
            }
            _ => unimplemented!(),
        };

        let r = self.var();
        lines.push(resolve_string_constant_len(
            &r,
            C_NEWLINE_NAME,
            C_NEWLINE_LENGTH,
        ));
        lines.push(format!("call i32 (i8*, ...) @printf(i8* {})", r));
        lines.push("ret void".to_string());
        lines
    }

    fn generate_abort(&mut self, message: String) -> Vec<String> {
        let global_var = self.var().replace("%", "@");
        self.string_constants.insert(global_var.clone(), message.clone());
        let result = self.var();
        let mut code = Vec::new();
        code.push(resolve_string_constant(&result, &global_var, message.len()));
        code.push(format!("call i32 (i8*, ...) @printf(i8* {})", result));
        let result = self.var();
        code.push(resolve_string_constant_len(
            &result,
            C_NEWLINE_NAME,
            C_NEWLINE_LENGTH,
        ));
        code.push(format!("call i32 (i8*, ...) @printf(i8* {})", result));
        code.push("call void @exit(i32 1)".to_string());
        code.push("unreachable".to_string());
        code
    }

    fn generate_function_definition(&mut self, definition: &Rc<FunctionDefinition>) -> String {
        self.open_scope();
        let (function_arg_types, function_return_type) =
            match &definition.function_type.as_ref().unwrap().enclosed_type.borrow() {
                Type::Function(from, to) => (from.iter().cloned().collect(), Rc::clone(to)),
                _ => (vec![], Rc::clone(&definition.function_type.as_ref().unwrap().enclosed_type))
            };

        let mut matches: Vec<String> = Vec::new();
        let mut rules: Vec<String> = Vec::new();
        for (i, body) in definition.function_bodies.iter().enumerate() {
            let (match_code, rule_code) = self.generate_function_body(body, &function_arg_types, &function_return_type, i);
            matches.extend(match_code);
            rules.extend(rule_code);
        }
        let mut bodies = Vec::new();
        bodies.extend(matches);
        bodies.extend(rules);
        bodies.push(format!("Body_{}_match:", definition.function_bodies.len()));
        bodies.extend(self.generate_abort(format!("Function '{}' does not match", definition.name)));

        let mut bodies_code = String::new();
        for (v, sc) in &self.string_constants {
            let mut string_constant_code = String::new();
            string_constant_code.push_str(&to_string_constant(v, sc));
            string_constant_code.push_str("\n");
            bodies_code.push_str(&string_constant_code);
        }
        self.string_constants.clear();


        let llvm_function_return_type = to_llvm_type(&function_return_type);
        bodies_code.push_str(&format!(
            "define {} @{}({}) {{\n",
            llvm_function_return_type,
            definition.name.replace("::", "_"),
            function_arg_types.iter().enumerate().map(|(i, fat)| format!("{} %a{}", to_llvm_type(fat), i)).collect::<Vec<String>>().join(", ")
        ));

        for b in bodies {
            bodies_code.push_str("\t");
            bodies_code.push_str(&b);
            bodies_code.push_str("\n");
        }

        bodies_code.push_str("}");
        self.close_scope();
        bodies_code
    }

    fn generate_function_body(&mut self, body: &Rc<FunctionBody>, function_argument_types: &Vec<Rc<Type>>, function_return_type: &Rc<Type>, current_body: usize) -> (Vec<String>, Vec<String>) {
        let mut match_code: Vec<String> = Vec::new();
        let mut rule_code: Vec<String> = Vec::new();
        let current_body_label = format!("Body_{}", current_body);
        let current_body_match_label = format!("Body_{}_match", current_body);
        let next_body_match_label = format!("Body_{}_match", (current_body + 1).to_string());

        for (i, (me, met)) in body.match_expressions.iter().zip(function_argument_types.iter()).enumerate() {
            let mut mc = Vec::new();
            mc.push(format!("{}:", current_body_match_label));
            mc.extend(self.generate_match_expr(me, format!("%a{}", i), met, current_body_label.clone(), next_body_match_label.clone()));

            match_code.extend(mc);
        }
        rule_code.push(format!("{}:", current_body_label));

        for (i, rule) in body.rules.iter().enumerate() {
            let rc = self.generate_function_rule(rule, function_return_type, i);
            rule_code.extend(rc);
        }

        (match_code, rule_code)
    }

    fn generate_function_rule(&mut self, rule: &Rc<FunctionRule>, function_return_type: &Rc<Type>, current_rule: usize) -> Vec<String> {
        let llvm_function_return_type = to_llvm_type(function_return_type);
        match rule.borrow() {
            FunctionRule::ConditionalRule(_, condition_expression, result_expression) => {

                let current_rule_result_label = format!("Rule_{}_result", current_rule);
                let next_rule_condition_label = format!("Rule_{}", current_rule + 1);

                let mut code = Vec::new();

                if current_rule > 0 {
                    let current_rule_condition_label = format!("Rule_{}", current_rule);
                    code.push(format!("{}:", current_rule_condition_label));
                }
                let (cv, cc) = self.generate_expr(condition_expression, &Rc::new(Type::Bool));
                code.extend(cc);
                code.push(format!("br i1 {}, label %{}, label %{}", cv, current_rule_result_label, next_rule_condition_label));
                let (rv, rc) = self.generate_expr(result_expression, function_return_type);
                code.push(format!("{}:", current_rule_result_label));
                code.extend(rc);
                code.push(format!("ret {} {}", llvm_function_return_type, rv));
                code
            }
            FunctionRule::ExpressionRule(_, e) => {
                let mut code = Vec::new();
                if current_rule > 0 {
                    let current_rule_label = format!("Rule_{}", current_rule);
                    code.push(format!("{}:", current_rule_label));
                }

                let (v, c) = self.generate_expr(e, function_return_type);
                code.extend(c);
                code.push(format!("ret {} {}", llvm_function_return_type, v));
                code
            }
            FunctionRule::LetRule(_, _, _) => unimplemented!("LetRule"),
        }
    }

    fn generate_match_expr(&mut self, me: &Rc<MatchExpression>, match_on: String, match_type: &Rc<Type>, match_label: String, no_match_label: String) -> Vec<String> {
        let (r, mut match_code) = match me.borrow() {
            MatchExpression::IntLiteral(_, i) => {
                let result = self.var();
                (result.clone(), vec![format!("{} = icmp eq i64 {}, {}", result.clone(), i, match_on)])
            },
            MatchExpression::CharLiteral(_, _) => unimplemented!("MatchExpression::CharLiteral"),
            MatchExpression::StringLiteral(_, _) => unimplemented!("MatchExpression::StringLiteral"),
            MatchExpression::BoolLiteral(_, _) => unimplemented!("MatchExpression::BoolLiteral"),
            MatchExpression::Identifier(_, id) => {
                self.var_to_type.last_mut().unwrap().insert(Rc::clone(id), Rc::clone(match_type));
                self.put(id.to_string(), match_on);

                ("true".to_string(), vec![])
            }
            MatchExpression::Tuple(_, _) => unimplemented!("MatchExpression::Tuple"),
            MatchExpression::ShorthandList(_, _) => unimplemented!("MatchExpression::ShorthandList"),
            MatchExpression::LonghandList(_, _, _) => unimplemented!("MatchExpression::LonghandList"),
            MatchExpression::Wildcard(_) => unimplemented!("MatchExpression::Wildcard"),
            MatchExpression::ADT(_, _, _) => unimplemented!("MatchExpression::ADT"),
            MatchExpression::Record(_, _, _) => unimplemented!("MatchExpression::Record"),
        };

        match_code.push(format!("br i1 {}, label %{}, label %{}", r, match_label, no_match_label));
        match_code
    }

    fn generate_expr(&mut self, e: &Rc<Expression>, result_type: &Rc<Type>) -> (SSAVar, Vec<String>) {
        let result = self.var();
        let e_code = match e.borrow() {
            Expression::BoolLiteral(_, true) => {
                return ("true".to_string(), vec![]);
            }
            Expression::BoolLiteral(_, false) => {
                return ("false".to_string(), vec![]);
            }
            Expression::IntegerLiteral(_, i) => {
                return (i.to_string(), vec![]);
            }
            Expression::StringLiteral(_, string) => {
                let global_var = self.var().replace("%", "@");
                self.string_constants
                    .insert(global_var.clone(), string.to_string());
                vec![format!(
                    "{} = getelementptr [{} x i8],[{} x i8]* {}, i64 0, i64 0",
                    result,
                    string.len() + 1,
                    string.len() + 1,
                    global_var
                )]
            }
            Expression::CharacterLiteral(_, c) => {
                let global_var = self.var().replace("%", "@");
                let mut buffer = [0; 4];
                let char_result = c.encode_utf8(&mut buffer);
                self.string_constants
                    .insert(global_var.clone(), result.to_string());
                vec![format!(
                    "{} = getelementptr [{} x i8],[{} x i8]* {}, i64 0, i64 0",
                    result,
                    char_result.len() + 1,
                    char_result.len() + 1,
                    global_var
                )]
            }

            Expression::FloatLiteral(_, f) => {
                let mut f = f.to_string();
                if !f.contains(".") {
                    // Otherwise LLVM will complain about integer literal instead of float literal.
                    f.push_str(".0")
                }
                return (f.to_string(), vec![]);
            }
            Expression::TupleLiteral(_, _) => unimplemented!(),
            Expression::EmptyListLiteral(_) => unimplemented!(),
            Expression::ShorthandListLiteral(_, _) => unimplemented!(),
            Expression::LonghandListLiteral(_, _, _) => unimplemented!(),
            Expression::ADTTypeConstructor(_, _, _) => unimplemented!(),
            Expression::Record(_, _, _) => unimplemented!(),
            Expression::Case(_, _, _) => unimplemented!(),
            Expression::Call(_, function_name, arguments) => {
                let mut code = Vec::new();
                let mut arguments_vars = Vec::new();
                for arg in arguments {
                    let arg_type = self.derive_type(arg);
                    let (v, c) = self.generate_expr(arg, &arg_type);
                    code.extend(c);
                    arguments_vars.push(format!("{} {}", to_llvm_type(&arg_type), self.resolve(v)));
                }
                code.push(format!("{} = call {} @{}({})", result, to_llvm_type(result_type), function_name.replace("::", "_"), arguments_vars.join(", ")));
                code
            }
            Expression::Variable(_, id) => return (self.resolve(id.to_string()), vec![]),
            Expression::Negation(_, e) => {
                let (var, mut code) = self.generate_expr(e, &Rc::new(Type::Bool));
                code.push(format!("{} = xor i1 {}, true", result, self.resolve(var)));
                code
            }
            Expression::Minus(_, e) => {
                let (var, mut code) = self.generate_expr(e, result_type);
                match result_type.borrow() {
                    Type::Float => code.push(format!(
                        "{} = fmul double -1.0, {}",
                        result,
                        self.resolve(var)
                    )),
                    Type::Int => {
                        code.push(format!("{} = mul i64 -1, {}", result, self.resolve(var)))
                    }
                    t => panic!("Unsupported type for Minus: {}", t),
                }
                code
            }
            Expression::Times(_, e1, e2) => {
                let (var1, code1) = self.generate_expr(e1, result_type);
                let (var2, code2) = self.generate_expr(e2, result_type);
                let mut code = Vec::new();
                code.extend(code1);
                code.extend(code2);
                match result_type.borrow() {
                    Type::Int => code.push(format!(
                        "{} = mul i64 {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    Type::Float => code.push(format!(
                        "{} = fmul double {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    t => panic!("Unsupported type for Times: {}", t),
                }
                code
            }
            Expression::Divide(_, e1, e2) => {
                let (var1, code1) = self.generate_expr(e1, result_type);
                let (var2, code2) = self.generate_expr(e2, result_type);
                let mut code = Vec::new();
                code.extend(code1);
                code.extend(code2);
                match result_type.borrow() {
                    Type::Int => code.push(format!(
                        "{} = sdiv i64 {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    Type::Float => code.push(format!(
                        "{} = fdiv double {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    t => panic!("Unsupported type for Times: {}", t),
                }
                code
            }
            Expression::Modulo(_, e1, e2) => {
                let (var1, code1) = self.generate_expr(e1, result_type);
                let (var2, code2) = self.generate_expr(e2, result_type);
                let mut code = Vec::new();
                code.extend(code1);
                code.extend(code2);
                match result_type.borrow() {
                    Type::Int => code.push(format!(
                        "{} = srem i64 {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    Type::Float => code.push(format!(
                        "{} = frem double {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    t => panic!("Unsupported type for Times: {}", t),
                }
                code
            }
            Expression::Add(_, e1, e2) => {
                let (var1, code1) = self.generate_expr(e1, result_type);
                let (var2, code2) = self.generate_expr(e2, result_type);
                let mut code = Vec::new();
                code.extend(code1);
                code.extend(code2);
                match result_type.borrow() {
                    Type::Int => code.push(format!(
                        "{} = add i64 {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    Type::Float => code.push(format!(
                        "{} = fadd double {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    t => panic!("Unsupported type for Times: {}", t),
                }
                code
            }
            Expression::Subtract(_, e1, e2) => {
                let (var1, code1) = self.generate_expr(e1, result_type);
                let (var2, code2) = self.generate_expr(e2, result_type);
                let mut code = Vec::new();
                code.extend(code1);
                code.extend(code2);
                match result_type.borrow() {
                    Type::Int => code.push(format!(
                        "{} = sub i64 {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    Type::Float => code.push(format!(
                        "{} = fsub double {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    t => panic!("Unsupported type for Times: {}", t),
                }
                code
            }
            Expression::ShiftLeft(_, e1, e2) => {
                let (var1, code1) = self.generate_expr(e1, &Rc::new(Type::Int));
                let (var2, code2) = self.generate_expr(e2, &Rc::new(Type::Int));
                let mut code = Vec::new();
                code.extend(code1);
                code.extend(code2);
                code.push(format!(
                    "{} = shl i64 {}, {}",
                    result,
                    self.resolve(var1),
                    self.resolve(var2)
                ));
                code
            }
            Expression::ShiftRight(_, e1, e2) => {
                let (var1, code1) = self.generate_expr(e1, &Rc::new(Type::Int));
                let (var2, code2) = self.generate_expr(e2, &Rc::new(Type::Int));
                let mut code = Vec::new();
                code.extend(code1);
                code.extend(code2);
                code.push(format!(
                    "{} = ashr i64 {}, {}",
                    result,
                    self.resolve(var1),
                    self.resolve(var2)
                ));
                code
            }
            Expression::Greater(_, e1, e2) => {
                let (var1, code1) = self.generate_expr(e1, &self.derive_type(e1));
                let (var2, code2) = self.generate_expr(e2, &self.derive_type(e2));
                let mut code = Vec::new();
                code.extend(code1);
                code.extend(code2);
                match self.derive_type(e1).borrow() {
                    Type::Int => code.push(format!(
                        "{} = icmp sgt i64 {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    Type::Float => code.push(format!(
                        "{} = fcmp ugt double {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    t => panic!("Unsupported type for Times: {}", t),
                }
                code
            }
            Expression::Greq(_, e1, e2) => {
                let (var1, code1) = self.generate_expr(e1, &self.derive_type(e1));
                let (var2, code2) = self.generate_expr(e2, &self.derive_type(e1));
                let mut code = Vec::new();
                code.extend(code1);
                code.extend(code2);
                match self.derive_type(e1).borrow() {
                    Type::Int => code.push(format!(
                        "{} = icmp sge i64 {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    Type::Float => code.push(format!(
                        "{} = fcmp uge double {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    t => panic!("Unsupported type for Times: {}", t),
                }
                code
            }
            Expression::Leq(_, e1, e2) => {
                let (var1, code1) = self.generate_expr(e1, &self.derive_type(e1));
                let (var2, code2) = self.generate_expr(e2, &self.derive_type(e1));
                let mut code = Vec::new();
                code.extend(code1);
                code.extend(code2);
                match self.derive_type(e1).borrow() {
                    Type::Int => code.push(format!(
                        "{} = icmp sle i64 {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    Type::Float => code.push(format!(
                        "{} = fcmp ule double {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    t => panic!("Unsupported type for Times: {}", t),
                }
                code
            }
            Expression::Lesser(_, e1, e2) => {
                let (var1, code1) = self.generate_expr(e1, &self.derive_type(e1));
                let (var2, code2) = self.generate_expr(e2, &self.derive_type(e1));
                let mut code = Vec::new();
                code.extend(code1);
                code.extend(code2);
                match self.derive_type(e1).borrow() {
                    Type::Int => code.push(format!(
                        "{} = icmp slt i64 {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    Type::Float => code.push(format!(
                        "{} = fcmp ult double {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    t => panic!("Unsupported type for Times: {}", t),
                }
                code
            }
            Expression::Eq(_, e1, e2) => {
                // TODO: Implement proper eq routine, type inferencer supports comparing arbitrary 'concrete' values.
                let (var1, code1) = self.generate_expr(e1, &self.derive_type(e1));
                let (var2, code2) = self.generate_expr(e2, &self.derive_type(e1));
                let mut code = Vec::new();
                code.extend(code1);
                code.extend(code2);
                match self.derive_type(e1).borrow() {
                    Type::Int => code.push(format!(
                        "{} = icmp eq i64 {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    Type::Float => code.push(format!(
                        "{} = fcmp ueq double {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    t => panic!("Unsupported type for Eq: {}", t),
                }
                code
            }
            Expression::Neq(_, e1, e2) => {
                // TODO: Implement proper neq routing, type inferencer supports comparing arbitrary 'concrete' values.
                let (var1, code1) = self.generate_expr(e1, &self.derive_type(e1));
                let (var2, code2) = self.generate_expr(e2, &self.derive_type(e1));
                let mut code = Vec::new();
                code.extend(code1);
                code.extend(code2);
                match self.derive_type(e1).borrow() {
                    Type::Int => code.push(format!(
                        "{} = icmp ne i64 {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    Type::Float => code.push(format!(
                        "{} = fcmp une double {}, {}",
                        result,
                        self.resolve(var1),
                        self.resolve(var2)
                    )),
                    t => panic!("Unsupported type for Neq: {}", t),
                }
                code
            }
            Expression::And(_, e1, e2) => {
                let (var1, code1) = self.generate_expr(e1, &Rc::new(Type::Bool));
                let (var2, code2) = self.generate_expr(e2, &Rc::new(Type::Bool));
                let mut code = Vec::new();
                code.extend(code1);
                code.extend(code2);
                code.push(format!(
                    "{} = and i1 {}, {}",
                    result,
                    self.resolve(var1),
                    self.resolve(var2)
                ));
                code
            }

            Expression::Or(_, e1, e2) => {
                let (var1, code1) = self.generate_expr(e1, &Rc::new(Type::Bool));
                let (var2, code2) = self.generate_expr(e2, &Rc::new(Type::Bool));
                let mut code = Vec::new();
                code.extend(code1);
                code.extend(code2);
                code.push(format!(
                    "{} = or i1 {}, {}",
                    result,
                    self.resolve(var1),
                    self.resolve(var2)
                ));
                code
            }
            Expression::RecordFieldAccess(_, _, _) => unimplemented!("RecordFieldAccess"),
            Expression::Lambda(_, _, _) => unimplemented!("Lambda"),
        };

        return (result, e_code);
    }
}
