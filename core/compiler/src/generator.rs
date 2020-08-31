/* Type mapping for LOZ Types to LLVM types:
   LOZ Type         | C-Type (for reference)  | LLVM Type |
   -----------------|-------------------------|-----------|
   Bool             | bool                    | i1        |
   Char             | ????                    | i32       |
   String           | *char                   | *i8           |
   Int              | int_64_t                | i64
   Float            | float                   | float

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

/* TODO:
   - Implement matching on ADTs
   - Implement lists
   - Implement tuples
   - Implement Lambda's (brrr..)
   - Implement
*/

use std::borrow::Borrow;
use std::collections::HashMap;
use std::path::Path;
use std::process::Command;
use std::rc::Rc;

use inkwell::attributes::AttributeLoc;
use inkwell::basic_block::BasicBlock;
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::module::{Linkage, Module};
use inkwell::targets::{
    CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetTriple,
};
use inkwell::types::{BasicType, BasicTypeEnum};
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue};
use inkwell::{AddressSpace, FloatPredicate, IntPredicate, OptimizationLevel};
use itertools::{EitherOrBoth, Itertools};

use crate::ast::{Expression, FunctionBody, FunctionDefinition, FunctionRule, MatchExpression};
use crate::rewriter::RuntimeModule;
use crate::{ADTDefinition, RecordDefinition, Type, MODULE_SEPARATOR, MONOMORPHIC_PREFIX};

pub fn generate(runtime_module: Rc<RuntimeModule>, output_directory: &Path) -> Result<(), String> {
    let context = Context::create();
    let module_name = runtime_module.name.clone();

    let state = GeneratorState::new(&context, runtime_module);

    // Generate the ${MODULE_NAME}.o object file
    println!("Generating module..");
    state.generate_module(&mut VarGenerator { n: 0 }, module_name.clone());
    let mut object_path = output_directory.to_path_buf();
    object_path.push(format!("{}.o", &module_name));

    println!(
        "Writing module to file {}..",
        object_path.to_str().unwrap().to_string()
    );
    state.write_module_object(object_path.as_path())?;

    // Generate the ${MODULE_NAME} executable
    let mut executable_path = output_directory.to_path_buf();
    executable_path.push(module_name.to_string());
    println!(
        "Linking module to executable {}",
        executable_path.to_str().unwrap().to_string()
    );
    link(object_path.as_path(), executable_path.as_path())
}

fn link(object_path: &Path, executable_path: &Path) -> Result<(), String> {
    match Command::new("ld")
        .arg("/usr/lib/x86_64-linux-gnu/crti.o")
        .arg("/usr/lib/x86_64-linux-gnu/crtn.o")
        .arg("/usr/lib/x86_64-linux-gnu/crt1.o")
        .arg("-o")
        .arg(executable_path)
        .arg(object_path)
        .arg("-lc")
        .arg("-dynamic-linker")
        .arg("/lib64/ld-linux-x86-64.so.2")
        .output()
    {
        Ok(r) => {
            println!("ld code: {}", r.status);
            println!("ld output: {}", String::from_utf8(r.stderr).unwrap());
            Ok(())
        }
        Err(e) => Err(e.to_string()),
    }
}

struct GeneratorState<'a> {
    functions: HashMap<Rc<String>, Rc<FunctionDefinition>>,
    function_name_to_type: HashMap<Rc<String>, Rc<Type>>,

    records: HashMap<Rc<String>, Rc<RecordDefinition>>,
    adts: HashMap<Rc<String>, Rc<ADTDefinition>>,

    llvm_context: &'a Context,
    module: Module<'a>,
    builder: Builder<'a>,
}

struct VarGenerator {
    n: i64,
}

impl VarGenerator {
    fn var(&mut self) -> String {
        let n = self.n;
        self.n += 1;
        format!("v{}$$", n)
    }

    fn global(&mut self) -> String {
        let n = self.n;
        self.n += 1;
        format!("g{}$$", n)
    }
}

impl<'a> GeneratorState<'a> {
    fn new(context: &'a Context, runtime_module: Rc<RuntimeModule>) -> Self {
        let module = context.create_module(&runtime_module.name);
        let builder = context.create_builder();

        GeneratorState {
            functions: runtime_module
                .functions
                .iter()
                .map(|(n, d)| (Rc::clone(n), Rc::clone(d)))
                .collect(),
            function_name_to_type: runtime_module
                .functions
                .iter()
                .map(|(n, d)| {
                    (
                        Rc::clone(n),
                        Rc::clone(&d.function_type.as_ref().unwrap().enclosed_type),
                    )
                })
                .collect(),
            llvm_context: context,
            module,
            builder,

            records: runtime_module.records.clone(),
            adts: runtime_module.adts.clone(),
        }
    }

    fn generate_module(&self, g: &mut VarGenerator, module_name: Rc<String>) {
        let main_function_name = format!("{}::main", module_name);

        self.generate_c_stdlib_definitions();
        self.generate_records(g);
        self.generate_adts(g);

        let main_type = &self
            .functions
            .iter()
            .filter(|(n, _)| n.ends_with("::main"))
            .next()
            .as_ref()
            .unwrap()
            .1
            .function_type
            .as_ref()
            .unwrap()
            .enclosed_type;
        let print_bool_function = self.generate_print_bool(g);
        let print_function = self.generate_print(g, main_type, print_bool_function);
        self.generate_function_definitions(g);
        let mut llvm_main_function = None;
        for fd in self.functions.values() {
            let bla = self.generate_function(g, fd);
            if bla.get_name().to_str().unwrap() == &main_function_name {
                llvm_main_function = Some(bla);
            }
        }
        let main_type = self.llvm_context.void_type().fn_type(&[], false);
        let main_function = self.module.add_function("main", main_type, None);
        let basic_block = self.llvm_context.append_basic_block(main_function, "Entry");
        self.builder.position_at_end(basic_block);
        let value = self
            .builder
            .build_call(llvm_main_function.unwrap(), &[], &main_function_name);
        self.builder.build_call(
            print_function,
            &[value.try_as_basic_value().left().unwrap()],
            "print_result",
        );
        self.builder.build_return(None);
    }

    fn generate_c_stdlib_definitions(&self) {
        self.module.add_function(
            "malloc",
            self.llvm_context
                .i8_type()
                .ptr_type(AddressSpace::Generic)
                .fn_type(&[self.llvm_context.i64_type().as_basic_type_enum()], false),
            Some(Linkage::External),
        );
        self.module.add_function(
            "puts",
            self.llvm_context.i32_type().fn_type(
                &[self
                    .llvm_context
                    .i8_type()
                    .ptr_type(AddressSpace::Generic)
                    .as_basic_type_enum()],
                false,
            ),
            Some(Linkage::External),
        );
        self.module.add_function(
            "printf",
            self.llvm_context.i32_type().fn_type(
                &[self
                    .llvm_context
                    .i8_type()
                    .ptr_type(AddressSpace::Generic)
                    .as_basic_type_enum()],
                true,
            ),
            Some(Linkage::External),
        );
        self.module
            .add_function(
                "strcmp",
                self.llvm_context.i32_type().fn_type(
                    &[
                        self.llvm_context
                            .i8_type()
                            .ptr_type(AddressSpace::Generic)
                            .as_basic_type_enum(),
                        self.llvm_context
                            .i8_type()
                            .ptr_type(AddressSpace::Generic)
                            .as_basic_type_enum(),
                    ],
                    false,
                ),
                Some(Linkage::External),
            )
            .add_attribute(
                AttributeLoc::Function,
                self.llvm_context.create_string_attribute("noreturn", ""),
            );
        self.module
            .add_function(
                "exit",
                self.llvm_context
                    .void_type()
                    .fn_type(&[self.llvm_context.i32_type().as_basic_type_enum()], false),
                Some(Linkage::External),
            )
            .add_attribute(
                AttributeLoc::Function,
                self.llvm_context.create_string_attribute("noreturn", ""),
            );
    }

    fn generate_records(&self, _g: &mut VarGenerator) {
        for r in self.records.values() {
            let struct_type = self.llvm_context.opaque_struct_type(&r.name);
            let field_types = r
                .fields
                .iter()
                .map(|(_, t)| self.to_llvm_type(t).as_basic_type_enum())
                .collect::<Vec<BasicTypeEnum>>();
            struct_type.set_body(field_types.as_slice(), false);
        }
    }

    fn generate_adts(&self, _g: &mut VarGenerator) {
        for adt in self.adts.values() {
            let field_tag_type = self.llvm_context.i8_type().as_basic_type_enum();
            let field_content_size = adt.constructors
                .values()
                .map(|c| c.elements.iter().map(|e| self.llvm_type_size(e)).sum())
                .max()
                .unwrap();

            for (cname, cdef) in adt.constructors.iter() {
                let constructor_struct_type = self.llvm_context.opaque_struct_type(&format!("{}__{}", adt.name, cname));
                let mut argument_types = cdef.elements.iter()
                    .map(|e| self.to_llvm_type(e).as_basic_type_enum())
                    .collect::<Vec<BasicTypeEnum>>();
                argument_types.insert(0, field_tag_type);
                constructor_struct_type.set_body(argument_types.as_slice(), false);
            }

            let adt_struct_type = self.llvm_context.opaque_struct_type(&adt.name);
            adt_struct_type.set_body(&[field_tag_type, self.llvm_context.i8_type().array_type(field_content_size).as_basic_type_enum()], false);
        }
    }

    fn generate_function_definitions(&self, _g: &mut VarGenerator) -> Vec<FunctionValue> {
        let mut function_values = Vec::new();
        for function_definition in self.functions.values() {
            let function_type = self
                .function_name_to_type
                .get(&function_definition.name)
                .unwrap();
            let (return_type, arguments) = match function_type.borrow() {
                Type::Function(args, return_type) => (return_type, args.iter().collect()),
                _ => (function_type, vec![]),
            };
            let llvm_arguments = arguments
                .iter()
                .map(|a| self.to_llvm_type(a).as_basic_type_enum())
                .collect::<Vec<BasicTypeEnum>>();
            let llvm_arguments = llvm_arguments.as_slice();
            let function_type = self
                .to_llvm_type(return_type)
                .fn_type(llvm_arguments, false);
            function_values.push(self.module.add_function(
                &function_definition.name,
                function_type,
                Some(Linkage::External),
            ));
            println!(
                "Added function declaration for {}",
                &function_definition.name
            )
        }
        function_values
    }

    fn generate_function(
        &self,
        g: &mut VarGenerator,
        function_definition: &Rc<FunctionDefinition>,
    ) -> FunctionValue {
        let llvm_function = self.module.get_function(&function_definition.name).unwrap();

        let mut function_body_blocks = Vec::new();
        for (i, _) in function_definition.function_bodies.iter().enumerate() {
            function_body_blocks.push(
                self.llvm_context
                    .append_basic_block(llvm_function, &format!("Body_{}M0", i)),
            );
        }

        let no_matching_function_body_block = self
            .llvm_context
            .append_basic_block(llvm_function, &format!("MatchFault"));
        self.builder
            .position_at_end(no_matching_function_body_block);
        self.generate_abort(
            g,
            format!(
                "Function '{}' does not match",
                function_definition
                    .name
                    .split(MODULE_SEPARATOR)
                    .last()
                    .unwrap()
                    .split(MONOMORPHIC_PREFIX)
                    .next()
                    .unwrap()
            ),
            2,
        );

        for (i, either) in function_definition
            .function_bodies
            .iter()
            .zip(function_body_blocks.iter().clone())
            .zip_longest(function_body_blocks.iter().skip(1).clone())
            .enumerate()
        {
            let (function_body, first_match_block, next_function_block) = match either {
                EitherOrBoth::Both((body, block), next_block) => {
                    (body, block.clone(), next_block.clone())
                }
                EitherOrBoth::Left((body, block)) => {
                    (body, block.clone(), no_matching_function_body_block)
                }
                EitherOrBoth::Right(_) => unreachable!(),
            };

            let mut match_blocks = vec![first_match_block.clone()];
            for (mi, _) in function_body.match_expressions.iter().enumerate().skip(1) {
                match_blocks.push(
                    self.llvm_context
                        .append_basic_block(llvm_function, &format!("Body_{}M{}", i, mi)),
                );
            }

            let first_rules_block = self.generate_function_body(
                g,
                llvm_function,
                function_body,
                match_blocks,
                next_function_block.clone(),
                &format!("Body_{}", i),
            );

            if function_body.match_expressions.len() == 0 {
                self.builder.position_at_end(first_match_block.clone());
                self.builder.build_unconditional_branch(first_rules_block);
            }
        }

        llvm_function
    }

    fn generate_function_body(
        &self,
        g: &mut VarGenerator,
        llvm_function: FunctionValue<'a>,
        function_body: &Rc<FunctionBody>,
        match_blocks: Vec<BasicBlock>,
        next_function_body: BasicBlock,
        label_prefix: &str,
    ) -> BasicBlock {
        let mut combined_value_information: HashMap<Rc<String>, BasicValueEnum> = HashMap::new();

        let first_rule_block = self
            .llvm_context
            .append_basic_block(llvm_function, &format!("{}R0", label_prefix));

        for either in function_body
            .match_expressions
            .iter()
            .enumerate()
            .zip(match_blocks.iter())
            .zip_longest(match_blocks.iter().skip(1))
        {
            let (i, match_expression, match_expression_block, next_match_block) = match either {
                EitherOrBoth::Both(((i, me), l), r) => (i, me, l.clone(), r.clone()),
                EitherOrBoth::Right(_) => unreachable!(),

                // If no match expressions are left, this body matches and we branch to the start of the function rules.
                EitherOrBoth::Left(((i, me), l)) => (i, me, l.clone(), first_rule_block),
            };
            self.builder.position_at_end(match_expression_block.clone());
            let cvi = self.generate_match_expression(
                g,
                match_expression,
                llvm_function.get_nth_param(i as u32).unwrap(),
                next_match_block,
                next_function_body,
            );
            combined_value_information.extend(cvi);
        }

        let mut rule_blocks = vec![first_rule_block];
        for (i, _) in function_body.rules.iter().enumerate().skip(1) {
            rule_blocks.push(
                self.llvm_context
                    .append_basic_block(llvm_function, &format!("{}R{}", label_prefix, i)),
            );
        }
        self.generate_function_rules(
            g,
            llvm_function,
            &rule_blocks,
            &function_body.rules,
            &combined_value_information,
            label_prefix,
        );
        first_rule_block
    }

    fn generate_function_rules(
        &self,
        g: &mut VarGenerator,
        llvm_function: FunctionValue<'a>,
        rule_blocks: &Vec<BasicBlock>,
        function_rules: &Vec<Rc<FunctionRule>>,
        value_information: &HashMap<Rc<String>, BasicValueEnum<'a>>,
        label_prefix: &str,
    ) {
        let combined_value_information: HashMap<Rc<String>, BasicValueEnum<'a>> =
            value_information.clone();

        let no_rules_match_block = self
            .llvm_context
            .append_basic_block(llvm_function, &format!("{}_NoRulesMatch", label_prefix));
        self.builder.position_at_end(no_rules_match_block);
        self.generate_abort(g, String::from("No matching rule"), 1);
        //self.builder.build_return(Some(&self.llvm_context.i64_type().const_int(1, false).as_basic_value_enum()));

        for either in function_rules
            .iter()
            .zip(rule_blocks.iter().cloned())
            .zip_longest(rule_blocks.iter().skip(1).cloned())
        {
            let (rule, current_rule_block, next_rule_block) = match either {
                EitherOrBoth::Both((rule, current_rule_block), next_rule_block) => {
                    (rule, current_rule_block, next_rule_block)
                }
                EitherOrBoth::Left((rule, current_rule_block)) => {
                    (rule, current_rule_block, no_rules_match_block)
                }
                EitherOrBoth::Right(_) => unreachable!(),
            };
            self.builder.position_at_end(current_rule_block);
            match rule.borrow() {
                FunctionRule::ConditionalRule(_, condition, result) => {
                    self.builder.position_at_end(current_rule_block.clone());
                    let cv = self.generate_expression(g, condition, &combined_value_information);

                    let result_block = self.llvm_context.append_basic_block(
                        llvm_function,
                        &format!("{}_result", current_rule_block.get_name().to_str().unwrap()),
                    );
                    self.builder.position_at_end(result_block);
                    let ev = self.generate_expression(g, result, &combined_value_information);
                    self.builder.build_return(Some(&ev));

                    self.builder.position_at_end(current_rule_block);
                    self.builder.build_conditional_branch(
                        cv.as_basic_value_enum().into_int_value(),
                        result_block,
                        next_rule_block,
                    );
                }
                FunctionRule::ExpressionRule(_, e) => {
                    self.builder.position_at_end(current_rule_block);
                    let ev = self.generate_expression(g, e, &combined_value_information);
                    self.builder.build_return(Some(&ev));
                }
                FunctionRule::LetRule(_, _, _, _) => unimplemented!("LetRule"),
            }
        }
    }

    fn generate_match_expression(
        &self,
        g: &mut VarGenerator,
        me: &Rc<MatchExpression>,
        match_value: BasicValueEnum<'a>,
        match_block: BasicBlock,
        no_match_block: BasicBlock,
    ) -> HashMap<Rc<String>, BasicValueEnum<'a>> {
        let mut value_information = HashMap::new();
        match me.borrow() {
            MatchExpression::IntLiteral(_, i) => {
                let matches = self.builder.build_int_compare(
                    IntPredicate::EQ,
                    self.llvm_context.i64_type().const_int(*i as u64, true),
                    match_value.into_int_value(),
                    &g.var(),
                );
                self.builder
                    .build_conditional_branch(matches, match_block, no_match_block);
            }
            MatchExpression::CharLiteral(_, c) => {
                let mut bla = [0; 4];
                let str = c.encode_utf8(&mut bla);
                let bla = self.builder.build_global_string_ptr(str, &g.var());
                let strcmp = self.module.get_function("strcmp").unwrap();
                let compared = self
                    .builder
                    .build_call(strcmp, &[bla.as_basic_value_enum(), match_value], &g.var())
                    .try_as_basic_value()
                    .left()
                    .unwrap()
                    .into_int_value();
                let eq = self.builder.build_int_compare(
                    IntPredicate::EQ,
                    compared,
                    self.llvm_context.i32_type().const_int(0, false),
                    &g.var(),
                );

                self.builder
                    .build_conditional_branch(eq, match_block, no_match_block);
            }
            MatchExpression::StringLiteral(_, s) => {
                let bla = self.builder.build_global_string_ptr(s, &g.var());
                let strcmp = self.module.get_function("strcmp").unwrap();
                let compared = self
                    .builder
                    .build_call(strcmp, &[bla.as_basic_value_enum(), match_value], &g.var())
                    .try_as_basic_value()
                    .left()
                    .unwrap()
                    .into_int_value();
                let eq = self.builder.build_int_compare(
                    IntPredicate::EQ,
                    compared,
                    self.llvm_context.i32_type().const_int(0, false),
                    &g.var(),
                );

                self.builder
                    .build_conditional_branch(eq, match_block, no_match_block);
            }
            MatchExpression::BoolLiteral(_, b) => {
                let eq = self.builder.build_int_compare(
                    IntPredicate::EQ,
                    self.llvm_context
                        .bool_type()
                        .const_int(if *b { 1 } else { 0 }, false),
                    match_value.into_int_value(),
                    &g.var(),
                );
                self.builder
                    .build_conditional_branch(eq, match_block, no_match_block);
            }
            MatchExpression::Identifier(_, name) => {
                value_information.insert(Rc::clone(name), match_value);
                self.builder.build_unconditional_branch(match_block);
            }
            MatchExpression::Tuple(_, _) => unimplemented!(""),
            MatchExpression::ShorthandList(_, _) => unimplemented!(""),
            MatchExpression::LonghandList(_, _, _) => unimplemented!(""),
            MatchExpression::Wildcard(_) => unimplemented!(""),
            MatchExpression::ADT(_, _, _) => unimplemented!(""),
            MatchExpression::Record(_, record_name, fields) => {
                let record_definition = self.records.get(record_name).unwrap();
                for field in fields {
                    let index = record_definition
                        .fields
                        .iter()
                        .enumerate()
                        .filter(|(_, (n, _))| n == field)
                        .map(|(i, _)| i)
                        .next()
                        .unwrap();
                    let field_pointer = self
                        .builder
                        .build_struct_gep(match_value.into_pointer_value(), index as u32, &g.var())
                        .unwrap();
                    let field_value = self.builder.build_load(field_pointer, &g.var());
                    value_information.insert(Rc::clone(field), field_value);
                }
                self.builder.build_unconditional_branch(match_block);
            }
        };
        value_information
    }

    fn generate_expression(
        &self,
        g: &mut VarGenerator,
        expression: &Rc<Expression>,
        value_information: &HashMap<Rc<String>, BasicValueEnum<'a>>,
    ) -> BasicValueEnum<'a> {
        match expression.borrow() {
            Expression::BoolLiteral(_, b) => self
                .llvm_context
                .bool_type()
                .const_int(if *b { 1 } else { 0 }, false)
                .as_basic_value_enum(),
            Expression::StringLiteral(_, string) => {
                let llvm_string = self.builder.build_global_string_ptr(&string, &g.global());
                llvm_string.as_basic_value_enum()
            }
            Expression::CharacterLiteral(_, character) => {
                let mut b = [0; 4];
                let str = character.encode_utf8(&mut b);
                let llvm_string = self.builder.build_global_string_ptr(str, &g.global());
                llvm_string.as_basic_value_enum()
            }
            Expression::IntegerLiteral(_, i) => self
                .llvm_context
                .i64_type()
                .const_int(*i as u64, true)
                .as_basic_value_enum(),
            Expression::FloatLiteral(_, f) => self
                .llvm_context
                .f64_type()
                .const_float(*f)
                .as_basic_value_enum(),
            Expression::TupleLiteral(_, elements) => {
                let mut element_values = Vec::new();
                for e in elements {
                    element_values.push(self.generate_expression(g, e, value_information));
                }
                let tuple_type = self.llvm_context.struct_type(
                    element_values
                        .iter()
                        .map(|ev| ev.get_type())
                        .collect::<Vec<BasicTypeEnum>>()
                        .as_slice(),
                    false,
                );
                let tuple_pointer = self
                    .builder
                    .build_call(
                        self.module.get_function("malloc").unwrap(),
                        &[tuple_type.size_of().unwrap().as_basic_value_enum()],
                        &g.var(),
                    )
                    .try_as_basic_value()
                    .left()
                    .unwrap()
                    .into_pointer_value()
                    .const_cast(tuple_type.ptr_type(AddressSpace::Generic));

                for (i, value) in element_values.into_iter().enumerate() {
                    let element_pointer = self
                        .builder
                        .build_struct_gep(tuple_pointer, i as u32, &g.var())
                        .unwrap();
                    self.builder.build_store(element_pointer, value);
                }
                tuple_pointer.as_basic_value_enum()
            }
            Expression::EmptyListLiteral(_) => unimplemented!(""),
            Expression::ShorthandListLiteral(_, _) => unimplemented!(""),
            Expression::LonghandListLiteral(_, _, _) => unimplemented!(""),
            Expression::ADTTypeConstructor(_, _, _, _) => unimplemented!(""),
            Expression::Record(_, _, c, d) => {
                let record_definition = self.records.get(c).unwrap();
                let record_llvm_type = self.module.get_struct_type(c).unwrap();
                let record_heap_pointer = self
                    .builder
                    .build_call(
                        self.module.get_function("malloc").unwrap(),
                        &[record_llvm_type.size_of().unwrap().as_basic_value_enum()],
                        &g.var(),
                    )
                    .try_as_basic_value()
                    .left()
                    .unwrap()
                    .into_pointer_value()
                    .const_cast(record_llvm_type.ptr_type(AddressSpace::Generic));

                for (i, (_, (_, field_expression))) in
                    record_definition.fields.iter().zip(d.iter()).enumerate()
                {
                    let v = self.generate_expression(g, field_expression, value_information);
                    let field_ptr = self
                        .builder
                        .build_struct_gep(record_heap_pointer, i as u32, &g.var())
                        .unwrap();
                    self.builder.build_store(field_ptr, v);
                }
                record_heap_pointer.as_basic_value_enum()
            }
            Expression::Case(_, _, _) => unimplemented!(""),
            Expression::Call(_, _, b, arguments) => {
                let mut llvm_argument_values = Vec::new();
                for a in arguments {
                    let llvm_a = self.generate_expression(g, a, value_information);
                    llvm_argument_values.push(llvm_a);
                }

                let llvm_function = self.module.get_function(b).unwrap();
                self.builder
                    .build_call(llvm_function, &llvm_argument_values.as_slice(), b)
                    .try_as_basic_value()
                    .left()
                    .unwrap()
            }
            Expression::Variable(_, v) => value_information.get(v).unwrap().clone(),
            Expression::Negation(_, e) => {
                let ev = self.generate_expression(g, e, value_information);
                self.builder
                    .build_xor(
                        ev.into_int_value(),
                        self.llvm_context.bool_type().const_int(1, false),
                        &g.var(),
                    )
                    .as_basic_value_enum()
            }
            Expression::Minus(_, e) => {
                let ev = self.generate_expression(g, e, value_information);
                if ev.is_int_value() {
                    self.builder
                        .build_int_mul(
                            ev.into_int_value(),
                            self.llvm_context
                                .i64_type()
                                .const_int((-1 as i64) as u64, true),
                            &g.var(),
                        )
                        .as_basic_value_enum()
                } else {
                    self.builder
                        .build_float_mul(
                            ev.into_float_value(),
                            self.llvm_context.f64_type().const_float(-1.0),
                            &g.var(),
                        )
                        .as_basic_value_enum()
                }
            }
            Expression::Times(_, l, r) => {
                let el = self.generate_expression(g, l, value_information);
                let er = self.generate_expression(g, r, value_information);
                if el.is_int_value() {
                    self.builder
                        .build_int_mul(el.into_int_value(), er.into_int_value(), &g.var())
                        .as_basic_value_enum()
                } else {
                    self.builder
                        .build_float_mul(el.into_float_value(), er.into_float_value(), &g.var())
                        .as_basic_value_enum()
                }
            }
            Expression::Divide(_, l, r) => {
                let el = self.generate_expression(g, l, value_information);
                let er = self.generate_expression(g, r, value_information);
                if el.is_int_value() {
                    self.builder
                        .build_int_signed_div(el.into_int_value(), er.into_int_value(), &g.var())
                        .as_basic_value_enum()
                } else {
                    self.builder
                        .build_float_div(el.into_float_value(), er.into_float_value(), &g.var())
                        .as_basic_value_enum()
                }
            }
            Expression::Modulo(_, l, r) => {
                let el = self.generate_expression(g, l, value_information);
                let er = self.generate_expression(g, r, value_information);
                if el.is_int_value() {
                    self.builder
                        .build_int_signed_rem(el.into_int_value(), er.into_int_value(), &g.var())
                        .as_basic_value_enum()
                } else {
                    self.builder
                        .build_float_rem(el.into_float_value(), er.into_float_value(), &g.var())
                        .as_basic_value_enum()
                }
            }
            Expression::Add(_, l, r) => {
                let el = self.generate_expression(g, l, value_information);
                let er = self.generate_expression(g, r, value_information);
                if el.is_int_value() {
                    self.builder
                        .build_int_add(el.into_int_value(), er.into_int_value(), &g.var())
                        .as_basic_value_enum()
                } else {
                    self.builder
                        .build_float_add(el.into_float_value(), er.into_float_value(), &g.var())
                        .as_basic_value_enum()
                }
            }
            Expression::Subtract(_, l, r) => {
                let el = self.generate_expression(g, l, value_information);
                let er = self.generate_expression(g, r, value_information);
                if el.is_int_value() {
                    self.builder
                        .build_int_sub(el.into_int_value(), er.into_int_value(), &g.var())
                        .as_basic_value_enum()
                } else {
                    self.builder
                        .build_float_sub(el.into_float_value(), er.into_float_value(), &g.var())
                        .as_basic_value_enum()
                }
            }
            Expression::ShiftLeft(_, l, r) => {
                let el = self.generate_expression(g, l, value_information);
                let er = self.generate_expression(g, r, value_information);
                self.builder
                    .build_left_shift(el.into_int_value(), er.into_int_value(), &g.var())
                    .as_basic_value_enum()
            }
            Expression::ShiftRight(_, l, r) => {
                let el = self.generate_expression(g, l, value_information);
                let er = self.generate_expression(g, r, value_information);
                self.builder
                    .build_right_shift(el.into_int_value(), er.into_int_value(), false, &g.var())
                    .as_basic_value_enum()
            }
            Expression::Greater(_, l, r) => {
                let el = self.generate_expression(g, l, value_information);
                let er = self.generate_expression(g, r, value_information);
                if el.is_int_value() {
                    self.builder
                        .build_int_compare(
                            IntPredicate::SGT,
                            el.into_int_value(),
                            er.into_int_value(),
                            &g.var(),
                        )
                        .as_basic_value_enum()
                } else {
                    self.builder
                        .build_float_compare(
                            FloatPredicate::OGT,
                            el.into_float_value(),
                            er.into_float_value(),
                            &g.var(),
                        )
                        .as_basic_value_enum()
                }
            }
            Expression::Greq(_, l, r) => {
                let el = self.generate_expression(g, l, value_information);
                let er = self.generate_expression(g, r, value_information);
                if el.is_int_value() {
                    self.builder
                        .build_int_compare(
                            IntPredicate::SGE,
                            el.into_int_value(),
                            er.into_int_value(),
                            &g.var(),
                        )
                        .as_basic_value_enum()
                } else {
                    self.builder
                        .build_float_compare(
                            FloatPredicate::OGE,
                            el.into_float_value(),
                            er.into_float_value(),
                            &g.var(),
                        )
                        .as_basic_value_enum()
                }
            }
            Expression::Leq(_, l, r) => {
                let el = self.generate_expression(g, l, value_information);
                let er = self.generate_expression(g, r, value_information);
                if el.is_int_value() {
                    self.builder
                        .build_int_compare(
                            IntPredicate::SLE,
                            el.into_int_value(),
                            er.into_int_value(),
                            &g.var(),
                        )
                        .as_basic_value_enum()
                } else {
                    self.builder
                        .build_float_compare(
                            FloatPredicate::OLE,
                            el.into_float_value(),
                            er.into_float_value(),
                            &g.var(),
                        )
                        .as_basic_value_enum()
                }
            }
            Expression::Lesser(_, l, r) => {
                let el = self.generate_expression(g, l, value_information);
                let er = self.generate_expression(g, r, value_information);
                if el.is_int_value() {
                    self.builder
                        .build_int_compare(
                            IntPredicate::SLT,
                            el.into_int_value(),
                            er.into_int_value(),
                            &g.var(),
                        )
                        .as_basic_value_enum()
                } else {
                    self.builder
                        .build_float_compare(
                            FloatPredicate::OLT,
                            el.into_float_value(),
                            er.into_float_value(),
                            &g.var(),
                        )
                        .as_basic_value_enum()
                }
            }
            Expression::Eq(_, l, r) => {
                let el = self.generate_expression(g, l, value_information);
                let er = self.generate_expression(g, r, value_information);
                if el.is_int_value() {
                    self.builder
                        .build_int_compare(
                            IntPredicate::EQ,
                            el.into_int_value(),
                            er.into_int_value(),
                            &g.var(),
                        )
                        .as_basic_value_enum()
                } else {
                    self.builder
                        .build_float_compare(
                            FloatPredicate::OGE,
                            el.into_float_value(),
                            er.into_float_value(),
                            &g.var(),
                        )
                        .as_basic_value_enum()
                }
            }
            Expression::Neq(_, l, r) => {
                let el = self.generate_expression(g, l, value_information);
                let er = self.generate_expression(g, r, value_information);
                if el.is_int_value() {
                    self.builder
                        .build_int_compare(
                            IntPredicate::NE,
                            el.into_int_value(),
                            er.into_int_value(),
                            &g.var(),
                        )
                        .as_basic_value_enum()
                } else {
                    self.builder
                        .build_float_compare(
                            FloatPredicate::ONE,
                            el.into_float_value(),
                            er.into_float_value(),
                            &g.var(),
                        )
                        .as_basic_value_enum()
                }
            }
            Expression::And(_, l, r) => {
                let el = self.generate_expression(g, l, value_information);
                let er = self.generate_expression(g, r, value_information);
                self.builder
                    .build_and(el.into_int_value(), er.into_int_value(), &g.var())
                    .as_basic_value_enum()
            }
            Expression::Or(_, l, r) => {
                let el = self.generate_expression(g, l, value_information);
                let er = self.generate_expression(g, r, value_information);
                self.builder
                    .build_or(el.into_int_value(), er.into_int_value(), &g.var())
                    .as_basic_value_enum()
            }
            Expression::RecordFieldAccess(_, _, record_name, l, r) => {
                let record_value = self.generate_expression(g, l, value_information);
                let field_name = match r.borrow() {
                    Expression::Variable(_, field) => field,
                    _ => unreachable!(),
                };
                let record_definition = self.records.get(record_name).unwrap();
                let record_field_index = record_definition
                    .fields
                    .iter()
                    .enumerate()
                    .filter(|(_, (n, _))| n == field_name)
                    .map(|t| t.0)
                    .next()
                    .unwrap();

                let field_pointer = self.builder.build_struct_gep(
                    record_value.into_pointer_value(),
                    record_field_index as u32,
                    &g.var(),
                );
                self.builder.build_load(field_pointer.unwrap(), &g.var())
            }
            Expression::Lambda(_, _, _, _) => unimplemented!(""),
        }
    }

    fn write_module_object(&self, object_file: &Path) -> Result<(), String> {
        println!("LLMVM IR:\n{}", self.module.print_to_string().to_string());
        Target::initialize_x86(&InitializationConfig::default());

        let opt = OptimizationLevel::Aggressive;
        let reloc = RelocMode::Default;
        let model = CodeModel::Default;
        let target = Target::from_name("x86-64").unwrap();
        let target_machine = target
            .create_target_machine(
                &TargetTriple::create("x86_64-pc-linux-gnu"),
                "x86-64",
                "",
                opt,
                reloc,
                model,
            )
            .unwrap();

        println!("Writing to file..");
        target_machine
            .write_to_file(&self.module, FileType::Object, object_file)
            .map_err(|e| e.to_string())
    }

    fn generate_abort(&self, g: &mut VarGenerator, message: String, exitcode: i32) {
        let puts = self.module.get_function("puts").unwrap();
        let message_pointer = self.builder.build_global_string_ptr(&message, &g.global());
        self.builder
            .build_call(puts, &[message_pointer.as_basic_value_enum()], &g.var());
        let exit = self.module.get_function("exit").unwrap();
        self.builder.build_call(
            exit,
            &[self
                .llvm_context
                .i32_type()
                .const_int(exitcode as u64, true)
                .into()],
            &g.var(),
        );
        self.builder.build_unreachable();
    }

    fn generate_print(
        &self,
        g: &mut VarGenerator,
        type_to_print: &Rc<Type>,
        print_bool_function: FunctionValue,
    ) -> FunctionValue {
        let print_value_type = self.llvm_context.void_type().fn_type(
            &[self.to_llvm_type(type_to_print).as_basic_type_enum()],
            false,
        );
        let function_print_value =
            self.module
                .add_function("print_value", print_value_type, Some(Linkage::External));
        let entry = self
            .llvm_context
            .append_basic_block(function_print_value, "Entry");
        self.builder.position_at_end(entry);
        self.generate_print_code(
            g,
            type_to_print,
            function_print_value
                .get_nth_param(0)
                .unwrap()
                .as_basic_value_enum(),
            print_bool_function,
        );
        self.builder.build_call(
            self.module.get_function("printf").unwrap(),
            &[self
                .builder
                .build_global_string_ptr("\n", "newline")
                .as_basic_value_enum()],
            "print_newline",
        );
        self.builder.build_return(None);
        function_print_value
    }

    fn generate_print_bool(&self, g: &mut VarGenerator) -> FunctionValue {
        let print_bool_type = self
            .llvm_context
            .void_type()
            .fn_type(&[self.llvm_context.bool_type().as_basic_type_enum()], false);
        let print_bool =
            self.module
                .add_function("print_bool", print_bool_type, Some(Linkage::External));
        let e = self.llvm_context.append_basic_block(print_bool, "Entry");
        let tt = self.llvm_context.append_basic_block(print_bool, "TT");
        let ff = self.llvm_context.append_basic_block(print_bool, "FF");
        let printf = self.module.get_function("printf").unwrap();

        self.builder.position_at_end(e);
        self.builder.build_conditional_branch(
            print_bool.get_nth_param(0).unwrap().into_int_value(),
            tt,
            ff,
        );

        self.builder.position_at_end(tt);
        self.builder.build_call(
            printf,
            &[self
                .builder
                .build_global_string_ptr("True", "true_string")
                .as_basic_value_enum()],
            &g.var(),
        );
        self.builder.build_return(None);

        self.builder.position_at_end(ff);
        self.builder.build_call(
            printf,
            &[self
                .builder
                .build_global_string_ptr("False", "false_string")
                .as_basic_value_enum()],
            &g.var(),
        );
        self.builder.build_return(None);

        print_bool
    }

    fn generate_print_code(
        &self,
        g: &mut VarGenerator,
        type_to_print: &Rc<Type>,
        value: BasicValueEnum,
        print_bool_function: FunctionValue,
    ) {
        let printf = self.module.get_function("printf").unwrap();
        match type_to_print.borrow() {
            Type::Bool => self
                .builder
                .build_call(print_bool_function, &[value], &g.var()),

            Type::Char => self.builder.build_call(
                printf,
                &[
                    self.builder
                        .build_global_string_ptr("'%s'", "char_format_string")
                        .as_basic_value_enum(),
                    value,
                ],
                &g.var(),
            ),
            Type::String => self.builder.build_call(
                printf,
                &[
                    self.builder
                        .build_global_string_ptr("\"%s\"", "string_format_string")
                        .as_basic_value_enum(),
                    value,
                ],
                &g.var(),
            ),
            Type::Int => self.builder.build_call(
                printf,
                &[
                    self.builder
                        .build_global_string_ptr("%d", "int_format_string")
                        .as_basic_value_enum(),
                    value,
                ],
                &g.var(),
            ),
            Type::Float => self.builder.build_call(
                printf,
                &[
                    self.builder
                        .build_global_string_ptr("%f", "float_format_string")
                        .as_basic_value_enum(),
                    value,
                ],
                &g.var(),
            ),
            Type::UserType(name, _) => {
                if self.records.contains_key(name) {
                    let print_string = self
                        .builder
                        .build_global_string_ptr("%s", "print_string")
                        .as_basic_value_enum();
                    let record_prefix = self
                        .builder
                        .build_global_string_ptr(
                            &format!("{{{}|", sanitize_name(name)),
                            "record_prefix",
                        )
                        .as_basic_value_enum();
                    let record_suffix = self
                        .builder
                        .build_global_string_ptr("}", "record_suffix")
                        .as_basic_value_enum();
                    let record_field_name = self
                        .builder
                        .build_global_string_ptr("%s = ", "record_field_name")
                        .as_basic_value_enum();
                    let record_field_separator = self
                        .builder
                        .build_global_string_ptr(", ", "record_field_separator")
                        .as_basic_value_enum();
                    self.builder
                        .build_call(printf, &[print_string, record_prefix], &g.var());

                    let record_definition = self.records.get(name).unwrap();
                    let struct_value = value.into_pointer_value();
                    for (i, (field_name, field_type)) in record_definition.fields.iter().enumerate()
                    {
                        let field_pointer = self
                            .builder
                            .build_struct_gep(struct_value, i as u32, &g.var())
                            .unwrap();
                        let field_value = self.builder.build_load(field_pointer, &g.var());
                        self.builder.build_call(
                            printf,
                            &[
                                record_field_name,
                                self.builder
                                    .build_global_string_ptr(field_name, field_name)
                                    .as_basic_value_enum(),
                            ],
                            &g.var(),
                        );
                        self.generate_print_code(g, field_type, field_value, print_bool_function);
                        if i < record_definition.fields.len() - 1 {
                            self.builder
                                .build_call(printf, &[record_field_separator], &g.var());
                        }
                    }
                    self.builder.build_call(printf, &[record_suffix], &g.var())
                } else {
                    unimplemented!("Printing ADTs")
                }
            }
            Type::Tuple(elements) => {
                let tuple_prefix = self
                    .builder
                    .build_global_string_ptr("(", "tuple_prefix")
                    .as_basic_value_enum();
                let tuple_separator = self
                    .builder
                    .build_global_string_ptr(", ", "tuple_separator")
                    .as_basic_value_enum();
                let tuple_suffix = self
                    .builder
                    .build_global_string_ptr(")", "tuple_suffix")
                    .as_basic_value_enum();
                self.builder.build_call(printf, &[tuple_prefix], &g.var());
                for (i, element_type) in elements.iter().enumerate() {
                    let element_pointer = self
                        .builder
                        .build_struct_gep(value.into_pointer_value(), i as u32, &g.var())
                        .unwrap();
                    let element_value = self.builder.build_load(element_pointer, &g.var());
                    self.generate_print_code(g, element_type, element_value, print_bool_function);
                    if i < elements.len() - 1 {
                        self.builder
                            .build_call(printf, &[tuple_separator], &g.var());
                    }
                }
                self.builder.build_call(printf, &[tuple_suffix], &g.var())
            }
            Type::List(_) => unimplemented!(""),
            Type::Variable(_) => unimplemented!(""),
            Type::Function(_, _) => unreachable!("Printing function not supported."),
        };
    }

    fn llvm_type_size(&self, loz_type: &Rc<Type>) -> u32 {
        match loz_type.borrow() {
            Type::Bool => 8,
            Type::Char => 64,
            Type::String => 64,
            Type::Int => 64,
            Type::Float => 64,
            Type::UserType(_, _) => 64,
            Type::Tuple(_) => 64,
            Type::List(_) => 64,
            Type::Variable(_) => unreachable!("Variable type in generator"),
            Type::Function(_, _) => unreachable!("Function type in generator"),
        }
    }

    fn to_llvm_type(&self, loz_type: &Rc<Type>) -> Box<dyn BasicType<'a> + 'a> {
        match loz_type.borrow() {
            Type::Bool => Box::new(self.llvm_context.bool_type().as_basic_type_enum()),
            Type::Int => Box::new(self.llvm_context.i64_type().as_basic_type_enum()),
            Type::Float => Box::new(self.llvm_context.f64_type().as_basic_type_enum()),
            Type::Char => Box::new(
                self.llvm_context
                    .i8_type()
                    .ptr_type(AddressSpace::Generic)
                    .as_basic_type_enum(),
            ),
            Type::String => Box::new(
                self.llvm_context
                    .i8_type()
                    .ptr_type(AddressSpace::Generic)
                    .as_basic_type_enum(),
            ),
            Type::UserType(name, _) => Box::new(
                self.module
                    .get_struct_type(name)
                    .unwrap()
                    .ptr_type(AddressSpace::Generic)
                    .as_basic_type_enum(),
            ),
            Type::Tuple(els) => Box::new(
                self.llvm_context
                    .struct_type(
                        els.iter()
                            .map(|e| self.to_llvm_type(e).as_basic_type_enum())
                            .collect::<Vec<BasicTypeEnum>>()
                            .as_slice(),
                        false,
                    )
                    .ptr_type(AddressSpace::Generic),
            ),
            _ => unimplemented!("{:?}", loz_type),
        }
    }
}

fn sanitize_name(name: &str) -> &str {
    name.split(MODULE_SEPARATOR)
        .last()
        .unwrap()
        .split(MONOMORPHIC_PREFIX)
        .next()
        .unwrap()
}
