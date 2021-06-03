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
use inkwell::types::{BasicType, BasicTypeEnum, PointerType};
use inkwell::values::{BasicValue, BasicValueEnum, FunctionValue, PointerValue};
use inkwell::{AddressSpace, FloatPredicate, IntPredicate, OptimizationLevel};
use itertools::{EitherOrBoth, Itertools};

use crate::generator::ir::{
    IRADTDefinition, IRExpression, IRFunctionBody, IRFunctionDefinition, IRFunctionRule,
    IRMatchExpression, IRRecordDefinition, IRType,
};
use crate::module_system::CompilerOptions;
use crate::rewriter::{IRModule, Monomorphized};
use crate::{ADT_SEPARATOR, MODULE_SEPARATOR, MONOMORPHIC_PREFIX};
use number_prefix::NumberPrefix;
use std::collections::hash_map::DefaultHasher;
use std::fs::File;
use std::hash::{Hash, Hasher};
use std::io::Write;

pub mod ir;

pub fn generate(
    runtime_module: Rc<IRModule>,
    output_directory: &Path,
    compiler_options: &CompilerOptions,
) -> Result<(), String> {
    let context = Context::create();
    let module_name = runtime_module.name.clone();

    let state = GeneratorState::new(&context, runtime_module);

    // Generate the ${MODULE_NAME}.o object file
    println!("Generating module..");

    state.generate_module(&mut VarGenerator { n: 0 }, module_name.clone());
    let mut object_path = output_directory.to_path_buf();
    object_path.push(format!("{}.o", &module_name));

    state.write_module_object(object_path.as_path(), compiler_options)?;

    // Generate the ${MODULE_NAME} executable
    let mut executable_path = output_directory.to_path_buf();
    executable_path.push(module_name.to_string());
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
            if r.status.success() {
                let executable_size = File::open(executable_path)
                    .unwrap()
                    .metadata()
                    .unwrap()
                    .len();
                println!(
                    "Linked executable {} ({})",
                    executable_path.display(),
                    format_size(executable_size as usize)
                );
                Ok(())
            } else {
                println!("ld error code: {}", r.status);
                println!("ld error output: {}", String::from_utf8(r.stderr).unwrap());
                Err(format!("Error linking, see previous output."))
            }
        }
        Err(e) => Err(e.to_string()),
    }
}

struct GeneratorState<'a> {
    functions: HashMap<Rc<String>, Rc<IRFunctionDefinition>>,
    function_name_to_type: HashMap<Rc<String>, Rc<IRType>>,

    records: HashMap<Rc<String>, Monomorphized<IRRecordDefinition>>,
    adts: HashMap<Rc<String>, Monomorphized<IRADTDefinition>>,

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
    fn new(context: &'a Context, runtime_module: Rc<IRModule>) -> Self {
        let module = context.create_module(&runtime_module.name);
        let builder = context.create_builder();

        GeneratorState {
            functions: runtime_module
                .functions
                .iter()
                .map(|(n, d)| (Rc::clone(n), d.clone()))
                .collect(),
            function_name_to_type: runtime_module
                .functions
                .iter()
                .map(|(n, d)| (Rc::clone(n), Rc::clone(&d.function_type)))
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
            .function_type;
        self.generate_print_bool(g);
        let print_function = self.generate_print(g, main_type);
        self.generate_function_definitions(g);
        let mut llvm_main_function = None;
        for (_, fd) in self.functions.iter() {
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
        for r in self.records.values().flat_map(|r| r.instances.values()) {
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
        for adt in self.adts.values().flat_map(|a| a.instances.values()) {
            self.llvm_context.opaque_struct_type(&adt.name);
        }

        for adt in self.adts.values().flat_map(|a| a.instances.values()) {
            let field_tag_type = self.llvm_context.i8_type().as_basic_type_enum();
            let field_content_size = adt
                .constructors
                .iter()
                .map(|c| c.elements.iter().map(|e| self.llvm_type_size(e)).sum())
                .max()
                .unwrap();

            for constructor in adt.constructors.iter() {
                let constructor_struct_name = format!("{}__{}", adt.name, &constructor.name);
                let constructor_struct_type = self
                    .llvm_context
                    .opaque_struct_type(&constructor_struct_name);
                let argument_types = constructor
                    .elements
                    .iter()
                    .map(|e| self.to_llvm_type(e).as_basic_type_enum())
                    .collect::<Vec<BasicTypeEnum>>();
                constructor_struct_type.set_body(argument_types.as_slice(), false);
            }

            let adt_struct_type = self.module.get_struct_type(&adt.name).unwrap();
            adt_struct_type.set_body(
                &[
                    field_tag_type,
                    self.llvm_context
                        .i8_type()
                        .array_type(field_content_size)
                        .as_basic_type_enum(),
                ],
                false,
            );
        }
    }

    fn generate_function_definitions(&self, _g: &mut VarGenerator) -> Vec<FunctionValue> {
        let mut function_values = Vec::new();
        for (_, function_definition) in self.functions.iter() {
            let function_type = self
                .function_name_to_type
                .get(&function_definition.name)
                .unwrap();
            let (return_type, arguments) = match function_type.borrow() {
                IRType::Function(args, return_type) => (return_type, args.iter().collect()),
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
        }
        function_values
    }

    fn generate_function(
        &self,
        g: &mut VarGenerator,
        function_definition: &Rc<IRFunctionDefinition>,
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
        function_body: &Rc<IRFunctionBody>,
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
        function_rules: &Vec<Rc<IRFunctionRule>>,
        value_information: &HashMap<Rc<String>, BasicValueEnum<'a>>,
        label_prefix: &str,
    ) {
        let mut combined_value_information: HashMap<Rc<String>, BasicValueEnum<'a>> =
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
                IRFunctionRule::ConditionalRule(_, condition, result) => {
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
                IRFunctionRule::ExpressionRule(_, e) => {
                    let ev = self.generate_expression(g, e, &combined_value_information);
                    self.builder.build_return(Some(&ev));
                }
                IRFunctionRule::LetRule(_, lhs, rhs) => {
                    let value = self.generate_expression(g, rhs, &combined_value_information);
                    combined_value_information.extend(self.generate_match_expression(
                        g,
                        lhs,
                        value,
                        next_rule_block,
                        no_rules_match_block,
                    ));
                }
            }
        }
    }

    fn generate_match_expression(
        &self,
        g: &mut VarGenerator,
        me: &Rc<IRMatchExpression>,
        match_value: BasicValueEnum<'a>,
        match_block: BasicBlock,
        no_match_block: BasicBlock,
    ) -> HashMap<Rc<String>, BasicValueEnum<'a>> {
        let mut value_information = HashMap::new();
        match me.borrow() {
            IRMatchExpression::IntLiteral(_, i) => {
                let matches = self.builder.build_int_compare(
                    IntPredicate::EQ,
                    self.llvm_context.i64_type().const_int(*i as u64, true),
                    match_value.into_int_value(),
                    &g.var(),
                );
                self.builder
                    .build_conditional_branch(matches, match_block, no_match_block);
            }
            IRMatchExpression::CharLiteral(_, c) => {
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
            IRMatchExpression::StringLiteral(_, s) => {
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
            IRMatchExpression::BoolLiteral(_, b) => {
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
            IRMatchExpression::Identifier(_, name) => {
                value_information.insert(Rc::clone(name), match_value);
                self.builder.build_unconditional_branch(match_block);
            }
            IRMatchExpression::Tuple(_, elements) => {
                let element_blocks: Vec<BasicBlock> = elements
                    .iter()
                    .map(|_| {
                        self.llvm_context
                            .append_basic_block(match_block.get_parent().unwrap(), &g.var())
                    })
                    .collect();

                self.builder
                    .build_unconditional_branch(element_blocks.get(0).unwrap().clone());

                for (index, (element, element_match_block)) in
                    elements.iter().zip(element_blocks.iter()).enumerate()
                {
                    self.builder.position_at_end(element_match_block.clone());
                    let element_pointer = self.builder.build_struct_gep(
                        match_value.into_pointer_value(),
                        index as u32,
                        &g.var(),
                    );
                    let element_value = self.builder.build_load(element_pointer.unwrap(), &g.var());
                    let next_match_block = element_blocks
                        .get(index + 1)
                        .cloned()
                        .unwrap_or_else(|| match_block);

                    value_information.extend(self.generate_match_expression(
                        g,
                        element,
                        element_value,
                        next_match_block,
                        no_match_block,
                    ));
                }
            }
            IRMatchExpression::ShorthandList(_, elements) => {
                // match_value: *{element: T, next: *List<T>}
                let list_pointer_value = match_value.into_pointer_value();
                let list_ptr_int = self.builder.build_ptr_to_int(
                    list_pointer_value,
                    self.llvm_context.i64_type(),
                    &g.var(),
                );
                let element_is_null = self.builder.build_int_compare(
                    IntPredicate::EQ,
                    list_ptr_int,
                    self.llvm_context.i64_type().const_int(0, false),
                    &g.var(),
                );

                let element_match_blocks: Vec<(BasicBlock, BasicBlock)> = elements
                    .iter()
                    .map(|_| {
                        (
                            self.llvm_context
                                .append_basic_block(match_block.get_parent().unwrap(), &g.var()),
                            self.llvm_context
                                .append_basic_block(match_block.get_parent().unwrap(), &g.var()),
                        )
                    })
                    .collect();

                if elements.len() == 0 {
                    self.builder.build_conditional_branch(
                        element_is_null,
                        match_block,
                        no_match_block,
                    );
                } else {
                    self.builder.build_conditional_branch(
                        element_is_null,
                        no_match_block,
                        element_match_blocks.get(0).unwrap().0.clone(),
                    );
                }

                if elements.len() > 0 {
                    let mut current_node_pointer = list_pointer_value;
                    for bla in elements
                        .iter()
                        .enumerate()
                        .zip(element_match_blocks.iter())
                        .zip_longest(element_match_blocks.iter().skip(1))
                    {
                        let (
                            (match_index, match_expression),
                            (current_value_block, current_next_node_block),
                            match_block,
                        ) = match bla {
                            EitherOrBoth::Both((me, cb), (mb, _)) => (me, cb.clone(), mb.clone()),
                            EitherOrBoth::Left((me, cb)) => (me, cb.clone(), match_block),
                            EitherOrBoth::Right(_) => panic!(""),
                        };
                        self.builder.position_at_end(current_value_block.clone());
                        let element_value_pointer = self
                            .builder
                            .build_struct_gep(current_node_pointer, 0, &g.var())
                            .unwrap();
                        let element_value =
                            self.builder.build_load(element_value_pointer, &g.var());
                        value_information.extend(self.generate_match_expression(
                            g,
                            match_expression,
                            element_value,
                            current_next_node_block,
                            no_match_block,
                        ));

                        self.builder.position_at_end(current_next_node_block);
                        let next_node_pointer = self
                            .builder
                            .build_struct_gep(current_node_pointer, 1, &g.var())
                            .unwrap();
                        let next_node_pointer_value = self
                            .builder
                            .build_load(next_node_pointer, &g.var())
                            .into_pointer_value();
                        let next_pointer_int = self.builder.build_ptr_to_int(
                            next_node_pointer_value,
                            self.llvm_context.i64_type(),
                            &g.var(),
                        );
                        let next_is_null = self.builder.build_int_compare(
                            IntPredicate::EQ,
                            next_pointer_int,
                            self.llvm_context.i64_type().const_int(0, false),
                            &g.var(),
                        );

                        if match_index + 1 == elements.len() {
                            self.builder.build_conditional_branch(
                                next_is_null,
                                match_block,
                                no_match_block,
                            );
                        } else {
                            self.builder.build_conditional_branch(
                                next_is_null,
                                no_match_block,
                                match_block,
                            );
                        }

                        current_node_pointer = next_node_pointer_value;
                    }
                }
            }
            IRMatchExpression::LonghandList(_, h, t) => {
                let match_head_block = self
                    .llvm_context
                    .append_basic_block(match_block.get_parent().unwrap(), &g.var());
                let match_tail_block = self
                    .llvm_context
                    .append_basic_block(match_block.get_parent().unwrap(), &g.var());

                // match_value: *{element: T, next: *List<T>}
                let list_pointer_value = match_value.into_pointer_value();
                let list_ptr_int = self.builder.build_ptr_to_int(
                    list_pointer_value,
                    self.llvm_context.i64_type(),
                    &g.var(),
                );
                let list_pointer_is_null = self.builder.build_int_compare(
                    IntPredicate::EQ,
                    list_ptr_int,
                    self.llvm_context.i64_type().const_int(0, false),
                    &g.var(),
                );

                self.builder.build_conditional_branch(
                    list_pointer_is_null,
                    no_match_block,
                    match_head_block,
                );

                self.builder.position_at_end(match_head_block);
                let head_value_pointer = self
                    .builder
                    .build_struct_gep(list_pointer_value, 0, &g.var())
                    .unwrap();
                let head_value = self.builder.build_load(head_value_pointer, &g.var());
                value_information.extend(self.generate_match_expression(
                    g,
                    h,
                    head_value,
                    match_tail_block,
                    no_match_block,
                ));

                self.builder.position_at_end(match_tail_block);
                let next_element_pointer_pointer = self
                    .builder
                    .build_struct_gep(list_pointer_value, 1, &g.var())
                    .unwrap();
                let next_element_pointer = self
                    .builder
                    .build_load(next_element_pointer_pointer, &g.var());
                value_information.extend(self.generate_match_expression(
                    g,
                    t,
                    next_element_pointer.as_basic_value_enum(),
                    match_block,
                    no_match_block,
                ))
            }
            IRMatchExpression::Wildcard(_) => {
                self.builder.build_unconditional_branch(match_block);
            }
            IRMatchExpression::ADT(_, adt_constructor_name, arguments) => {
                let mut bla = adt_constructor_name.split(MONOMORPHIC_PREFIX);
                let mut blie = bla.next().unwrap().split(ADT_SEPARATOR);
                let adt_name = blie.next().unwrap();
                let constructor_name = blie.next().unwrap();
                let type_str = bla.next().unwrap();

                let adt_definition = self.adts.get(&adt_name.to_string()).unwrap();
                let constructor_index = adt_definition
                    .base
                    .constructors
                    .iter()
                    .enumerate()
                    .filter(|(_, c)| &c.name == &Rc::new(constructor_name.to_string()))
                    .map(|(i, _)| i)
                    .next()
                    .unwrap();

                // 1. Check whether the tag field of the matched ADT value struct corresponds with the match
                //    expression.
                let tag_pointer = self
                    .builder
                    .build_struct_gep(match_value.into_pointer_value(), 0 as u32, &g.var())
                    .unwrap();
                let tag_value = self.builder.build_load(tag_pointer, &g.var());
                let tag_matches_value = self.builder.build_int_compare(
                    IntPredicate::EQ,
                    tag_value.into_int_value(),
                    self.llvm_context
                        .i8_type()
                        .const_int(constructor_index as u64, true),
                    &g.var(),
                );

                if arguments.len() == 0 {
                    self.builder.build_conditional_branch(
                        tag_matches_value,
                        match_block,
                        no_match_block,
                    );
                } else {
                    let argument_preparation_block = self
                        .llvm_context
                        .append_basic_block(match_block.get_parent().unwrap(), &g.var());
                    self.builder.build_conditional_branch(
                        tag_matches_value,
                        argument_preparation_block,
                        no_match_block,
                    );

                    self.builder.position_at_end(argument_preparation_block);
                    let value_pointer = self
                        .builder
                        .build_struct_gep(match_value.into_pointer_value(), 1 as u32, &g.var())
                        .unwrap();

                    let struct_name = format!(
                        "{}{}{}__{}",
                        adt_name, MONOMORPHIC_PREFIX, type_str, constructor_name
                    );
                    let value_struct_pointer_type = self
                        .module
                        .get_struct_type(&struct_name)
                        .unwrap()
                        .ptr_type(AddressSpace::Generic);
                    let value_struct_pointer = value_pointer.const_cast(value_struct_pointer_type);

                    let argument_blocks: Vec<BasicBlock> = arguments
                        .iter()
                        .map(|_| {
                            self.llvm_context
                                .append_basic_block(match_block.get_parent().unwrap(), &g.var())
                        })
                        .collect();
                    self.builder
                        .build_unconditional_branch(argument_blocks.get(0).unwrap().clone());

                    for (i, (argument, block)) in
                        arguments.iter().zip(argument_blocks.iter()).enumerate()
                    {
                        self.builder.position_at_end(block.clone());

                        let argument_value_pointer = self
                            .builder
                            .build_struct_gep(value_struct_pointer, i as u32, &g.var())
                            .unwrap();
                        let argument_value =
                            self.builder.build_load(argument_value_pointer, &g.var());

                        let next_match_block = argument_blocks
                            .get(i + 1)
                            .cloned()
                            .unwrap_or_else(|| match_block);

                        value_information.extend(self.generate_match_expression(
                            g,
                            argument,
                            argument_value,
                            next_match_block,
                            no_match_block,
                        ));
                    }
                }
            }
            IRMatchExpression::Record(_, record_name, fields) => {
                let record_definition = self
                    .records
                    .get(
                        &record_name
                            .split(MONOMORPHIC_PREFIX)
                            .next()
                            .unwrap()
                            .to_string(),
                    )
                    .unwrap();
                for field in fields {
                    let index = record_definition
                        .base
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
        expression: &Rc<IRExpression>,
        value_information: &HashMap<Rc<String>, BasicValueEnum<'a>>,
    ) -> BasicValueEnum<'a> {
        match expression.borrow() {
            IRExpression::BoolLiteral(_, b) => self
                .llvm_context
                .bool_type()
                .const_int(if *b { 1 } else { 0 }, false)
                .as_basic_value_enum(),
            IRExpression::StringLiteral(_, string) => {
                let llvm_string = self.builder.build_global_string_ptr(&string, &g.global());
                llvm_string.as_basic_value_enum()
            }
            IRExpression::CharacterLiteral(_, character) => {
                let mut b = [0; 4];
                let str = character.encode_utf8(&mut b);
                let llvm_string = self.builder.build_global_string_ptr(str, &g.global());
                llvm_string.as_basic_value_enum()
            }
            IRExpression::IntegerLiteral(_, i) => self
                .llvm_context
                .i64_type()
                .const_int(*i as u64, true)
                .as_basic_value_enum(),
            IRExpression::FloatLiteral(_, f) => self
                .llvm_context
                .f64_type()
                .const_float(*f)
                .as_basic_value_enum(),
            IRExpression::TupleLiteral(_, elements) => {
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
            IRExpression::EmptyListLiteral(_, list_type) => {
                let element_type = match list_type.borrow() {
                    IRType::List(element_type) => element_type,
                    _ => unreachable!("List literal without list type"),
                };
                self.retrieve_list_type(element_type)
                    .const_null()
                    .as_basic_value_enum()
            }
            IRExpression::ShorthandListLiteral(_, list_type, arguments) => {
                let element_type = match list_type.borrow() {
                    IRType::List(element_type) => element_type,
                    _ => unreachable!("List literal without list type"),
                };

                let list_pointer_type = self.retrieve_list_type(element_type);
                let list_struct_type = list_pointer_type.get_element_type().into_struct_type();

                let mut first_node_pointer: Option<PointerValue> = None;
                let mut previous_node_pointer: Option<PointerValue> = None;
                for argument in arguments {
                    let argument_value = self.generate_expression(g, argument, value_information);
                    let list_node_struct_pointer = self
                        .builder
                        .build_call(
                            self.module.get_function("malloc").unwrap(),
                            &[list_struct_type.size_of().unwrap().as_basic_value_enum()],
                            &g.var(),
                        )
                        .try_as_basic_value()
                        .left()
                        .unwrap()
                        .into_pointer_value()
                        .const_cast(list_struct_type.ptr_type(AddressSpace::Generic));
                    let list_node_value_pointer = self
                        .builder
                        .build_struct_gep(list_node_struct_pointer, 0, &g.var())
                        .unwrap();
                    self.builder
                        .build_store(list_node_value_pointer, argument_value);

                    if let None = first_node_pointer {
                        first_node_pointer = Some(list_node_struct_pointer);
                    }

                    if let Some(previous_node_pointer) = previous_node_pointer {
                        let previous_node_next_pointer = self
                            .builder
                            .build_struct_gep(previous_node_pointer, 1, &g.var())
                            .unwrap();
                        self.builder.build_store(
                            previous_node_next_pointer,
                            list_node_struct_pointer.as_basic_value_enum(),
                        );
                    }

                    previous_node_pointer = Some(list_node_struct_pointer)
                }

                first_node_pointer.unwrap().as_basic_value_enum()
            }
            IRExpression::LonghandListLiteral(
                _,
                list_type,
                head_expression,
                tail_list_expression,
            ) => {
                let element_type = match list_type.borrow() {
                    IRType::List(element_type) => element_type,
                    _ => unreachable!("List literal without list type"),
                };

                let list_pointer_type = self.retrieve_list_type(element_type);
                let list_struct_type = list_pointer_type.get_element_type().into_struct_type();

                let head_value = self.generate_expression(g, head_expression, value_information);
                let tail_list_value =
                    self.generate_expression(g, tail_list_expression, value_information);
                let list_node_struct_pointer = self
                    .builder
                    .build_call(
                        self.module.get_function("malloc").unwrap(),
                        &[list_struct_type.size_of().unwrap().as_basic_value_enum()],
                        &g.var(),
                    )
                    .try_as_basic_value()
                    .left()
                    .unwrap()
                    .into_pointer_value()
                    .const_cast(list_struct_type.ptr_type(AddressSpace::Generic));

                let value_pointer = self
                    .builder
                    .build_struct_gep(list_node_struct_pointer, 0, &g.var())
                    .unwrap();
                self.builder.build_store(value_pointer, head_value);
                let next_pointer = self
                    .builder
                    .build_struct_gep(list_node_struct_pointer, 1, &g.var())
                    .unwrap();
                self.builder.build_store(next_pointer, tail_list_value);

                list_node_struct_pointer.as_basic_value_enum()
            }
            IRExpression::ADTTypeConstructor(_, adt_type, name, arguments) => {
                let adt_name = match adt_type.borrow() {
                    IRType::UserType(name) => name,
                    _ => unreachable!("ADTTypeConstuctor without Type::UserType type"),
                };
                let adt_definition = self
                    .adts
                    .get(
                        &adt_name
                            .split(MONOMORPHIC_PREFIX)
                            .next()
                            .unwrap()
                            .to_string(),
                    )
                    .unwrap();
                let adt_llvm_type = self.module.get_struct_type(adt_name).unwrap();

                let adt_value_pointer = self
                    .builder
                    .build_call(
                        self.module.get_function("malloc").unwrap(),
                        &[adt_llvm_type.size_of().unwrap().as_basic_value_enum()],
                        &g.var(),
                    )
                    .try_as_basic_value()
                    .left()
                    .unwrap()
                    .into_pointer_value()
                    .const_cast(adt_llvm_type.ptr_type(AddressSpace::Generic));

                let adt_constructor_llvm_type = self
                    .module
                    .get_struct_type(&format!("{}__{}", adt_name, name))
                    .unwrap();
                let constructor_index = adt_definition
                    .base
                    .constructors
                    .iter()
                    .enumerate()
                    .filter(|(_, c)| &c.name == name)
                    .map(|(i, _)| i)
                    .next()
                    .unwrap();

                let tag_pointer = self
                    .builder
                    .build_struct_gep(adt_value_pointer, 0 as u32, &g.var())
                    .unwrap();
                self.builder.build_store(
                    tag_pointer,
                    self.llvm_context
                        .i8_type()
                        .const_int(constructor_index as u64, false),
                );

                let adt_constructor_value_pointer = self
                    .builder
                    .build_struct_gep(adt_value_pointer, 1 as u32, &g.var())
                    .unwrap()
                    .const_cast(adt_constructor_llvm_type.ptr_type(AddressSpace::Generic));

                for (i, argument_expression) in arguments.iter().enumerate() {
                    let v = self.generate_expression(g, argument_expression, value_information);
                    let field_ptr = self
                        .builder
                        .build_struct_gep(adt_constructor_value_pointer, i as u32, &g.var())
                        .unwrap();
                    self.builder.build_store(field_ptr, v);
                }
                adt_value_pointer.as_basic_value_enum()
            }

            IRExpression::Record(_, _, c, d) => {
                let record_definition = self
                    .records
                    .get(&c.split(MONOMORPHIC_PREFIX).next().unwrap().to_string())
                    .unwrap();
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

                for (i, (_, (_, field_expression))) in record_definition
                    .base
                    .fields
                    .iter()
                    .zip(d.iter())
                    .enumerate()
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
            IRExpression::Case(_, e, rules, result_type) => {
                let ev = self.generate_expression(g, e, value_information);
                let current_function = self
                    .builder
                    .get_insert_block()
                    .unwrap()
                    .get_parent()
                    .unwrap();
                let rule_blocks: Vec<(BasicBlock, BasicBlock)> = rules
                    .iter()
                    .map(|_| {
                        let match_block = self
                            .llvm_context
                            .append_basic_block(current_function, &g.var());
                        let result_block = self
                            .llvm_context
                            .append_basic_block(current_function, &g.var());
                        (match_block, result_block)
                    })
                    .collect();
                let current_block = self.builder.get_insert_block().unwrap();
                let no_match_block = self
                    .llvm_context
                    .append_basic_block(current_function, &g.var());
                let case_result_block = self
                    .llvm_context
                    .append_basic_block(current_function, &g.var());
                self.builder.position_at_end(no_match_block);
                self.generate_abort(g, String::from("No matching case rule"), 1);
                self.builder.position_at_end(current_block);

                let result_variable = self.builder.build_alloca(
                    self.to_llvm_type(result_type).as_basic_type_enum(),
                    &g.var(),
                );

                self.builder
                    .build_unconditional_branch(rule_blocks.first().unwrap().0.clone());

                for bla in rules
                    .iter()
                    .zip(rule_blocks.iter())
                    .zip_longest(rule_blocks.iter().skip(1))
                {
                    let (rule, match_block, result_block, next_match_block) = match bla {
                        EitherOrBoth::Both(
                            (rule, (match_block, result_block)),
                            (next_match_block, _),
                        ) => (
                            rule,
                            match_block.clone(),
                            result_block.clone(),
                            next_match_block.clone(),
                        ),
                        EitherOrBoth::Left((rule, (match_block, result_block))) => (
                            rule,
                            match_block.clone(),
                            result_block.clone(),
                            no_match_block,
                        ),
                        EitherOrBoth::Right(_) => unreachable!(),
                    };
                    self.builder.position_at_end(match_block);
                    let match_value_information = self.generate_match_expression(
                        g,
                        &rule.case_rule,
                        ev,
                        result_block,
                        next_match_block,
                    );

                    self.builder.position_at_end(result_block);
                    let mut combined_value_information = HashMap::new();
                    combined_value_information.extend(
                        value_information
                            .iter()
                            .map(|(l, r)| (l.clone(), r.clone()))
                            .collect::<HashMap<Rc<String>, BasicValueEnum>>(),
                    );
                    combined_value_information.extend(match_value_information);

                    let value =
                        self.generate_expression(g, &rule.result_rule, &combined_value_information);
                    self.builder.build_store(result_variable, value);
                    self.builder.build_unconditional_branch(case_result_block);
                }
                self.builder.position_at_end(case_result_block);
                let result = self.builder.build_load(result_variable, &g.var());
                result
            }
            IRExpression::Call(_, _, b, arguments) => {
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
            IRExpression::Variable(_, v) => value_information.get(v).unwrap().clone(),
            IRExpression::Negation(_, e) => {
                let ev = self.generate_expression(g, e, value_information);
                self.builder
                    .build_xor(
                        ev.into_int_value(),
                        self.llvm_context.bool_type().const_int(1, false),
                        &g.var(),
                    )
                    .as_basic_value_enum()
            }
            IRExpression::Minus(_, e) => {
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
            IRExpression::Times(_, l, r) => {
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
            IRExpression::Divide(_, l, r) => {
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
            IRExpression::Modulo(_, l, r) => {
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
            IRExpression::Add(_, l, r) => {
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
            IRExpression::Subtract(_, l, r) => {
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
            IRExpression::ShiftLeft(_, l, r) => {
                let el = self.generate_expression(g, l, value_information);
                let er = self.generate_expression(g, r, value_information);
                self.builder
                    .build_left_shift(el.into_int_value(), er.into_int_value(), &g.var())
                    .as_basic_value_enum()
            }
            IRExpression::ShiftRight(_, l, r) => {
                let el = self.generate_expression(g, l, value_information);
                let er = self.generate_expression(g, r, value_information);
                self.builder
                    .build_right_shift(el.into_int_value(), er.into_int_value(), false, &g.var())
                    .as_basic_value_enum()
            }
            IRExpression::Greater(_, l, r) => {
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
            IRExpression::Greq(_, l, r) => {
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
            IRExpression::Leq(_, l, r) => {
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
            IRExpression::Lesser(_, l, r) => {
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
            IRExpression::Eq(_, l, r) => {
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
            IRExpression::Neq(_, l, r) => {
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
            IRExpression::And(_, l, r) => {
                let el = self.generate_expression(g, l, value_information);
                let er = self.generate_expression(g, r, value_information);
                self.builder
                    .build_and(el.into_int_value(), er.into_int_value(), &g.var())
                    .as_basic_value_enum()
            }
            IRExpression::Or(_, l, r) => {
                let el = self.generate_expression(g, l, value_information);
                let er = self.generate_expression(g, r, value_information);
                self.builder
                    .build_or(el.into_int_value(), er.into_int_value(), &g.var())
                    .as_basic_value_enum()
            }
            IRExpression::RecordFieldAccess(_, _, record_name, l, r) => {
                let record_value = self.generate_expression(g, l, value_information);
                let field_name = match r.borrow() {
                    IRExpression::Variable(_, field) => field,
                    _ => unreachable!(),
                };
                let record_definition = self
                    .records
                    .get(
                        &record_name
                            .split(MONOMORPHIC_PREFIX)
                            .next()
                            .unwrap()
                            .to_string(),
                    )
                    .unwrap();
                let record_field_index = record_definition
                    .base
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
        }
    }

    fn write_module_object(
        &self,
        object_file_path: &Path,
        compiler_options: &CompilerOptions,
    ) -> Result<(), String> {
        Target::initialize_x86(&InitializationConfig::default());

        if compiler_options.emit_llvm_ir {
            let llvm_ir_file_path = object_file_path.with_extension("ll");
            let llvm_ir_string = self.module.print_to_string();
            let llvm_ir_bytes = llvm_ir_string.to_bytes();
            match File::create(llvm_ir_file_path.clone()) {
                Ok(mut file) => {
                    file.write_all(llvm_ir_bytes).map_err(|e| {
                        format!(
                            "Unable to write to LLVM IR file {}: {}",
                            llvm_ir_file_path.display(),
                            e
                        )
                    })?;
                    let bytes_string = format_size(llvm_ir_bytes.len());
                    println!(
                        "Wrote LLVM IR to {} ({})",
                        llvm_ir_file_path.display(),
                        bytes_string
                    );
                }
                Err(e) => eprintln!(
                    "Unable to create LLVM IR file {}: {}",
                    llvm_ir_file_path.display(),
                    e
                ),
            }
        }

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

        target_machine
            .write_to_file(&self.module, FileType::Object, object_file_path)
            .map_err(|e| {
                format!(
                    "Error writing to object file {}: {}",
                    object_file_path.display(),
                    e.to_string()
                )
            })?;

        let object_file = File::open(object_file_path).unwrap();
        println!(
            "Wrote to object file {} ({})",
            object_file_path.display(),
            format_size(object_file.metadata().unwrap().len() as usize)
        );
        Ok(())
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

    fn generate_print(&self, g: &mut VarGenerator, type_to_print: &Rc<IRType>) -> FunctionValue {
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
        type_to_print: &Rc<IRType>,
        value: BasicValueEnum<'a>,
    ) {
        let printf = self.module.get_function("printf").unwrap();
        let print_bool = self.module.get_function("print_bool").unwrap();
        match type_to_print.borrow() {
            IRType::Bool => {
                self.builder.build_call(print_bool, &[value], &g.var());
            }

            IRType::Char => {
                self.builder.build_call(
                    printf,
                    &[
                        self.builder
                            .build_global_string_ptr("'%s'", "char_format_string")
                            .as_basic_value_enum(),
                        value,
                    ],
                    &g.var(),
                );
            }
            IRType::String => {
                self.builder.build_call(
                    printf,
                    &[
                        self.builder
                            .build_global_string_ptr("\"%s\"", "string_format_string")
                            .as_basic_value_enum(),
                        value,
                    ],
                    &g.var(),
                );
            }
            IRType::Int => {
                self.builder.build_call(
                    printf,
                    &[
                        self.builder
                            .build_global_string_ptr("%d", "int_format_string")
                            .as_basic_value_enum(),
                        value,
                    ],
                    &g.var(),
                );
            }
            IRType::Float => {
                self.builder.build_call(
                    printf,
                    &[
                        self.builder
                            .build_global_string_ptr("%f", "float_format_string")
                            .as_basic_value_enum(),
                        value,
                    ],
                    &g.var(),
                );
            }
            IRType::UserType(name) => {
                let base_name = name.split(MONOMORPHIC_PREFIX).next().unwrap().to_string();
                if self.records.contains_key(&base_name) {
                    let print_string = self
                        .builder
                        .build_global_string_ptr("%s", "print_string")
                        .as_basic_value_enum();
                    let record_prefix = self
                        .builder
                        .build_global_string_ptr(&format!("{{{}|", sanitize_name(name)), &g.var())
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

                    let record_definition = self
                        .records
                        .get(&name.split(MONOMORPHIC_PREFIX).next().unwrap().to_string())
                        .unwrap();
                    let record_instance_definition = record_definition.instances.get(name).unwrap();
                    let struct_value = value.into_pointer_value();
                    for (i, (field_name, field_type)) in
                        record_instance_definition.fields.iter().enumerate()
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
                        self.generate_print_code(g, field_type, field_value);
                        if i < record_instance_definition.fields.len() - 1 {
                            self.builder
                                .build_call(printf, &[record_field_separator], &g.var());
                        }
                    }
                    self.builder.build_call(printf, &[record_suffix], &g.var());
                } else if self.adts.contains_key(&base_name) {
                    // TODO: Extend printing ADTs with their respective constructors.
                    let adt_name_string = self
                        .builder
                        .build_global_string_ptr(
                            name.split(MONOMORPHIC_PREFIX).next().unwrap(),
                            &g.var(),
                        )
                        .as_basic_value_enum();
                    self.builder
                        .build_call(printf, &[adt_name_string], &g.var());
                } else {
                    unreachable!("Printing ADTs")
                }
            }
            IRType::Tuple(elements) => {
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
                    self.generate_print_code(g, element_type, element_value);
                    if i < elements.len() - 1 {
                        self.builder
                            .build_call(printf, &[tuple_separator], &g.var());
                    }
                }
                self.builder.build_call(printf, &[tuple_suffix], &g.var());
            }
            IRType::List(element_type) => {
                let list_open = self
                    .builder
                    .build_global_string_ptr("[", "list_open")
                    .as_basic_value_enum();
                self.builder.build_call(printf, &[list_open], &g.var());

                let print_list_function = self.generate_print_list(g, element_type);
                self.builder
                    .build_call(print_list_function, &[value], &g.var());

                let list_close = self
                    .builder
                    .build_global_string_ptr("]", "list_close")
                    .as_basic_value_enum();
                self.builder.build_call(printf, &[list_close], &g.var());
            }
            IRType::Function(_, _) => unreachable!("Printing function type"),
        };
    }

    fn generate_print_list(
        &self,
        g: &mut VarGenerator,
        element_type: &Rc<IRType>,
    ) -> FunctionValue {
        let current_block = self.builder.get_insert_block().unwrap();
        let printf = self.module.get_function("printf").unwrap();

        let type_hash = hash_ir_type(element_type);
        let print_list_function = self.module.add_function(
            &format!("__print__list__{}", type_hash),
            self.llvm_context.void_type().fn_type(
                &[self
                    .to_llvm_type(&Rc::new(IRType::List(Rc::clone(element_type))))
                    .as_basic_type_enum()],
                false,
            ),
            Some(Linkage::External),
        );

        let print_list_null_block = self
            .llvm_context
            .append_basic_block(print_list_function, "Null");
        let print_list_value_block = self
            .llvm_context
            .append_basic_block(print_list_function, "Entry");
        let print_list_next_block = self
            .llvm_context
            .append_basic_block(print_list_function, "Next");
        let print_list_end_block = self
            .llvm_context
            .append_basic_block(print_list_function, "End");
        self.builder.position_at_end(print_list_null_block);

        let argument_pointer = print_list_function
            .get_nth_param(0)
            .unwrap()
            .into_pointer_value();
        let argument_pointer_int =
            self.builder
                .build_ptr_to_int(argument_pointer, self.llvm_context.i64_type(), &g.var());
        let argument_is_null = self.builder.build_int_compare(
            IntPredicate::EQ,
            argument_pointer_int,
            self.llvm_context.i64_type().const_int(0, false),
            &g.var(),
        );

        self.builder.build_conditional_branch(
            argument_is_null,
            print_list_end_block,
            print_list_value_block,
        );
        self.builder.position_at_end(print_list_value_block);

        let current_value_pointer = self
            .builder
            .build_struct_gep(argument_pointer, 0, &g.var())
            .unwrap();
        let current_value = self.builder.build_load(current_value_pointer, &g.var());
        self.generate_print_code(g, element_type, current_value);

        let next_pointer_pointer = self
            .builder
            .build_struct_gep(argument_pointer, 1, &g.var())
            .unwrap();
        let next_pointer = self.builder.build_load(next_pointer_pointer, &g.var());

        let next_pointer_int = self.builder.build_ptr_to_int(
            next_pointer.into_pointer_value(),
            self.llvm_context.i64_type(),
            &g.var(),
        );

        let has_next = self.builder.build_int_compare(
            IntPredicate::NE,
            next_pointer_int,
            self.llvm_context.i64_type().const_int(0, false),
            &g.var(),
        );

        self.builder.build_conditional_branch(
            has_next,
            print_list_next_block,
            print_list_end_block,
        );

        self.builder.position_at_end(print_list_end_block);
        self.builder.build_return(None);

        self.builder.position_at_end(print_list_next_block);
        let list_separator = self
            .builder
            .build_global_string_ptr(", ", "list_separator")
            .as_basic_value_enum();
        self.builder.build_call(printf, &[list_separator], &g.var());
        self.builder
            .build_call(print_list_function, &[next_pointer], &g.var());
        self.builder.build_return(None);

        self.builder.position_at_end(current_block);
        print_list_function
    }

    fn llvm_type_size(&self, loz_type: &Rc<IRType>) -> u32 {
        match loz_type.borrow() {
            IRType::Bool => 8,
            IRType::Char => 64,
            IRType::String => 64,
            IRType::Int => 64,
            IRType::Float => 64,
            IRType::UserType(_) => 64,
            IRType::Tuple(_) => 64,
            IRType::List(_) => 64,
            IRType::Function(_, _) => unreachable!("Function type in generator"),
        }
    }

    fn to_llvm_type(&self, loz_type: &Rc<IRType>) -> Box<dyn BasicType<'a> + 'a> {
        match loz_type.borrow() {
            IRType::Bool => Box::new(self.llvm_context.bool_type().as_basic_type_enum()),
            IRType::Int => Box::new(self.llvm_context.i64_type().as_basic_type_enum()),
            IRType::Float => Box::new(self.llvm_context.f64_type().as_basic_type_enum()),
            IRType::Char => Box::new(
                self.llvm_context
                    .i8_type()
                    .ptr_type(AddressSpace::Generic)
                    .as_basic_type_enum(),
            ),
            IRType::String => Box::new(
                self.llvm_context
                    .i8_type()
                    .ptr_type(AddressSpace::Generic)
                    .as_basic_type_enum(),
            ),
            IRType::UserType(name) => Box::new(
                self.module
                    .get_struct_type(name)
                    .expect(&format!("Struct type {} not found", name))
                    .ptr_type(AddressSpace::Generic)
                    .as_basic_type_enum(),
            ),
            IRType::Tuple(els) => Box::new(
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
            IRType::List(element_type) => {
                Box::new(self.retrieve_list_type(element_type).as_basic_type_enum())
            }
            IRType::Function(_, _) => unreachable!("Function type"),
        }
    }

    fn retrieve_list_type(&self, element_type: &Rc<IRType>) -> PointerType<'a> {
        let list_struct_name = format!("__list__{}", hash_ir_type(element_type));
        if let Some(bla) = self.module.get_struct_type(&list_struct_name) {
            return bla.ptr_type(AddressSpace::Generic);
        } else {
            let list_struct_type = self.llvm_context.opaque_struct_type(&list_struct_name);
            let llvm_element_type = self.to_llvm_type(element_type).as_basic_type_enum();
            list_struct_type.set_body(
                &[
                    llvm_element_type,
                    list_struct_type
                        .ptr_type(AddressSpace::Generic)
                        .as_basic_type_enum(),
                ],
                false,
            );
            return list_struct_type.ptr_type(AddressSpace::Generic);
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

fn format_size(size: usize) -> String {
    match NumberPrefix::binary(size as f64) {
        NumberPrefix::Standalone(bytes) => format!("{} bytes", bytes),
        NumberPrefix::Prefixed(prefix, n) => format!("{:.1} {}B", n, prefix),
    }
}

fn hash_ir_type(t: &Rc<IRType>) -> String {
    fn hash<T: Hash>(t: &Rc<T>) -> String {
        let mut s = DefaultHasher::new();
        t.hash(&mut s);
        format!("{}", s.finish())
    }

    fn replace_variable_types(t: &Rc<IRType>) -> Rc<IRType> {
        match t.borrow() {
            IRType::Bool => Rc::new(IRType::Bool),
            IRType::Char => Rc::new(IRType::Char),
            IRType::String => Rc::new(IRType::String),
            IRType::Int => Rc::new(IRType::Int),
            IRType::Float => Rc::new(IRType::Float),
            IRType::UserType(name) => Rc::new(IRType::UserType(Rc::clone(name))),

            IRType::Tuple(element_types) => Rc::new(IRType::Tuple(
                element_types
                    .iter()
                    .map(|et| replace_variable_types(et))
                    .collect(),
            )),
            IRType::List(list_type) => Rc::new(IRType::List(replace_variable_types(list_type))),
            IRType::Function(argument_types, result_type) => Rc::new(IRType::Function(
                argument_types
                    .iter()
                    .map(|at| replace_variable_types(at))
                    .collect(),
                replace_variable_types(result_type),
            )),
        }
    }

    return hash(&replace_variable_types(t));
}
