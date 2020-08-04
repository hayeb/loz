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
use std::io::Error;
use std::path::Path;
use std::process::{Command, Output};
use std::rc::Rc;

use inkwell::{AddressSpace, OptimizationLevel};
use inkwell::builder::Builder;
use inkwell::context::Context;
use inkwell::execution_engine::{ExecutionEngine, JitFunction};
use inkwell::module::{Linkage, Module};
use inkwell::support::LLVMString;
use inkwell::targets::{CodeModel, FileType, InitializationConfig, RelocMode, Target, TargetMachine, TargetTriple};
use inkwell::types::{BasicType, BasicTypeEnum};
use inkwell::values::IntValue;

use crate::{ADTDefinition, RecordDefinition, Type};
use crate::ast::{FunctionDefinition, FunctionRule, FunctionBody, MatchExpression};
use crate::rewriter::RuntimeModule;

pub fn generate(runtime_module: Rc<RuntimeModule>, output_directory: &Path) -> Result<(), String> {
    let context = Context::create();
    let state = GeneratorState::new(&context, runtime_module);

    // Generate the ${MODULE_NAME}.o object file
    state.generate_module()?;
    let mut object_path = output_directory.to_path_buf();
    object_path.push(format!("{}.o", &runtime_module.name));
    state.write_module_object(object_path.as_path())?;

    // Generate the ${MODULE_NAME} executable
    let mut executable_path = output_directory.to_path_buf();
    executable_path.push(runtime_module.name.to_string());
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
        .output() {
        Ok(_) => Ok(()),
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

impl<'a> GeneratorState<'a> {
    fn new(context: &'a Context, runtime_module: Rc<RuntimeModule>) -> Self {
        let module = context.create_module(&runtime_module.name);
        let builder = context.create_builder();

        GeneratorState {
            functions: runtime_module.functions.iter().map(|(n, d)| (Rc::clone(n), Rc::clone(d))).collect(),
            function_name_to_type: runtime_module.functions.iter().map(|(n, d)| (Rc::clone(n), Rc::clone(&d.function_type.as_ref().unwrap().enclosed_type))).collect(),
            llvm_context: context,
            module,
            builder,

            records: runtime_module.records.clone(),
            adts: runtime_module.adts.clone(),
        }
    }

    fn generate_module(&self, ) {
        self.generate_records();
        for fd in self.functions.values(){
            self.generate_function(fd)
        }
    }

    fn generate_records(&self) {
        for r in self.records.values() {
            let struct_type = self.context.struct_type(r.fields.iter().map(|(n, t)| to_llvm_type(&context, t).as_basic_type_enum()).collect::<Vec<BasicTypeEnum>>().as_slice(), false);
            self.module.add_global(struct_type, None, &r.name);
        }
    }

    fn generate_adts(&self) {
        unimplemented!("Generating ADT types")
    }

    fn generate_function(&self, function_definition: &Rc<FunctionDefinition>) {
        let (return_type, arguments) = match self.function_name_to_type.get(&function_definition.name).unwrap().borrow() {
            Type::Function(args, return_type) => (return_type, args),
            t => (t, vec![])
        };
        let llvm_arguments = arguments.iter().map(|a| to_llvm_type(self.llvm_context, a)).collect::<Vec<BasicTypeEnum>>().as_slice();
        let function_type = to_llvm_type(self.llvm_context, return_type).fn_type(llvm_arguments, false);
        let llvm_function = self.module.add_function(&function_definition.name, function_type, None);
        let entry_block = self.llvm_context.append_basic_block(llvm_function, "entry");
        self.builder.position_at_end(entry_block);

        for (body_index, b) in function_definition.function_bodies.iter().enumerate() {
            self.llvm_context.append_basic_block(llvm_function, &format!("Body_{}_match", body_index));
            for (match_index, _) in b.match_expressions.iter().enumerate() {
                self.llvm_context.append_basic_block(llvm_function, &format!("Body_{}_match_{}", body_index, match_index))
            }
        }
        self.llvm_context.append_basic_block(llvm_function, "MatchFault");

        for (n, function_body) in function_definition.function_bodies.iter().enumerate() {
            let body_name = format!("Body_{}_match", n);
            let basic_block = llvm_function.get_basic_blocks().into_iter()
                .filter(|b| b.get_name().to_str().unwrap() == &body_name)
                .next()
                .unwrap();

            self.builder.position_at_end(basic_block);

            for (match_index, match_expression) in function_body.match_expressions.iter().enumerate() {
                llvm_function.get

            }

            // TODO: Generate match expression


            self.generate_function_rule()
        }
    }

    fn generate_function_body(&self, function_body: &Rc<FunctionBody>) {

    }

    fn generate_function_rule(&self, function_rule: &Rc<FunctionRule>) {

    }

    fn generate_match_Expression(&self, me: &Rc<MatchExpression>, )

    fn write_module_object(&self, object_file: &Path) -> Result<(), String> {
        Target::initialize_x86(&InitializationConfig::default());

        let opt = OptimizationLevel::Default;
        let reloc = RelocMode::Default;
        let model = CodeModel::Default;
        let target = Target::from_name("x86-64").unwrap();
        let target_machine = target.create_target_machine(
            &TargetTriple::create("x86_64-pc-linux-gnu"),
            "x86-64",
            "+avx2",
            opt,
            reloc,
            model,
        )
            .unwrap();


        target_machine.write_to_file(&module, FileType::Object, object_path.as_path()).map_err(|e| e.to_string())
    }
}

fn to_llvm_type<'a>(context: &'a Context, loz_type: &Rc<Type>) -> Box<dyn BasicType<'a> + 'a> {
    match loz_type.borrow() {
        Type::Bool => Box::new(context.bool_type()),
        Type::Int => Box::new(context.i64_type()),
        Type::Float => Box::new(context.f64_type()),
        Type::Char => Box::new(context.i8_type().ptr_type(AddressSpace::Generic)),
        Type::String => Box::new(context.i8_type().ptr_type(AddressSpace::Generic)),
        Type::UserType(name, _) => Box::new(context.opaque_struct_type(&name)),
        _ => unimplemented!("{:?}", loz_type),
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

impl GeneratorState {}
