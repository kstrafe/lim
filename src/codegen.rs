//! Small native x86-64 backend for the currently supported integer subset.
//!
//! The backend emits GNU assembler syntax in Intel mode and follows the Linux
//! System V ABI. It intentionally rejects types and expressions that do not
//! have a representation in this first backend instead of silently generating
//! incorrect code.

use std::collections::HashMap;

use crate::{check_types, Expr, Function, Item, Program, Statement, Type};

const ARGUMENT_REGISTERS: [&str; 6] = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"];

pub fn generate_assembly(program: &Program) -> Result<String, String> {
    check_types(program)?;
    let mut output = String::from(".intel_syntax noprefix\n.text\n");
    for item in &program.items {
        match item {
            Item::Function(function) => generate_function(function, &mut output)?,
            Item::Let { name, .. } => {
                return Err(format!(
                    "top-level let '{name}' is not supported by the native backend"
                ));
            }
        }
    }
    output.push_str(".section .note.GNU-stack,\"\",@progbits\n");
    Ok(output)
}

fn generate_function(function: &Function, output: &mut String) -> Result<(), String> {
    ensure_integer_type(&function.return_type)?;
    if function.parameters.len() > ARGUMENT_REGISTERS.len() {
        return Err(format!(
            "function '{}' has more than six parameters",
            function.name
        ));
    }
    for parameter in &function.parameters {
        ensure_integer_type(&parameter.ty)?;
    }

    let mut locals = HashMap::new();
    let mut next_slot = 1usize;
    for parameter in &function.parameters {
        add_local(&mut locals, &parameter.name, &mut next_slot)?;
    }
    for statement in &function.body {
        if let Statement::Let { name, ty, .. } = statement {
            ensure_integer_type(ty)?;
            add_local(&mut locals, name, &mut next_slot)?;
        }
    }
    let frame_size = ((next_slot.saturating_sub(1) * 8 + 15) / 16) * 16;

    output.push_str(&format!(
        ".globl {}\n.type {}, @function\n{}:\n",
        function.name, function.name, function.name
    ));
    output.push_str("    push rbp\n    mov rbp, rsp\n");
    if frame_size != 0 {
        output.push_str(&format!("    sub rsp, {frame_size}\n"));
    }
    for (index, parameter) in function.parameters.iter().enumerate() {
        output.push_str(&format!(
            "    mov QWORD PTR [rbp-{}], {}\n",
            locals[&parameter.name] * 8,
            ARGUMENT_REGISTERS[index]
        ));
    }

    let mut context = FunctionContext {
        locals,
        labels: 0,
        stack_depth: 0,
        output: String::new(),
    };
    for statement in &function.body {
        match statement {
            Statement::Let { name, value, .. } => {
                context.expression(value)?;
                context.output.push_str(&format!(
                    "    mov QWORD PTR [rbp-{}], rax\n",
                    context.locals[name] * 8
                ));
            }
            Statement::Expr(expression) => context.expression(expression)?,
        }
    }
    if function.body.is_empty() {
        context.output.push_str("    xor eax, eax\n");
    }
    output.push_str(&context.output);
    output.push_str("    mov rsp, rbp\n    pop rbp\n    ret\n\n");
    Ok(())
}

fn add_local(
    locals: &mut HashMap<String, usize>,
    name: &str,
    next_slot: &mut usize,
) -> Result<(), String> {
    if locals.insert(name.to_owned(), *next_slot).is_some() {
        return Err(format!("duplicate local '{name}'"));
    }
    *next_slot += 1;
    Ok(())
}

fn ensure_integer_type(ty: &Type) -> Result<(), String> {
    if matches!(
        ty,
        Type::Bool
            | Type::I8
            | Type::I16
            | Type::I32
            | Type::I64
            | Type::I128
            | Type::Isize
            | Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::U128
            | Type::Usize
    ) {
        Ok(())
    } else {
        Err(format!(
            "native integer backend does not support type {ty:?}"
        ))
    }
}

struct FunctionContext {
    locals: HashMap<String, usize>,
    labels: usize,
    stack_depth: usize,
    output: String,
}

impl FunctionContext {
    fn expression(&mut self, expression: &Expr) -> Result<(), String> {
        match expression {
            Expr::Integer(value) => self.output.push_str(&format!("    mov rax, {value}\n")),
            Expr::Symbol(name) if name == "true" => self.output.push_str("    mov eax, 1\n"),
            Expr::Symbol(name) if name == "false" => self.output.push_str("    xor eax, eax\n"),
            Expr::Symbol(name) => {
                let slot = self
                    .locals
                    .get(name)
                    .ok_or_else(|| format!("unknown variable '{name}'"))?;
                self.output
                    .push_str(&format!("    mov rax, QWORD PTR [rbp-{}]\n", slot * 8));
            }
            Expr::List(items) => self.list_expression(items)?,
            Expr::String(_) => return Err("strings are not supported by the native backend".into()),
            Expr::At => return Err("@ is not an executable expression".into()),
            Expr::Quote(_) => return Err("quoted expressions are not executable".into()),
        }
        Ok(())
    }

    fn list_expression(&mut self, items: &[Expr]) -> Result<(), String> {
        let operator = match items.first() {
            Some(Expr::Symbol(name)) => name.as_str(),
            _ => return Err("expression list must start with a symbol".into()),
        };
        match operator {
            "+" | "-" | "*" => self.binary_operator(operator, items),
            "<" | "<=" | ">" | ">=" | "==" | "!=" => self.comparison(operator, items),
            "if" => self.if_expression(items),
            _ => self.call(operator, &items[1..]),
        }
    }

    fn binary_operator(&mut self, operator: &str, items: &[Expr]) -> Result<(), String> {
        if items.len() != 3 {
            return Err(format!("operator '{operator}' requires two operands"));
        }
        self.expression(&items[1])?;
        self.push_rax();
        self.expression(&items[2])?;
        self.output.push_str("    mov rcx, rax\n    pop rax\n");
        self.stack_depth -= 1;
        match operator {
            "+" => self.output.push_str("    add rax, rcx\n"),
            "-" => self.output.push_str("    sub rax, rcx\n"),
            "*" => self.output.push_str("    imul rax, rcx\n"),
            _ => unreachable!(),
        }
        Ok(())
    }

    fn comparison(&mut self, operator: &str, items: &[Expr]) -> Result<(), String> {
        if items.len() != 3 {
            return Err(format!("comparison '{operator}' requires two operands"));
        }
        self.expression(&items[1])?;
        self.push_rax();
        self.expression(&items[2])?;
        self.output
            .push_str("    mov rcx, rax\n    pop rax\n    cmp rax, rcx\n");
        self.stack_depth -= 1;
        let condition = match operator {
            "<" => "l",
            "<=" => "le",
            ">" => "g",
            ">=" => "ge",
            "==" => "e",
            "!=" => "ne",
            _ => unreachable!(),
        };
        self.output
            .push_str(&format!("    set{condition} al\n    movzx rax, al\n"));
        Ok(())
    }

    fn if_expression(&mut self, items: &[Expr]) -> Result<(), String> {
        if items.len() != 4 {
            return Err("if requires a condition, then expression, and else expression".into());
        }
        let else_label = self.label("else");
        let end_label = self.label("endif");
        self.expression(&items[1])?;
        self.output
            .push_str(&format!("    test rax, rax\n    jz {else_label}\n"));
        self.expression(&items[2])?;
        self.output
            .push_str(&format!("    jmp {end_label}\n{else_label}:\n"));
        self.expression(&items[3])?;
        self.output.push_str(&format!("{end_label}:\n"));
        Ok(())
    }

    fn call(&mut self, name: &str, arguments: &[Expr]) -> Result<(), String> {
        if arguments.len() > ARGUMENT_REGISTERS.len() {
            return Err(format!("call to '{name}' has more than six arguments"));
        }
        for argument in arguments {
            self.expression(argument)?;
            self.push_rax();
        }
        for register in ARGUMENT_REGISTERS[..arguments.len()].iter().rev() {
            self.output.push_str(&format!("    pop {register}\n"));
            self.stack_depth -= 1;
        }
        let needs_padding = self.stack_depth % 2 == 1;
        if needs_padding {
            self.output.push_str("    sub rsp, 8\n");
        }
        self.output.push_str(&format!("    call {name}\n"));
        if needs_padding {
            self.output.push_str("    add rsp, 8\n");
        }
        Ok(())
    }

    fn push_rax(&mut self) {
        self.output.push_str("    push rax\n");
        self.stack_depth += 1;
    }

    fn label(&mut self, prefix: &str) -> String {
        let label = format!(".L{prefix}_{}", self.labels);
        self.labels += 1;
        label
    }
}
