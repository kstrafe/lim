//! Small native x86-64 backend for the currently supported integer subset.
//!
//! The backend emits GNU assembler syntax in Intel mode and follows the Linux
//! System V ABI. It intentionally rejects types and expressions that do not
//! have a representation in this first backend instead of silently generating
//! incorrect code.

use std::collections::HashMap;

use crate::{check_types, Expr, Field, Function, Item, Program, Statement, Type};

const ARGUMENT_REGISTERS: [&str; 6] = ["rdi", "rsi", "rdx", "rcx", "r8", "r9"];

pub fn generate_assembly(program: &Program) -> Result<String, String> {
    check_types(program)?;
    let structs: HashMap<String, Vec<Field>> = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Struct { name, fields } => Some((name.clone(), fields.clone())),
            _ => None,
        })
        .collect();
    let mut output = String::from(".intel_syntax noprefix\n.text\n");
    for item in &program.items {
        match item {
            Item::Function(function) => generate_function(function, &mut output, &structs)?,
            Item::Struct { .. } => {}
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

fn generate_function(
    function: &Function,
    output: &mut String,
    structs: &HashMap<String, Vec<Field>>,
) -> Result<(), String> {
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
        add_local(
            &mut locals,
            &parameter.name,
            &parameter.ty,
            structs,
            &mut next_slot,
        )?;
    }
    for statement in &function.body {
        collect_locals(statement, &mut locals, structs, &mut next_slot)?;
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
            scalar_slot(&locals, &parameter.name) * 8,
            ARGUMENT_REGISTERS[index]
        ));
    }

    let return_label = format!(".Lreturn_{}", function.name);
    let mut context = FunctionContext {
        locals,
        structs: structs.clone(),
        labels: 0,
        stack_depth: 0,
        loop_labels: Vec::new(),
        return_label: return_label.clone(),
        output: String::new(),
    };
    for statement in &function.body {
        context.statement(statement)?;
    }
    if function.body.is_empty() {
        context.output.push_str("    xor eax, eax\n");
    }
    output.push_str(&context.output);
    output.push_str(&format!("{return_label}:\n"));
    output.push_str("    mov rsp, rbp\n    pop rbp\n    ret\n\n");
    Ok(())
}

fn collect_locals(
    statement: &Statement,
    locals: &mut HashMap<String, Storage>,
    structs: &HashMap<String, Vec<Field>>,
    next_slot: &mut usize,
) -> Result<(), String> {
    match statement {
        Statement::Let { name, ty, .. } => {
            add_local(locals, name, ty, structs, next_slot)?;
        }
        Statement::While { body, .. } => {
            for statement in body {
                collect_locals(statement, locals, structs, next_slot)?;
            }
        }
        Statement::Assign { .. }
        | Statement::Break
        | Statement::Continue
        | Statement::Return(_)
        | Statement::Expr(_) => {}
    }
    Ok(())
}

fn add_local(
    locals: &mut HashMap<String, Storage>,
    name: &str,
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
    next_slot: &mut usize,
) -> Result<(), String> {
    let storage = if ensure_integer_type(ty).is_ok() {
        let slot = *next_slot;
        *next_slot += 1;
        Storage::Scalar(slot)
    } else if let Type::Named(struct_name) = ty {
        let fields = structs
            .get(struct_name)
            .ok_or_else(|| format!("unknown struct '{struct_name}'"))?;
        let mut slots = Vec::with_capacity(fields.len());
        for field in fields {
            ensure_integer_type(&field.ty)
                .map_err(|_| format!("struct field '{}' is not scalar", field.name))?;
            slots.push((field.name.clone(), *next_slot));
            *next_slot += 1;
        }
        Storage::Struct(slots)
    } else {
        return Err(format!("native backend does not support local type {ty:?}"));
    };
    if locals.insert(name.to_owned(), storage).is_some() {
        return Err(format!("duplicate local '{name}'"));
    }
    Ok(())
}

#[derive(Clone, Debug)]
enum Storage {
    Scalar(usize),
    Struct(Vec<(String, usize)>),
}

fn scalar_slot(locals: &HashMap<String, Storage>, name: &str) -> usize {
    match locals.get(name).expect("validated local") {
        Storage::Scalar(slot) => *slot,
        Storage::Struct(_) => panic!("validated scalar local is aggregate"),
    }
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
    locals: HashMap<String, Storage>,
    structs: HashMap<String, Vec<Field>>,
    labels: usize,
    stack_depth: usize,
    loop_labels: Vec<(String, String)>,
    return_label: String,
    output: String,
}

impl FunctionContext {
    fn statement(&mut self, statement: &Statement) -> Result<(), String> {
        match statement {
            Statement::Let {
                name, ty, value, ..
            } => {
                if let Type::Named(struct_name) = ty {
                    self.store_struct(name, struct_name, value)?;
                } else {
                    self.expression(value)?;
                    self.output.push_str(&format!(
                        "    mov QWORD PTR [rbp-{}], rax\n",
                        scalar_slot(&self.locals, name) * 8
                    ));
                }
            }
            Statement::Assign { name, value } => {
                self.expression(value)?;
                let slot = self
                    .locals
                    .get(name)
                    .ok_or_else(|| format!("unknown variable '{name}'"))?;
                let Storage::Scalar(slot) = slot else {
                    return Err(format!("cannot assign aggregate local '{name}'"));
                };
                self.output
                    .push_str(&format!("    mov QWORD PTR [rbp-{}], rax\n", slot * 8));
            }
            Statement::While { condition, body } => {
                let start = self.label("while");
                let end = self.label("endwhile");
                self.output.push_str(&format!("{start}:\n"));
                self.expression(condition)?;
                self.output
                    .push_str(&format!("    test rax, rax\n    jz {end}\n"));
                self.loop_labels.push((start.clone(), end.clone()));
                for statement in body {
                    self.statement(statement)?;
                }
                self.loop_labels.pop();
                self.output.push_str(&format!("    jmp {start}\n{end}:\n"));
            }
            Statement::Break => {
                let Some((_, end)) = self.loop_labels.last() else {
                    return Err("break used outside a loop".into());
                };
                self.output.push_str(&format!("    jmp {end}\n"));
            }
            Statement::Continue => {
                let Some((start, _)) = self.loop_labels.last() else {
                    return Err("continue used outside a loop".into());
                };
                self.output.push_str(&format!("    jmp {start}\n"));
            }
            Statement::Return(value) => {
                if let Some(value) = value {
                    self.expression(value)?;
                } else {
                    self.output.push_str("    xor eax, eax\n");
                }
                self.output
                    .push_str(&format!("    jmp {}\n", self.return_label));
            }
            Statement::Expr(expression) => self.expression(expression)?,
        }
        Ok(())
    }

    fn store_struct(&mut self, name: &str, struct_name: &str, value: &Expr) -> Result<(), String> {
        let Expr::List(items) = value else {
            return Err(format!("struct local '{name}' requires a constructor"));
        };
        let Some(Expr::Symbol(constructor)) = items.first() else {
            return Err("struct constructor must start with a symbol".into());
        };
        if constructor != struct_name {
            return Err(format!("expected '{struct_name}' constructor"));
        }
        let fields = self
            .structs
            .get(struct_name)
            .ok_or_else(|| format!("unknown struct '{struct_name}'"))?
            .clone();
        if items.len() - 1 != fields.len() {
            return Err(format!("constructor '{struct_name}' has wrong field count"));
        }
        let Storage::Struct(slots) = self
            .locals
            .get(name)
            .ok_or_else(|| format!("unknown local '{name}'"))?
        else {
            return Err(format!("'{name}' is not a struct"));
        };
        let slots = slots.clone();
        for ((_, slot), value) in slots.iter().zip(&items[1..]) {
            self.expression(value)?;
            self.output
                .push_str(&format!("    mov QWORD PTR [rbp-{}], rax\n", slot * 8));
        }
        Ok(())
    }

    fn expression(&mut self, expression: &Expr) -> Result<(), String> {
        match expression {
            Expr::Integer(value) => self.output.push_str(&format!("    mov rax, {value}\n")),
            Expr::Symbol(name) if name == "true" => self.output.push_str("    mov eax, 1\n"),
            Expr::Symbol(name) if name == "false" => self.output.push_str("    xor eax, eax\n"),
            Expr::Symbol(name) => {
                let slot = scalar_slot(&self.locals, name);
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
            "-" if items.len() == 2 => self.unary_negate(items),
            "+" | "-" | "*" | "/" | "%" | "&" | "|" | "^" | "<<" | ">>" => {
                self.binary_operator(operator, items)
            }
            "<" | "<=" | ">" | ">=" | "==" | "!=" => self.comparison(operator, items),
            "if" => self.if_expression(items),
            "get" => self.field_expression(items),
            "!" => self.boolean_not(items),
            "&&" | "||" => self.boolean_logic(operator, items),
            _ => self.call(operator, &items[1..]),
        }
    }

    fn unary_negate(&mut self, items: &[Expr]) -> Result<(), String> {
        self.expression(&items[1])?;
        self.output.push_str("    neg rax\n");
        Ok(())
    }

    fn field_expression(&mut self, items: &[Expr]) -> Result<(), String> {
        if items.len() != 3 {
            return Err("get requires a value and field".into());
        }
        let field_name = match &items[2] {
            Expr::Symbol(name) => name,
            _ => return Err("get requires a field name".into()),
        };
        match &items[1] {
            Expr::Symbol(local) => {
                let Storage::Struct(fields) = self
                    .locals
                    .get(local)
                    .ok_or_else(|| format!("unknown local '{local}'"))?
                else {
                    return Err(format!("'{local}' is not a struct"));
                };
                let slot = fields
                    .iter()
                    .find(|(name, _)| name == field_name)
                    .map(|(_, slot)| *slot)
                    .ok_or_else(|| format!("unknown field '{field_name}'"))?;
                self.output
                    .push_str(&format!("    mov rax, QWORD PTR [rbp-{}]\n", slot * 8));
                Ok(())
            }
            Expr::List(constructor) => {
                let Some(Expr::Symbol(struct_name)) = constructor.first() else {
                    return Err("get constructor must start with a struct name".into());
                };
                let fields = self
                    .structs
                    .get(struct_name)
                    .ok_or_else(|| format!("unknown struct '{struct_name}'"))?
                    .clone();
                let index = fields
                    .iter()
                    .position(|field| field.name == *field_name)
                    .ok_or_else(|| format!("unknown field '{field_name}'"))?;
                let value = constructor
                    .get(index + 1)
                    .ok_or_else(|| "constructor has too few fields".to_owned())?;
                self.expression(value)
            }
            _ => Err("get requires a struct local or constructor".into()),
        }
    }

    fn boolean_not(&mut self, items: &[Expr]) -> Result<(), String> {
        if items.len() != 2 {
            return Err("! requires one operand".into());
        }
        self.expression(&items[1])?;
        self.output.push_str("    xor eax, 1\n");
        Ok(())
    }

    fn boolean_logic(&mut self, operator: &str, items: &[Expr]) -> Result<(), String> {
        if items.len() != 3 {
            return Err(format!("operator '{operator}' requires two operands"));
        }
        let short_label = self.label(if operator == "&&" {
            "and_false"
        } else {
            "or_true"
        });
        let end_label = self.label("logic_end");
        self.expression(&items[1])?;
        self.output.push_str(&format!(
            "    test rax, rax\n    {} {short_label}\n",
            if operator == "&&" { "jz" } else { "jnz" }
        ));
        self.expression(&items[2])?;
        self.output
            .push_str("    test rax, rax\n    setne al\n    movzx rax, al\n");
        self.output
            .push_str(&format!("    jmp {end_label}\n{short_label}:\n"));
        self.output.push_str(if operator == "&&" {
            "    xor eax, eax\n"
        } else {
            "    mov eax, 1\n"
        });
        self.output.push_str(&format!("{end_label}:\n"));
        Ok(())
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
            "/" => self.output.push_str("    cqo\n    idiv rcx\n"),
            "%" => self
                .output
                .push_str("    cqo\n    idiv rcx\n    mov rax, rdx\n"),
            "&" => self.output.push_str("    and rax, rcx\n"),
            "|" => self.output.push_str("    or rax, rcx\n"),
            "^" => self.output.push_str("    xor rax, rcx\n"),
            "<<" => self.output.push_str("    shl rax, cl\n"),
            ">>" => self.output.push_str("    sar rax, cl\n"),
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
