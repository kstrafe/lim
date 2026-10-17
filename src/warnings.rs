//! Non-fatal, source-spanned diagnostics collected explicitly by compiler clients.
use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
};

use crate::{Diagnostic, DiagnosticCode, DiagnosticSeverity, Expr, Item, Program, Statement, Type};

thread_local! {
    static WARNINGS: RefCell<Option<Vec<Diagnostic>>> = const { RefCell::new(None) };
}

/// Collect warnings without printing from library code. Nested sessions are isolated.
pub fn with_warnings<R>(operation: impl FnOnce() -> R) -> (R, Vec<Diagnostic>) {
    struct Restore(Option<Vec<Diagnostic>>);
    impl Drop for Restore {
        fn drop(&mut self) {
            WARNINGS.with(|warnings| warnings.replace(self.0.take()));
        }
    }
    let _restore = Restore(WARNINGS.with(|warnings| warnings.replace(Some(Vec::new()))));
    let result = operation();
    let warnings = WARNINGS.with(|warnings| warnings.borrow_mut().take().unwrap());
    (result, warnings)
}

pub(crate) fn record_program(program: &Program) {
    if !WARNINGS.with(|warnings| warnings.borrow().is_some()) {
        return;
    }
    let diagnostics = unused_type_warnings(program);
    WARNINGS.with(|warnings| {
        let mut warnings = warnings.borrow_mut();
        let Some(warnings) = warnings.as_mut() else {
            return;
        };
        for diagnostic in diagnostics {
            if !warnings.contains(&diagnostic) {
                warnings.push(diagnostic);
            }
        }
    });
}

struct Uses<'a> {
    candidates: &'a HashSet<&'a str>,
    names: HashSet<String>,
}

impl<'a> Uses<'a> {
    fn new(candidates: &'a HashSet<&'a str>) -> Self {
        Self {
            candidates,
            names: HashSet::new(),
        }
    }

    fn insert(&mut self, name: &str) {
        if self.candidates.contains(name) {
            self.names.insert(name.to_owned());
        }
    }
}

fn type_names(ty: &Type, names: &mut Uses<'_>) {
    match ty {
        Type::Named(name) => {
            names.insert(name);
        }
        Type::Reference { target, .. }
        | Type::PinnedReference { target, .. }
        | Type::RawPointer { target, .. }
        | Type::PinOwned(target)
        | Type::PinShared(target)
        | Type::Slice(target)
        | Type::MutableSlice(target)
        | Type::Atomic(target)
        | Type::Array(target, _) => type_names(target, names),
        Type::Tuple(fields) => {
            for field in fields {
                type_names(field, names);
            }
        }
        _ => {}
    }
}

fn argument_values(expression: &Expr, names: &mut Uses<'_>) {
    if let Expr::List(arguments) = expression {
        for argument in arguments {
            if let Expr::List(pair) = argument {
                for value in pair.iter().skip(1) {
                    expression_names(value, names);
                }
            }
        }
    }
}

fn expression_names(expression: &Expr, names: &mut Uses<'_>) {
    match expression {
        Expr::Block(body) | Expr::Loop(body) => {
            for statement in body {
                statement_names(statement, names);
            }
        }
        Expr::Labeled { expression, .. } => expression_names(expression, names),
        Expr::Symbol(name) => {
            names.insert(name);
        }
        Expr::List(items) => {
            let head = items.first().and_then(|head| {
                if let Expr::Symbol(name) = head {
                    Some(name.trim_start_matches('#'))
                } else {
                    None
                }
            });
            match head {
                Some("call" | "unsafe-call") => {
                    if let Some(arguments) = items.get(2) {
                        argument_values(arguments, names);
                    }
                }
                Some("struct-literal") => {
                    if let Some(ty) = items.get(1) {
                        expression_names(ty, names);
                    }
                    if let Some(fields) = items.get(2) {
                        argument_values(fields, names);
                    }
                }
                Some("asm") => {
                    if let Some(ty) = items.get(1) {
                        expression_names(ty, names);
                    }
                    if let Some(bindings) = items.get(2) {
                        argument_values(bindings, names);
                    }
                }
                Some("get" | "get-mut" | "pin-get" | "pin-get-mut" | "offset-of") => {
                    if let Some(receiver) = items.get(1) {
                        expression_names(receiver, names);
                    }
                }
                _ => {
                    for item in items {
                        expression_names(item, names);
                    }
                }
            }
        }
        _ => {}
    }
}

fn statement_names(statement: &Statement, names: &mut Uses<'_>) {
    match statement {
        Statement::Let { ty, value, .. } | Statement::Destructure { ty, value, .. } => {
            type_names(ty, names);
            expression_names(value, names);
        }
        Statement::LetElse {
            ty,
            value,
            else_body,
            ..
        } => {
            type_names(ty, names);
            expression_names(value, names);
            for statement in else_body {
                statement_names(statement, names);
            }
        }
        Statement::Assign { value, .. }
        | Statement::FieldAssign { value, .. }
        | Statement::TupleAssign { value, .. }
        | Statement::EnumPayloadAssign { value, .. }
        | Statement::Expr(value)
        | Statement::BreakValue(value)
        | Statement::BreakToValue { value, .. } => expression_names(value, names),
        Statement::ArrayAssign { index, value, .. } => {
            expression_names(index, names);
            expression_names(value, names);
        }
        Statement::Return(Some(value)) => expression_names(value, names),
        Statement::While { condition, body } => {
            expression_names(condition, names);
            for statement in body {
                statement_names(statement, names);
            }
        }
        Statement::Loop { body } => {
            for statement in body {
                statement_names(statement, names);
            }
        }
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            statement_names(init, names);
            expression_names(condition, names);
            statement_names(step, names);
            for statement in body {
                statement_names(statement, names);
            }
        }
        Statement::Labeled { statement, .. } => statement_names(statement, names),
        Statement::Return(None)
        | Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_) => {}
    }
}

/// Find structs, enums and aliases not referenced by any function or global,
/// following type-to-type dependencies. Self/mutual references alone are not use.
/// This is not function dead-code analysis: every declared function is a root,
/// including library entry points, so checks do not depend on having `main`.
pub fn unused_type_warnings(program: &Program) -> Vec<Diagnostic> {
    let mut candidates = HashSet::new();
    for item in &program.items {
        match item {
            Item::Struct { name, .. } | Item::TypeAlias { name, .. } => {
                candidates.insert(name.as_str());
            }
            Item::Enum { name, variants, .. } => {
                candidates.insert(name.as_str());
                candidates.extend(variants.iter().map(|variant| variant.name.as_str()));
            }
            _ => {}
        }
    }
    let mut dependencies = HashMap::<String, Uses<'_>>::new();
    let mut variants = HashMap::new();
    let mut roots = Uses::new(&candidates);
    for item in &program.items {
        match item {
            Item::Struct { name, fields, .. } => {
                let used = dependencies
                    .entry(name.clone())
                    .or_insert_with(|| Uses::new(&candidates));
                for field in fields {
                    type_names(&field.ty, used);
                }
            }
            Item::Enum {
                name,
                variants: cases,
                ..
            } => {
                let used = dependencies
                    .entry(name.clone())
                    .or_insert_with(|| Uses::new(&candidates));
                for variant in cases {
                    variants.insert(variant.name.clone(), name.clone());
                    for ty in &variant.fields {
                        type_names(ty, used);
                    }
                }
            }
            Item::TypeAlias { name, target, .. } => type_names(
                target,
                dependencies
                    .entry(name.clone())
                    .or_insert_with(|| Uses::new(&candidates)),
            ),
            Item::Function(function) => {
                for parameter in &function.parameters {
                    type_names(&parameter.ty, &mut roots);
                }
                type_names(&function.return_type, &mut roots);
                for statement in &function.body {
                    statement_names(statement, &mut roots);
                }
            }
            Item::Let { ty, value, .. } | Item::Static { ty, value, .. } => {
                type_names(ty, &mut roots);
                expression_names(value, &mut roots);
            }
            Item::ThreadTask {
                generated_functions,
                ..
            } => {
                for function in generated_functions {
                    for parameter in &function.parameters {
                        type_names(&parameter.ty, &mut roots);
                    }
                    type_names(&function.return_type, &mut roots);
                }
            }
            _ => {}
        }
    }
    let mut used = HashSet::new();
    let mut pending = roots.names.into_iter().collect::<Vec<_>>();
    while let Some(name) = pending.pop() {
        let name = variants.get(&name).unwrap_or(&name).clone();
        if !used.insert(name.clone()) {
            continue;
        }
        if let Some(dependencies) = dependencies.get(&name) {
            pending.extend(dependencies.names.iter().cloned());
        }
    }
    let mut diagnostics = Vec::new();
    for item in &program.items {
        let (name, kind) = match item {
            Item::Struct { name, .. } => (name, "struct"),
            Item::Enum { name, .. } => (name, "enum"),
            Item::TypeAlias { name, .. } => (name, "type alias"),
            _ => continue,
        };
        if used.contains(name) || name.starts_with("lim.gensym.") {
            continue;
        }
        let Some(declaration) = program.declaration_expressions.get(name) else {
            continue;
        };
        let Some(span) = declaration.children.get(1).map(|name| name.span) else {
            continue;
        };
        let mut diagnostic = crate::analysis_diagnostic(
            format!("{kind} '{name}' is never used"),
            DiagnosticCode::UnusedType,
            Some(span),
            Vec::new(),
            program,
        );
        diagnostic.severity = DiagnosticSeverity::Warning;
        diagnostics.push(diagnostic);
    }
    diagnostics
}
