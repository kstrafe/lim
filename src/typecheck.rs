#![allow(clippy::too_many_arguments)]

use std::collections::{HashMap, HashSet};

use crate::{
    parse_type, CallingConvention, EnumVariant, Expr, Field, Function, Item, Program,
    Representation, Statement, ThreadProperty, Type,
};

const LOOP_VALUE_CONTEXT: &str = "\0lim-loop-value";
const BORROW_ERROR_MARKER: &str = "\0lim-borrow-error\0";

fn borrow_error(message: &str) -> String {
    format!("{BORROW_ERROR_MARKER}{message}")
}

#[derive(Clone)]
struct Signature {
    type_parameters: Vec<String>,
    parameters: Vec<Type>,
    parameter_names: Vec<String>,
    return_type: Type,
}

pub fn check_types(program: &Program) -> Result<(), String> {
    check_types_with_span(program).map_err(|(message, _, _, _)| message)
}

/// An immutable program whose semantic validation has succeeded. The private
/// field prevents emission callers from constructing or invalidating this proof.
pub struct CheckedProgram<'a>(&'a Program);

pub(crate) type AnalysisError = (
    String,
    crate::DiagnosticCode,
    Option<crate::Span>,
    Vec<(crate::Span, String)>,
);

impl<'a> CheckedProgram<'a> {
    pub(crate) fn validate_with_span(program: &'a Program) -> Result<Self, AnalysisError> {
        check_types_with_span(program)?;
        Ok(Self(program))
    }
    pub fn validate(program: &'a Program) -> Result<Self, String> {
        check_types(program)?;
        Ok(Self(program))
    }

    pub(crate) fn program(&self) -> &'a Program {
        self.0
    }

    /// Emit a previously validated, immutably borrowed program.
    pub fn generate_assembly(&self, target: crate::TargetDescription) -> Result<String, String> {
        crate::codegen::generate_checked_assembly(self, target)
    }
}

#[cfg(test)]
thread_local! {
    pub(crate) static SEMANTIC_PASSES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
mod checked_program_tests {
    use super::*;

    #[test]
    fn normal_compilation_checks_once_and_unchecked_emission_still_validates() {
        let source = "(#fn main () u64 (#return 42u64))";
        let directory = std::env::temp_dir().join(format!("lim-checked-{}", std::process::id()));
        SEMANTIC_PASSES.with(|passes| passes.set(0));
        crate::compile_source_to_assembly(
            source,
            &directory.join("input.lim"),
            &crate::CompileConfig::default(),
            &directory.join("cache"),
            crate::TargetDescription::X86_64_SYSTEM_V,
        )
        .unwrap();
        SEMANTIC_PASSES.with(|passes| assert_eq!(passes.get(), 1));
        let mut program = crate::parse_program(source).unwrap();
        let Item::Function(function) = &mut program.items[0] else {
            panic!()
        };
        function.return_type = Type::Bool;
        assert!(crate::generate_assembly_for_target(
            &program,
            crate::TargetDescription::X86_64_SYSTEM_V
        )
        .is_err());
        SEMANTIC_PASSES.with(|passes| assert_eq!(passes.get(), 2));
    }
}

pub(crate) fn check_types_with_span(
    program: &Program,
) -> Result<
    (),
    (
        String,
        crate::DiagnosticCode,
        Option<crate::Span>,
        Vec<(crate::Span, String)>,
    ),
> {
    let mut diagnostic_span = None;
    let mut diagnostic_code = crate::DiagnosticCode::Type;
    let mut diagnostic_labels = Vec::new();
    check_types_inner(
        program,
        &mut diagnostic_code,
        &mut diagnostic_span,
        &mut diagnostic_labels,
    )
    .map_err(|message| (message, diagnostic_code, diagnostic_span, diagnostic_labels))
}

fn check_types_inner(
    program: &Program,
    diagnostic_code: &mut crate::DiagnosticCode,
    diagnostic_span: &mut Option<crate::Span>,
    diagnostic_labels: &mut Vec<(crate::Span, String)>,
) -> Result<(), String> {
    #[cfg(test)]
    SEMANTIC_PASSES.with(|passes| passes.set(passes.get() + 1));
    for item in &program.items {
        match item {
            Item::Function(function)
                if function.external != (function.calling_convention == CallingConvention::C) =>
            {
                *diagnostic_span = function_name_span(program, &function.name);
                return Err(format!(
                    "function '{}' has an inconsistent calling convention",
                    function.name
                ));
            }
            Item::Enum {
                name,
                representation: Representation::C,
                variants,
                ..
            } if variants
                .iter()
                .any(|variant| variant.discriminant > i32::MAX as u64) =>
            {
                *diagnostic_span =
                    program
                        .declaration_expressions
                        .get(name)
                        .and_then(|declaration| {
                            let variant_list = declaration
                                .children
                                .iter()
                                .rev()
                                .find(|child| matches!(&child.expr, Expr::List(_)))?;
                            variants
                                .iter()
                                .zip(&variant_list.children)
                                .find(|(variant, _)| variant.discriminant > i32::MAX as u64)
                                .and_then(|(_, form)| {
                                    form.children
                                        .get(1)
                                        .or_else(|| form.children.first())
                                        .map(|value| value.span)
                                })
                        });
                return Err(format!(
                    "#repr-c enum '{name}' discriminants must fit in signed 32-bit C int"
                ));
            }
            _ => {}
        }
    }
    let mut declared_types = HashSet::new();
    for item in &program.items {
        match item {
            Item::TypeAlias { name, .. }
            | Item::Struct { name, .. }
            | Item::Enum { name, .. }
            | Item::ThreadTask { name, .. }
                if !declared_types.insert(name) =>
            {
                *diagnostic_span = declaration_name_span(program, name);
                record_generated_invocation(program, diagnostic_span, diagnostic_labels);
                return Err(format!("duplicate type name '{name}'"));
            }
            _ => {}
        }
    }
    let mut unsafe_thread_properties = HashSet::new();
    for item in &program.items {
        let Item::UnsafeThreadAnnotation {
            property,
            type_name,
        } = item
        else {
            continue;
        };
        if !declared_types.contains(type_name) {
            *diagnostic_span = unsafe_impl_type_span(program, type_name, *property, 0);
            return Err(format!(
                "unsafe {:?} annotation refers to undeclared type '{type_name}'",
                property
            ));
        }
        let generic = program.items.iter().any(|declaration| match declaration {
            Item::Struct {
                name,
                type_parameters,
                ..
            }
            | Item::Enum {
                name,
                type_parameters,
                ..
            }
            | Item::TypeAlias {
                name,
                type_parameters,
                ..
            } if name == type_name => !type_parameters.is_empty(),
            _ => false,
        });
        if generic {
            *diagnostic_span = unsafe_impl_type_span(program, type_name, *property, 0);
            return Err(format!(
                "unsafe {:?} annotation for generic type '{type_name}' is not supported",
                property
            ));
        }
        if !unsafe_thread_properties.insert((type_name.clone(), *property)) {
            *diagnostic_span = unsafe_impl_type_span(program, type_name, *property, 1);
            return Err(format!(
                "duplicate unsafe {:?} annotation for '{type_name}'",
                property
            ));
        }
    }
    let mut aliases = HashMap::new();
    for item in &program.items {
        if let Item::TypeAlias { name, target, .. } = item {
            if aliases.insert(name.clone(), target.clone()).is_some() {
                return Err(format!("duplicate type alias '{name}'"));
            }
        }
    }
    for item in &program.items {
        let Item::TypeAlias { name, .. } = item else {
            continue;
        };
        if let Err(error) = resolve_type(&Type::Named(name.clone()), &aliases) {
            *diagnostic_span = program
                .declaration_expressions
                .get(name)
                .and_then(|declaration| declaration.children.get(2))
                .map(|target| target.span);
            return Err(error);
        }
    }
    let mut globals = HashMap::new();
    for item in &program.items {
        let (name, ty, mutable) = match item {
            Item::Let {
                name, ty, mutable, ..
            } => (name, ty, *mutable),
            Item::Static { name, ty, .. } => (name, ty, false),
            _ => continue,
        };
        {
            if mutable {
                return Err(format!("top-level binding '{name}' cannot be mutable"));
            }
            if globals
                .insert(name.clone(), resolve_type(ty, &aliases)?)
                .is_some()
            {
                *diagnostic_span = declaration_name_span(program, name);
                record_generated_invocation(program, diagnostic_span, diagnostic_labels);
                return Err(format!("duplicate global '{name}'"));
            }
        }
    }
    let mut structs = HashMap::new();
    for item in &program.items {
        if let Item::Struct { name, fields, .. } = item {
            let mut field_names = HashSet::new();
            let fields = fields
                .iter()
                .map(|field| {
                    if !field_names.insert(field.name.clone()) {
                        *diagnostic_span =
                            declaration_member_span(program, name, 2, &field.name, 1);
                        return Err(format!(
                            "duplicate field '{}' in struct '{name}'",
                            field.name
                        ));
                    }
                    Ok(Field {
                        name: field.name.clone(),
                        ty: resolve_type(&field.ty, &aliases)?,
                    })
                })
                .collect::<Result<Vec<_>, String>>()?;
            if structs.insert(name.clone(), fields).is_some() {
                return Err(format!("duplicate struct '{name}'"));
            }
        }
        if let Item::ThreadTask { name, .. } = item {
            if structs
                .insert(
                    name.clone(),
                    vec![Field {
                        name: "__lim_thread_context".into(),
                        ty: Type::RawPointer {
                            mutable: true,
                            target: Box::new(Type::Unit),
                        },
                    }],
                )
                .is_some()
            {
                return Err(format!("duplicate thread task type '{name}'"));
            }
        }
    }
    let mut enums = HashMap::new();
    let mut variant_names = HashMap::new();
    for item in &program.items {
        if let Item::Enum { name, variants, .. } = item {
            let mut local_variant_names = HashSet::new();
            let variants = variants
                .iter()
                .map(|variant| {
                    if !local_variant_names.insert(variant.name.clone()) {
                        *diagnostic_span =
                            declaration_member_span(program, name, 2, &variant.name, 1);
                        return Err(format!(
                            "duplicate variant '{}' in enum '{name}'",
                            variant.name
                        ));
                    }
                    if let Some(previous) = variant_names.insert(variant.name.clone(), name.clone())
                    {
                        *diagnostic_span = global_enum_member_span(program, &variant.name, 1);
                        return Err(format!(
                            "variant '{}' is already defined in enum '{previous}'",
                            variant.name
                        ));
                    }
                    Ok(EnumVariant {
                        name: variant.name.clone(),
                        fields: variant
                            .fields
                            .iter()
                            .map(|field| resolve_type(field, &aliases))
                            .collect::<Result<Vec<_>, _>>()?,
                        discriminant: variant.discriminant,
                    })
                })
                .collect::<Result<Vec<_>, String>>()?;
            if enums.insert(name.clone(), variants).is_some() {
                return Err(format!("duplicate enum '{name}'"));
            }
        }
    }
    let mut functions = HashMap::new();
    for item in &program.items {
        let Item::Function(function) = item else {
            continue;
        };
        if function.external && !function.type_parameters.is_empty() {
            *diagnostic_span = function_name_span(program, &function.name);
            return Err(format!(
                "external function '{}' cannot be generic",
                function.name
            ));
        }
        if functions
            .insert(
                function.name.clone(),
                Signature {
                    type_parameters: function.type_parameters.clone(),
                    parameter_names: function
                        .parameters
                        .iter()
                        .map(|parameter| parameter.name.clone())
                        .collect(),
                    parameters: function
                        .parameters
                        .iter()
                        .map(|parameter| resolve_type(&parameter.ty, &aliases))
                        .collect::<Result<Vec<_>, String>>()?,
                    return_type: resolve_type(&function.return_type, &aliases)?,
                },
            )
            .is_some()
        {
            *diagnostic_span = function_name_span(program, &function.name);
            return Err(format!("duplicate function '{}'", function.name));
        }
    }
    for item in &program.items {
        let Item::ThreadTask { name, worker, .. } = item else {
            continue;
        };
        let worker_item = program.items.iter().find_map(|item| match item {
            Item::Function(function) if function.name == *worker => Some(function),
            _ => None,
        });
        let Some(worker_item) = worker_item else {
            *diagnostic_span = program
                .declaration_expressions
                .get(name)
                .and_then(|declaration| first_symbol_span(declaration, worker));
            if let Some(invocation) = diagnostic_span
                .and_then(|span| program.generated_source_invocations.get(&span.source_id))
            {
                diagnostic_labels.push((*invocation, "generated from this invocation".into()));
            }
            return Err(format!(
                "thread task '{name}' refers to unknown worker function '{worker}'"
            ));
        };
        if !worker_item.type_parameters.is_empty() {
            return Err(format!(
                "thread worker '{worker}' must be monomorphic; specialize it before spawning"
            ));
        }
        let worker_signature = functions
            .get(worker)
            .expect("worker signature collected")
            .clone();
        for (parameter_index, (parameter, ty)) in worker_item
            .parameters
            .iter()
            .zip(&worker_signature.parameters)
            .enumerate()
        {
            let send = match type_has_thread_property(program, ty, ThreadProperty::Send) {
                Ok(send) => send,
                Err(error) => {
                    *diagnostic_span = first_unresolved_type(ty, &declared_types, &aliases)
                        .and_then(|unknown| {
                            worker_parameter_type_span(program, worker, parameter_index, &unknown)
                        });
                    record_generated_invocation(program, diagnostic_span, diagnostic_labels);
                    return Err(format!("{error} while checking thread worker '{worker}'"));
                }
            };
            if !send {
                *diagnostic_span = worker_parameter_span(program, worker, parameter_index);
                record_generated_invocation(program, diagnostic_span, diagnostic_labels);
                return Err(format!(
                    "thread worker '{worker}' parameter '{}' does not implement Send",
                    parameter.name
                ));
            }
        }
        let return_send = match type_has_thread_property(
            program,
            &worker_signature.return_type,
            ThreadProperty::Send,
        ) {
            Ok(send) => send,
            Err(error) => {
                *diagnostic_span =
                    first_unresolved_type(&worker_signature.return_type, &declared_types, &aliases)
                        .and_then(|unknown| worker_return_type_span(program, worker, &unknown));
                record_generated_invocation(program, diagnostic_span, diagnostic_labels);
                return Err(format!("{error} while checking thread worker '{worker}'"));
            }
        };
        if !return_send {
            *diagnostic_span = worker_return_span(program, worker);
            record_generated_invocation(program, diagnostic_span, diagnostic_labels);
            return Err(format!(
                "thread worker '{worker}' return type does not implement Send"
            ));
        }
        if contains_reference_type(
            &worker_signature.return_type,
            &structs,
            &enums,
            &mut HashSet::new(),
        ) {
            *diagnostic_span = worker_return_span(program, worker);
            record_generated_invocation(program, diagnostic_span, diagnostic_labels);
            return Err(format!(
                "thread worker '{worker}' cannot return reference-containing values"
            ));
        }
        let task_type = Type::Named(name.clone());
        let spawn_result_type = Type::Named(format!("{name}-spawn-result"));
        let join_result_type = Type::Named(format!("{name}-join-result"));
        for (generated_name, signature) in [
            (
                format!("{name}-spawn"),
                Signature {
                    type_parameters: Vec::new(),
                    parameters: worker_signature.parameters.clone(),
                    parameter_names: worker_signature.parameter_names.clone(),
                    return_type: spawn_result_type,
                },
            ),
            (
                format!("{name}-join"),
                Signature {
                    type_parameters: Vec::new(),
                    parameters: vec![task_type],
                    parameter_names: vec!["task".into()],
                    return_type: join_result_type,
                },
            ),
        ] {
            if functions
                .insert(generated_name.clone(), signature)
                .is_some()
            {
                return Err(format!(
                    "generated thread function '{generated_name}' conflicts with an existing function"
                ));
            }
        }
    }
    reject_recursive_calls(program, &functions).map_err(|error| {
        *diagnostic_span = error.span;
        error.message
    })?;
    for item in &program.items {
        match item {
            Item::Function(function) if function.external => {}
            Item::Function(function) => {
                if let Err(error) = check_function(
                    function,
                    &functions,
                    &structs,
                    &enums,
                    &globals,
                    &aliases,
                    &program.statement_spans,
                    &program.statement_expressions,
                    &program.source_files,
                    program.declaration_expressions.get(&function.name),
                ) {
                    let missing_generated_body_spans = program
                        .declaration_expressions
                        .get(&function.name)
                        .is_some_and(|expression| expression.children.is_empty());
                    *diagnostic_span = error.span.or_else(|| {
                        missing_generated_body_spans
                            .then(|| program.declaration_spans.get(&function.name).copied())
                            .flatten()
                    });
                    if let Some(invocation) = error
                        .span
                        .and_then(|span| program.generated_source_invocations.get(&span.source_id))
                    {
                        diagnostic_labels
                            .push((*invocation, "generated from this invocation".into()));
                    }
                    *diagnostic_code = error.code;
                    return Err(error.message);
                }
            }
            Item::TypeAlias { .. }
            | Item::Struct { .. }
            | Item::Enum { .. }
            | Item::UnsafeThreadAnnotation { .. }
            | Item::ThreadTask { .. } => {}
            Item::Let { name, value, .. } | Item::Static { name, value, .. } => {
                let ty = globals.get(name).expect("global type collected");
                let result = (|| {
                    let actual = expression(
                        value,
                        &globals,
                        &functions,
                        &structs,
                        &enums,
                        &HashSet::new(),
                        &aliases,
                        Some(ty),
                    )?;
                    require_type(&actual, ty, &format!("top-level let '{name}'"))
                })();
                result.map_err(|error: String| {
                    let Some(declaration) = program.declaration_expressions.get(name) else {
                        return error;
                    };
                    let Some(file) = program
                        .source_files
                        .get(declaration.span.source_id as usize)
                    else {
                        return error;
                    };
                    let source = file.source.as_str();
                    *diagnostic_span = precise_type_error_span(declaration, &error, source);
                    if let Some(invocation) = diagnostic_span
                        .and_then(|span| program.generated_source_invocations.get(&span.source_id))
                    {
                        diagnostic_labels
                            .push((*invocation, "generated from this invocation".into()));
                    }
                    error
                })?;
            }
        }
    }
    check_thread_task_ownership(program, &aliases, diagnostic_span, diagnostic_labels)?;
    *diagnostic_code = crate::DiagnosticCode::Linear;
    crate::linearcheck::check_program_with_span(program).map_err(|(message, span)| {
        *diagnostic_span = span;
        message
    })?;
    *diagnostic_code = crate::DiagnosticCode::Borrow;
    crate::borrowcheck::check_program(program).map_err(|error| {
        *diagnostic_span = error.span;
        *diagnostic_labels = error.labels;
        error.message
    })?;
    *diagnostic_code = crate::DiagnosticCode::Unsafe;
    crate::unsafecheck::check_program_with_span(program).map_err(|(message, span)| {
        *diagnostic_span = span;
        message
    })?;
    Ok(())
}

fn check_thread_task_ownership(
    program: &Program,
    aliases: &HashMap<String, Type>,
    diagnostic_span: &mut Option<crate::Span>,
    diagnostic_labels: &mut Vec<(crate::Span, String)>,
) -> Result<(), String> {
    let tasks = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::ThreadTask { name, worker, .. } => Some((name.clone(), worker.clone())),
            _ => None,
        })
        .collect::<HashMap<_, _>>();
    let task_result_enums = tasks
        .keys()
        .flat_map(|task| {
            [
                format!("{task}-spawn-result"),
                format!("{task}-join-result"),
            ]
        })
        .collect::<HashSet<_>>();
    let enum_fields = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Enum { name, variants, .. } => Some((
                name.clone(),
                variants
                    .iter()
                    .flat_map(|variant| variant.fields.iter().cloned())
                    .collect::<Vec<_>>(),
            )),
            _ => None,
        })
        .collect::<HashMap<_, _>>();
    if tasks.is_empty() {
        return Ok(());
    }

    for item in &program.items {
        match item {
            Item::Struct { name, fields, .. } => {
                for field in fields {
                    if type_mentions_task(
                        &resolve_type(&field.ty, aliases)?,
                        &tasks,
                        &enum_fields,
                        &mut HashSet::new(),
                    ) {
                        *diagnostic_span = task_type_in_declaration_span(
                            program,
                            name,
                            &tasks,
                            aliases,
                            &enum_fields,
                        );
                        record_generated_invocation(program, diagnostic_span, diagnostic_labels);
                        return Err(format!(
                            "thread task handles cannot be stored in struct '{name}'"
                        ));
                    }
                }
            }
            Item::Enum { name, variants, .. } => {
                if variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|ty| {
                        resolve_type(ty, aliases).is_ok_and(|ty| {
                            type_mentions_task(&ty, &tasks, &enum_fields, &mut HashSet::new())
                        })
                    })
                {
                    if !task_result_enums.contains(name) {
                        *diagnostic_span = task_type_in_declaration_span(
                            program,
                            name,
                            &tasks,
                            aliases,
                            &enum_fields,
                        );
                        record_generated_invocation(program, diagnostic_span, diagnostic_labels);
                        return Err(format!(
                            "thread task handles cannot be stored in enum '{name}'"
                        ));
                    }
                }
            }
            Item::TypeAlias { name, target, .. } => {
                if type_mentions_task(
                    &resolve_type(target, aliases)?,
                    &tasks,
                    &enum_fields,
                    &mut HashSet::new(),
                ) {
                    *diagnostic_span =
                        task_type_in_declaration_span(program, name, &tasks, aliases, &enum_fields);
                    record_generated_invocation(program, diagnostic_span, diagnostic_labels);
                    return Err(format!(
                        "type alias '{name}' cannot contain a thread task handle"
                    ));
                }
            }
            Item::Let { name, ty, .. } | Item::Static { name, ty, .. } => {
                if type_mentions_task(
                    &resolve_type(ty, aliases)?,
                    &tasks,
                    &enum_fields,
                    &mut HashSet::new(),
                ) {
                    *diagnostic_span =
                        task_type_in_declaration_span(program, name, &tasks, aliases, &enum_fields);
                    record_generated_invocation(program, diagnostic_span, diagnostic_labels);
                    return Err(format!(
                        "global '{name}' cannot contain a thread task handle"
                    ));
                }
            }
            Item::Function(function) => {
                if function.parameters.iter().any(|parameter| {
                    resolve_type(&parameter.ty, aliases).is_ok_and(|ty| {
                        type_mentions_task(&ty, &tasks, &enum_fields, &mut HashSet::new())
                    })
                }) || type_mentions_task(
                    &resolve_type(&function.return_type, aliases)?,
                    &tasks,
                    &enum_fields,
                    &mut HashSet::new(),
                ) {
                    *diagnostic_span = task_type_in_declaration_span(
                        program,
                        &function.name,
                        &tasks,
                        aliases,
                        &enum_fields,
                    );
                    record_generated_invocation(program, diagnostic_span, diagnostic_labels);
                    return Err(format!(
                        "function '{}' cannot accept, return, or retain a thread task handle",
                        function.name
                    ));
                }
                for statement in &function.body {
                    check_task_statement(statement, &HashMap::new(), &tasks)?;
                }
                let function_locals = function
                    .parameters
                    .iter()
                    .map(|parameter| (parameter.name.clone(), parameter.ty.clone()))
                    .collect::<HashMap<_, _>>();
                validate_thread_result_matches(
                    &function.body,
                    function_locals,
                    &tasks,
                    &enum_fields,
                    program,
                    aliases,
                )?;
                if !function
                    .body
                    .iter()
                    .any(|statement| statement_contains_thread_operation(statement, &tasks))
                {
                    check_function_task_uses(function, &tasks)?;
                }
                // Task handles are linear values. The ordinary linearity checker
                // requires every handle extracted from a spawn/join result to be
                // consumed, while the opaque task type can only be passed to its
                // generated join function (user signatures containing it are
                // rejected above). This also permits a failed join's returned
                // handle to be retried without ending its captured borrows.
            }
            Item::UnsafeThreadAnnotation { .. } | Item::ThreadTask { .. } => {}
        }
    }
    Ok(())
}

fn type_mentions_task(
    ty: &Type,
    tasks: &HashMap<String, String>,
    enums: &HashMap<String, Vec<Type>>,
    seen: &mut HashSet<String>,
) -> bool {
    match ty {
        Type::Named(name) => {
            tasks.contains_key(name)
                || (seen.insert(name.clone())
                    && enums.get(name).is_some_and(|fields| {
                        fields
                            .iter()
                            .any(|field| type_mentions_task(field, tasks, enums, seen))
                    }))
        }
        Type::Reference { target, .. }
        | Type::RawPointer { target, .. }
        | Type::Cell(target)
        | Type::Array(target, _) => type_mentions_task(target, tasks, enums, seen),
        Type::Tuple(fields) => fields
            .iter()
            .any(|field| type_mentions_task(field, tasks, enums, seen)),
        _ => false,
    }
}

fn validate_thread_result_matches(
    statements: &[Statement],
    mut locals: HashMap<String, Type>,
    tasks: &HashMap<String, String>,
    enum_fields: &HashMap<String, Vec<Type>>,
    program: &Program,
    aliases: &HashMap<String, Type>,
) -> Result<(), String> {
    let all_enums = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Enum { name, variants, .. } => Some((name.clone(), variants.clone())),
            _ => None,
        })
        .collect::<HashMap<_, _>>();
    validate_task_match_statements(
        statements,
        &mut locals,
        tasks,
        enum_fields,
        &all_enums,
        aliases,
    )
}

fn validate_task_match_statements(
    statements: &[Statement],
    locals: &mut HashMap<String, Type>,
    tasks: &HashMap<String, String>,
    enum_fields: &HashMap<String, Vec<Type>>,
    all_enums: &HashMap<String, Vec<EnumVariant>>,
    aliases: &HashMap<String, Type>,
) -> Result<(), String> {
    for statement in statements {
        match statement {
            Statement::Let {
                name, ty, value, ..
            } => {
                validate_task_match_expression(
                    value,
                    locals,
                    tasks,
                    enum_fields,
                    all_enums,
                    aliases,
                )?;
                locals.insert(name.clone(), ty.clone());
            }
            Statement::Destructure { value, .. }
            | Statement::LetElse { value, .. }
            | Statement::Assign { value, .. }
            | Statement::FieldAssign { value, .. }
            | Statement::TupleAssign { value, .. }
            | Statement::EnumPayloadAssign { value, .. }
            | Statement::BreakValue(value)
            | Statement::BreakToValue { value, .. }
            | Statement::Return(Some(value))
            | Statement::Expr(value) => validate_task_match_expression(
                value,
                locals,
                tasks,
                enum_fields,
                all_enums,
                aliases,
            )?,
            Statement::ArrayAssign { index, value, .. } => {
                validate_task_match_expression(
                    index,
                    locals,
                    tasks,
                    enum_fields,
                    all_enums,
                    aliases,
                )?;
                validate_task_match_expression(
                    value,
                    locals,
                    tasks,
                    enum_fields,
                    all_enums,
                    aliases,
                )?;
            }
            Statement::While { condition, body } => {
                validate_task_match_expression(
                    condition,
                    locals,
                    tasks,
                    enum_fields,
                    all_enums,
                    aliases,
                )?;
                validate_task_match_statements(
                    body,
                    &mut locals.clone(),
                    tasks,
                    enum_fields,
                    all_enums,
                    aliases,
                )?;
            }
            Statement::Loop { body } => validate_task_match_statements(
                body,
                &mut locals.clone(),
                tasks,
                enum_fields,
                all_enums,
                aliases,
            )?,
            Statement::For {
                init,
                condition,
                step,
                body,
            } => {
                validate_task_match_statements(
                    std::slice::from_ref(init),
                    &mut locals.clone(),
                    tasks,
                    enum_fields,
                    all_enums,
                    aliases,
                )?;
                validate_task_match_expression(
                    condition,
                    locals,
                    tasks,
                    enum_fields,
                    all_enums,
                    aliases,
                )?;
                validate_task_match_statements(
                    std::slice::from_ref(step),
                    &mut locals.clone(),
                    tasks,
                    enum_fields,
                    all_enums,
                    aliases,
                )?;
                validate_task_match_statements(
                    body,
                    &mut locals.clone(),
                    tasks,
                    enum_fields,
                    all_enums,
                    aliases,
                )?;
            }
            Statement::Labeled { statement, .. } => validate_task_match_statements(
                std::slice::from_ref(statement),
                locals,
                tasks,
                enum_fields,
                all_enums,
                aliases,
            )?,
            Statement::Return(None)
            | Statement::Break
            | Statement::BreakTo(_)
            | Statement::Continue
            | Statement::ContinueTo(_) => {}
        }
    }
    Ok(())
}

fn validate_task_match_expression(
    expression: &Expr,
    locals: &HashMap<String, Type>,
    tasks: &HashMap<String, String>,
    enum_fields: &HashMap<String, Vec<Type>>,
    all_enums: &HashMap<String, Vec<EnumVariant>>,
    aliases: &HashMap<String, Type>,
) -> Result<(), String> {
    match expression {
        Expr::List(items) => {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "#match" || operator == "match")
                && items.len() >= 3
            {
                if let Some(Type::Named(result_type)) = thread_result_type(&items[1], locals, tasks)
                {
                    if let Some(variants) = all_enums.get(&result_type) {
                        for variant in variants {
                            if !variant.fields.iter().any(|field| {
                                type_mentions_task(field, tasks, enum_fields, &mut HashSet::new())
                            }) {
                                continue;
                            }
                            let required_arm = items[2..].iter().find_map(|arm| {
                                let Expr::List(arm_parts) = arm else {
                                    return None;
                                };
                                let pattern = arm_parts.first()?;
                                (pattern_variant_name(pattern) == Some(variant.name.as_str()))
                                    .then_some(pattern)
                            });
                            let Some(pattern) = required_arm else {
                                return Err(format!(
                                    "thread result match must explicitly handle variant '{}' and its task handle",
                                    variant.name
                                ));
                            };
                            validate_task_variant_pattern(
                                pattern,
                                variant,
                                tasks,
                                enum_fields,
                                aliases,
                            )?;
                        }
                    }
                }
            }
            for item in items {
                validate_task_match_expression(
                    item,
                    locals,
                    tasks,
                    enum_fields,
                    all_enums,
                    aliases,
                )?;
            }
        }
        Expr::Block(body) | Expr::Loop(body) => validate_task_match_statements(
            body,
            &mut locals.clone(),
            tasks,
            enum_fields,
            all_enums,
            aliases,
        )?,
        Expr::Labeled { expression, .. }
        | Expr::Quote(expression)
        | Expr::QuasiQuote(expression)
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => validate_task_match_expression(
            expression,
            locals,
            tasks,
            enum_fields,
            all_enums,
            aliases,
        )?,
        _ => {}
    }
    Ok(())
}

fn thread_result_type(
    expression: &Expr,
    locals: &HashMap<String, Type>,
    tasks: &HashMap<String, String>,
) -> Option<Type> {
    if let Expr::Symbol(name) = expression {
        return locals.get(name).cloned();
    }
    let Expr::List(items) = expression else {
        return None;
    };
    let Expr::Symbol(function) = items.first()? else {
        return None;
    };
    tasks.keys().find_map(|task| {
        (function == &format!("{task}-spawn"))
            .then(|| Type::Named(format!("{task}-spawn-result")))
            .or_else(|| {
                (function == &format!("{task}-join"))
                    .then(|| Type::Named(format!("{task}-join-result")))
            })
    })
}

fn pattern_variant_name(pattern: &Expr) -> Option<&str> {
    match pattern {
        Expr::Symbol(name) => Some(name),
        Expr::List(items) => match items.first()? {
            Expr::Symbol(name) => Some(name),
            _ => None,
        },
        _ => None,
    }
}

fn validate_task_variant_pattern(
    pattern: &Expr,
    variant: &EnumVariant,
    tasks: &HashMap<String, String>,
    enum_fields: &HashMap<String, Vec<Type>>,
    aliases: &HashMap<String, Type>,
) -> Result<(), String> {
    let payload_patterns = match pattern {
        Expr::List(items) => &items[1..],
        _ => &[],
    };
    for (ty, payload_pattern) in variant.fields.iter().zip(payload_patterns) {
        if !type_mentions_task(ty, tasks, enum_fields, &mut HashSet::new()) {
            continue;
        }
        if !task_payload_pattern_is_bound(ty, payload_pattern, tasks, enum_fields, aliases) {
            return Err(format!(
                "thread result variant '{}' must bind its task handle instead of discarding it",
                variant.name
            ));
        }
    }
    Ok(())
}

fn task_payload_pattern_is_bound(
    ty: &Type,
    pattern: &Expr,
    tasks: &HashMap<String, String>,
    enum_fields: &HashMap<String, Vec<Type>>,
    aliases: &HashMap<String, Type>,
) -> bool {
    let ty = resolve_type(ty, aliases).unwrap_or_else(|_| ty.clone());
    match ty {
        Type::Named(name) if tasks.contains_key(&name) => {
            matches!(pattern, Expr::Symbol(binding) if binding != "_")
        }
        Type::Tuple(fields) => {
            let Expr::List(patterns) = pattern else {
                return false;
            };
            if !matches!(patterns.first(), Some(Expr::Symbol(head)) if head == "tuple")
                || patterns.len() != fields.len() + 1
            {
                return false;
            }
            fields
                .iter()
                .zip(&patterns[1..])
                .all(|(field, field_pattern)| {
                    !type_mentions_task(field, tasks, enum_fields, &mut HashSet::new())
                        || task_payload_pattern_is_bound(
                            field,
                            field_pattern,
                            tasks,
                            enum_fields,
                            aliases,
                        )
                })
        }
        _ => false,
    }
}

fn check_function_task_uses(
    function: &Function,
    tasks: &HashMap<String, String>,
) -> Result<(), String> {
    let mut handles = HashMap::<String, String>::new();
    let mut pending = HashSet::<String>::new();
    let mut consumed = HashSet::<String>::new();
    for statement in &function.body {
        match statement {
            Statement::Let {
                name,
                ty: Type::Named(task_type),
                value,
                mutable,
            } if tasks.contains_key(task_type) => {
                if *mutable {
                    return Err(format!(
                        "thread task handle '{name}' must be immutable and consumed by join"
                    ));
                }
                let expected_spawn = format!("{task_type}-spawn");
                if !is_direct_thread_call(value, &expected_spawn) {
                    return Err(format!(
                        "thread task '{name}' must be initialized directly by '{expected_spawn}'"
                    ));
                }
                let Expr::List(items) = value else {
                    unreachable!()
                };
                check_task_expression_children(&items[1..], &handles, tasks)?;
                if handles.insert(name.clone(), task_type.clone()).is_some() {
                    return Err(format!("duplicate thread task binding '{name}'"));
                }
                pending.insert(name.clone());
            }
            Statement::Let { name, value, .. } => {
                if let Some((task_type, handle)) = direct_task_join(value, tasks) {
                    consume_thread_handle(
                        &task_type,
                        &handle,
                        &handles,
                        &mut pending,
                        &mut consumed,
                    )?;
                } else {
                    check_task_statement_expr(value, &handles, tasks)?;
                    reject_thread_control_flow_while_pending(value, &pending)?;
                }
                let _ = name;
            }
            Statement::Expr(value) => {
                if let Some((task_type, handle)) = direct_task_join(value, tasks) {
                    consume_thread_handle(
                        &task_type,
                        &handle,
                        &handles,
                        &mut pending,
                        &mut consumed,
                    )?;
                } else {
                    check_task_statement_expr(value, &handles, tasks)?;
                    reject_thread_control_flow_while_pending(value, &pending)?;
                }
            }
            Statement::Return(Some(value)) => {
                if let Some((task_type, handle)) = direct_task_join(value, tasks) {
                    consume_thread_handle(
                        &task_type,
                        &handle,
                        &handles,
                        &mut pending,
                        &mut consumed,
                    )?;
                } else {
                    check_task_statement_expr(value, &handles, tasks)?;
                    if !pending.is_empty() {
                        return Err(format!(
                            "function '{}' may return while thread task '{}' is still running",
                            function.name,
                            pending.iter().next().unwrap()
                        ));
                    }
                }
            }
            Statement::Return(None) => {
                if !pending.is_empty() {
                    return Err(format!(
                        "function '{}' may return while thread task '{}' is still running",
                        function.name,
                        pending.iter().next().unwrap()
                    ));
                }
            }
            _ => {
                check_task_statement(statement, &handles, tasks)?;
                if !pending.is_empty() && is_control_statement(statement) {
                    return Err(format!(
                        "thread task handles cannot cross control flow; join '{}' before this statement",
                        pending.iter().next().unwrap()
                    ));
                }
            }
        }
    }
    if let Some(handle) = pending.iter().next() {
        return Err(format!(
            "thread task handle '{handle}' is not joined exactly once"
        ));
    }
    if let Some(handle) = handles.keys().find(|handle| !consumed.contains(*handle)) {
        return Err(format!(
            "thread task handle '{handle}' is not joined exactly once"
        ));
    }
    Ok(())
}

fn reject_thread_control_flow_while_pending(
    expression: &Expr,
    pending: &HashSet<String>,
) -> Result<(), String> {
    if !pending.is_empty() && expression_has_control_flow(expression) {
        return Err(format!(
            "thread task handles cannot cross control flow; join '{}' first",
            pending.iter().next().unwrap()
        ));
    }
    Ok(())
}

fn is_control_statement(statement: &Statement) -> bool {
    matches!(
        statement,
        Statement::While { .. }
            | Statement::Loop { .. }
            | Statement::For { .. }
            | Statement::Labeled { .. }
            | Statement::Break
            | Statement::BreakValue(_)
            | Statement::BreakTo(_)
            | Statement::BreakToValue { .. }
            | Statement::Continue
            | Statement::ContinueTo(_)
            | Statement::LetElse { .. }
    )
}

fn expression_has_control_flow(expression: &Expr) -> bool {
    match expression {
        Expr::List(items) => {
            matches!(items.first(), Some(Expr::Symbol(name)) if matches!(name.as_str(), "if" | "if-let" | "match" | "while" | "loop" | "for"))
                || items.iter().any(expression_has_control_flow)
        }
        Expr::Block(_) | Expr::Loop(_) => true,
        Expr::Labeled { expression, .. }
        | Expr::Quote(expression)
        | Expr::QuasiQuote(expression)
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => expression_has_control_flow(expression),
        _ => false,
    }
}

fn direct_task_join(
    expression: &Expr,
    tasks: &HashMap<String, String>,
) -> Option<(String, String)> {
    let Expr::List(items) = expression else {
        return None;
    };
    let Expr::Symbol(operator) = items.first()? else {
        return None;
    };
    for task_type in tasks.keys() {
        if operator == &format!("{task_type}-join") && items.len() == 2 {
            let Expr::Symbol(handle) = &items[1] else {
                return None;
            };
            return Some((task_type.clone(), handle.clone()));
        }
    }
    None
}

fn is_direct_thread_call(expression: &Expr, expected: &str) -> bool {
    matches!(expression, Expr::List(items)
        if matches!(items.first(), Some(Expr::Symbol(operator)) if operator == expected))
}

fn consume_thread_handle(
    task_type: &str,
    handle: &str,
    handles: &HashMap<String, String>,
    pending: &mut HashSet<String>,
    consumed: &mut HashSet<String>,
) -> Result<(), String> {
    match handles.get(handle) {
        Some(actual) if actual == task_type && pending.remove(handle) => {
            consumed.insert(handle.to_owned());
            Ok(())
        }
        Some(_) if consumed.contains(handle) => Err(format!(
            "thread task handle '{handle}' was joined more than once"
        )),
        Some(_) => Err(format!("thread task handle '{handle}' is not active")),
        None => Err(format!("'{handle}' is not a thread task handle")),
    }
}

fn contains_thread_operation(expression: &Expr, tasks: &HashMap<String, String>) -> bool {
    match expression {
        Expr::List(items) => {
            let head = items.first().and_then(|item| match item {
                Expr::Symbol(name) => Some(name),
                _ => None,
            });
            head.is_some_and(|head| {
                tasks
                    .keys()
                    .any(|task| head == &format!("{task}-spawn") || head == &format!("{task}-join"))
            }) || items
                .iter()
                .any(|item| contains_thread_operation(item, tasks))
        }
        Expr::Block(statements) | Expr::Loop(statements) => statements
            .iter()
            .any(|statement| statement_contains_thread_operation(statement, tasks)),
        Expr::Labeled { expression, .. }
        | Expr::Quote(expression)
        | Expr::QuasiQuote(expression)
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => contains_thread_operation(expression, tasks),
        _ => false,
    }
}

fn check_task_statement_expr(
    expression: &Expr,
    handles: &HashMap<String, String>,
    tasks: &HashMap<String, String>,
) -> Result<(), String> {
    if !handles.is_empty() && contains_thread_operation(expression, tasks) {
        return Err("thread spawn and join must be direct top-level statements".into());
    }
    check_task_expression_children(std::slice::from_ref(expression), handles, tasks)
}

fn check_task_expression_children(
    expressions: &[Expr],
    handles: &HashMap<String, String>,
    tasks: &HashMap<String, String>,
) -> Result<(), String> {
    for expression in expressions {
        match expression {
            Expr::Symbol(name) if handles.contains_key(name) => {
                return Err(format!(
                    "thread task handle '{name}' may only be used once as the direct argument to join"
                ));
            }
            Expr::List(items) => {
                if let Some(Expr::Symbol(name)) = items.first() {
                    if tasks.contains_key(name) && items.len() > 1 {
                        return Err(format!(
                            "thread task type '{name}' is opaque and cannot be constructed directly"
                        ));
                    }
                }
                check_task_expression_children(items, handles, tasks)?;
            }
            Expr::Block(statements) | Expr::Loop(statements) => {
                for statement in statements {
                    check_task_statement(statement, handles, tasks)?;
                }
            }
            Expr::Labeled { expression, .. }
            | Expr::Quote(expression)
            | Expr::QuasiQuote(expression)
            | Expr::Unquote(expression)
            | Expr::UnquoteSplicing(expression) => {
                check_task_expression_children(std::slice::from_ref(expression), handles, tasks)?;
            }
            _ => {}
        }
    }
    Ok(())
}

fn statement_contains_thread_operation(
    statement: &Statement,
    tasks: &HashMap<String, String>,
) -> bool {
    match statement {
        Statement::Let { value, .. }
        | Statement::Destructure { value, .. }
        | Statement::LetElse { value, .. }
        | Statement::Assign { value, .. }
        | Statement::FieldAssign { value, .. }
        | Statement::TupleAssign { value, .. }
        | Statement::EnumPayloadAssign { value, .. }
        | Statement::BreakValue(value)
        | Statement::BreakToValue { value, .. }
        | Statement::Return(Some(value))
        | Statement::Expr(value) => contains_thread_operation(value, tasks),
        Statement::ArrayAssign { index, value, .. } => {
            contains_thread_operation(index, tasks) || contains_thread_operation(value, tasks)
        }
        Statement::While { condition, body } => {
            contains_thread_operation(condition, tasks)
                || body
                    .iter()
                    .any(|statement| statement_contains_thread_operation(statement, tasks))
        }
        Statement::Loop { body } => body
            .iter()
            .any(|statement| statement_contains_thread_operation(statement, tasks)),
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            statement_contains_thread_operation(init, tasks)
                || contains_thread_operation(condition, tasks)
                || statement_contains_thread_operation(step, tasks)
                || body
                    .iter()
                    .any(|statement| statement_contains_thread_operation(statement, tasks))
        }
        Statement::Labeled { statement, .. } => {
            statement_contains_thread_operation(statement, tasks)
        }
        Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_)
        | Statement::Return(None) => false,
    }
}

fn check_task_statement(
    statement: &Statement,
    handles: &HashMap<String, String>,
    tasks: &HashMap<String, String>,
) -> Result<(), String> {
    match statement {
        Statement::Let { value, .. }
        | Statement::Destructure { value, .. }
        | Statement::LetElse { value, .. }
        | Statement::Assign { value, .. }
        | Statement::FieldAssign { value, .. }
        | Statement::TupleAssign { value, .. }
        | Statement::EnumPayloadAssign { value, .. }
        | Statement::BreakValue(value)
        | Statement::BreakToValue { value, .. }
        | Statement::Return(Some(value))
        | Statement::Expr(value) => check_task_statement_expr(value, handles, tasks),
        Statement::ArrayAssign { index, value, .. } => {
            check_task_statement_expr(index, handles, tasks)?;
            check_task_statement_expr(value, handles, tasks)
        }
        Statement::While { condition, body } => {
            check_task_statement_expr(condition, handles, tasks)?;
            for statement in body {
                check_task_statement(statement, handles, tasks)?;
            }
            Ok(())
        }
        Statement::Loop { body } => {
            for statement in body {
                check_task_statement(statement, handles, tasks)?;
            }
            Ok(())
        }
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            check_task_statement(init, handles, tasks)?;
            check_task_statement_expr(condition, handles, tasks)?;
            check_task_statement(step, handles, tasks)?;
            for statement in body {
                check_task_statement(statement, handles, tasks)?;
            }
            Ok(())
        }
        Statement::Labeled { statement, .. } => check_task_statement(statement, handles, tasks),
        Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_)
        | Statement::Return(None) => Ok(()),
    }
}

/// Determine whether a concrete type satisfies Lim's built-in Send or Sync
/// thread property. Explicit `#unsafe-impl` declarations override structural rules.
pub fn type_has_thread_property(
    program: &Program,
    ty: &Type,
    property: ThreadProperty,
) -> Result<bool, String> {
    let aliases = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::TypeAlias { name, target, .. } => Some((name.clone(), target.clone())),
            _ => None,
        })
        .collect::<HashMap<_, _>>();
    let structs = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Struct { name, fields, .. } => Some((
                name.clone(),
                fields
                    .iter()
                    .map(|field| Ok((field.name.clone(), resolve_type(&field.ty, &aliases)?)))
                    .collect::<Result<Vec<_>, String>>(),
            )),
            Item::ThreadTask { name, .. } => Some((
                name.clone(),
                Ok(vec![(
                    "__lim_thread_context".to_owned(),
                    Type::RawPointer {
                        mutable: true,
                        target: Box::new(Type::Unit),
                    },
                )]),
            )),
            _ => None,
        })
        .map(|(name, fields)| fields.map(|fields| (name, fields)))
        .collect::<Result<HashMap<_, _>, _>>()?;
    let enums = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Enum { name, variants, .. } => Some((
                name.clone(),
                variants
                    .iter()
                    .map(|variant| {
                        variant
                            .fields
                            .iter()
                            .map(|ty| resolve_type(ty, &aliases))
                            .collect::<Result<Vec<_>, _>>()
                    })
                    .collect::<Result<Vec<_>, String>>(),
            )),
            _ => None,
        })
        .map(|(name, variants)| variants.map(|variants| (name, variants)))
        .collect::<Result<HashMap<_, _>, _>>()?;
    let overrides = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::UnsafeThreadAnnotation {
                property,
                type_name,
            } => Some((type_name.clone(), *property)),
            _ => None,
        })
        .collect::<HashSet<_>>();
    type_has_thread_property_inner(
        &resolve_type(ty, &aliases)?,
        property,
        &structs,
        &enums,
        &overrides,
        &mut HashSet::new(),
    )
}

fn type_has_thread_property_inner(
    ty: &Type,
    property: ThreadProperty,
    structs: &HashMap<String, Vec<(String, Type)>>,
    enums: &HashMap<String, Vec<Vec<Type>>>,
    overrides: &HashSet<(String, ThreadProperty)>,
    active: &mut HashSet<String>,
) -> Result<bool, String> {
    let all = |types: Vec<&Type>, active: &mut HashSet<String>| -> Result<bool, String> {
        for nested in types {
            if !type_has_thread_property_inner(nested, property, structs, enums, overrides, active)?
            {
                return Ok(false);
            }
        }
        Ok(true)
    };
    match ty {
        Type::Unit
        | Type::Never
        | Type::Bool
        | Type::Char
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
        | Type::F32
        | Type::F64 => Ok(true),
        Type::Generic(_) => Ok(false),
        Type::RawPointer { .. } => Ok(false),
        Type::Cell(inner) => match property {
            ThreadProperty::Send => {
                type_has_thread_property_inner(inner, property, structs, enums, overrides, active)
            }
            ThreadProperty::Sync => Ok(false),
        },
        Type::Reference { mutable, target } => match (property, mutable) {
            (ThreadProperty::Send, false) | (ThreadProperty::Sync, _) => {
                type_has_thread_property_inner(
                    target,
                    ThreadProperty::Sync,
                    structs,
                    enums,
                    overrides,
                    active,
                )
            }
            (ThreadProperty::Send, true) => type_has_thread_property_inner(
                target,
                ThreadProperty::Send,
                structs,
                enums,
                overrides,
                active,
            ),
        },
        Type::Slice(target) => type_has_thread_property_inner(
            target,
            ThreadProperty::Sync,
            structs,
            enums,
            overrides,
            active,
        ),
        Type::MutableSlice(target) => match property {
            ThreadProperty::Send => type_has_thread_property_inner(
                target,
                ThreadProperty::Send,
                structs,
                enums,
                overrides,
                active,
            ),
            ThreadProperty::Sync => Ok(false),
        },
        Type::Atomic(target) => Ok(is_atomic_scalar(target)),
        Type::Tuple(fields) => all(fields.iter().collect(), active),
        Type::Array(element, _) => {
            type_has_thread_property_inner(element, property, structs, enums, overrides, active)
        }
        Type::Named(name) => {
            if overrides.contains(&(name.clone(), property)) {
                return Ok(true);
            }
            if !active.insert(name.clone()) {
                return Ok(true);
            }
            let result = if let Some(fields) = structs.get(name) {
                all(fields.iter().map(|(_, ty)| ty).collect(), active)?
            } else if let Some(variants) = enums.get(name) {
                all(
                    variants.iter().flat_map(|variant| variant.iter()).collect(),
                    active,
                )?
            } else {
                return Err(format!("unknown type '{name}' while checking {property:?}"));
            };
            active.remove(name);
            Ok(result)
        }
    }
}

fn reject_recursive_calls(
    program: &Program,
    functions: &HashMap<String, Signature>,
) -> Result<(), FunctionTypeError> {
    let names = functions.keys().cloned().collect::<HashSet<_>>();
    let mut edges = HashMap::<String, HashSet<String>>::new();
    for item in &program.items {
        let Item::Function(function) = item else {
            continue;
        };
        if function.external {
            continue;
        }
        let calls = edges.entry(function.name.clone()).or_default();
        for statement in &function.body {
            collect_statement_calls(statement, &names, calls);
        }
    }

    let mut state = HashMap::<String, bool>::new();
    let mut path = Vec::new();
    let mut ordered_names = names.into_iter().collect::<Vec<_>>();
    ordered_names.sort();
    for name in ordered_names {
        visit_call_graph(program, &name, &edges, &mut state, &mut path)?;
    }
    Ok(())
}

fn recursive_call_span(program: &Program, caller: &str, callee: &str) -> Option<crate::Span> {
    fn find_call(expression: &crate::SpannedExpr, callee: &str) -> Option<crate::Span> {
        if let Expr::List(items) = &expression.expr {
            let target_index = if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#call" || head == "call")
            {
                1
            } else if matches!(items.first(), Some(Expr::Symbol(head)) if head == callee) {
                return expression.children.first().map(|head| head.span);
            } else {
                usize::MAX
            };
            if target_index != usize::MAX
                && matches!(items.get(target_index), Some(Expr::Symbol(name)) if name == callee)
            {
                return expression
                    .children
                    .get(target_index)
                    .map(|target| target.span);
            }
        }
        expression
            .children
            .iter()
            .find_map(|child| find_call(child, callee))
    }

    let mut expressions = program
        .statement_expressions
        .iter()
        .filter(|((function, _), _)| function == caller)
        .collect::<Vec<_>>();
    expressions.sort_by_key(|((_, index), _)| *index);
    expressions
        .into_iter()
        .find_map(|(_, expression)| find_call(expression, callee))
}

pub(crate) fn function_call_depths(program: &Program) -> HashMap<String, usize> {
    let names = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Function(function) => Some(function.name.clone()),
            _ => None,
        })
        .collect::<HashSet<_>>();
    let mut edges = HashMap::<String, HashSet<String>>::new();
    for item in &program.items {
        let Item::Function(function) = item else {
            continue;
        };
        let calls = edges.entry(function.name.clone()).or_default();
        for statement in &function.body {
            collect_statement_calls(statement, &names, calls);
        }
    }
    let mut depths = HashMap::new();
    for name in &names {
        let depth = call_depth(name, &edges, &mut depths);
        depths.insert(name.clone(), depth);
    }
    depths
}

fn call_depth(
    name: &str,
    edges: &HashMap<String, HashSet<String>>,
    depths: &mut HashMap<String, usize>,
) -> usize {
    if let Some(depth) = depths.get(name) {
        return *depth;
    }
    let depth = edges
        .get(name)
        .into_iter()
        .flat_map(|calls| calls.iter())
        .map(|called| call_depth(called, edges, depths))
        .max()
        .unwrap_or(0)
        + 1;
    depths.insert(name.to_owned(), depth);
    depth
}

fn visit_call_graph(
    program: &Program,
    name: &str,
    edges: &HashMap<String, HashSet<String>>,
    state: &mut HashMap<String, bool>,
    path: &mut Vec<String>,
) -> Result<(), FunctionTypeError> {
    if state.get(name) == Some(&true) {
        let start = path.iter().position(|item| item == name).unwrap_or(0);
        let mut cycle = path[start..].to_vec();
        cycle.push(name.to_owned());
        let caller = cycle.first().map(String::as_str);
        let callee = cycle.get(1).map(String::as_str);
        let span = caller
            .zip(callee)
            .and_then(|(caller, callee)| recursive_call_span(program, caller, callee));
        return Err(FunctionTypeError {
            message: format!("recursive calls are not allowed: {}", cycle.join(" -> ")),
            span,
            code: crate::DiagnosticCode::Type,
        });
    }
    if state.get(name) == Some(&false) {
        return Ok(());
    }
    state.insert(name.to_owned(), true);
    path.push(name.to_owned());
    if let Some(calls) = edges.get(name) {
        let mut ordered_calls = calls.iter().collect::<Vec<_>>();
        ordered_calls.sort();
        for called in ordered_calls {
            visit_call_graph(program, called, edges, state, path)?;
        }
    }
    path.pop();
    state.insert(name.to_owned(), false);
    Ok(())
}

fn collect_statement_calls(
    statement: &Statement,
    functions: &HashSet<String>,
    calls: &mut HashSet<String>,
) {
    match statement {
        Statement::Let { value, .. }
        | Statement::Destructure { value, .. }
        | Statement::Assign { value, .. }
        | Statement::FieldAssign { value, .. }
        | Statement::TupleAssign { value, .. }
        | Statement::EnumPayloadAssign { value, .. }
        | Statement::BreakValue(value)
        | Statement::BreakToValue { value, .. }
        | Statement::Return(Some(value))
        | Statement::Expr(value) => collect_expression_calls(value, functions, calls),
        Statement::ArrayAssign { index, value, .. } => {
            collect_expression_calls(index, functions, calls);
            collect_expression_calls(value, functions, calls);
        }
        Statement::While { condition, body } => {
            collect_expression_calls(condition, functions, calls);
            for statement in body {
                collect_statement_calls(statement, functions, calls);
            }
        }
        Statement::LetElse {
            value, else_body, ..
        } => {
            collect_expression_calls(value, functions, calls);
            for statement in else_body {
                collect_statement_calls(statement, functions, calls);
            }
        }
        Statement::Loop { body } => {
            for statement in body {
                collect_statement_calls(statement, functions, calls);
            }
        }
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            collect_statement_calls(init, functions, calls);
            collect_expression_calls(condition, functions, calls);
            collect_statement_calls(step, functions, calls);
            for statement in body {
                collect_statement_calls(statement, functions, calls);
            }
        }
        Statement::Labeled { statement, .. } => {
            collect_statement_calls(statement, functions, calls);
        }
        Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_)
        | Statement::Return(None) => {}
    }
}

fn collect_expression_calls(
    expression: &Expr,
    functions: &HashSet<String>,
    calls: &mut HashSet<String>,
) {
    match expression {
        Expr::List(items) => {
            if let Some(Expr::Symbol(operator)) = items.first() {
                let candidate = operator.split('<').next().unwrap_or(operator);
                if functions.contains(operator) {
                    calls.insert(operator.clone());
                } else if functions.contains(candidate) {
                    calls.insert(candidate.to_owned());
                }
            }
            for item in items {
                collect_expression_calls(item, functions, calls);
            }
        }
        Expr::Block(statements) => {
            for statement in statements {
                collect_statement_calls(statement, functions, calls);
            }
        }
        Expr::Loop(statements) => {
            for statement in statements {
                collect_statement_calls(statement, functions, calls);
            }
        }
        Expr::Labeled { expression, .. } => {
            collect_expression_calls(expression, functions, calls);
        }
        Expr::Quote(value)
        | Expr::QuasiQuote(value)
        | Expr::Unquote(value)
        | Expr::UnquoteSplicing(value) => collect_expression_calls(value, functions, calls),
        Expr::Symbol(_)
        | Expr::Integer(_)
        | Expr::UnsignedInteger(_)
        | Expr::Float(_)
        | Expr::Char(_)
        | Expr::String(_)
        | Expr::At => {}
    }
}

fn member_name(form: &crate::SpannedExpr) -> Option<&crate::SpannedExpr> {
    match &form.expr {
        Expr::Symbol(_) => Some(form),
        Expr::List(_) => form.children.first(),
        _ => None,
    }
}

fn declaration_member_span(
    program: &Program,
    declaration_name: &str,
    members_child: usize,
    wanted_name: &str,
    occurrence: usize,
) -> Option<crate::Span> {
    let declaration = program.declaration_expressions.get(declaration_name)?;
    let members = declaration.children.get(members_child)?;
    members
        .children
        .iter()
        .filter_map(member_name)
        .filter(|name| matches!(&name.expr, Expr::Symbol(name) if name == wanted_name))
        .nth(occurrence)
        .map(|name| name.span)
}

fn global_enum_member_span(
    program: &Program,
    wanted: &str,
    occurrence: usize,
) -> Option<crate::Span> {
    let mut spans = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Enum { name, .. } => program.declaration_expressions.get(name),
            _ => None,
        })
        .filter_map(|declaration| declaration.children.get(2))
        .flat_map(|variants| variants.children.iter())
        .filter_map(member_name)
        .filter(|name| matches!(&name.expr, Expr::Symbol(name) if name == wanted))
        .map(|name| name.span)
        .collect::<Vec<_>>();
    spans.sort_by_key(|span| (span.source_id, span.start));
    spans.get(occurrence).copied()
}

fn check_function(
    function: &Function,
    functions: &HashMap<String, Signature>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    globals: &HashMap<String, Type>,
    aliases: &HashMap<String, Type>,
    statement_spans: &HashMap<(String, usize), crate::Span>,
    statement_expressions: &HashMap<(String, usize), crate::SpannedExpr>,
    source_files: &[crate::SourceFile],
    declaration_expression: Option<&crate::SpannedExpr>,
) -> Result<(), FunctionTypeError> {
    let mut variables = globals.clone();
    let mut mutable = HashSet::new();
    let mut parameter_names = HashSet::new();
    let return_type = resolve_type(&function.return_type, aliases)?;
    for parameter in &function.parameters {
        if !parameter_names.insert(parameter.name.clone()) {
            let span = declaration_expression
                .and_then(|declaration| declaration.children.get(2))
                .and_then(|parameters| {
                    parameters
                        .children
                        .iter()
                        .filter_map(|parameter| parameter.children.first())
                        .filter(|name| {
                            matches!(&name.expr, Expr::Symbol(name) if name == &parameter.name)
                        })
                        .nth(1)
                        .map(|name| name.span)
                });
            return Err(FunctionTypeError {
                message: format!(
                    "duplicate parameter '{}' in function '{}'",
                    parameter.name, function.name
                ),
                span,
                code: crate::DiagnosticCode::Type,
            });
        }
        variables.insert(
            parameter.name.clone(),
            resolve_type(&parameter.ty, aliases)?,
        );
        if parameter.mutable {
            mutable.insert(parameter.name.clone());
        }
    }
    let mut last_type = Type::Unit;
    for (index, statement) in function.body.iter().enumerate() {
        let result = (|| {
            if index + 1 == function.body.len() {
                if let Statement::Expr(value) = statement {
                    expression(
                        value,
                        &variables,
                        functions,
                        structs,
                        enums,
                        &mutable,
                        aliases,
                        Some(&return_type),
                    )
                } else {
                    statement_type(
                        statement,
                        &mut variables,
                        &mut mutable,
                        functions,
                        structs,
                        enums,
                        &return_type,
                        aliases,
                        false,
                    )
                }
            } else {
                statement_type(
                    statement,
                    &mut variables,
                    &mut mutable,
                    functions,
                    structs,
                    enums,
                    &return_type,
                    aliases,
                    false,
                )
            }
        })();
        last_type = result.map_err(|error: String| {
            let (error, code) = if let Some(message) = error.strip_prefix(BORROW_ERROR_MARKER) {
                (message.to_owned(), crate::DiagnosticCode::Borrow)
            } else {
                (error, crate::DiagnosticCode::Type)
            };
            let statement_span = statement_spans
                .get(&(function.name.clone(), index))
                .copied();
            let source_expression = statement_expressions.get(&(function.name.clone(), index));
            let precise_span = source_expression
                .and_then(|expression| {
                    let source = source_files
                        .get(expression.span.source_id as usize)
                        .map(|file| file.source.as_str())?;
                    precise_type_error_span(expression, &error, source)
                })
                .or_else(|| source_expression.map(crate::source_value_span))
                .or(statement_span);
            FunctionTypeError {
                message: error,
                span: precise_span,
                code,
            }
        })?;
    }
    require_type(
        &last_type,
        &return_type,
        &format!("return of function '{}'", function.name),
    )
    .map_err(|error| {
        let span = function.body.len().checked_sub(1).and_then(|index| {
            statement_expressions
                .get(&(function.name.clone(), index))
                .map(|expression| expression_value_span(expression))
                .or_else(|| {
                    statement_spans
                        .get(&(function.name.clone(), index))
                        .copied()
                })
        });
        FunctionTypeError {
            message: error,
            span,
            code: crate::DiagnosticCode::Type,
        }
    })
}

struct FunctionTypeError {
    message: String,
    span: Option<crate::Span>,
    code: crate::DiagnosticCode,
}

impl From<String> for FunctionTypeError {
    fn from(message: String) -> Self {
        Self {
            message,
            span: None,
            code: crate::DiagnosticCode::Type,
        }
    }
}

fn precise_type_error_span(
    statement: &crate::SpannedExpr,
    error: &str,
    source: &str,
) -> Option<crate::Span> {
    let value = crate::source_value_expression(statement);
    if let Some(index) = error
        .strip_prefix("tuple element ")
        .and_then(|rest| rest.split_whitespace().next())
        .and_then(|index| index.parse::<usize>().ok())
    {
        if let Some(span) = tuple_element_span(value, index) {
            return Some(span);
        }
    }
    if let Some(index) = error
        .strip_prefix("array element ")
        .and_then(|rest| rest.split_whitespace().next())
        .and_then(|index| index.parse::<usize>().ok())
    {
        if let Some(span) = array_element_span(value, index) {
            return Some(span);
        }
    }
    for (prefix, operator) in [
        ("tuple constructor expects ", "#tuple"),
        ("array constructor expects ", "#array"),
    ] {
        if let Some(expected) = error
            .strip_prefix(prefix)
            .and_then(|rest| rest.split_whitespace().next())
            .and_then(|count| count.parse::<usize>().ok())
        {
            if let Some(span) = constructor_arity_span(value, operator, expected) {
                return Some(span);
            }
        }
    }
    if let Some((payload_index, variant_name)) = error
        .strip_prefix("payload ")
        .and_then(|rest| {
            rest.split_once(" of variant '")
                .map(|(index, rest)| (index, rest))
        })
        .and_then(|(index, rest)| {
            let index = index.parse::<usize>().ok()?;
            let variant = rest.split_once('\'')?.0;
            Some((index, variant))
        })
    {
        if let Some(span) = enum_constructor_payload_span(value, variant_name, payload_index) {
            return Some(span);
        }
    }
    if let Some(field_name) = error
        .strip_prefix("field '")
        .and_then(|rest| rest.split_once("' of '").map(|(field, _)| field))
    {
        if let Some(span) = struct_literal_field_value_span(value, field_name) {
            return Some(span);
        }
    }
    let name = error
        .strip_prefix("unknown variable or enum variant '")
        .and_then(|tail| tail.split('\'').next());
    if let Some(name) = name {
        return first_symbol_span(value, name).or(Some(value.span));
    }
    let unknown_type = error
        .strip_prefix("unknown type '")
        .and_then(|tail| tail.split('\'').next());
    if let Some(name) = unknown_type {
        return declared_type_span(statement, name)
            .or_else(|| first_symbol_span(statement, name))
            .or_else(|| first_symbol_span(value, name))
            .or(Some(value.span));
    }
    let named_target = [
        "cannot assign to immutable variable '",
        "cannot replace '",
        "cannot replace reference-containing elements of '",
        "cannot mutate immutable variable '",
        "cannot mutably borrow immutable variable '",
        "unknown variable '",
    ]
    .iter()
    .find_map(|prefix| error.strip_prefix(prefix)?.split('\'').next());
    let named_target = named_target.or_else(|| {
        let rest = error.strip_prefix('\'')?;
        let (name, suffix) = rest.split_once('\'')?;
        [
            " is not an array",
            " is not a struct",
            " is not an enum",
            " is not a tuple",
        ]
        .contains(&suffix)
        .then_some(name)
    });
    let named_target = named_target.or_else(|| {
        error
            .strip_prefix("unknown enum variant '")
            .or_else(|| error.strip_prefix("unknown variant '"))
            .or_else(|| error.strip_prefix("variant '"))
            .and_then(|rest| rest.split('\'').next())
    });
    let named_target = named_target.or_else(|| {
        error
            .strip_prefix('\'')?
            .split_once("' is not a variant of '")
            .map(|(name, _)| name)
    });
    let duplicate_pattern = if error == "duplicate wildcard match pattern" {
        Some("_")
    } else {
        error
            .strip_prefix("duplicate boolean match pattern '")
            .or_else(|| error.strip_prefix("duplicate enum match pattern '"))
            .and_then(|rest| rest.split('\'').next())
    };
    if let Some(pattern) = duplicate_pattern {
        if let Some(span) = last_match_pattern_symbol_span(statement, pattern) {
            return Some(span);
        }
    }
    if error.starts_with("duplicate character match pattern") {
        if let Some(span) = last_match_pattern_char_span(statement) {
            return Some(span);
        }
    }
    let integer_pattern = error
        .strip_prefix("integer match pattern ")
        .or_else(|| error.strip_prefix("unsigned integer match pattern "))
        .or_else(|| error.strip_prefix("duplicate integer match pattern "))
        .and_then(|rest| {
            rest.split_once(" does not fit")
                .map_or(rest, |(value, _)| value)
                .parse::<u128>()
                .ok()
        });
    if let Some(value) = integer_pattern {
        if let Some(span) = last_match_pattern_integer_span(statement, value) {
            return Some(span);
        }
    }
    if error.contains("range pattern") || error.starts_with("range patterns require") {
        if let Some(span) = match_range_pattern_span(statement, error) {
            return Some(span);
        }
    }
    let enum_pattern_target = error
        .strip_prefix('\'')
        .and_then(|rest| {
            rest.split_once("' is not a variant of '")
                .map(|(name, _)| name)
        })
        .or_else(|| {
            error
                .strip_prefix("unknown enum variant '")
                .and_then(|rest| rest.split('\'').next())
        })
        .or_else(|| {
            error
                .strip_prefix("variant '")
                .and_then(|rest| rest.split('\'').next())
        });
    if let Some(name) = enum_pattern_target {
        if let Some(span) = type_pattern_symbol_span(statement, name) {
            return Some(span);
        }
    }
    if let Some(name) = named_target {
        if let Some(span) = first_symbol_span(statement, name) {
            return Some(span);
        }
    }
    if let Some(span) = type_error_argument_span(value, error) {
        return Some(span);
    }
    if error.starts_with("operator '")
        || error.starts_with("function '")
        || error.starts_with("unknown function '")
    {
        if let Some(operator) = error.split('\'').nth(1) {
            if let Some(span) = source_operator_span(statement, operator) {
                return Some(span);
            }
        }
    }
    if error.contains("match is not exhaustive") {
        if let Some(span) = source_operator_span(statement, "match") {
            return Some(span);
        }
    }
    if let Some(name) = error
        .split_once("expected Named(\"")
        .and_then(|(_, rest)| rest.split_once('\"').map(|(name, _)| name))
    {
        if let Some(span) = declared_type_span(statement, name) {
            return Some(span);
        }
        if let Some(span) = first_symbol_span(statement, name) {
            return Some(span);
        }
    }
    if let Some((parameter_name, function_name)) = error
        .strip_prefix("argument '")
        .and_then(|rest| {
            rest.split_once("' to '")
                .map(|(parameter, rest)| (parameter, rest))
        })
        .and_then(|(parameter, rest)| {
            rest.split_once('\'')
                .map(|(function, _)| (parameter, function))
        })
    {
        if let Some(span) = named_call_argument_span(statement, function_name, parameter_name) {
            return Some(span);
        }
    }

    let mismatch_type = error
        .split_once("mismatched types ")
        .and_then(|(context, types)| {
            let (left, right) = types.split_once(" and ")?;
            let right = right.split(';').next().unwrap_or(right);
            let operator_type = typed_operator_qualifier(
                value,
                context.trim().split_whitespace().next().unwrap_or_default(),
            );
            Some(match operator_type {
                Some(qualifier) if qualifier.eq_ignore_ascii_case(left) => right,
                Some(qualifier) if qualifier.eq_ignore_ascii_case(right) => left,
                _ => right,
            })
        })
        .or_else(|| {
            error
                .split_once(" has type ")
                .and_then(|(_, rest)| rest.split_once(", expected ").map(|(actual, _)| actual))
        })
        .or_else(|| error.split_once(", got ").map(|(_, actual)| actual));
    if let Some(mismatch_type) = mismatch_type {
        if error.starts_with("if branches has mismatched types")
            || error.starts_with("match arms has mismatched types")
        {
            return control_flow_mismatch_span(value, mismatch_type, source).or(Some(value.span));
        }
        if let Some(span) = expression_with_type_hint(value, mismatch_type, source) {
            return Some(span);
        }
    }
    Some(value.span)
}

fn tuple_element_span(expression: &crate::SpannedExpr, index: usize) -> Option<crate::Span> {
    if let Expr::List(items) = &expression.expr {
        if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#tuple" || head == "tuple")
        {
            let value_start = usize::from(items.get(1).is_some_and(|item| {
                parse_type(Some(item)).is_ok_and(|ty| matches!(ty, Type::Tuple(_)))
            })) + 1;
            if let Some(value) = expression.children.get(value_start + index) {
                return Some(value.span);
            }
        }
    }
    expression
        .children
        .iter()
        .find_map(|child| tuple_element_span(child, index))
}

fn array_element_span(expression: &crate::SpannedExpr, index: usize) -> Option<crate::Span> {
    if let Expr::List(items) = &expression.expr {
        if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#array" || head == "array")
        {
            let value_start = usize::from(items.get(1).is_some_and(|item| {
                parse_type(Some(item)).is_ok_and(|ty| matches!(ty, Type::Array(_, _)))
            })) + 1;
            if let Some(value) = expression.children.get(value_start + index) {
                return Some(value.span);
            }
        }
    }
    expression
        .children
        .iter()
        .find_map(|child| array_element_span(child, index))
}

fn constructor_arity_span(
    expression: &crate::SpannedExpr,
    operator: &str,
    expected: usize,
) -> Option<crate::Span> {
    if let Expr::List(items) = &expression.expr {
        if matches!(items.first(), Some(Expr::Symbol(head)) if head == operator) {
            let has_explicit_type = items.get(1).is_some_and(|item| {
                parse_type(Some(item)).is_ok_and(|ty| match operator {
                    "#tuple" => matches!(ty, Type::Tuple(_)),
                    "#array" => matches!(ty, Type::Array(_, _)),
                    _ => false,
                })
            });
            let value_start = usize::from(has_explicit_type) + 1;
            let actual = items.len().saturating_sub(value_start);
            if actual > expected {
                return expression
                    .children
                    .get(value_start + expected)
                    .map(|extra| extra.span);
            }
            if actual < expected {
                return expression.children.first().map(|head| head.span);
            }
        }
    }
    expression
        .children
        .iter()
        .find_map(|child| constructor_arity_span(child, operator, expected))
}

fn enum_constructor_payload_span(
    expression: &crate::SpannedExpr,
    variant_name: &str,
    payload_index: usize,
) -> Option<crate::Span> {
    if let Expr::List(items) = &expression.expr {
        if matches!(items.first(), Some(Expr::Symbol(name)) if name == variant_name) {
            return expression
                .children
                .get(payload_index + 1)
                .map(|payload| payload.span);
        }
    }
    expression
        .children
        .iter()
        .find_map(|child| enum_constructor_payload_span(child, variant_name, payload_index))
}

fn struct_literal_field_value_span(
    expression: &crate::SpannedExpr,
    field_name: &str,
) -> Option<crate::Span> {
    fn find_field(expression: &crate::SpannedExpr, field_name: &str) -> Option<crate::Span> {
        if let Expr::List(items) = &expression.expr {
            if matches!(items.first(), Some(Expr::Symbol(name)) if name == field_name)
                && items.len() == 2
            {
                return expression.children.get(1).map(|value| value.span);
            }
        }
        expression
            .children
            .iter()
            .find_map(|child| find_field(child, field_name))
    }

    if let Expr::List(items) = &expression.expr {
        if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#struct-literal" | "struct-literal"))
        {
            return find_field(expression, field_name);
        }
    }
    expression
        .children
        .iter()
        .find_map(|child| struct_literal_field_value_span(child, field_name))
}

fn control_flow_mismatch_span(
    expression: &crate::SpannedExpr,
    wanted: &str,
    source: &str,
) -> Option<crate::Span> {
    if let Expr::List(items) = &expression.expr {
        if let Some(Expr::Symbol(head)) = items.first() {
            match head.as_str() {
                "#if" | "if" => {
                    for branch in expression.children.get(2..4).into_iter().flatten() {
                        if let Some(span) = control_flow_mismatch_span(branch, wanted, source) {
                            return Some(span);
                        }
                    }
                    return None;
                }
                "#match" | "match" => {
                    for arm in expression.children.iter().skip(2) {
                        if let Some(value) = arm.children.get(1) {
                            if let Some(span) = control_flow_mismatch_span(value, wanted, source) {
                                return Some(span);
                            }
                        }
                    }
                    return None;
                }
                "#call" | "call" => return None,
                _ => {}
            }
        }
    }
    expression
        .children
        .iter()
        .find_map(|child| control_flow_mismatch_span(child, wanted, source))
        .or_else(|| expression_with_type_hint(expression, wanted, source))
}

fn named_call_argument_span(
    expression: &crate::SpannedExpr,
    function_name: &str,
    parameter_name: &str,
) -> Option<crate::Span> {
    if let Expr::List(items) = &expression.expr {
        if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#call" | "call"))
            && matches!(items.get(1), Some(Expr::Symbol(callee)) if callee == function_name)
        {
            let arguments = expression.children.get(2)?;
            if let Some(value) = arguments.children.iter().skip(1).find_map(|argument| {
                let Expr::List(parts) = &argument.expr else {
                    return None;
                };
                matches!(parts.first(), Some(Expr::Symbol(name)) if name == parameter_name)
                    .then(|| argument.children.get(1).map(|value| value.span))
                    .flatten()
            }) {
                return Some(value);
            }
        }
    }
    expression
        .children
        .iter()
        .find_map(|child| named_call_argument_span(child, function_name, parameter_name))
}

fn type_error_argument_span(expression: &crate::SpannedExpr, error: &str) -> Option<crate::Span> {
    let (operators, argument) = if error == "index requires an array" {
        (&["index"][..], 1)
    } else if error == "array index must be an integer"
        || error.starts_with("array index ") && error.contains(" is out of bounds")
    {
        (&["index"][..], 2)
    } else if error.starts_with("if condition has type ") {
        (&["if"][..], 1)
    } else if error.starts_with("while condition has type ") {
        (&["while"][..], 1)
    } else if error.starts_with("for condition has type ") {
        (&["for"][..], 2)
    } else if error.starts_with("shift count ") {
        (&["<<", ">>"][..], 2)
    } else if error == "unary '-' requires a numeric operand" {
        (&["-"][..], 1)
    } else if error.starts_with("slice requires ")
        || error == "slice-len requires a slice"
        || error == "slice-idx requires a slice"
    {
        let operators: &[&str] = if error.starts_with("slice requires ") {
            &["slice-of"]
        } else if error == "slice-len requires a slice" {
            &["slice-len"]
        } else {
            &["slice-idx"]
        };
        return find_operator_argument(expression, operators, 1);
    } else if error == "get requires a struct or tuple value" {
        (&["get"][..], 1)
    } else if error == "get-payload requires an enum value" {
        (&["get-payload"][..], 1)
    } else if error.contains(" has no field '") {
        (&["get"][..], 2)
    } else if error.contains(" has no variant '") {
        (&["get-payload"][..], 2)
    } else if error == "deref-set requires a mutable reference" {
        (&["deref-set"][..], 1)
    } else if error == "cannot mutably borrow through an immutable reference" {
        (&["borrow-mut"][..], 1)
    } else {
        return None;
    };
    find_operator_argument(expression, operators, argument)
}

fn find_operator_argument(
    expression: &crate::SpannedExpr,
    operators: &[&str],
    argument: usize,
) -> Option<crate::Span> {
    if let Expr::List(items) = &expression.expr {
        if let Some(Expr::Symbol(head)) = items.first() {
            let normalized = head.strip_prefix('#').unwrap_or(head);
            if operators.iter().any(|operator| {
                normalized == *operator
                    || normalized.split('.').skip(1).any(|part| part == *operator)
            }) {
                if let Some(argument) = expression.children.get(argument) {
                    return Some(argument.span);
                }
            }
        }
    }
    expression
        .children
        .iter()
        .find_map(|child| find_operator_argument(child, operators, argument))
}

fn source_operator_span(expression: &crate::SpannedExpr, target: &str) -> Option<crate::Span> {
    if let Expr::List(items) = &expression.expr {
        if let Some(Expr::Symbol(head)) = items.first() {
            let normalized = head.strip_prefix('#').unwrap_or(head);
            if normalized == target || normalized.split('.').skip(1).any(|part| part == target) {
                return expression.children.first().map(|head| head.span);
            }
            if matches!(head.as_str(), "#call" | "call")
                && matches!(items.get(1), Some(Expr::Symbol(name)) if name == target)
            {
                return expression.children.get(1).map(|name| name.span);
            }
        }
    }
    expression
        .children
        .iter()
        .find_map(|child| source_operator_span(child, target))
}

fn typed_operator_qualifier<'a>(
    expression: &'a crate::SpannedExpr,
    operator: &str,
) -> Option<&'a str> {
    if let Expr::List(items) = &expression.expr {
        if let Some(Expr::Symbol(head)) = items.first() {
            if let Some(qualified) = head.strip_prefix('#') {
                if let Some((qualifier, operation)) = qualified.split_once('.') {
                    if operation.split('.').next() == Some(operator) {
                        return Some(qualifier);
                    }
                }
            }
        }
    }
    expression
        .children
        .iter()
        .find_map(|child| typed_operator_qualifier(child, operator))
}

fn expression_with_type_hint(
    expression: &crate::SpannedExpr,
    wanted: &str,
    source: &str,
) -> Option<crate::Span> {
    fn has_type_hint(expression: &crate::SpannedExpr, wanted: &str, source: &str) -> bool {
        let text = source
            .get(expression.span.start..expression.span.end)
            .unwrap_or("");
        let primitive = match &expression.expr {
            Expr::Symbol(name) if matches!(name.as_str(), "true" | "false") => "Bool",
            Expr::Char(_) => "Char",
            Expr::Float(_) if text.ends_with("f32") => "F32",
            Expr::Float(_) => "F64",
            Expr::Integer(_) if text.ends_with("i8") => "I8",
            Expr::Integer(_) if text.ends_with("i16") => "I16",
            Expr::Integer(_) if text.ends_with("i32") => "I32",
            Expr::Integer(_) if text.ends_with("i64") => "I64",
            Expr::Integer(_) if text.ends_with("i128") => "I128",
            Expr::Integer(_) if text.ends_with("isize") => "Isize",
            Expr::UnsignedInteger(_) if text.ends_with("u8") => "U8",
            Expr::UnsignedInteger(_) if text.ends_with("u16") => "U16",
            Expr::UnsignedInteger(_) if text.ends_with("u32") => "U32",
            Expr::UnsignedInteger(_) if text.ends_with("u64") => "U64",
            Expr::UnsignedInteger(_) if text.ends_with("u128") => "U128",
            Expr::UnsignedInteger(_) if text.ends_with("usize") => "Usize",
            _ => "",
        };
        if primitive == wanted {
            return true;
        }
        let Expr::List(items) = &expression.expr else {
            return false;
        };
        let Some(Expr::Symbol(head)) = items.first() else {
            return false;
        };
        if head == "#literal" {
            return matches!(items.get(1), Some(Expr::Symbol(ty)) if ty.eq_ignore_ascii_case(wanted));
        }
        // A function call's result type is not encoded in its syntax. Do not
        // mistake one of its arguments for the result when pinpointing a
        // mismatch reported by the caller.
        if matches!(head.as_str(), "#call" | "call") {
            return false;
        }
        head.strip_prefix('#')
            .and_then(|qualified| qualified.split_once('.'))
            .is_some_and(|(qualifier, _)| {
                is_builtin_scalar_name(qualifier) && qualifier.eq_ignore_ascii_case(wanted)
            })
    }

    if has_type_hint(expression, wanted, source) {
        return Some(expression.span);
    }
    let Expr::List(items) = &expression.expr else {
        return None;
    };
    let Some(Expr::Symbol(head)) = items.first() else {
        return None;
    };
    if matches!(head.as_str(), "#call" | "call") {
        return None;
    }
    let is_typed_scalar_operator = head
        .strip_prefix('#')
        .and_then(|qualified| qualified.split_once('.'))
        .is_some_and(|(qualifier, _)| is_builtin_scalar_name(qualifier));
    if !is_typed_scalar_operator {
        return expression
            .children
            .iter()
            .filter_map(|child| expression_with_type_hint(child, wanted, source))
            .min_by_key(|span| span.end.saturating_sub(span.start));
    }
    expression
        .children
        .iter()
        .filter_map(|child| expression_with_type_hint(child, wanted, source))
        .min_by_key(|span| span.end.saturating_sub(span.start))
}

fn is_builtin_scalar_name(name: &str) -> bool {
    matches!(
        name,
        "i8" | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "f32"
            | "f64"
            | "bool"
    )
}

fn expression_value_span(statement: &crate::SpannedExpr) -> crate::Span {
    crate::source_value_span(statement)
}

fn first_symbol_span(expression: &crate::SpannedExpr, target: &str) -> Option<crate::Span> {
    if matches!(&expression.expr, Expr::Symbol(name) if name == target) {
        return Some(expression.span);
    }
    let Expr::List(items) = &expression.expr else {
        return None;
    };
    let children = &expression.children[..];
    let start = usize::from(matches!(items.first(), Some(Expr::Symbol(_))));
    children
        .iter()
        .skip(start)
        .find_map(|child| first_symbol_span(child, target))
}

fn function_name_span(program: &Program, name: &str) -> Option<crate::Span> {
    program
        .declaration_expressions
        .get(name)?
        .children
        .get(1)
        .map(|expression| expression.span)
}

fn declaration_name_span(program: &Program, name: &str) -> Option<crate::Span> {
    program
        .declaration_occurrences
        .get(name)?
        .get(1)?
        .children
        .get(1)
        .map(|expression| expression.span)
}

fn unsafe_impl_type_span(
    program: &Program,
    type_name: &str,
    property: ThreadProperty,
    occurrence: usize,
) -> Option<crate::Span> {
    program
        .declaration_occurrences
        .get(&format!("$unsafe-impl:{property:?}:{type_name}"))?
        .get(occurrence)
        .and_then(|expression| first_symbol_span(expression, type_name))
}

fn task_type_in_declaration_span(
    program: &Program,
    declaration: &str,
    tasks: &HashMap<String, String>,
    aliases: &HashMap<String, Type>,
    enum_fields: &HashMap<String, Vec<Type>>,
) -> Option<crate::Span> {
    let expression = program.declaration_expressions.get(declaration)?;
    let head = match &expression.children.first()?.expr {
        Expr::Symbol(head) => head.trim_start_matches('#'),
        _ => return None,
    };
    let children = &expression.children;
    let mut candidates = Vec::new();
    match head {
        "struct" => {
            for field in &children.last()?.children {
                if let Some(ty) = field.children.get(1) {
                    candidates.push(ty);
                }
            }
        }
        "enum" => {
            for variant in &children.last()?.children {
                candidates.extend(variant.children.iter().skip(1));
            }
        }
        "type" => candidates.push(children.last()?),
        "let" | "let-mut" | "static" | "static-mut" => candidates.push(children.get(2)?),
        "fn" | "extern-fn" => {
            let start = if head == "extern-fn" { 3 } else { 2 };
            for parameter in &children.get(start)?.children {
                if let Some(ty) = parameter.children.get(1) {
                    candidates.push(ty);
                }
            }
            candidates.push(children.get(start + 1)?);
        }
        _ => return None,
    }
    // Walk only type positions, in source order. A field/parameter/variant
    // selector that happens to share a task's name must never be selected.
    candidates.into_iter().find_map(|node| {
        let ty = parse_type(Some(&crate::normalize_keywords(node.expr.clone()))).ok()?;
        let resolved = resolve_type(&ty, aliases).ok()?;
        if !type_mentions_task(&resolved, tasks, enum_fields, &mut HashSet::new()) {
            return None;
        }
        fn direct(
            node: &crate::SpannedExpr,
            tasks: &HashMap<String, String>,
        ) -> Option<crate::Span> {
            if matches!(&node.expr, Expr::Symbol(name) if tasks.contains_key(name)) {
                return Some(node.span);
            }
            node.children.iter().find_map(|child| direct(child, tasks))
        }
        Some(direct(node, tasks).unwrap_or(node.span))
    })
}

fn first_unresolved_type<'a>(
    ty: &'a Type,
    declared_types: &HashSet<&String>,
    aliases: &HashMap<String, Type>,
) -> Option<&'a str> {
    match ty {
        Type::Named(name) if !declared_types.contains(name) && !aliases.contains_key(name) => {
            Some(name)
        }
        Type::Reference { target, .. }
        | Type::RawPointer { target, .. }
        | Type::Cell(target)
        | Type::Slice(target)
        | Type::MutableSlice(target)
        | Type::Atomic(target)
        | Type::Array(target, _) => first_unresolved_type(target, declared_types, aliases),
        Type::Tuple(fields) => fields
            .iter()
            .find_map(|field| first_unresolved_type(field, declared_types, aliases)),
        _ => None,
    }
}

fn worker_parameter_type_span(
    program: &Program,
    worker: &str,
    parameter_index: usize,
    unknown_type: &str,
) -> Option<crate::Span> {
    program
        .declaration_expressions
        .get(worker)?
        .children
        .get(2)?
        .children
        .get(parameter_index)?
        .children
        .get(1)
        .and_then(|ty| first_symbol_span(ty, unknown_type))
}

fn worker_parameter_span(
    program: &Program,
    worker: &str,
    parameter_index: usize,
) -> Option<crate::Span> {
    program
        .declaration_expressions
        .get(worker)?
        .children
        .get(2)?
        .children
        .get(parameter_index)?
        .children
        .get(1)
        .map(|ty| ty.span)
}

fn worker_return_type_span(
    program: &Program,
    worker: &str,
    unknown_type: &str,
) -> Option<crate::Span> {
    program
        .declaration_expressions
        .get(worker)?
        .children
        .get(3)
        .and_then(|ty| first_symbol_span(ty, unknown_type))
}

fn worker_return_span(program: &Program, worker: &str) -> Option<crate::Span> {
    program
        .declaration_expressions
        .get(worker)?
        .children
        .get(3)
        .map(|ty| ty.span)
}

fn record_generated_invocation(
    program: &Program,
    diagnostic_span: &Option<crate::Span>,
    diagnostic_labels: &mut Vec<(crate::Span, String)>,
) {
    if let Some(invocation) =
        diagnostic_span.and_then(|span| program.generated_source_invocations.get(&span.source_id))
    {
        diagnostic_labels.push((*invocation, "generated from this invocation".into()));
    }
}

fn declared_type_span(statement: &crate::SpannedExpr, target: &str) -> Option<crate::Span> {
    let Expr::List(items) = &statement.expr else {
        return None;
    };
    if !matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#let" | "#let-mut" | "#let-else"))
    {
        return None;
    }
    statement
        .children
        .get(2)
        .filter(|ty| matches!(&ty.expr, Expr::Symbol(name) if name == target))
        .map(|ty| ty.span)
}

fn type_pattern_symbol_span(expression: &crate::SpannedExpr, target: &str) -> Option<crate::Span> {
    fn inclusive_symbol_span(expression: &crate::SpannedExpr, target: &str) -> Option<crate::Span> {
        if matches!(&expression.expr, Expr::Symbol(name) if name == target) {
            return Some(expression.span);
        }
        expression
            .children
            .iter()
            .find_map(|child| inclusive_symbol_span(child, target))
    }

    if let Expr::List(items) = &expression.expr {
        if matches!(items.first(), Some(Expr::Symbol(operator)) if operator.strip_prefix('#').unwrap_or(operator) == "match")
        {
            for arm in expression.children.iter().skip(2) {
                if let Some(pattern) = arm.children.first() {
                    if let Some(span) = inclusive_symbol_span(pattern, target) {
                        return Some(span);
                    }
                }
            }
        } else if matches!(items.first(), Some(Expr::Symbol(operator)) if matches!(operator.strip_prefix('#').unwrap_or(operator), "let-else" | "if-let" | "while-let"))
        {
            if let Some(pattern) = expression.children.get(1) {
                if let Some(span) = inclusive_symbol_span(pattern, target) {
                    return Some(span);
                }
            }
        }
    }
    expression
        .children
        .iter()
        .find_map(|child| type_pattern_symbol_span(child, target))
}

fn last_match_pattern_symbol_span(
    expression: &crate::SpannedExpr,
    target: &str,
) -> Option<crate::Span> {
    fn collect_symbols(
        expression: &crate::SpannedExpr,
        target: &str,
        spans: &mut Vec<crate::Span>,
    ) {
        if matches!(&expression.expr, Expr::Symbol(name) if name == target) {
            spans.push(expression.span);
        }
        for child in &expression.children {
            collect_symbols(child, target, spans);
        }
    }
    fn collect_patterns(
        expression: &crate::SpannedExpr,
        target: &str,
        spans: &mut Vec<crate::Span>,
    ) {
        if let Expr::List(items) = &expression.expr {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator.strip_prefix('#').unwrap_or(operator) == "match")
            {
                for arm in expression.children.iter().skip(2) {
                    if let Some(pattern) = arm.children.first() {
                        collect_symbols(pattern, target, spans);
                    }
                }
            }
        }
        for child in &expression.children {
            collect_patterns(child, target, spans);
        }
    }
    let mut spans = Vec::new();
    collect_patterns(expression, target, &mut spans);
    spans.into_iter().max_by_key(|span| span.start)
}

fn last_match_pattern_integer_span(
    expression: &crate::SpannedExpr,
    target: u128,
) -> Option<crate::Span> {
    fn collect_integers(
        expression: &crate::SpannedExpr,
        target: u128,
        spans: &mut Vec<crate::Span>,
    ) {
        if matches!(&expression.expr, Expr::Integer(value) if *value >= 0 && *value as u128 == target)
            || matches!(&expression.expr, Expr::UnsignedInteger(value) if *value == target)
        {
            spans.push(expression.span);
        }
        for child in &expression.children {
            collect_integers(child, target, spans);
        }
    }
    fn collect_patterns(
        expression: &crate::SpannedExpr,
        target: u128,
        spans: &mut Vec<crate::Span>,
    ) {
        if let Expr::List(items) = &expression.expr {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator.strip_prefix('#').unwrap_or(operator) == "match")
            {
                for arm in expression.children.iter().skip(2) {
                    if let Some(pattern) = arm.children.first() {
                        collect_integers(pattern, target, spans);
                    }
                }
            }
        }
        for child in &expression.children {
            collect_patterns(child, target, spans);
        }
    }
    let mut spans = Vec::new();
    collect_patterns(expression, target, &mut spans);
    spans.into_iter().max_by_key(|span| span.start)
}

fn last_match_pattern_char_span(expression: &crate::SpannedExpr) -> Option<crate::Span> {
    fn collect_chars(expression: &crate::SpannedExpr, spans: &mut Vec<crate::Span>) {
        if matches!(expression.expr, Expr::Char(_)) {
            spans.push(expression.span);
        }
        for child in &expression.children {
            collect_chars(child, spans);
        }
    }
    fn collect_patterns(expression: &crate::SpannedExpr, spans: &mut Vec<crate::Span>) {
        if let Expr::List(items) = &expression.expr {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator.strip_prefix('#').unwrap_or(operator) == "match")
            {
                for arm in expression.children.iter().skip(2) {
                    if let Some(pattern) = arm.children.first() {
                        collect_chars(pattern, spans);
                    }
                }
            }
        }
        for child in &expression.children {
            collect_patterns(child, spans);
        }
    }
    let mut spans = Vec::new();
    collect_patterns(expression, &mut spans);
    spans.into_iter().max_by_key(|span| span.start)
}

fn match_range_pattern_span(expression: &crate::SpannedExpr, error: &str) -> Option<crate::Span> {
    fn collect(expression: &crate::SpannedExpr, error: &str, spans: &mut Vec<crate::Span>) {
        if let Expr::List(items) = &expression.expr {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator.strip_prefix('#').unwrap_or(operator) == "range")
            {
                let span = if error.contains("lower bound exceeds upper bound") {
                    expression
                        .children
                        .get(2)
                        .map_or(expression.span, |upper| upper.span)
                } else {
                    expression.span
                };
                spans.push(span);
            }
        }
        for child in &expression.children {
            collect(child, error, spans);
        }
    }
    let mut spans = Vec::new();
    collect(expression, error, &mut spans);
    spans.into_iter().min_by_key(|span| span.start)
}

fn statement_type(
    statement: &Statement,
    variables: &mut HashMap<String, Type>,
    mutable: &mut HashSet<String>,
    functions: &HashMap<String, Signature>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    return_type: &Type,
    aliases: &HashMap<String, Type>,
    in_loop: bool,
) -> Result<Type, String> {
    match statement {
        Statement::Let {
            name,
            ty,
            value,
            mutable: is_mutable,
        } => {
            if variables.contains_key(name) {
                return Err(format!("duplicate local '{name}'"));
            }
            let binding_type = resolve_type(ty, aliases)?;
            let actual = expression(
                value,
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&binding_type),
            )?;
            require_type(&actual, &binding_type, &format!("let '{name}'"))?;
            variables.insert(name.clone(), binding_type);
            if *is_mutable {
                mutable.insert(name.clone());
            }
            Ok(Type::Unit)
        }
        Statement::Labeled { label, statement } => {
            let marker = format!("\0lim-label:{label}");
            if mutable.contains(&marker) {
                return Err(format!("duplicate loop label '{label}'"));
            }
            let mut labeled_mutable = mutable.clone();
            labeled_mutable.insert(marker);
            statement_type(
                statement,
                variables,
                &mut labeled_mutable,
                functions,
                structs,
                enums,
                return_type,
                aliases,
                in_loop,
            )
        }
        Statement::Destructure {
            pattern,
            ty,
            value,
            mutable: is_mutable,
        } => {
            let binding_type = resolve_type(ty, aliases)?;
            let actual = expression(
                value,
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&binding_type),
            )?;
            require_type(&actual, &binding_type, "destructuring let")?;
            for (name, field_type) in check_destructure_pattern(pattern, &binding_type, structs)? {
                if variables.contains_key(&name) {
                    return Err(format!("duplicate local '{name}'"));
                }
                variables.insert(name.clone(), field_type);
                if *is_mutable {
                    mutable.insert(name);
                }
            }
            Ok(Type::Unit)
        }
        Statement::LetElse {
            pattern,
            ty,
            value,
            else_body,
        } => {
            let binding_type = resolve_type(ty, aliases)?;
            let actual = expression(
                value,
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&binding_type),
            )?;
            require_type(&actual, &binding_type, "let-else value")?;
            if !else_body.last().is_some_and(statement_diverges) {
                return Err(
                    "let-else body must diverge with return, break, continue, panic, or unreachable"
                        .into(),
                );
            }
            let mut else_variables = variables.clone();
            let mut else_mutable = mutable.clone();
            for statement in else_body {
                statement_type(
                    statement,
                    &mut else_variables,
                    &mut else_mutable,
                    functions,
                    structs,
                    enums,
                    return_type,
                    aliases,
                    in_loop,
                )?;
            }
            for (name, field_type) in
                check_let_else_pattern(pattern, &binding_type, variables, structs, enums)?
            {
                if variables.contains_key(&name) {
                    return Err(format!("duplicate local '{name}'"));
                }
                variables.insert(name, field_type);
            }
            Ok(Type::Unit)
        }
        Statement::Assign { name, value } => {
            let ty = variables
                .get(name)
                .ok_or_else(|| format!("unknown variable '{name}'"))?
                .clone();
            if !mutable.contains(name) {
                return Err(format!("cannot assign to immutable variable '{name}'"));
            }
            if contains_reference_type(&ty, structs, enums, &mut HashSet::new()) {
                return Err(format!(
                    "cannot replace '{name}' because its type retains references"
                ));
            }
            let actual = expression(
                value,
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&ty),
            )?;
            require_type(&actual, &ty, &format!("assignment to '{name}'"))?;
            Ok(Type::Unit)
        }
        Statement::ArrayAssign { name, index, value } => {
            let ty = variables
                .get(name)
                .ok_or_else(|| format!("unknown variable '{name}'"))?
                .clone();
            if !mutable.contains(name) {
                return Err(format!("cannot assign to immutable variable '{name}'"));
            }
            let Type::Array(element, length) = ty else {
                return Err(format!("'{name}' is not an array"));
            };
            if contains_reference_type(&element, structs, enums, &mut HashSet::new()) {
                return Err(format!(
                    "cannot replace reference-containing elements of '{name}'"
                ));
            }
            check_index(
                index, length, variables, functions, structs, enums, mutable, aliases,
            )?;
            let actual = expression(
                value,
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&element),
            )?;
            require_type(&actual, &element, &format!("array assignment to '{name}'"))?;
            Ok(Type::Unit)
        }
        Statement::FieldAssign { name, field, value } => {
            let ty = variables
                .get(name)
                .ok_or_else(|| format!("unknown variable '{name}'"))?
                .clone();
            if !mutable.contains(name) {
                return Err(format!("cannot assign to immutable variable '{name}'"));
            }
            let Type::Named(struct_name) = ty else {
                return Err(format!("'{name}' is not a struct"));
            };
            let fields = structs
                .get(&struct_name)
                .ok_or_else(|| format!("unknown struct '{struct_name}'"))?;
            let field_type = fields
                .iter()
                .find(|field_info| field_info.name == *field)
                .map(|field_info| field_info.ty.clone())
                .ok_or_else(|| format!("struct '{struct_name}' has no field '{field}'"))?;
            if contains_reference_type(&field_type, structs, enums, &mut HashSet::new()) {
                return Err(format!(
                    "reference field '{field}' in '{struct_name}' cannot be replaced"
                ));
            }
            let actual = expression(
                value,
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&field_type),
            )?;
            require_type(
                &actual,
                &field_type,
                &format!("assignment to field '{field}'"),
            )?;
            Ok(Type::Unit)
        }
        Statement::EnumPayloadAssign {
            name,
            variant,
            index,
            value,
        } => {
            let ty = variables
                .get(name)
                .ok_or_else(|| format!("unknown variable '{name}'"))?
                .clone();
            if !mutable.contains(name) {
                return Err(format!("cannot assign to immutable variable '{name}'"));
            }
            let Type::Named(enum_name) = ty else {
                return Err(format!("'{name}' is not an enum"));
            };
            let variants = enums
                .get(&enum_name)
                .ok_or_else(|| format!("unknown enum '{enum_name}'"))?;
            let enum_variant = variants
                .iter()
                .find(|candidate| candidate.name == *variant)
                .ok_or_else(|| format!("enum '{enum_name}' has no variant '{variant}'"))?;
            let field_type = enum_variant.fields.get(*index).ok_or_else(|| {
                format!("variant '{variant}' has no payload field at index {index}")
            })?;
            if contains_reference_type(field_type, structs, enums, &mut HashSet::new()) {
                return Err(format!(
                    "reference payload '{variant}[{index}]' cannot be replaced"
                ));
            }
            let actual = expression(
                value,
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(field_type),
            )?;
            require_type(
                &actual,
                field_type,
                &format!("assignment to enum payload '{variant}[{index}]'"),
            )?;
            Ok(Type::Unit)
        }
        Statement::TupleAssign { name, index, value } => {
            let ty = variables
                .get(name)
                .ok_or_else(|| format!("unknown variable '{name}'"))?
                .clone();
            if !mutable.contains(name) {
                return Err(format!("cannot assign to immutable variable '{name}'"));
            }
            let Type::Tuple(fields) = ty else {
                return Err(format!("'{name}' is not a tuple"));
            };
            let field_type = fields
                .get(*index)
                .ok_or_else(|| format!("tuple field index {index} is out of bounds"))?;
            if contains_reference_type(field_type, structs, enums, &mut HashSet::new()) {
                return Err(format!(
                    "cannot replace reference-containing tuple field {index}"
                ));
            }
            let actual = expression(
                value,
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(field_type),
            )?;
            require_type(
                &actual,
                field_type,
                &format!("assignment to tuple field {index}"),
            )?;
            Ok(Type::Unit)
        }
        Statement::While { condition, body } => {
            if body.iter().any(statement_has_value_break) {
                return Err("break with a value is only valid in a loop expression".into());
            }
            let actual = expression(
                condition,
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&Type::Bool),
            )?;
            require_type(&actual, &Type::Bool, "while condition")?;
            let mut loop_variables = variables.clone();
            let mut loop_mutable = mutable.clone();
            for nested in body {
                statement_type(
                    nested,
                    &mut loop_variables,
                    &mut loop_mutable,
                    functions,
                    structs,
                    enums,
                    return_type,
                    aliases,
                    true,
                )?;
            }
            Ok(Type::Unit)
        }
        Statement::Loop { body } => {
            if body.iter().any(statement_has_value_break) {
                return Err("break with a value is only valid in a loop expression".into());
            }
            let mut loop_variables = variables.clone();
            let mut loop_mutable = mutable.clone();
            for nested in body {
                statement_type(
                    nested,
                    &mut loop_variables,
                    &mut loop_mutable,
                    functions,
                    structs,
                    enums,
                    return_type,
                    aliases,
                    true,
                )?;
            }
            Ok(Type::Unit)
        }
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            if body.iter().any(statement_has_value_break) {
                return Err("break with a value is only valid in a loop expression".into());
            }
            let mut loop_variables = variables.clone();
            let mut loop_mutable = mutable.clone();
            statement_type(
                init,
                &mut loop_variables,
                &mut loop_mutable,
                functions,
                structs,
                enums,
                return_type,
                aliases,
                false,
            )?;
            let actual = expression(
                condition,
                &loop_variables,
                functions,
                structs,
                enums,
                &loop_mutable,
                aliases,
                Some(&Type::Bool),
            )?;
            require_type(&actual, &Type::Bool, "for condition")?;
            for nested in body {
                statement_type(
                    nested,
                    &mut loop_variables,
                    &mut loop_mutable,
                    functions,
                    structs,
                    enums,
                    return_type,
                    aliases,
                    true,
                )?;
            }
            statement_type(
                step,
                &mut loop_variables,
                &mut loop_mutable,
                functions,
                structs,
                enums,
                return_type,
                aliases,
                true,
            )?;
            Ok(Type::Unit)
        }
        Statement::BreakValue(value) => {
            if !mutable.contains(LOOP_VALUE_CONTEXT) {
                return Err("break with a value used outside a loop".into());
            }
            expression(
                value, variables, functions, structs, enums, mutable, aliases, None,
            )
        }
        Statement::BreakToValue { label, value } => {
            if !mutable.contains(&format!("\0lim-value-label:{label}")) {
                return Err(format!(
                    "value break used with inactive or non-value label '{label}'"
                ));
            }
            expression(
                value, variables, functions, structs, enums, mutable, aliases, None,
            )
        }
        Statement::BreakTo(label) | Statement::ContinueTo(label) => {
            if mutable.contains(&format!("\0lim-label:{label}")) {
                Ok(Type::Unit)
            } else {
                Err(format!("unknown or inactive loop label '{label}'"))
            }
        }
        Statement::Break | Statement::Continue => {
            if in_loop {
                Ok(Type::Unit)
            } else {
                Err("break or continue used outside a loop".into())
            }
        }
        Statement::Return(value) => {
            let actual = match value {
                Some(value) => expression(
                    value,
                    variables,
                    functions,
                    structs,
                    enums,
                    mutable,
                    aliases,
                    Some(return_type),
                )?,
                None => Type::Unit,
            };
            require_type(&actual, return_type, "return statement")?;
            Ok(return_type.clone())
        }
        Statement::Expr(value) => expression(
            value, variables, functions, structs, enums, mutable, aliases, None,
        ),
    }
}

fn statement_diverges(statement: &Statement) -> bool {
    match statement {
        Statement::Return(_) | Statement::Break | Statement::Continue => true,
        Statement::Labeled { statement, .. } => statement_diverges(statement),
        Statement::Expr(Expr::List(items)) => matches!(
            items.first(),
            Some(Expr::Symbol(name)) if matches!(name.as_str(), "panic" | "unreachable")
        ),
        _ => false,
    }
}

fn check_destructure_pattern(
    pattern: &Expr,
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
) -> Result<Vec<(String, Type)>, String> {
    let Expr::List(items) = pattern else {
        return Err("destructuring pattern must be a tuple or struct constructor".into());
    };
    let Some(Expr::Symbol(constructor)) = items.first() else {
        return Err("destructuring pattern must start with a constructor".into());
    };
    let fields = match ty {
        Type::Tuple(fields) if constructor == "tuple" => fields.clone(),
        Type::Array(element, length) if constructor == "array" => {
            vec![*element.clone(); *length]
        }
        Type::Named(name) if name == constructor => structs
            .get(name)
            .ok_or_else(|| format!("unknown struct '{name}'"))?
            .iter()
            .map(|field| field.ty.clone())
            .collect(),
        _ => return Err("destructuring pattern does not match its declared type".into()),
    };
    if items.len() - 1 != fields.len() {
        return Err(format!(
            "destructuring pattern expects {} fields",
            fields.len()
        ));
    }
    let mut bindings = Vec::new();
    for (binding, field_type) in items[1..].iter().zip(fields) {
        match binding {
            Expr::Symbol(binding) if binding == "_" => {}
            Expr::Symbol(binding) => bindings.push((binding.clone(), field_type)),
            Expr::List(_) => {
                bindings.extend(check_destructure_pattern(binding, &field_type, structs)?)
            }
            _ => return Err("destructuring fields must be bindings or nested patterns".into()),
        }
    }
    Ok(bindings)
}

fn check_let_else_pattern(
    pattern: &Expr,
    ty: &Type,
    variables: &HashMap<String, Type>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
) -> Result<Vec<(String, Type)>, String> {
    let mut bindings = variables.clone();
    if let Type::Named(enum_name) = ty {
        if let Some(variants) = enums.get(enum_name) {
            if let Expr::List(items) = pattern {
                if items.len() >= 2
                    && matches!(items.first(), Some(Expr::Symbol(name)) if name == "or")
                {
                    for alternative in &items[1..] {
                        let (name, payload_patterns): (&str, Vec<&Expr>) = match alternative {
                            Expr::Symbol(name) => (name, Vec::new()),
                            Expr::List(items) if !items.is_empty() => {
                                let Expr::Symbol(name) = &items[0] else {
                                    return Err(
                                        "enum let-else alternatives must be variants".into()
                                    );
                                };
                                (name, items[1..].iter().collect())
                            }
                            _ => return Err("enum let-else alternatives must be variants".into()),
                        };
                        let Some(variant) = variants.iter().find(|variant| variant.name == name)
                        else {
                            return Err(format!("unknown enum variant '{name}'"));
                        };
                        if !payload_patterns.is_empty()
                            && payload_patterns.len() != variant.fields.len()
                        {
                            return Err(format!(
                                "variant '{name}' expects {} payload patterns",
                                variant.fields.len()
                            ));
                        }
                        let mut alternative_variables = variables.clone();
                        for (binding, field_type) in payload_patterns.iter().zip(&variant.fields) {
                            check_enum_payload_pattern(
                                binding,
                                field_type,
                                &mut alternative_variables,
                                variables,
                                structs,
                            )?;
                        }
                        if alternative_variables.len() != variables.len() {
                            return Err("enum let-else alternatives cannot bind values".into());
                        }
                    }
                    return Ok(Vec::new());
                }
            }
            let (variant_name, payload_patterns): (&str, Vec<&Expr>) = match pattern {
                Expr::Symbol(name) => (name, Vec::new()),
                Expr::List(items) if !items.is_empty() => {
                    let Expr::Symbol(name) = &items[0] else {
                        return Err("let-else enum pattern must start with a variant".into());
                    };
                    (name, items[1..].iter().collect())
                }
                _ => return Err("let-else pattern must be a variant constructor".into()),
            };
            if variant_name == "_" {
                return Ok(Vec::new());
            }
            let variant = variants
                .iter()
                .find(|variant| variant.name == variant_name)
                .ok_or_else(|| format!("'{variant_name}' is not a variant of '{enum_name}'"))?;
            if payload_patterns.len() != variant.fields.len() {
                return Err(format!(
                    "variant '{variant_name}' expects {} payload patterns",
                    variant.fields.len()
                ));
            }
            for (binding, field_type) in payload_patterns.iter().zip(&variant.fields) {
                check_enum_payload_pattern(binding, field_type, &mut bindings, variables, structs)?;
            }
            return Ok(bindings
                .into_iter()
                .filter(|(name, _)| !variables.contains_key(name))
                .collect());
        }
    }
    check_aggregate_pattern(pattern, ty, &mut bindings, variables, structs)?;
    Ok(bindings
        .into_iter()
        .filter(|(name, _)| !variables.contains_key(name))
        .collect())
}

fn expression(
    value: &Expr,
    variables: &HashMap<String, Type>,
    functions: &HashMap<String, Signature>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    mutable: &HashSet<String>,
    aliases: &HashMap<String, Type>,
    expected: Option<&Type>,
) -> Result<Type, String> {
    match value {
        Expr::Integer(value) => {
            let ty = expected
                .filter(|ty| is_integer(ty))
                .cloned()
                .unwrap_or(Type::I64);
            if !fits_integer(*value, &ty) {
                return Err(format!("integer literal {value} does not fit in {ty:?}"));
            }
            Ok(ty)
        }
        Expr::UnsignedInteger(value) => {
            let ty = expected
                .filter(|ty| is_integer(ty))
                .cloned()
                .unwrap_or(Type::U128);
            if !fits_unsigned_integer(*value, &ty) {
                return Err(format!("integer literal {value} does not fit in {ty:?}"));
            }
            Ok(ty)
        }
        Expr::Float(value) => {
            let ty = expected
                .filter(|ty| matches!(ty, Type::F32 | Type::F64))
                .cloned()
                .unwrap_or(Type::F64);
            let finite = if matches!(ty, Type::F32) {
                value
                    .parse::<f32>()
                    .map_err(|_| format!("invalid floating-point literal '{value}'"))?
                    .is_finite()
            } else {
                value
                    .parse::<f64>()
                    .map_err(|_| format!("invalid floating-point literal '{value}'"))?
                    .is_finite()
            };
            if !finite {
                return Err(format!(
                    "floating-point literal '{value}' is not finite for {ty:?}"
                ));
            }
            Ok(ty)
        }
        Expr::Char(_) => Ok(Type::Char),
        Expr::Symbol(name) if name == "true" || name == "false" => Ok(Type::Bool),
        Expr::Symbol(name) => variables
            .get(name)
            .cloned()
            .or_else(|| enum_variant_type(name, enums))
            .ok_or_else(|| format!("unknown variable or enum variant '{name}'")),
        Expr::String(value) => Ok(Type::Array(Box::new(Type::Char), value.chars().count())),
        Expr::Block(statements) => {
            let mut block_variables = variables.clone();
            let mut block_mutable = mutable.clone();
            let block_return = expected.cloned().unwrap_or(Type::Unit);
            let mut result = Type::Unit;
            for (index, statement) in statements.iter().enumerate() {
                result = if index + 1 == statements.len() {
                    if let Statement::Expr(value) = statement {
                        expression(
                            value,
                            &block_variables,
                            functions,
                            structs,
                            enums,
                            &block_mutable,
                            aliases,
                            expected,
                        )?
                    } else {
                        statement_type(
                            statement,
                            &mut block_variables,
                            &mut block_mutable,
                            functions,
                            structs,
                            enums,
                            &block_return,
                            aliases,
                            false,
                        )?
                    }
                } else {
                    statement_type(
                        statement,
                        &mut block_variables,
                        &mut block_mutable,
                        functions,
                        structs,
                        enums,
                        &block_return,
                        aliases,
                        false,
                    )?
                };
            }
            Ok(result)
        }
        Expr::Loop(statements) => {
            let mut loop_variables = variables.clone();
            let mut loop_mutable = mutable.clone();
            loop_mutable.insert(LOOP_VALUE_CONTEXT.to_owned());
            let mut result_type = None;
            for statement in statements {
                let has_value_break = statement_has_value_break(statement);
                let actual = if let Statement::BreakValue(value)
                | Statement::BreakToValue { value, .. } = statement
                {
                    expression(
                        value,
                        &loop_variables,
                        functions,
                        structs,
                        enums,
                        &loop_mutable,
                        aliases,
                        expected,
                    )?
                } else {
                    statement_type(
                        statement,
                        &mut loop_variables,
                        &mut loop_mutable,
                        functions,
                        structs,
                        enums,
                        &expected.cloned().unwrap_or(Type::Unit),
                        aliases,
                        true,
                    )?
                };
                if has_value_break {
                    if let Some(previous) = &result_type {
                        result_type = Some(merge_types(previous, &actual, "loop break values")?);
                    } else {
                        result_type = Some(actual);
                    }
                }
            }
            let result = result_type.unwrap_or(Type::Unit);
            if let Some(expected) = expected {
                require_type(&result, expected, "loop expression")?;
            }
            Ok(result)
        }
        Expr::Labeled {
            label,
            expression: loop_expression,
        } => {
            if !matches!(loop_expression.as_ref(), Expr::Loop(_)) {
                return Err("expression label must wrap a value-producing loop".into());
            }
            let marker = format!("\0lim-label:{label}");
            if mutable.contains(&marker) {
                return Err(format!("duplicate loop label '{label}'"));
            }
            let mut labeled_mutable = mutable.clone();
            labeled_mutable.insert(marker);
            labeled_mutable.insert(format!("\0lim-value-label:{label}"));
            expression(
                loop_expression,
                variables,
                functions,
                structs,
                enums,
                &labeled_mutable,
                aliases,
                expected,
            )
        }
        Expr::At
        | Expr::Quote(_)
        | Expr::QuasiQuote(_)
        | Expr::Unquote(_)
        | Expr::UnquoteSplicing(_) => {
            Err("generated and quoted expressions are not typed yet".into())
        }
        Expr::List(items) => list_expression(
            items, variables, functions, structs, enums, mutable, aliases, expected,
        ),
    }
}

fn statement_has_value_break(statement: &Statement) -> bool {
    match statement {
        Statement::BreakValue(_) | Statement::BreakToValue { .. } => true,
        Statement::Expr(expression) => expression_has_value_break(expression),
        Statement::While { .. } | Statement::Loop { .. } | Statement::For { .. } => false,
        _ => false,
    }
}

fn expression_has_value_break(expression: &Expr) -> bool {
    match expression {
        Expr::Loop(_) | Expr::Labeled { .. } => false,
        Expr::Block(statements) => statements.iter().any(statement_has_value_break),
        Expr::List(items) => {
            if matches!(
                items.first(),
                Some(Expr::Symbol(name))
                    if matches!(name.as_str(), "loop" | "while" | "while-let" | "for" | "for-range")
            ) {
                false
            } else {
                items.iter().any(expression_has_value_break)
            }
        }
        Expr::Quote(value)
        | Expr::QuasiQuote(value)
        | Expr::Unquote(value)
        | Expr::UnquoteSplicing(value) => expression_has_value_break(value),
        _ => false,
    }
}

fn type_contains_thread_task_value(
    ty: &Type,
    functions: &HashMap<String, Signature>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    aliases: &HashMap<String, Type>,
    seen: &mut HashSet<String>,
) -> bool {
    let ty = resolve_type(ty, aliases).unwrap_or_else(|_| ty.clone());
    match &ty {
        Type::Named(name) => {
            functions.contains_key(&format!("{name}-join"))
                || (seen.insert(name.clone())
                    && enums.get(name).is_some_and(|variants| {
                        variants
                            .iter()
                            .flat_map(|variant| &variant.fields)
                            .any(|field| {
                                type_contains_thread_task_value(
                                    field, functions, enums, aliases, seen,
                                )
                            })
                    }))
        }
        Type::Reference { target, .. }
        | Type::RawPointer { target, .. }
        | Type::Cell(target)
        | Type::Array(target, _) => {
            type_contains_thread_task_value(target, functions, enums, aliases, seen)
        }
        Type::Tuple(fields) => fields
            .iter()
            .any(|field| type_contains_thread_task_value(field, functions, enums, aliases, seen)),
        _ => false,
    }
}

fn list_expression(
    items: &[Expr],
    variables: &HashMap<String, Type>,
    functions: &HashMap<String, Signature>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    mutable: &HashSet<String>,
    aliases: &HashMap<String, Type>,
    expected: Option<&Type>,
) -> Result<Type, String> {
    if items.is_empty() {
        return Ok(Type::Unit);
    }
    let Some(Expr::Symbol(operator)) = items.first() else {
        return Err("expression list must start with a symbol".into());
    };
    let raw_operator = operator.as_str();
    if raw_operator.contains('<') && raw_operator.contains('>') && !raw_operator.starts_with('#') {
        return Err(
            "angle-bracket generic calls are not supported; use a concrete generated function"
                .into(),
        );
    }
    let (qualifier, operator, mode) = typed_operator_parts(raw_operator);
    let operator_type = qualifier.map(Type::from_name);
    match operator {
        "clone" => {
            require_arity(operator, items, 2)?;
            let cloned = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, expected,
            )?;
            if type_contains_mutable_reference(&cloned, structs, enums, &mut HashSet::new()) {
                return Err("a mutable reference cannot be cloned".into());
            }
            if type_contains_thread_task_value(
                &cloned,
                functions,
                enums,
                aliases,
                &mut HashSet::new(),
            ) {
                return Err("thread task handles and results cannot be cloned".into());
            }
            if let Type::Named(name) = &cloned {
                if functions.contains_key(&format!("{name}-join")) {
                    return Err(format!("thread task '{name}' cannot be cloned"));
                }
                if let Some(signature) = functions.get(&format!("{name}-clone")) {
                    if signature.parameters != [cloned.clone()] || signature.return_type != cloned {
                        return Err(format!(
                            "'{name}-clone' must take and return exactly one '{name}' value"
                        ));
                    }
                }
            }
            Ok(cloned)
        }
        "drop" | "forget" => {
            require_arity(operator, items, 2)?;
            let forgotten = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            if type_contains_thread_task_value(
                &forgotten,
                functions,
                enums,
                aliases,
                &mut HashSet::new(),
            ) {
                return Err(
                    "thread task values and results cannot be dropped or forgotten; match and join them".into(),
                );
            }
            if let Type::Named(name) = &forgotten {
                if functions.contains_key(&format!("{name}-join")) {
                    return Err(format!(
                        "thread task '{name}' must be joined; it cannot be dropped or forgotten"
                    ));
                }
                let thread_result_task = name
                    .strip_suffix("-spawn-result")
                    .or_else(|| name.strip_suffix("-join-result"));
                if thread_result_task
                    .is_some_and(|task| functions.contains_key(&format!("{task}-spawn")))
                {
                    return Err(format!(
                        "thread result '{name}' must be matched so any task handle is joined"
                    ));
                }
            }
            Ok(Type::Unit)
        }
        "cell" => {
            require_arity(operator, items, 2)?;
            let expected_inner = match expected {
                Some(Type::Cell(inner)) => Some(inner.as_ref()),
                _ => None,
            };
            let inner = expression(
                &items[1],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                expected_inner,
            )?;
            if !is_cell_value_type(&inner, enums) {
                return Err(format!("cell does not support values of type {inner:?}"));
            }
            Ok(Type::Cell(Box::new(inner)))
        }
        "cell-get" => {
            require_arity(operator, items, 2)?;
            match expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )? {
                Type::Cell(inner) => Ok(*inner),
                _ => Err("cell-get requires a cell place".into()),
            }
        }
        "cell-set" => {
            require_arity(operator, items, 3)?;
            let Type::Cell(inner) = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?
            else {
                return Err("cell-set requires a cell place".into());
            };
            let actual = expression(
                &items[2],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&inner),
            )?;
            require_type(&actual, &inner, "cell-set value")?;
            Ok(Type::Unit)
        }
        "-" if items.len() == 2 => {
            let actual = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, expected,
            )?;
            if !is_numeric(&actual) {
                return Err("unary '-' requires a numeric operand".into());
            }
            if let Some(qualifier) = qualifier {
                require_operator_type(qualifier, &actual, raw_operator)?;
                require_arithmetic_mode(operator, mode, raw_operator, &actual)?;
            }
            Ok(actual)
        }
        "+" | "-" | "*" | "/" | "%" | "&" | "|" | "^" | "<<" | ">>" => {
            require_arity(operator, items, 3)?;
            let left = expression(
                &items[1],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                operator_type.as_ref().or(expected),
            )?;
            let right = expression(
                &items[2],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&left),
            )?;
            require_same(&left, &right, operator)?;
            if let Some(qualifier) = qualifier {
                require_operator_type(qualifier, &left, raw_operator)?;
                require_arithmetic_mode(operator, mode, raw_operator, &left)?;
            }
            let bitwise = matches!(operator, "&" | "|" | "^");
            let valid = if bitwise {
                is_integer(&left) || matches!(left, Type::Bool)
            } else {
                is_numeric(&left)
            };
            if !valid {
                return Err(format!(
                    "operator '{operator}' requires integer or boolean operands"
                ));
            }
            if matches!(operator, "<<" | ">>") {
                if let Expr::Integer(count) = &items[2] {
                    if *count < 0 || integer_width(&left).is_some_and(|width| *count >= width) {
                        return Err(format!("shift count {count} is out of range for {left:?}"));
                    }
                }
            }
            Ok(left)
        }
        "<" | "<=" | ">" | ">=" | "==" | "!=" => {
            require_arity(operator, items, 3)?;
            let left = expression(
                &items[1],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                operator_type.as_ref(),
            )?;
            let right = expression(
                &items[2],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&left),
            )?;
            require_same(&left, &right, operator)?;
            if let Some(qualifier) = qualifier {
                require_operator_type(qualifier, &left, raw_operator)?;
            }
            if !is_numeric(&left) && !matches!(left, Type::Bool | Type::Char) {
                return Err(format!(
                    "comparison operator '{operator}' requires scalar operands"
                ));
            }
            Ok(Type::Bool)
        }
        "if" => {
            if items.len() != 3 && items.len() != 4 {
                return Err(
                    "if requires a condition, then expression, and optional else expression".into(),
                );
            }
            let condition = expression(
                &items[1],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&Type::Bool),
            )?;
            require_type(&condition, &Type::Bool, "if condition")?;
            let then_type = expression(
                &items[2],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                if items.len() == 3 {
                    Some(&Type::Unit)
                } else {
                    expected
                },
            )?;
            if items.len() == 3 {
                require_type(&then_type, &Type::Unit, "if without else")?;
                return Ok(Type::Unit);
            }
            let else_type = expression(
                &items[3],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                if matches!(then_type, Type::Never) {
                    expected
                } else {
                    Some(&then_type)
                },
            )?;
            merge_types(&then_type, &else_type, "if branches")
        }
        "as" => {
            require_arity(operator, items, 3)?;
            let source = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            let target = resolve_type(&parse_type(items.get(2))?, aliases)?;
            let fieldless_enum = matches!(&source, Type::Named(name)
            if enums.get(name).is_some_and(|variants| {
                variants.iter().all(|variant| variant.fields.is_empty())
            }));
            if (!is_cast_operand(&source) && !fieldless_enum)
                || !is_cast_target(&target)
                || (fieldless_enum && !is_integer(&target))
            {
                return Err(
                    "as requires numeric, char, or bool operands and a numeric or char target"
                        .into(),
                );
            }
            Ok(target)
        }
        "literal" => {
            require_arity(operator, items, 3)?;
            let ty = resolve_type(&parse_type(items.get(1))?, aliases)?;
            if !is_integer(&ty) && !matches!(ty, Type::F32 | Type::F64) {
                return Err("typed literal suffix must name a numeric type".into());
            }
            let actual = expression(
                &items[2],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&ty),
            )?;
            require_type(&actual, &ty, "typed literal")?;
            Ok(ty)
        }
        "atomic-init" => {
            require_arity(operator, items, 3)?;
            let scalar = resolve_type(&parse_type(items.get(1))?, aliases)?;
            if !is_atomic_scalar(&scalar) {
                return Err("atomic-init supports only i8/i16/i32/i64/u8/u16/u32/u64/usize".into());
            }
            let actual = expression(
                &items[2],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&scalar),
            )?;
            require_type(&actual, &scalar, "atomic initializer")?;
            Ok(Type::Atomic(Box::new(scalar)))
        }
        "atomic-load" | "atomic-store" | "atomic-fetch-add" => {
            let expected = if operator == "atomic-load" { 3 } else { 4 };
            require_arity(operator, items, expected)?;
            let Type::Reference { target, .. } = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?
            else {
                return Err(format!(
                    "{operator} requires a shared reference to an atomic scalar"
                ));
            };
            let Type::Atomic(scalar) = *target else {
                return Err(format!(
                    "{operator} requires a reference to an atomic scalar"
                ));
            };
            let order_index = if operator == "atomic-load" { 2 } else { 3 };
            let order = atomic_memory_order(items.get(order_index))
                .ok_or_else(|| format!("{operator} requires an explicit #memory-* ordering"))?;
            match operator {
                "atomic-load" if !matches!(order, "relaxed" | "acquire" | "seq-cst") => {
                    return Err("atomic-load ordering must be relaxed, acquire, or seq-cst".into());
                }
                "atomic-store" if !matches!(order, "relaxed" | "release" | "seq-cst") => {
                    return Err("atomic-store ordering must be relaxed, release, or seq-cst".into());
                }
                _ => {}
            }
            if operator != "atomic-load" {
                let actual = expression(
                    &items[2],
                    variables,
                    functions,
                    structs,
                    enums,
                    mutable,
                    aliases,
                    Some(&scalar),
                )?;
                require_type(&actual, &scalar, "atomic operand")?;
            }
            if operator == "atomic-store" {
                Ok(Type::Unit)
            } else {
                Ok(*scalar)
            }
        }
        "slice-of" => {
            require_arity(operator, items, 2)?;
            let source = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            let Type::Reference {
                mutable: false,
                target,
            } = source
            else {
                return Err("slice requires an immutable reference to an array".into());
            };
            let Type::Array(element, _) = *target else {
                return Err("slice requires a reference to an array".into());
            };
            Ok(Type::Slice(element))
        }
        "slice-mut-of" => {
            require_arity(operator, items, 2)?;
            let Type::Reference {
                mutable: true,
                target,
            } = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?
            else {
                return Err("slice-mut-of requires a mutable reference to an array".into());
            };
            let Type::Array(element, _) = *target else {
                return Err("slice-mut-of requires a mutable reference to an array".into());
            };
            Ok(Type::MutableSlice(element))
        }
        "slice-len" => {
            require_arity(operator, items, 2)?;
            if !matches!(
                expression(
                    &items[1], variables, functions, structs, enums, mutable, aliases, None
                )?,
                Type::Slice(_)
            ) {
                return Err("slice-len requires a slice".into());
            }
            Ok(Type::Usize)
        }
        "slice-idx" => {
            require_arity(operator, items, 3)?;
            let Type::Slice(element) = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?
            else {
                return Err("slice-idx requires a slice".into());
            };
            let index = expression(
                &items[2],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&Type::Usize),
            )?;
            require_type(&index, &Type::Usize, "slice index")?;
            Ok(Type::Reference {
                mutable: false,
                target: element,
            })
        }
        "slice-range" => {
            require_arity(operator, items, 4)?;
            let Type::Slice(element) = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?
            else {
                return Err("slice-range requires a slice".into());
            };
            for bound in &items[2..4] {
                let ty = expression(
                    bound,
                    variables,
                    functions,
                    structs,
                    enums,
                    mutable,
                    aliases,
                    Some(&Type::Usize),
                )?;
                require_type(&ty, &Type::Usize, "slice range bound")?;
            }
            Ok(Type::Slice(element))
        }
        "slice-mut-len" | "slice-mut-idx" | "slice-mut-split" => {
            let expected_arity = match operator {
                "slice-mut-len" => 2,
                "slice-mut-idx" | "slice-mut-split" => 3,
                _ => unreachable!(),
            };
            require_arity(operator, items, expected_arity)?;
            let Type::MutableSlice(element) = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?
            else {
                return Err(format!("{operator} requires a mutable slice"));
            };
            if operator == "slice-mut-len" {
                return Ok(Type::Usize);
            }
            let index = expression(
                &items[2],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&Type::Usize),
            )?;
            require_type(&index, &Type::Usize, "mutable slice index")?;
            if operator == "slice-mut-idx" {
                Ok(Type::Reference {
                    mutable: true,
                    target: element,
                })
            } else {
                Ok(Type::Tuple(vec![
                    Type::MutableSlice(element.clone()),
                    Type::MutableSlice(element),
                ]))
            }
        }
        "borrow" | "borrow-mut" => {
            if items.len() == 2 {
                let (target, base_mutable) = match &items[1] {
                    Expr::Symbol(name) => {
                        let owner_type = variables.get(name).ok_or_else(|| {
                            format!("{operator} refers to unknown variable '{name}'")
                        })?;
                        if matches!(owner_type, Type::Reference { .. }) {
                            return Err(format!(
                                "{operator} cannot borrow a reference variable directly; borrow one of its fields"
                            ));
                        }
                        (owner_type.clone(), mutable.contains(name))
                    }
                    Expr::List(place)
                        if (place.len() == 3
                            && matches!(place.first(), Some(Expr::Symbol(name)) if name == "get" || name == "index"))
                            || (place.len() == 4
                                && matches!(place.first(), Some(Expr::Symbol(name)) if name == "get-payload")) =>
                    {
                        let root = projection_root(&place[1]).ok_or_else(|| {
                            format!("{operator} projection borrowing requires a reference")
                        })?;
                        let base_type = expression(
                            root, variables, functions, structs, enums, mutable, aliases, None,
                        )?;
                        let Type::Reference {
                            mutable: reference_mutable,
                            target,
                        } = base_type
                        else {
                            return Err(format!(
                                "{operator} projection borrowing requires a reference"
                            ));
                        };
                        let _ = target;
                        let field_type = expression(
                            &items[1], variables, functions, structs, enums, mutable, aliases, None,
                        )?;
                        (field_type, reference_mutable)
                    }
                    _ => {
                        return Err(format!(
                            "{operator} requires a variable or a struct field through a reference"
                        ))
                    }
                };
                if operator == "borrow-mut" && !base_mutable {
                    return Err(borrow_error(
                        "cannot mutably borrow through an immutable reference",
                    ));
                }
                if !is_reference_target(&target) {
                    return Err(format!("{operator} cannot borrow a unit or never value"));
                }
                return Ok(Type::Reference {
                    mutable: operator == "borrow-mut",
                    target: Box::new(target),
                });
            }
            require_arity(operator, items, 3)?;
            match &items[1] {
                Expr::Symbol(owner) => {
                    if !variables.contains_key(owner) {
                        return Err(format!("{operator} refers to unknown variable '{owner}'"));
                    }
                    if operator == "borrow-mut" && !mutable.contains(owner) {
                        return Err(format!(
                            "cannot mutably borrow immutable variable '{owner}'"
                        ));
                    }
                }
                Expr::List(place)
                    if (matches!(place.first(), Some(Expr::Symbol(name)) if name == "get" || name == "index")
                        && place.len() == 3)
                        || (matches!(place.first(), Some(Expr::Symbol(name)) if name == "get-payload")
                            && place.len() == 4) =>
                {
                    let root = projection_root(&items[1]).ok_or_else(|| {
                        format!("{operator} projection borrowing requires a reference")
                    })?;
                    let Type::Reference {
                        mutable: reference_mutable,
                        ..
                    } = expression(
                        root, variables, functions, structs, enums, mutable, aliases, None,
                    )?
                    else {
                        return Err(format!(
                            "{operator} projection borrowing requires a reference"
                        ));
                    };
                    if operator == "borrow-mut" && !reference_mutable {
                        return Err(borrow_error(
                            "cannot mutably borrow through an immutable reference",
                        ));
                    }
                    expression(
                        &items[1], variables, functions, structs, enums, mutable, aliases, None,
                    )?;
                }
                _ => {
                    return Err(format!(
                        "{operator} requires a variable or a struct field through a reference"
                    ))
                }
            }
            expression(
                &items[2], variables, functions, structs, enums, mutable, aliases, expected,
            )
        }
        "deref" => {
            require_arity(operator, items, 2)?;
            let actual = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            match actual {
                Type::Reference { target, .. } => Ok(*target),
                _ => Err("deref requires a reference".into()),
            }
        }
        "deref-set" => {
            require_arity(operator, items, 3)?;
            let reference_type = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            let Type::Reference {
                mutable: true,
                target,
            } = reference_type
            else {
                return Err("deref-set requires a mutable reference".into());
            };
            let actual = expression(
                &items[2],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&target),
            )?;
            require_type(&actual, &target, "deref-set value")?;
            Ok(Type::Unit)
        }
        "unsafe" => {
            require_arity(operator, items, 2)?;
            expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, expected,
            )
        }
        "addr-of" | "addr-of-mut" => {
            require_arity(operator, items, 2)?;
            let owner = match &items[1] {
                Expr::Symbol(name) => name,
                _ => return Err(format!("{operator} requires a variable name")),
            };
            let owner_type = variables
                .get(owner)
                .ok_or_else(|| format!("{operator} refers to unknown variable '{owner}'"))?;
            if !is_scalar_reference_target(owner_type, enums) {
                return Err(format!("{operator} currently supports scalar values only"));
            }
            if operator == "addr-of-mut" && !mutable.contains(owner) {
                return Err(format!(
                    "cannot take a mutable pointer to immutable variable '{owner}'"
                ));
            }
            Ok(Type::RawPointer {
                mutable: operator == "addr-of-mut",
                target: Box::new(owner_type.clone()),
            })
        }
        "ptr-null" => {
            require_arity(operator, items, 2)?;
            match resolve_type(&parse_type(items.get(1))?, aliases)? {
                pointer @ Type::RawPointer { .. } => Ok(pointer),
                _ => Err("ptr-null requires an explicit raw-pointer type".into()),
            }
        }
        "ptr-is-null" => {
            require_arity(operator, items, 2)?;
            match expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )? {
                Type::RawPointer { .. } => Ok(Type::Bool),
                _ => Err("ptr-is-null requires a raw pointer".into()),
            }
        }
        "ptr-borrow" | "ptr-borrow-mut" => {
            require_arity(operator, items, 3)?;
            let owner = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            let Type::Reference {
                mutable: owner_mutable,
                ..
            } = owner
            else {
                return Err(format!("{operator} requires a reference lifetime anchor"));
            };
            let pointer = expression(
                &items[2], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            let Type::RawPointer {
                mutable: pointer_mutable,
                target,
            } = pointer
            else {
                return Err(format!("{operator} requires a raw pointer"));
            };
            let borrowed_mutable = operator == "ptr-borrow-mut";
            if borrowed_mutable && (!owner_mutable || !pointer_mutable) {
                return Err(
                    "ptr-borrow-mut requires a mutable reference anchor and mutable pointer".into(),
                );
            }
            Ok(Type::Reference {
                mutable: borrowed_mutable,
                target,
            })
        }
        "ptr-read" => {
            require_arity(operator, items, 2)?;
            let actual = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            match actual {
                Type::RawPointer { target, .. } => Ok(*target),
                _ => Err("ptr-read requires a raw pointer".into()),
            }
        }
        "ptr-offset" => {
            require_arity(operator, items, 3)?;
            let pointer = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            let Type::RawPointer {
                mutable: pointer_mutable,
                target,
            } = pointer
            else {
                return Err("ptr-offset requires a raw pointer and usize element index".into());
            };
            let index_type = expression(
                &items[2],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&Type::Usize),
            )?;
            require_type(&index_type, &Type::Usize, "ptr-offset index")?;
            validate_layout_type(&target, structs, enums)?;
            Ok(Type::RawPointer {
                mutable: pointer_mutable,
                target,
            })
        }
        "ptr-write" => {
            require_arity(operator, items, 3)?;
            let pointer = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            let Type::RawPointer {
                mutable: true,
                target,
            } = pointer
            else {
                return Err("ptr-write requires a mutable raw pointer".into());
            };
            let actual = expression(
                &items[2],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&target),
            )?;
            require_type(&actual, &target, "ptr-write value")?;
            Ok(Type::Unit)
        }
        "size-of" | "align-of" => {
            require_arity(operator, items, 2)?;
            let ty = resolve_type(&parse_type(items.get(1))?, aliases)?;
            validate_layout_type(&ty, structs, enums)?;
            Ok(Type::Usize)
        }
        "offset-of" => {
            require_arity(operator, items, 3)?;
            let ty = resolve_type(&parse_type(items.get(1))?, aliases)?;
            let Type::Named(name) = ty else {
                return Err("offset-of requires a #repr-c struct type".into());
            };
            let field = match items.get(2) {
                Some(Expr::Symbol(field)) => field,
                _ => return Err("offset-of field must be an identifier".into()),
            };
            let _ = (name, field);
            Ok(Type::Usize)
        }
        "array" => {
            let (element, length, value_start) = match expected {
                Some(Type::Array(element, length)) => {
                    let explicit = parse_type(items.get(1))
                        .ok()
                        .and_then(|ty| resolve_type(&ty, aliases).ok())
                        .is_some_and(|ty| ty == Type::Array(element.clone(), *length));
                    (
                        element.clone(),
                        *length,
                        if explicit && items.len() >= 2 { 2 } else { 1 },
                    )
                }
                Some(_) => {
                    return Err("array construction requires an array-typed expected value".into())
                }
                None => {
                    let declared = resolve_type(
                        &parse_type(items.get(1)).map_err(|_| {
                            "direct array constructors require an explicit (array Element Length) type"
                                .to_owned()
                        })?,
                        aliases,
                    )?;
                    let Type::Array(element, length) = declared else {
                        return Err("direct array constructors require an explicit (array Element Length) type".into());
                    };
                    (element, length, 2)
                }
            };
            if items.len() - value_start != length {
                return Err(format!("array constructor expects {length} elements"));
            }
            for (index, value) in items[value_start..].iter().enumerate() {
                let actual = expression(
                    value,
                    variables,
                    functions,
                    structs,
                    enums,
                    mutable,
                    aliases,
                    Some(element.as_ref()),
                )?;
                require_type(&actual, element.as_ref(), &format!("array element {index}"))?;
            }
            Ok(Type::Array(element, length))
        }
        "array-repeat" => {
            let (element, length, value_index) = match expected {
                Some(Type::Array(element, length)) => (element.clone(), *length, 1),
                Some(_) => {
                    return Err(
                        "array-repeat construction requires an array-typed expected value".into(),
                    )
                }
                None => {
                    let declared = resolve_type(
                        &parse_type(items.get(1)).map_err(|_| {
                            "direct array-repeat constructors require an explicit (array Element Length) type"
                                .to_owned()
                        })?,
                        aliases,
                    )?;
                    let Type::Array(element, length) = declared else {
                        return Err("direct array-repeat constructors require an explicit (array Element Length) type".into());
                    };
                    (element, length, 2)
                }
            };
            if items.len() != value_index + 1 {
                return Err("array-repeat requires one value".into());
            }
            let actual = expression(
                &items[value_index],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(element.as_ref()),
            )?;
            require_type(&actual, element.as_ref(), "array-repeat element")?;
            Ok(Type::Array(element, length))
        }
        "tuple" => {
            let (fields, value_start) = match expected {
                Some(Type::Tuple(fields)) => {
                    let explicit = parse_type(items.get(1))
                        .ok()
                        .and_then(|ty| resolve_type(&ty, aliases).ok())
                        .is_some_and(|ty| ty == Type::Tuple(fields.clone()));
                    (
                        fields.clone(),
                        if explicit && items.len() >= 2 { 2 } else { 1 },
                    )
                }
                Some(_) => {
                    return Err("tuple construction requires an expected (tuple ...) type".into())
                }
                None => {
                    let declared = parse_type(items.get(1)).map_err(|_| {
                        "direct tuple constructors require an explicit (tuple Type ...) type"
                            .to_owned()
                    })?;
                    let Type::Tuple(fields) = declared else {
                        return Err(
                            "direct tuple constructors require an explicit (tuple Type ...) type"
                                .into(),
                        );
                    };
                    (fields, 2)
                }
            };
            if items.len() - value_start != fields.len() {
                return Err(format!(
                    "tuple constructor expects {} elements",
                    fields.len()
                ));
            }
            for (index, (value, field)) in
                items[value_start..].iter().zip(fields.iter()).enumerate()
            {
                let actual = expression(
                    value,
                    variables,
                    functions,
                    structs,
                    enums,
                    mutable,
                    aliases,
                    Some(field),
                )?;
                require_type(&actual, field, &format!("tuple element {index}"))?;
            }
            Ok(Type::Tuple(fields))
        }
        "index" => {
            if items.len() != 3 {
                return Err("index requires the form (index array index)".into());
            }
            let array_type = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            let array_type = match array_type {
                Type::Reference { target, .. } => *target,
                other => other,
            };
            let Type::Array(element, length) = array_type else {
                return Err("index requires an array".into());
            };
            check_index(
                &items[2], length, variables, functions, structs, enums, mutable, aliases,
            )?;
            Ok(*element)
        }
        "match" => {
            if items.len() < 3 {
                return Err("match requires a value and at least one arm".into());
            }
            let scrutinee = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            if matches!(scrutinee, Type::Tuple(_)) {
                return check_tuple_match(
                    items, &scrutinee, variables, functions, structs, enums, mutable, aliases,
                    expected,
                );
            }
            if matches!(scrutinee, Type::Array(_, _)) {
                return check_array_match(
                    items, &scrutinee, variables, functions, structs, enums, mutable, aliases,
                    expected,
                );
            }
            if let Type::Named(struct_name) = &scrutinee {
                if structs.contains_key(struct_name) {
                    return check_struct_match(
                        items,
                        struct_name,
                        variables,
                        functions,
                        structs,
                        enums,
                        mutable,
                        aliases,
                        expected,
                    );
                }
            }
            let Type::Named(enum_name) = &scrutinee else {
                if !is_matchable_scalar(&scrutinee) {
                    return Err("match requires an enum or scalar value".into());
                }
                return check_scalar_match(
                    items, &scrutinee, variables, functions, structs, enums, mutable, aliases,
                    expected,
                );
            };
            if !enums.contains_key(enum_name) {
                if !is_matchable_scalar(&scrutinee) {
                    return Err("match requires an enum or scalar value".into());
                }
                return check_scalar_match(
                    items, &scrutinee, variables, functions, structs, enums, mutable, aliases,
                    expected,
                );
            }
            let variants = enums
                .get(enum_name)
                .ok_or_else(|| format!("unknown enum '{enum_name}'"))?;
            let mut wildcard = false;
            let mut seen = Vec::new();
            let mut result_type = None;
            for arm in &items[2..] {
                let (pattern_expr, guard, body) = match_arm_parts(arm)?;
                let (pattern, payload_patterns, alternatives) = match pattern_expr {
                    Expr::Symbol(pattern) => (pattern.as_str(), Vec::new(), Vec::new()),
                    Expr::List(pattern)
                        if pattern.len() >= 2
                            && matches!(pattern.first(), Some(Expr::Symbol(name)) if name == "or") =>
                    {
                        let alternatives = pattern[1..]
                            .iter()
                            .map(|alternative| match alternative {
                                Expr::Symbol(name) => Ok((name.as_str(), Vec::new())),
                                Expr::List(items) if !items.is_empty() => {
                                    let Expr::Symbol(name) = &items[0] else {
                                        return Err(
                                            "enum or-pattern alternatives must be variants"
                                                .to_owned(),
                                        );
                                    };
                                    Ok((name.as_str(), items[1..].iter().collect()))
                                }
                                _ => {
                                    Err("enum or-pattern alternatives must be variants".to_owned())
                                }
                            })
                            .collect::<Result<Vec<(&str, Vec<&Expr>)>, String>>()?;
                        ("", Vec::new(), alternatives)
                    }
                    Expr::List(pattern) if !pattern.is_empty() => {
                        let variant = match &pattern[0] {
                            Expr::Symbol(variant) => variant.as_str(),
                            _ => return Err("match variant pattern must be a symbol".into()),
                        };
                        let payloads = pattern[1..].iter().collect::<Vec<_>>();
                        (variant, payloads, Vec::new())
                    }
                    _ => return Err("match pattern must be a symbol or (variant _)".into()),
                };
                if !alternatives.is_empty() {
                    for (alternative, alternative_payloads) in alternatives {
                        let Some(variant) =
                            variants.iter().find(|variant| variant.name == alternative)
                        else {
                            return Err(format!(
                                "'{alternative}' is not a variant of '{enum_name}'"
                            ));
                        };
                        if !alternative_payloads.is_empty()
                            && alternative_payloads.len() != variant.fields.len()
                        {
                            return Err(format!(
                                "variant '{alternative}' expects {} payload patterns",
                                variant.fields.len()
                            ));
                        }
                        let mut alternative_variables = variables.clone();
                        for (binding, field_type) in
                            alternative_payloads.iter().zip(&variant.fields)
                        {
                            check_enum_payload_pattern(
                                binding,
                                field_type,
                                &mut alternative_variables,
                                variables,
                                structs,
                            )?;
                        }
                        if alternative_variables.len() != variables.len() {
                            return Err("enum or-pattern alternatives cannot bind values".into());
                        }
                        if guard.is_none() && !seen.contains(&alternative) {
                            seen.push(alternative);
                        }
                    }
                } else if pattern == "_" {
                    if !payload_patterns.is_empty() {
                        return Err("wildcard pattern cannot have a payload".into());
                    }
                    if guard.is_none() && wildcard {
                        return Err("duplicate wildcard match pattern".into());
                    }
                    if guard.is_none() {
                        wildcard = true;
                    }
                } else {
                    let Some(variant) = variants.iter().find(|variant| variant.name == pattern)
                    else {
                        return Err(format!("'{pattern}' is not a variant of '{enum_name}'"));
                    };
                    if !payload_patterns.is_empty()
                        && payload_patterns.len() != variant.fields.len()
                    {
                        return Err(format!(
                            "variant '{pattern}' expects {} payload patterns",
                            variant.fields.len()
                        ));
                    }
                    if guard.is_none() && seen.contains(&pattern) {
                        return Err(format!("duplicate enum match pattern '{pattern}'"));
                    }
                    if guard.is_none() {
                        seen.push(pattern);
                    }
                }
                let mut arm_variables = variables.clone();
                if !payload_patterns.is_empty() {
                    let variant = variants
                        .iter()
                        .find(|variant| variant.name == pattern)
                        .ok_or_else(|| format!("unknown variant '{pattern}'"))?;
                    for (binding, field_type) in payload_patterns.iter().zip(&variant.fields) {
                        check_enum_payload_pattern(
                            binding,
                            field_type,
                            &mut arm_variables,
                            variables,
                            structs,
                        )?;
                    }
                }
                if let Some(guard) = guard {
                    let guard_type = expression(
                        guard,
                        &arm_variables,
                        functions,
                        structs,
                        enums,
                        mutable,
                        aliases,
                        Some(&Type::Bool),
                    )?;
                    require_type(&guard_type, &Type::Bool, "match guard")?;
                }
                let arm_type = expression(
                    body,
                    &arm_variables,
                    functions,
                    structs,
                    enums,
                    mutable,
                    aliases,
                    result_type
                        .as_ref()
                        .filter(|ty| !matches!(ty, Type::Never))
                        .or(expected),
                )?;
                if let Some(previous) = &result_type {
                    result_type = Some(merge_types(previous, &arm_type, "match arms")?);
                } else {
                    result_type = Some(arm_type);
                }
            }
            if !wildcard && seen.len() != variants.len() {
                return Err("match is not exhaustive; add '_' arm".into());
            }
            Ok(result_type.unwrap_or(Type::Unit))
        }
        "!" => {
            require_arity(operator, items, 2)?;
            let operand = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, expected,
            )?;
            if !matches!(operand, Type::Bool) && !is_integer(&operand) {
                return Err("! operand must be a boolean or integer".into());
            }
            Ok(operand)
        }
        "&&" | "||" => {
            require_arity(operator, items, 3)?;
            for operand in &items[1..] {
                let actual = expression(
                    operand,
                    variables,
                    functions,
                    structs,
                    enums,
                    mutable,
                    aliases,
                    Some(&Type::Bool),
                )?;
                require_type(&actual, &Type::Bool, &format!("{operator} operand"))?;
            }
            Ok(Type::Bool)
        }
        "assert" | "debug-assert" => {
            require_arity(operator, items, 2)?;
            let actual = expression(
                &items[1],
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&Type::Bool),
            )?;
            require_type(&actual, &Type::Bool, &format!("{operator} condition"))?;
            Ok(Type::Unit)
        }
        "panic" | "unreachable" => {
            require_arity(operator, items, 1)?;
            Ok(Type::Never)
        }
        "let" => Err("let is only valid as a statement".into()),
        "get" => {
            if items.len() != 3 {
                return Err("get requires the form (get value field)".into());
            }
            let value_type = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            let value_type = match value_type {
                Type::Reference { target, .. } => *target,
                other => other,
            };
            if let Type::Tuple(fields) = value_type {
                let index = match &items[2] {
                    Expr::Integer(index) if *index >= 0 => usize::try_from(*index)
                        .map_err(|_| "tuple field index is too large".to_owned())?,
                    _ => return Err("tuple get requires a non-negative integer index".into()),
                };
                return fields
                    .get(index)
                    .cloned()
                    .ok_or_else(|| format!("tuple field index {index} is out of bounds"));
            }
            let Type::Named(struct_name) = value_type else {
                return Err("get requires a struct or tuple value".into());
            };
            let field_name = match &items[2] {
                Expr::Symbol(name) => name,
                _ => return Err("get requires a field name".into()),
            };
            let fields = structs
                .get(&struct_name)
                .ok_or_else(|| format!("unknown struct '{struct_name}'"))?;
            fields
                .iter()
                .find(|field| field.name == *field_name)
                .map(|field| field.ty.clone())
                .ok_or_else(|| format!("struct '{struct_name}' has no field '{field_name}'"))
        }
        "get-payload" => {
            if items.len() != 4 {
                return Err(
                    "get-payload requires the form (get-payload enum variant index)".into(),
                );
            }
            let value_type = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            let value_type = match value_type {
                Type::Reference { target, .. } => *target,
                other => other,
            };
            let Type::Named(enum_name) = value_type else {
                return Err("get-payload requires an enum value".into());
            };
            let Expr::Symbol(variant_name) = &items[2] else {
                return Err("get-payload requires a variant name".into());
            };
            let index = match &items[3] {
                Expr::Integer(index) if *index >= 0 => usize::try_from(*index)
                    .map_err(|_| "enum payload index is too large".to_owned())?,
                Expr::UnsignedInteger(index) => usize::try_from(*index)
                    .map_err(|_| "enum payload index is too large".to_owned())?,
                _ => return Err("get-payload requires a non-negative integer index".into()),
            };
            let variants = enums
                .get(&enum_name)
                .ok_or_else(|| format!("unknown enum '{enum_name}'"))?;
            let variant = variants
                .iter()
                .find(|variant| variant.name == *variant_name)
                .ok_or_else(|| format!("enum '{enum_name}' has no variant '{variant_name}'"))?;
            variant.fields.get(index).cloned().ok_or_else(|| {
                format!("variant '{variant_name}' has no payload field at index {index}")
            })
        }
        _ => {
            if let Some(fields) = structs.get(operator) {
                if items.len() - 1 != fields.len() {
                    return Err(format!(
                        "constructor '{operator}' expects {} fields",
                        fields.len()
                    ));
                }
                for (argument, field) in items[1..].iter().zip(fields) {
                    let actual = expression(
                        argument,
                        variables,
                        functions,
                        structs,
                        enums,
                        mutable,
                        aliases,
                        Some(&field.ty),
                    )?;
                    require_type(
                        &actual,
                        &field.ty,
                        &format!("field '{}' of '{operator}'", field.name),
                    )?;
                }
                return Ok(Type::Named(operator.to_owned()));
            }
            for (enum_name, variants) in enums {
                let Some(variant) = variants.iter().find(|variant| variant.name == *operator)
                else {
                    continue;
                };
                if items.len() - 1 != variant.fields.len() {
                    return Err(format!(
                        "variant '{operator}' expects {} payloads",
                        variant.fields.len()
                    ));
                }
                for (payload_index, (argument, field_type)) in
                    items[1..].iter().zip(&variant.fields).enumerate()
                {
                    let actual = expression(
                        argument,
                        variables,
                        functions,
                        structs,
                        enums,
                        mutable,
                        aliases,
                        Some(field_type),
                    )?;
                    require_type(
                        &actual,
                        field_type,
                        &format!("payload {payload_index} of variant '{operator}'"),
                    )?;
                }
                return Ok(Type::Named(enum_name.clone()));
            }
            let (function_name, type_arguments) = split_generic_call(operator)?;
            let signature = functions
                .get(&function_name)
                .ok_or_else(|| format!("unknown function '{operator}'"))?;
            let substitutions = generic_substitutions(signature, &type_arguments, aliases)?;
            let parameter_types = signature
                .parameters
                .iter()
                .map(|parameter| substitute_type(parameter, &substitutions))
                .collect::<Vec<_>>();
            let return_type = substitute_type(&signature.return_type, &substitutions);
            if items.len() - 1 != signature.parameters.len() {
                return Err(format!(
                    "function '{operator}' expects {} arguments",
                    parameter_types.len()
                ));
            }
            for ((argument, parameter_type), parameter) in items[1..]
                .iter()
                .zip(&parameter_types)
                .zip(&signature.parameter_names)
            {
                let actual = expression(
                    argument,
                    variables,
                    functions,
                    structs,
                    enums,
                    mutable,
                    aliases,
                    Some(parameter_type),
                )?;
                require_type(
                    &actual,
                    parameter_type,
                    &format!("argument '{parameter}' to '{operator}'"),
                )?;
            }
            Ok(return_type)
        }
    }
}

fn projection_root(expression: &Expr) -> Option<&Expr> {
    match expression {
        Expr::Symbol(_) => Some(expression),
        Expr::List(items)
            if (items.len() == 3
                && matches!(items.first(), Some(Expr::Symbol(name)) if name == "get" || name == "index"))
                || (items.len() == 4
                    && matches!(items.first(), Some(Expr::Symbol(name)) if name == "get-payload")) =>
        {
            projection_root(&items[1])
        }
        _ => None,
    }
}

fn check_scalar_match(
    items: &[Expr],
    scrutinee: &Type,
    variables: &HashMap<String, Type>,
    functions: &HashMap<String, Signature>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    mutable: &HashSet<String>,
    aliases: &HashMap<String, Type>,
    expected: Option<&Type>,
) -> Result<Type, String> {
    let mut wildcard = false;
    let mut seen_bool = [false, false];
    let mut seen_integers = HashSet::new();
    let mut seen_unsigned_integers = HashSet::new();
    let mut seen_chars = HashSet::new();
    let mut result_type = None;
    for arm in &items[2..] {
        let (pattern, guard, body) = match_arm_parts(arm)?;
        match pattern {
            pattern if is_typed_integer_pattern(pattern) => {
                check_scalar_pattern(pattern, scrutinee)?;
            }
            Expr::List(parts)
                if parts.len() >= 2
                    && matches!(parts.first(), Some(Expr::Symbol(name)) if name == "or") =>
            {
                if parts[1..]
                    .iter()
                    .any(|alternative| matches!(alternative, Expr::Symbol(name) if name == "_"))
                    && guard.is_none()
                {
                    wildcard = true;
                }
                for alternative in &parts[1..] {
                    check_scalar_pattern(alternative, scrutinee)?;
                    if let Expr::Symbol(name) = alternative {
                        if matches!(scrutinee, Type::Bool)
                            && matches!(name.as_str(), "true" | "false")
                        {
                            let index = usize::from(name == "true");
                            if seen_bool[index] {
                                return Err(format!("duplicate boolean match pattern '{name}'"));
                            }
                            seen_bool[index] = true;
                        }
                    }
                }
            }
            Expr::List(parts)
                if parts.len() == 3
                    && matches!(parts.first(), Some(Expr::Symbol(name)) if name == "range") =>
            {
                check_scalar_range_pattern(parts, scrutinee)?;
            }
            Expr::Symbol(pattern) if pattern == "_" => {
                if guard.is_none() && wildcard {
                    return Err("duplicate wildcard match pattern".into());
                }
                if guard.is_none() {
                    wildcard = true;
                }
            }
            Expr::Symbol(pattern) if matches!(scrutinee, Type::Bool) => {
                let index = match pattern.as_str() {
                    "false" => 0,
                    "true" => 1,
                    _ => return Err("boolean match pattern must be true, false, or _".into()),
                };
                if seen_bool[index] {
                    return Err(format!("duplicate boolean match pattern '{pattern}'"));
                }
                seen_bool[index] = true;
            }
            Expr::Integer(value) if is_integer(scrutinee) => {
                if !fits_integer(*value, scrutinee) {
                    return Err(format!(
                        "integer match pattern {value} does not fit in {scrutinee:?}"
                    ));
                }
                if !seen_integers.insert(*value) {
                    return Err(format!("duplicate integer match pattern {value}"));
                }
            }
            Expr::UnsignedInteger(value) if is_integer(scrutinee) => {
                if !fits_unsigned_integer(*value, scrutinee) {
                    return Err(format!(
                        "unsigned integer match pattern {value} does not fit in {scrutinee:?}"
                    ));
                }
                if !seen_unsigned_integers.insert(*value) {
                    return Err(format!("duplicate integer match pattern {value}"));
                }
            }
            Expr::Char(value) if matches!(scrutinee, Type::Char) => {
                if !seen_chars.insert(*value) {
                    return Err(format!("duplicate character match pattern {value:?}"));
                }
            }
            _ => return Err("scalar match pattern does not match the scrutinee type".into()),
        }
        if let Some(guard) = guard {
            let guard_type = expression(
                guard,
                variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&Type::Bool),
            )?;
            require_type(&guard_type, &Type::Bool, "match guard")?;
        }
        let arm_type = expression(
            body,
            variables,
            functions,
            structs,
            enums,
            mutable,
            aliases,
            result_type
                .as_ref()
                .filter(|ty| !matches!(ty, Type::Never))
                .or(expected),
        )?;
        if let Some(previous) = &result_type {
            result_type = Some(merge_types(previous, &arm_type, "match arms")?);
        } else {
            result_type = Some(arm_type);
        }
    }
    if !wildcard && !(matches!(scrutinee, Type::Bool) && seen_bool.iter().all(|seen| *seen)) {
        return Err("match is not exhaustive; add '_' arm".into());
    }
    Ok(result_type.unwrap_or(Type::Unit))
}

fn check_scalar_pattern(pattern: &Expr, scrutinee: &Type) -> Result<(), String> {
    if let Some(value) = typed_integer_pattern_value(pattern, scrutinee)? {
        return check_scalar_pattern(value, scrutinee);
    }
    if let Expr::List(parts) = pattern {
        if parts.len() >= 2 && matches!(parts.first(), Some(Expr::Symbol(name)) if name == "or") {
            for alternative in &parts[1..] {
                check_scalar_pattern(alternative, scrutinee)?;
            }
            return Ok(());
        }
    }
    match pattern {
        Expr::List(parts)
            if parts.len() == 3
                && matches!(parts.first(), Some(Expr::Symbol(name)) if name == "range") =>
        {
            check_scalar_range_pattern(parts, scrutinee)
        }
        Expr::Symbol(name) if name == "_" => Ok(()),
        Expr::Symbol(name)
            if matches!(scrutinee, Type::Bool) && matches!(name.as_str(), "true" | "false") =>
        {
            Ok(())
        }
        Expr::Integer(value) if is_integer(scrutinee) && fits_integer(*value, scrutinee) => Ok(()),
        Expr::UnsignedInteger(value)
            if is_integer(scrutinee) && fits_unsigned_integer(*value, scrutinee) =>
        {
            Ok(())
        }
        Expr::Char(_) if matches!(scrutinee, Type::Char) => Ok(()),
        _ => Err("scalar or-pattern alternative does not match the scrutinee type".into()),
    }
}

fn check_scalar_range_pattern(parts: &[Expr], scrutinee: &Type) -> Result<(), String> {
    if is_integer(scrutinee) {
        let signed = matches!(
            scrutinee,
            Type::I8 | Type::I16 | Type::I32 | Type::I64 | Type::I128 | Type::Isize
        );
        if signed {
            let lower_expression = range_bound_expression(&parts[1], scrutinee)?;
            let upper_expression = range_bound_expression(&parts[2], scrutinee)?;
            let lower = signed_range_bound(lower_expression)?;
            let upper = signed_range_bound(upper_expression)?;
            if !fits_integer(lower, scrutinee) || !fits_integer(upper, scrutinee) {
                return Err("integer range pattern does not fit its scrutinee type".into());
            }
            if lower > upper {
                return Err("integer range pattern lower bound exceeds upper bound".into());
            }
        } else {
            let lower_expression = range_bound_expression(&parts[1], scrutinee)?;
            let upper_expression = range_bound_expression(&parts[2], scrutinee)?;
            let lower = unsigned_range_bound(lower_expression)?;
            let upper = unsigned_range_bound(upper_expression)?;
            if !fits_unsigned_integer(lower, scrutinee) || !fits_unsigned_integer(upper, scrutinee)
            {
                return Err("unsigned range pattern does not fit its scrutinee type".into());
            }
            if lower > upper {
                return Err("unsigned range pattern lower bound exceeds upper bound".into());
            }
        }
        return Ok(());
    }
    if matches!(scrutinee, Type::Char) {
        let Expr::Char(lower) = parts[1] else {
            return Err("character range patterns require character bounds".into());
        };
        let Expr::Char(upper) = parts[2] else {
            return Err("character range patterns require character bounds".into());
        };
        if lower > upper {
            return Err("character range pattern lower bound exceeds upper bound".into());
        }
        return Ok(());
    }
    Err("range patterns require an integer or char scrutinee".into())
}

fn is_typed_integer_pattern(pattern: &Expr) -> bool {
    matches!(
        pattern,
        Expr::List(items)
            if items.len() == 3
                && matches!(items.first(), Some(Expr::Symbol(name)) if name == "literal")
    )
}

fn typed_integer_pattern_value<'a>(
    pattern: &'a Expr,
    scrutinee: &Type,
) -> Result<Option<&'a Expr>, String> {
    let Expr::List(items) = pattern else {
        return Ok(None);
    };
    if !is_typed_integer_pattern(pattern) {
        return Ok(None);
    }
    let literal_type = parse_type(items.get(1))?;
    if literal_type != *scrutinee || !is_integer(&literal_type) {
        return Err(format!(
            "typed integer pattern has type {literal_type:?}, expected {scrutinee:?}"
        ));
    }
    if !matches!(items[2], Expr::Integer(_) | Expr::UnsignedInteger(_)) {
        return Err("typed integer pattern requires an integer literal".into());
    }
    Ok(Some(&items[2]))
}

fn range_bound_expression<'a>(expression: &'a Expr, scrutinee: &Type) -> Result<&'a Expr, String> {
    let Expr::List(items) = expression else {
        return Ok(expression);
    };
    if items.len() != 3 || !matches!(items.first(), Some(Expr::Symbol(name)) if name == "literal") {
        return Ok(expression);
    }
    let literal_type = parse_type(items.get(1))?;
    if &literal_type != scrutinee {
        return Err(format!(
            "typed range bound has type {literal_type:?}, expected {scrutinee:?}"
        ));
    }
    Ok(&items[2])
}

fn signed_range_bound(expression: &Expr) -> Result<i128, String> {
    match expression {
        Expr::Integer(value) => Ok(*value),
        Expr::UnsignedInteger(value) => {
            i128::try_from(*value).map_err(|_| "signed range bound is too large".to_owned())
        }
        _ => Err("integer range patterns require integer bounds".into()),
    }
}

fn unsigned_range_bound(expression: &Expr) -> Result<u128, String> {
    match expression {
        Expr::Integer(value) if *value >= 0 => Ok(*value as u128),
        Expr::Integer(_) => Err("unsigned range bounds cannot be negative".into()),
        Expr::UnsignedInteger(value) => Ok(*value),
        _ => Err("integer range patterns require integer bounds".into()),
    }
}

fn match_arm_parts(arm: &Expr) -> Result<(&Expr, Option<&Expr>, &Expr), String> {
    let Expr::List(arm) = arm else {
        return Err("match arms must have the form (pattern expression)".into());
    };
    match arm.as_slice() {
        [pattern, body] => Ok((pattern, None, body)),
        [pattern, Expr::List(guard), body]
            if matches!(guard.first(), Some(Expr::Symbol(name)) if name == "when")
                && guard.len() == 2 =>
        {
            Ok((pattern, Some(&guard[1]), body))
        }
        _ => Err(
            "match arms must have the form (pattern expression) or (pattern (when guard) expression)"
                .into(),
        ),
    }
}

fn check_tuple_match(
    items: &[Expr],
    scrutinee: &Type,
    variables: &HashMap<String, Type>,
    functions: &HashMap<String, Signature>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    mutable: &HashSet<String>,
    aliases: &HashMap<String, Type>,
    expected: Option<&Type>,
) -> Result<Type, String> {
    let Type::Tuple(fields) = scrutinee else {
        unreachable!()
    };
    let mut wildcard = false;
    let mut result_type = None;
    for arm in &items[2..] {
        let (pattern, guard, body) = match_arm_parts(arm)?;
        let mut arm_variables = variables.clone();
        match pattern {
            Expr::Symbol(pattern) if pattern == "_" => {
                if guard.is_none() && wildcard {
                    return Err("duplicate wildcard match pattern".into());
                }
                if guard.is_none() {
                    wildcard = true;
                }
            }
            Expr::List(pattern)
                if pattern.len() >= 2
                    && matches!(pattern.first(), Some(Expr::Symbol(name)) if name == "or") =>
            {
                if check_aggregate_or_pattern(pattern, scrutinee, structs)? && guard.is_none() {
                    wildcard = true;
                }
            }
            Expr::List(pattern) if matches!(pattern.first(), Some(Expr::Symbol(name)) if name == "tuple") =>
            {
                if pattern.len() - 1 != fields.len() {
                    return Err(format!(
                        "tuple match pattern expects {} elements",
                        fields.len()
                    ));
                }
                for (pattern, field) in pattern[1..].iter().zip(fields) {
                    check_aggregate_pattern(
                        pattern,
                        field,
                        &mut arm_variables,
                        variables,
                        structs,
                    )?;
                }
            }
            _ => return Err("tuple match pattern must be _ or (tuple pattern ...)".into()),
        }
        if let Some(guard) = guard {
            let guard_type = expression(
                guard,
                &arm_variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&Type::Bool),
            )?;
            require_type(&guard_type, &Type::Bool, "match guard")?;
        }
        let arm_type = expression(
            body,
            &arm_variables,
            functions,
            structs,
            enums,
            mutable,
            aliases,
            result_type
                .as_ref()
                .filter(|ty| !matches!(ty, Type::Never))
                .or(expected),
        )?;
        if let Some(previous) = &result_type {
            result_type = Some(merge_types(previous, &arm_type, "match arms")?);
        } else {
            result_type = Some(arm_type);
        }
    }
    if !wildcard {
        return Err("tuple match is not exhaustive; add '_' arm".into());
    }
    Ok(result_type.unwrap_or(Type::Unit))
}

fn check_aggregate_pattern(
    pattern: &Expr,
    ty: &Type,
    arm_variables: &mut HashMap<String, Type>,
    variables: &HashMap<String, Type>,
    structs: &HashMap<String, Vec<Field>>,
) -> Result<(), String> {
    if let Some(value) = typed_integer_pattern_value(pattern, ty)? {
        return check_aggregate_pattern(value, ty, arm_variables, variables, structs);
    }
    if let Expr::List(items) = pattern {
        if items.len() == 3 && matches!(items.first(), Some(Expr::Symbol(name)) if name == "range")
        {
            return check_scalar_range_pattern(items, ty);
        }
        if items.len() >= 2 && matches!(items.first(), Some(Expr::Symbol(name)) if name == "or") {
            if is_integer(ty) || matches!(ty, Type::Char | Type::Bool) {
                return check_scalar_pattern(pattern, ty);
            }
            check_aggregate_or_pattern(items, ty, structs)?;
            return Ok(());
        }
    }
    match pattern {
        Expr::Symbol(name) if name == "_" => Ok(()),
        Expr::Symbol(name) if name == "true" || name == "false" => {
            if !matches!(ty, Type::Bool) {
                return Err("boolean tuple pattern does not match its field type".into());
            }
            Ok(())
        }
        Expr::Symbol(name) => {
            if variables.contains_key(name) || arm_variables.contains_key(name) {
                return Err(format!("duplicate match binding '{name}'"));
            }
            arm_variables.insert(name.clone(), ty.clone());
            Ok(())
        }
        Expr::Integer(value) if is_integer(ty) => {
            if !fits_integer(*value, ty) {
                return Err(format!(
                    "integer match pattern {value} does not fit in {ty:?}"
                ));
            }
            Ok(())
        }
        Expr::UnsignedInteger(value) if is_integer(ty) => {
            if !fits_unsigned_integer(*value, ty) {
                return Err(format!(
                    "unsigned integer match pattern {value} does not fit in {ty:?}"
                ));
            }
            Ok(())
        }
        Expr::Char(_) if matches!(ty, Type::Char) => Ok(()),
        Expr::List(items) => {
            let Some(Expr::Symbol(constructor)) = items.first() else {
                return Err("aggregate pattern must start with a constructor".into());
            };
            let fields = match ty {
                Type::Tuple(fields) if constructor == "tuple" => fields.clone(),
                Type::Array(element, length) if constructor == "array" => {
                    vec![element.as_ref().clone(); *length]
                }
                Type::Named(name) if constructor == name => structs
                    .get(name)
                    .ok_or_else(|| format!("unknown struct '{name}'"))?
                    .iter()
                    .map(|field| field.ty.clone())
                    .collect(),
                _ => {
                    return Err(
                        "aggregate pattern constructor does not match its field type".into(),
                    )
                }
            };
            if items.len() - 1 != fields.len() {
                return Err(format!("aggregate pattern expects {} fields", fields.len()));
            }
            for (nested, field) in items[1..].iter().zip(fields) {
                check_aggregate_pattern(nested, &field, arm_variables, variables, structs)?;
            }
            Ok(())
        }
        _ => Err("tuple field pattern does not match its field type".into()),
    }
}

fn check_aggregate_or_pattern(
    pattern: &[Expr],
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
) -> Result<bool, String> {
    let mut wildcard = false;
    for alternative in &pattern[1..] {
        if matches!(alternative, Expr::Symbol(name) if name == "_") {
            wildcard = true;
        }
        let mut bindings = HashMap::new();
        check_aggregate_pattern(alternative, ty, &mut bindings, &HashMap::new(), structs)?;
        if !bindings.is_empty() {
            return Err("aggregate or-pattern alternatives cannot bind values".into());
        }
    }
    Ok(wildcard)
}

fn check_array_match(
    items: &[Expr],
    scrutinee: &Type,
    variables: &HashMap<String, Type>,
    functions: &HashMap<String, Signature>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    mutable: &HashSet<String>,
    aliases: &HashMap<String, Type>,
    expected: Option<&Type>,
) -> Result<Type, String> {
    let Type::Array(element, length) = scrutinee else {
        unreachable!()
    };
    let fields = vec![element.as_ref().clone(); *length];
    let mut wildcard = false;
    let mut result_type = None;
    for arm in &items[2..] {
        let (pattern, guard, body) = match_arm_parts(arm)?;
        let mut arm_variables = variables.clone();
        match pattern {
            Expr::Symbol(pattern) if pattern == "_" => {
                if guard.is_none() && wildcard {
                    return Err("duplicate wildcard match pattern".into());
                }
                if guard.is_none() {
                    wildcard = true;
                }
            }
            Expr::List(pattern)
                if pattern.len() >= 2
                    && matches!(pattern.first(), Some(Expr::Symbol(name)) if name == "or") =>
            {
                if check_aggregate_or_pattern(pattern, scrutinee, structs)? && guard.is_none() {
                    wildcard = true;
                }
            }
            Expr::List(pattern) if matches!(pattern.first(), Some(Expr::Symbol(name)) if name == "array") =>
            {
                if pattern.len() - 1 != *length {
                    return Err(format!("array match pattern expects {} elements", length));
                }
                for (pattern, field) in pattern[1..].iter().zip(&fields) {
                    check_aggregate_pattern(
                        pattern,
                        field,
                        &mut arm_variables,
                        variables,
                        structs,
                    )?;
                }
            }
            _ => return Err("array match pattern must be _ or (array pattern ...)".into()),
        }
        if let Some(guard) = guard {
            let guard_type = expression(
                guard,
                &arm_variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&Type::Bool),
            )?;
            require_type(&guard_type, &Type::Bool, "match guard")?;
        }
        let arm_type = expression(
            body,
            &arm_variables,
            functions,
            structs,
            enums,
            mutable,
            aliases,
            result_type
                .as_ref()
                .filter(|ty| !matches!(ty, Type::Never))
                .or(expected),
        )?;
        if let Some(previous) = &result_type {
            result_type = Some(merge_types(previous, &arm_type, "match arms")?);
        } else {
            result_type = Some(arm_type);
        }
    }
    if !wildcard {
        return Err("array match is not exhaustive; add '_' arm".into());
    }
    Ok(result_type.unwrap_or(Type::Unit))
}

fn check_enum_payload_pattern(
    pattern: &Expr,
    ty: &Type,
    arm_variables: &mut HashMap<String, Type>,
    variables: &HashMap<String, Type>,
    structs: &HashMap<String, Vec<Field>>,
) -> Result<(), String> {
    if let Some(value) = typed_integer_pattern_value(pattern, ty)? {
        return check_enum_payload_pattern(value, ty, arm_variables, variables, structs);
    }
    if let Expr::List(items) = pattern {
        if items.len() == 3 && matches!(items.first(), Some(Expr::Symbol(name)) if name == "range")
        {
            return check_scalar_range_pattern(items, ty);
        }
    }
    match pattern {
        Expr::Symbol(name) if name == "_" => Ok(()),
        Expr::Symbol(name) if name == "true" || name == "false" => {
            if !matches!(ty, Type::Bool) {
                return Err("boolean enum payload pattern does not match its field type".into());
            }
            Ok(())
        }
        Expr::Symbol(name) => {
            if variables.contains_key(name) || arm_variables.contains_key(name) {
                return Err(format!("duplicate match binding '{name}'"));
            }
            arm_variables.insert(name.clone(), ty.clone());
            Ok(())
        }
        Expr::List(parts)
            if parts.len() >= 2
                && matches!(parts.first(), Some(Expr::Symbol(name)) if name == "or") =>
        {
            for alternative in &parts[1..] {
                check_scalar_pattern(alternative, ty)?;
            }
            Ok(())
        }
        Expr::Integer(value) if is_integer(ty) => {
            if !fits_integer(*value, ty) {
                return Err(format!(
                    "integer enum payload pattern {value} does not fit in {ty:?}"
                ));
            }
            Ok(())
        }
        Expr::UnsignedInteger(value) if is_integer(ty) => {
            if !fits_unsigned_integer(*value, ty) {
                return Err(format!(
                    "unsigned enum payload pattern {value} does not fit in {ty:?}"
                ));
            }
            Ok(())
        }
        Expr::Char(_) if matches!(ty, Type::Char) => Ok(()),
        Expr::List(_) => check_aggregate_pattern(pattern, ty, arm_variables, variables, structs),
        _ => Err("enum payload pattern does not match its field type".into()),
    }
}

fn check_struct_match(
    items: &[Expr],
    struct_name: &str,
    variables: &HashMap<String, Type>,
    functions: &HashMap<String, Signature>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    mutable: &HashSet<String>,
    aliases: &HashMap<String, Type>,
    expected: Option<&Type>,
) -> Result<Type, String> {
    let fields = structs
        .get(struct_name)
        .ok_or_else(|| format!("unknown struct '{struct_name}'"))?;
    let mut wildcard = false;
    let mut result_type = None;
    for arm in &items[2..] {
        let (pattern, guard, body) = match_arm_parts(arm)?;
        let mut arm_variables = variables.clone();
        match pattern {
            Expr::Symbol(pattern) if pattern == "_" => {
                if guard.is_none() && wildcard {
                    return Err("duplicate wildcard match pattern".into());
                }
                if guard.is_none() {
                    wildcard = true;
                }
            }
            Expr::List(pattern)
                if pattern.len() >= 2
                    && matches!(pattern.first(), Some(Expr::Symbol(name)) if name == "or") =>
            {
                if check_aggregate_or_pattern(
                    pattern,
                    &Type::Named(struct_name.to_owned()),
                    structs,
                )? && guard.is_none()
                {
                    wildcard = true;
                }
            }
            Expr::List(pattern) if matches!(pattern.first(), Some(Expr::Symbol(name)) if name == struct_name) =>
            {
                if pattern.len() - 1 != fields.len() {
                    return Err(format!(
                        "struct match pattern expects {} fields",
                        fields.len()
                    ));
                }
                for (pattern, field) in pattern[1..].iter().zip(fields) {
                    check_aggregate_pattern(
                        pattern,
                        &field.ty,
                        &mut arm_variables,
                        variables,
                        structs,
                    )?;
                }
            }
            _ => {
                return Err(format!(
                    "struct match pattern must be _ or ({struct_name} field-pattern ...)"
                ))
            }
        }
        if let Some(guard) = guard {
            let guard_type = expression(
                guard,
                &arm_variables,
                functions,
                structs,
                enums,
                mutable,
                aliases,
                Some(&Type::Bool),
            )?;
            require_type(&guard_type, &Type::Bool, "match guard")?;
        }
        let arm_type = expression(
            body,
            &arm_variables,
            functions,
            structs,
            enums,
            mutable,
            aliases,
            result_type
                .as_ref()
                .filter(|ty| !matches!(ty, Type::Never))
                .or(expected),
        )?;
        if let Some(previous) = &result_type {
            result_type = Some(merge_types(previous, &arm_type, "match arms")?);
        } else {
            result_type = Some(arm_type);
        }
    }
    if !wildcard {
        return Err("struct match is not exhaustive; add '_' arm".into());
    }
    Ok(result_type.unwrap_or(Type::Unit))
}

fn require_arity(operator: &str, items: &[Expr], expected: usize) -> Result<(), String> {
    if items.len() != expected {
        Err(format!(
            "operator '{operator}' expects {} operands",
            expected - 1
        ))
    } else {
        Ok(())
    }
}

fn split_generic_call(operator: &str) -> Result<(String, Vec<String>), String> {
    let Some(open) = operator.find('<') else {
        return Ok((operator.to_owned(), Vec::new()));
    };
    if !operator.ends_with('>') || open == 0 {
        return Err(format!("malformed generic call '{operator}'"));
    }
    let name = operator[..open].to_owned();
    let arguments = &operator[open + 1..operator.len() - 1];
    if arguments.is_empty() {
        return Err(format!("generic call '{operator}' has no type arguments"));
    }
    let arguments = arguments
        .split(',')
        .map(str::trim)
        .map(|argument| {
            if argument.is_empty() {
                Err(format!(
                    "generic call '{operator}' has an empty type argument"
                ))
            } else {
                Ok(argument.to_owned())
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((name, arguments))
}

fn generic_substitutions(
    signature: &Signature,
    arguments: &[String],
    aliases: &HashMap<String, Type>,
) -> Result<HashMap<String, Type>, String> {
    if signature.type_parameters.len() != arguments.len() {
        if signature.type_parameters.is_empty() && arguments.is_empty() {
            return Ok(HashMap::new());
        }
        return Err(format!(
            "generic function expects {} type arguments, got {}",
            signature.type_parameters.len(),
            arguments.len()
        ));
    }
    signature
        .type_parameters
        .iter()
        .zip(arguments)
        .map(|(parameter, argument)| {
            let ty = resolve_type(&Type::from_name(argument), aliases)?;
            if matches!(ty, Type::Generic(_)) {
                return Err(format!(
                    "generic type argument '{argument}' is not concrete"
                ));
            }
            Ok((parameter.clone(), ty))
        })
        .collect()
}

fn substitute_type(ty: &Type, substitutions: &HashMap<String, Type>) -> Type {
    match ty {
        Type::Generic(name) => substitutions
            .get(name)
            .cloned()
            .unwrap_or_else(|| ty.clone()),
        Type::Array(element, length) => {
            Type::Array(Box::new(substitute_type(element, substitutions)), *length)
        }
        Type::Slice(element) => Type::Slice(Box::new(substitute_type(element, substitutions))),
        Type::MutableSlice(element) => {
            Type::MutableSlice(Box::new(substitute_type(element, substitutions)))
        }
        Type::Tuple(fields) => Type::Tuple(
            fields
                .iter()
                .map(|field| substitute_type(field, substitutions))
                .collect(),
        ),
        Type::Reference { mutable, target } => Type::Reference {
            mutable: *mutable,
            target: Box::new(substitute_type(target, substitutions)),
        },
        Type::RawPointer { mutable, target } => Type::RawPointer {
            mutable: *mutable,
            target: Box::new(substitute_type(target, substitutions)),
        },
        Type::Cell(target) => Type::Cell(Box::new(substitute_type(target, substitutions))),
        Type::Atomic(target) => Type::Atomic(Box::new(substitute_type(target, substitutions))),
        _ => ty.clone(),
    }
}

fn resolve_type(ty: &Type, aliases: &HashMap<String, Type>) -> Result<Type, String> {
    resolve_type_with_seen(ty, aliases, &mut HashSet::new())
}

fn resolve_type_with_seen(
    ty: &Type,
    aliases: &HashMap<String, Type>,
    seen: &mut HashSet<String>,
) -> Result<Type, String> {
    match ty {
        Type::Named(name) => {
            let Some(target) = aliases.get(name) else {
                return Ok(ty.clone());
            };
            if !seen.insert(name.clone()) {
                return Err(format!("type alias '{name}' is recursive"));
            }
            let result = resolve_type_with_seen(target, aliases, seen);
            seen.remove(name);
            result
        }
        Type::Array(element, length) => Ok(Type::Array(
            Box::new(resolve_type_with_seen(element, aliases, seen)?),
            *length,
        )),
        Type::Slice(element) => Ok(Type::Slice(Box::new(resolve_type_with_seen(
            element, aliases, seen,
        )?))),
        Type::MutableSlice(element) => Ok(Type::MutableSlice(Box::new(resolve_type_with_seen(
            element, aliases, seen,
        )?))),
        Type::Atomic(element) => Ok(Type::Atomic(Box::new(resolve_type_with_seen(
            element, aliases, seen,
        )?))),
        Type::Tuple(fields) => Ok(Type::Tuple(
            fields
                .iter()
                .map(|field| resolve_type_with_seen(field, aliases, seen))
                .collect::<Result<Vec<_>, _>>()?,
        )),
        Type::Reference { mutable, target } => Ok(Type::Reference {
            mutable: *mutable,
            target: Box::new(resolve_type_with_seen(target, aliases, seen)?),
        }),
        Type::RawPointer { mutable, target } => Ok(Type::RawPointer {
            mutable: *mutable,
            target: Box::new(resolve_type_with_seen(target, aliases, seen)?),
        }),
        Type::Cell(target) => Ok(Type::Cell(Box::new(resolve_type_with_seen(
            target, aliases, seen,
        )?))),
        _ => Ok(ty.clone()),
    }
}

fn validate_layout_type(
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
) -> Result<(), String> {
    match ty {
        Type::Atomic(target) if is_atomic_scalar(target) => Ok(()),
        Type::Atomic(_) => Err("atomic type requires a supported integer scalar".into()),
        Type::Named(name) if structs.contains_key(name) => structs
            .get(name)
            .into_iter()
            .flat_map(|fields| fields.iter())
            .try_for_each(|field| validate_layout_type(&field.ty, structs, enums)),
        Type::Named(name) if enums.contains_key(name) => enums
            .get(name)
            .into_iter()
            .flat_map(|variants| variants.iter())
            .flat_map(|variant| variant.fields.iter())
            .try_for_each(|field| validate_layout_type(field, structs, enums)),
        Type::Named(name) => Err(format!("unknown type '{name}' in size-of")),
        Type::Array(element, _) | Type::Slice(element) | Type::MutableSlice(element) => {
            validate_layout_type(element, structs, enums)
        }
        Type::Tuple(fields) => fields
            .iter()
            .try_for_each(|field| validate_layout_type(field, structs, enums)),
        Type::Generic(name) => Err(format!("generic type '{name}' has no concrete size")),
        _ => Ok(()),
    }
}

fn enum_variant_type(name: &str, enums: &HashMap<String, Vec<EnumVariant>>) -> Option<Type> {
    enums.iter().find_map(|(enum_name, variants)| {
        variants
            .iter()
            .any(|variant| variant.name == name)
            .then(|| Type::Named(enum_name.clone()))
    })
}

fn check_index(
    index: &Expr,
    length: usize,
    variables: &HashMap<String, Type>,
    functions: &HashMap<String, Signature>,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    mutable: &HashSet<String>,
    aliases: &HashMap<String, Type>,
) -> Result<(), String> {
    let actual = expression(
        index, variables, functions, structs, enums, mutable, aliases, None,
    )?;
    if !is_integer(&actual) {
        return Err("array index must be an integer".into());
    }
    if let Expr::Integer(value) = index {
        if *value < 0 || *value >= length as i128 {
            return Err(format!(
                "array index {value} is out of bounds for length {length}"
            ));
        }
    }
    Ok(())
}

fn require_type(actual: &Type, expected: &Type, context: &str) -> Result<(), String> {
    if actual == expected || matches!(actual, Type::Never) {
        Ok(())
    } else {
        Err(format!(
            "{context} has type {actual:?}, expected {expected:?}"
        ))
    }
}

fn merge_types(left: &Type, right: &Type, context: &str) -> Result<Type, String> {
    if matches!(left, Type::Never) {
        return Ok(right.clone());
    }
    if matches!(right, Type::Never) {
        return Ok(left.clone());
    }
    require_same(left, right, context)?;
    Ok(left.clone())
}

fn require_same(left: &Type, right: &Type, context: &str) -> Result<(), String> {
    if left == right {
        Ok(())
    } else {
        Err(format!(
            "{context} has mismatched types {left:?} and {right:?}"
        ))
    }
}

fn is_integer(ty: &Type) -> bool {
    matches!(
        ty,
        Type::I8
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
    )
}

fn is_numeric(ty: &Type) -> bool {
    is_integer(ty) || matches!(ty, Type::F32 | Type::F64)
}

fn is_reference_target(ty: &Type) -> bool {
    !matches!(ty, Type::Unit | Type::Never)
}

fn is_scalar_reference_target(ty: &Type, enums: &HashMap<String, Vec<EnumVariant>>) -> bool {
    (is_numeric(ty) && !matches!(ty, Type::I128 | Type::U128))
        || matches!(ty, Type::Bool | Type::Char | Type::RawPointer { .. })
        || matches!(ty, Type::Named(name) if enums
            .get(name)
            .is_some_and(|variants| variants.iter().all(|variant| variant.fields.is_empty())))
}

fn is_cell_value_type(ty: &Type, enums: &HashMap<String, Vec<EnumVariant>>) -> bool {
    if matches!(ty, Type::Cell(_)) {
        return false;
    }
    (is_numeric(ty) && !matches!(ty, Type::I128 | Type::U128))
        || matches!(ty, Type::Bool | Type::Char | Type::RawPointer { .. })
        || matches!(ty, Type::Named(name) if enums
            .get(name)
            .is_some_and(|variants| variants.iter().all(|variant| variant.fields.is_empty())))
}

fn contains_reference_type(
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    seen: &mut HashSet<String>,
) -> bool {
    match ty {
        Type::Reference { .. } | Type::Slice(_) | Type::MutableSlice(_) => true,
        Type::Array(element, _) | Type::Cell(element) => {
            contains_reference_type(element, structs, enums, seen)
        }
        Type::Tuple(fields) => fields
            .iter()
            .any(|field| contains_reference_type(field, structs, enums, seen)),
        Type::Named(name) if seen.insert(name.clone()) => {
            let result = structs.get(name).is_some_and(|fields| {
                fields
                    .iter()
                    .any(|field| contains_reference_type(&field.ty, structs, enums, seen))
            }) || enums.get(name).is_some_and(|variants| {
                variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|field| contains_reference_type(field, structs, enums, seen))
            });
            seen.remove(name);
            result
        }
        _ => false,
    }
}

fn type_contains_mutable_reference(
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    seen: &mut HashSet<String>,
) -> bool {
    match ty {
        Type::Reference { mutable: true, .. } => true,
        Type::MutableSlice(_) => true,
        Type::Reference { mutable: false, .. } | Type::RawPointer { .. } => false,
        Type::Array(element, _) | Type::Cell(element) => {
            type_contains_mutable_reference(element, structs, enums, seen)
        }
        Type::Tuple(fields) => fields
            .iter()
            .any(|field| type_contains_mutable_reference(field, structs, enums, seen)),
        Type::Named(name) if seen.insert(name.clone()) => {
            let result = structs.get(name).is_some_and(|fields| {
                fields
                    .iter()
                    .any(|field| type_contains_mutable_reference(&field.ty, structs, enums, seen))
            }) || enums.get(name).is_some_and(|variants| {
                variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|field| type_contains_mutable_reference(field, structs, enums, seen))
            });
            seen.remove(name);
            result
        }
        _ => false,
    }
}

fn require_operator_type(qualifier: &str, ty: &Type, operator: &str) -> Result<(), String> {
    let expected = match ty {
        Type::Unit => "()",
        Type::Never => "!",
        Type::Bool => "bool",
        Type::Char => "char",
        Type::I8 => "i8",
        Type::I16 => "i16",
        Type::I32 => "i32",
        Type::I64 => "i64",
        Type::I128 => "i128",
        Type::Isize => "isize",
        Type::U8 => "u8",
        Type::U16 => "u16",
        Type::U32 => "u32",
        Type::U64 => "u64",
        Type::U128 => "u128",
        Type::Usize => "usize",
        Type::F32 => "f32",
        Type::F64 => "f64",
        Type::Reference { .. } => "reference",
        Type::Slice(_) => "slice",
        Type::MutableSlice(_) => "mutable slice",
        Type::Atomic(_) => "atomic",
        Type::RawPointer { .. } => "raw pointer",
        Type::Cell(_) => "interior mutable cell",
        Type::Generic(name) | Type::Named(name) => name,
        Type::Array(_, _) | Type::Tuple(_) => {
            return Err(format!(
                "operator '{operator}' has an unsupported operand type {ty:?}"
            ))
        }
    };
    if qualifier == expected {
        Ok(())
    } else {
        Err(format!(
            "operator '{operator}' is qualified for '{qualifier}', but its operand type is '{expected}'"
        ))
    }
}

fn is_atomic_scalar(ty: &Type) -> bool {
    matches!(
        ty,
        Type::I8
            | Type::I16
            | Type::I32
            | Type::I64
            | Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::Usize
    )
}

fn atomic_memory_order(expression: Option<&Expr>) -> Option<&str> {
    let Expr::Symbol(name) = expression? else {
        return None;
    };
    name.strip_prefix("#memory-")
        .or_else(|| name.strip_prefix("memory-"))
}

fn typed_operator_parts(operator: &str) -> (Option<&str>, &str, Option<&str>) {
    let Some((qualifier, operation)) = operator.split_once('.') else {
        return (None, operator, None);
    };
    if !is_builtin_operator_type(qualifier)
        || !matches!(
            operation.split('.').next(),
            Some(
                "+" | "-"
                    | "*"
                    | "/"
                    | "%"
                    | "&"
                    | "|"
                    | "^"
                    | "<<"
                    | ">>"
                    | "<"
                    | "<="
                    | ">"
                    | ">="
                    | "=="
                    | "!="
                    | "!"
                    | "&&"
                    | "||"
            )
        )
    {
        return (None, operator, None);
    }
    let Some((operation, mode)) = operation.split_once('.') else {
        return (Some(qualifier), operation, None);
    };
    (Some(qualifier), operation, Some(mode))
}

fn is_builtin_operator_type(name: &str) -> bool {
    matches!(
        name,
        "bool"
            | "char"
            | "i8"
            | "i16"
            | "i32"
            | "i64"
            | "i128"
            | "isize"
            | "u8"
            | "u16"
            | "u32"
            | "u64"
            | "u128"
            | "usize"
            | "f32"
            | "f64"
    )
}

fn require_arithmetic_mode(
    operation: &str,
    mode: Option<&str>,
    operator: &str,
    ty: &Type,
) -> Result<(), String> {
    if !matches!(operation, "+" | "-" | "*" | "/" | "%") {
        if mode.is_some() {
            return Err(format!(
                "non-arithmetic operator '{operator}' cannot have a wrapping mode"
            ));
        }
        return Ok(());
    }
    if matches!(ty, Type::F32 | Type::F64) {
        if mode.is_some() {
            return Err(format!(
                "floating-point operator '{operator}' cannot have a wrapping mode"
            ));
        }
        return Ok(());
    }
    if !is_numeric(ty) {
        return Ok(());
    }
    let Some(mode) = mode else {
        return Err(format!(
            "arithmetic operator '{operator}' requires '.wrap' or '.saturate'"
        ));
    };
    if !matches!(mode, "wrap" | "saturate") {
        return Err(format!(
            "arithmetic operator '{operator}' has unknown mode '.{mode}'"
        ));
    }
    Ok(())
}

fn is_matchable_scalar(ty: &Type) -> bool {
    is_integer(ty) || matches!(ty, Type::Bool | Type::Char)
}

fn integer_width(ty: &Type) -> Option<i128> {
    match ty {
        Type::I8 | Type::U8 => Some(8),
        Type::I16 | Type::U16 => Some(16),
        Type::I32 | Type::U32 => Some(32),
        Type::I64 | Type::U64 | Type::Isize | Type::Usize => Some(64),
        Type::I128 | Type::U128 => Some(128),
        _ => None,
    }
}

fn is_cast_operand(ty: &Type) -> bool {
    is_numeric(ty) || matches!(ty, Type::Bool | Type::Char)
}

fn is_cast_target(ty: &Type) -> bool {
    is_numeric(ty) || matches!(ty, Type::Char)
}

fn fits_integer(value: i128, ty: &Type) -> bool {
    let (minimum, maximum) = match ty {
        Type::I8 => (i8::MIN as i128, i8::MAX as i128),
        Type::I16 => (i16::MIN as i128, i16::MAX as i128),
        Type::I32 => (i32::MIN as i128, i32::MAX as i128),
        Type::I64 => (i64::MIN as i128, i64::MAX as i128),
        Type::I128 => (i128::MIN, i128::MAX),
        Type::Isize => (isize::MIN as i128, isize::MAX as i128),
        Type::U8 => (0, u8::MAX as i128),
        Type::U16 => (0, u16::MAX as i128),
        Type::U32 => (0, u32::MAX as i128),
        Type::U64 => (0, u64::MAX as i128),
        Type::U128 => (0, i128::MAX),
        Type::Usize => (0, usize::MAX as i128),
        _ => return false,
    };
    (minimum..=maximum).contains(&value)
}

fn fits_unsigned_integer(value: u128, ty: &Type) -> bool {
    let maximum = match ty {
        Type::I8 => i8::MAX as u128,
        Type::I16 => i16::MAX as u128,
        Type::I32 => i32::MAX as u128,
        Type::I64 => i64::MAX as u128,
        Type::I128 => i128::MAX as u128,
        Type::Isize => isize::MAX as u128,
        Type::U8 => u8::MAX as u128,
        Type::U16 => u16::MAX as u128,
        Type::U32 => u32::MAX as u128,
        Type::U64 => u64::MAX as u128,
        Type::U128 => u128::MAX,
        Type::Usize => usize::MAX as u128,
        _ => return false,
    };
    value <= maximum
}
