#![allow(clippy::too_many_arguments)]

use std::collections::{HashMap, HashSet};

use crate::{
    parse_type, CallingConvention, EnumVariant, Expr, Field, Function, Item, Program,
    Representation, Statement, ThreadProperty, Type,
};

const LOOP_VALUE_CONTEXT: &str = "\0lim-loop-value";
#[derive(Clone, Debug)]
enum ErrorSite {
    Value,
    Symbol(String),
    DeclaredType(String),
    Operator(String),
    Argument(String, usize),
    TupleElement(usize),
    ArrayElement(usize),
    ConstructorArity(&'static str, usize),
    Payload(String, usize),
    Field(String),
    NamedArgument(String, String),
    PatternSymbol(String),
    PatternInteger(u128),
    PatternCharacter,
    PatternRange(bool),
    Mismatch(Type, Option<Type>),
    BranchMismatch(Type),
}

#[derive(Clone, Debug)]
struct SemanticError {
    message: String,
    code: crate::DiagnosticCode,
    site: Box<ErrorSite>,
    scope: Option<Box<Expr>>,
    origin: Option<usize>,
}
impl SemanticError {
    fn at(mut self, site: ErrorSite) -> Self {
        self.site = Box::new(site);
        self
    }
}
impl From<String> for SemanticError {
    fn from(message: String) -> Self {
        #[cfg(test)]
        let message = if REWORD_ERRORS.with(|flag| flag.get()) {
            "wording deliberately replaced".into()
        } else {
            message
        };
        Self {
            message,
            code: crate::DiagnosticCode::Type,
            site: Box::new(ErrorSite::Value),
            scope: None,
            origin: None,
        }
    }
}

#[cfg(test)]
thread_local! { static REWORD_ERRORS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) }; }
impl From<&str> for SemanticError {
    fn from(message: &str) -> Self {
        message.to_owned().into()
    }
}
impl From<SemanticError> for String {
    fn from(error: SemanticError) -> Self {
        error.message
    }
}
impl std::ops::Deref for SemanticError {
    type Target = str;
    fn deref(&self) -> &str {
        &self.message
    }
}
impl std::fmt::Display for SemanticError {
    fn fmt(&self, output: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        output.write_str(&self.message)
    }
}

macro_rules! semantic_format {
    ($($args:tt)*) => { format!($($args)*).into() };
}
macro_rules! semantic_at {
    ($site:expr, $($args:tt)*) => { SemanticError::from(format!($($args)*)).at($site) };
}

fn borrow_error(message: &str) -> SemanticError {
    let mut error = SemanticError::from(message).at(ErrorSite::Argument("borrow-mut".into(), 1));
    error.code = crate::DiagnosticCode::Borrow;
    error
}

use crate::typed_ir::{Declarations, Signature};

#[derive(Default)]
struct FunctionTable {
    signatures: HashMap<String, Signature>,
    expression_types: std::cell::RefCell<HashMap<usize, Type>>,
    source_spans: std::cell::RefCell<HashMap<usize, crate::Span>>,
    collecting_sources: std::cell::Cell<bool>,
}

impl std::ops::Deref for FunctionTable {
    type Target = HashMap<String, Signature>;
    fn deref(&self) -> &Self::Target {
        &self.signatures
    }
}

impl std::ops::DerefMut for FunctionTable {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.signatures
    }
}

pub fn check_types(program: &Program) -> Result<(), String> {
    check_types_with_span(program).map_err(|(message, _, _, _)| message)
}

/// An immutable program whose semantic validation has succeeded. The private
/// field prevents emission callers from constructing or invalidating this proof.
pub struct CheckedProgram<'a> {
    program: &'a Program,
    declarations: Declarations,
}

pub(crate) type AnalysisError = (
    String,
    crate::DiagnosticCode,
    Option<crate::Span>,
    Vec<(crate::Span, String)>,
);

impl<'a> CheckedProgram<'a> {
    pub(crate) fn validate_with_span(program: &'a Program) -> Result<Self, AnalysisError> {
        let declarations = resolve_program(program)?;
        Ok(Self {
            program,
            declarations,
        })
    }
    pub fn validate(program: &'a Program) -> Result<Self, String> {
        Self::validate_with_span(program).map_err(|error| error.0)
    }

    pub(crate) fn program(&self) -> &'a Program {
        self.program
    }

    pub(crate) fn declarations(&self) -> &Declarations {
        &self.declarations
    }

    /// Inspect the retained body representation. This is a compiler debugging
    /// format, not a stable interchange format.
    pub fn dump_typed_ir(&self) -> String {
        let mut names: Vec<_> = self.declarations.bodies.keys().collect();
        names.sort();
        names
            .into_iter()
            .map(|name| {
                format!(
                    "function {name}\n{}{}",
                    self.declarations.bodies[name].dump(),
                    self.declarations.flows[name].dump(&self.declarations.liveness[name])
                )
            })
            .collect()
    }

    /// Emit a previously validated, immutably borrowed program.
    pub fn generate_assembly(&self, target: crate::TargetDescription) -> Result<String, String> {
        crate::codegen::generate_checked_assembly(self, target).map_err(String::from)
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
    fn semantic_locations_do_not_depend_on_rendered_wording() {
        let cases = [
            ("(#fn main () u64 (#let value u64 (#u64.+.wrap 1u64 false)) (#return value))", "false"),
            ("(#fn main () u64 (#let value u64 1u64) (#let value bool false) (#return (#u64.+.wrap 2u64 value)))", "value"),
            ("(#fn add ((first u64) (second u64)) u64 (#return (#u64.+.wrap first second))) (#fn main () u64 (#return (#call add (#fn-args (second false) (first 1u64)))))", "false"),
            ("(#struct Inner ((value u64))) (#struct Outer ((first Inner) (second Inner))) (#fn main () Outer (#return (#struct-literal Outer ((first (#struct-literal Inner ((value 1u64)))) (second (#struct-literal Inner ((value false))))))))", "false"),
            ("(#fn main () u64 (#let-mut value u64 0u64) (#let shared (#ref u64) (#borrow value)) (#let mutable (#ref-mut u64) (#borrow-mut shared)) (#return 0u64))", "shared"),
            ("(#fn main () u64 (#return (#get (#tuple (#tuple u64 u64) 1u64 false) 0)))", "false"),
            ("(#fn main () u64 (#return (#u64.+.wrap (#if false 1u64 2u64) false)))", "false"),
            ("(#fn choose ((flag bool) (value u64)) u64 (#return value)) (#fn main () u64 (#return (#call choose (#fn-args (value false) (flag false)))))", "false"),
            ("(#struct Point ((value u64))) (#fn main () u64 (#let-mut owner Point (#struct-literal Point ((value 1u64)))) (#let shared (#ref Point) (#borrow owner)) (#let exclusive (#ref-mut u64) (#borrow-mut (#get shared value))) (#return 0u64))", "(#get shared value)"),
            ("(#fn main () u64 (#return (#block (#let value u64 1u64) (#u64.+.wrap value 2u64) (#let value bool false) (#u64.+.wrap value 2u64))))", "value"),
        ];
        for (source, offending) in cases {
            let program = crate::parse_program(source).unwrap();
            let normal = check_types_with_span(&program).unwrap_err();
            REWORD_ERRORS.with(|flag| flag.set(true));
            let changed = check_types_with_span(&program).unwrap_err();
            REWORD_ERRORS.with(|flag| flag.set(false));
            assert_eq!(normal.1, changed.1);
            assert_eq!(normal.2, changed.2, "{source}");
            assert_eq!(normal.3, changed.3);
            assert_ne!(
                normal.0, changed.0,
                "producer did not use the structured error path: {source}"
            );
            let span = normal.2.unwrap();
            assert_eq!(
                &source[span.start..span.end],
                offending,
                "{}: {source}",
                normal.0
            );
            if source.contains("(#if false") {
                assert_eq!(span.start, source.rfind("false").unwrap());
            }
            if source.contains("(#fn choose") {
                assert_eq!(
                    span.start,
                    source.find("(value false)").unwrap() + "(value ".len()
                );
            }
            if source.contains("(#return (#block") {
                assert_eq!(span.start, source.rfind("value").unwrap());
            }
        }
    }

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
    resolve_program(program).map(|_| ())
}

fn resolve_program(program: &Program) -> Result<Declarations, AnalysisError> {
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
) -> Result<Declarations, String> {
    #[cfg(test)]
    SEMANTIC_PASSES.with(|passes| passes.set(passes.get() + 1));
    for item in &program.items {
        match item {
            Item::Function(function)
                if function.external != (function.calling_convention == CallingConvention::C) =>
            {
                *diagnostic_span = function_name_span(program, &function.name);
                return Err(semantic_format!(
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
                return Err(semantic_format!(
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
                return Err(semantic_format!("duplicate type name '{name}'"));
            }
            _ => {}
        }
    }
    let mut linear_annotations = HashSet::new();
    for item in &program.items {
        let Item::LinearAnnotation { type_name } = item else {
            continue;
        };
        let key = format!("$linear:{type_name}");
        let occurrence = usize::from(linear_annotations.contains(type_name));
        *diagnostic_span = program
            .declaration_occurrences
            .get(&key)
            .and_then(|sources| sources.get(occurrence))
            .or_else(|| program.declaration_expressions.get(&key))
            .and_then(|source| source.children.get(1))
            .map(|source| source.span);
        if !program.items.iter().any(|item| {
            matches!(item,
            Item::Struct { name, type_parameters, .. } | Item::Enum { name, type_parameters, .. }
                if name == type_name && type_parameters.is_empty())
        }) {
            return Err(format!(
                "#linear requires a concrete struct or enum, got '{type_name}'"
            ));
        }
        if !linear_annotations.insert(type_name) {
            return Err(format!("duplicate #linear annotation for '{type_name}'"));
        }
    }
    *diagnostic_span = None;
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
            return Err(semantic_format!(
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
            return Err(semantic_format!(
                "unsafe {:?} annotation for generic type '{type_name}' is not supported",
                property
            ));
        }
        if !unsafe_thread_properties.insert((type_name.clone(), *property)) {
            *diagnostic_span = unsafe_impl_type_span(program, type_name, *property, 1);
            return Err(semantic_format!(
                "duplicate unsafe {:?} annotation for '{type_name}'",
                property
            ));
        }
    }
    let mut aliases = HashMap::new();
    for item in &program.items {
        if let Item::TypeAlias { name, target, .. } = item {
            if aliases.insert(name.clone(), target.clone()).is_some() {
                return Err(semantic_format!("duplicate type alias '{name}'"));
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
            return Err(error.into());
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
                return Err(semantic_format!(
                    "top-level binding '{name}' cannot be mutable"
                ));
            }
            if globals
                .insert(name.clone(), resolve_type(ty, &aliases)?)
                .is_some()
            {
                *diagnostic_span = declaration_name_span(program, name);
                record_generated_invocation(program, diagnostic_span, diagnostic_labels);
                return Err(semantic_format!("duplicate global '{name}'"));
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
                        return Err(semantic_format!(
                            "duplicate field '{}' in struct '{name}'",
                            field.name
                        ));
                    }
                    Ok(Field {
                        name: field.name.clone(),
                        ty: resolve_type(&field.ty, &aliases)?,
                    })
                })
                .collect::<Result<Vec<_>, SemanticError>>()?;
            if structs.insert(name.clone(), fields).is_some() {
                return Err(semantic_format!("duplicate struct '{name}'"));
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
                return Err(semantic_format!("duplicate thread task type '{name}'"));
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
                        return Err(semantic_format!(
                            "duplicate variant '{}' in enum '{name}'",
                            variant.name
                        ));
                    }
                    if let Some(previous) = variant_names.insert(variant.name.clone(), name.clone())
                    {
                        *diagnostic_span = global_enum_member_span(program, &variant.name, 1);
                        return Err(semantic_format!(
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
                .collect::<Result<Vec<_>, SemanticError>>()?;
            if enums.insert(name.clone(), variants).is_some() {
                return Err(semantic_format!("duplicate enum '{name}'"));
            }
        }
    }
    let mut functions = FunctionTable::default();
    for item in &program.items {
        let Item::Function(function) = item else {
            continue;
        };
        let clone_hook = function
            .name
            .strip_suffix("-clone")
            .is_some_and(|name| structs.contains_key(name) || enums.contains_key(name));
        if (function.external || function.unsafe_call) && (function.name == "main" || clone_hook) {
            *diagnostic_span = function_name_span(program, &function.name);
            return Err(semantic_format!(
                "implicit entry point '{}' must be safe; use an explicit unsafe call inside a safe wrapper",
                function.name
            ));
        }
        if function.external && !function.type_parameters.is_empty() {
            *diagnostic_span = function_name_span(program, &function.name);
            return Err(semantic_format!(
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
                        .collect::<Result<Vec<_>, SemanticError>>()?,
                    return_type: resolve_type(&function.return_type, &aliases)?,
                },
            )
            .is_some()
        {
            *diagnostic_span = function_name_span(program, &function.name);
            return Err(semantic_format!("duplicate function '{}'", function.name));
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
            return Err(semantic_format!(
                "thread task '{name}' refers to unknown worker function '{worker}'"
            ));
        };
        if worker_item.external || worker_item.unsafe_call {
            *diagnostic_span = program
                .declaration_expressions
                .get(name)
                .and_then(|declaration| first_symbol_span(declaration, worker));
            return Err(semantic_format!(
                "thread worker '{worker}' must be safe; use a safe wrapper with an explicit unsafe call"
            ));
        }
        if !worker_item.type_parameters.is_empty() {
            return Err(semantic_format!(
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
                    return Err(semantic_format!(
                        "{error} while checking thread worker '{worker}'"
                    ));
                }
            };
            if !send {
                *diagnostic_span = worker_parameter_span(program, worker, parameter_index);
                record_generated_invocation(program, diagnostic_span, diagnostic_labels);
                return Err(semantic_format!(
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
                return Err(semantic_format!(
                    "{error} while checking thread worker '{worker}'"
                ));
            }
        };
        if !return_send {
            *diagnostic_span = worker_return_span(program, worker);
            record_generated_invocation(program, diagnostic_span, diagnostic_labels);
            return Err(semantic_format!(
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
            return Err(semantic_format!(
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
                return Err(semantic_format!(
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
            | Item::LinearAnnotation { .. }
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
                result.map_err(|error: SemanticError| {
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
                    let origin = semantic_expression_source(
                        value,
                        crate::source_value_expression(declaration),
                        error.origin,
                        false,
                        &functions,
                        &structs,
                    );
                    *diagnostic_span =
                        semantic_error_span(origin.unwrap_or(declaration), &error, source);
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
    functions.collecting_sources.set(true);
    for item in &program.items {
        match item {
            Item::Function(function) => {
                for (index, statement) in function.body.iter().enumerate() {
                    if let Some(source) = program
                        .statement_expressions
                        .get(&(function.name.clone(), index))
                    {
                        semantic_statement_source(
                            statement,
                            source,
                            Some(usize::MAX),
                            false,
                            &functions,
                            &structs,
                        );
                    }
                }
            }
            Item::Let { name, value, .. } | Item::Static { name, value, .. } => {
                if let Some(source) = program.declaration_expressions.get(name) {
                    semantic_expression_source(
                        value,
                        crate::source_value_expression(source),
                        Some(usize::MAX),
                        false,
                        &functions,
                        &structs,
                    );
                }
            }
            _ => {}
        }
    }
    let mut declarations = Declarations::new(
        aliases,
        structs,
        enums,
        globals,
        functions.signatures,
        &program.declaration_spans,
    );
    declarations.lower_bodies(
        program,
        &functions.expression_types.into_inner(),
        &functions.source_spans.into_inner(),
    )?;
    check_thread_task_ownership(
        program,
        &declarations.aliases,
        diagnostic_span,
        diagnostic_labels,
    )?;
    *diagnostic_code = crate::DiagnosticCode::Linear;
    crate::linearcheck::check_program_with_span(program).map_err(|(message, span, labels)| {
        *diagnostic_span = span;
        *diagnostic_labels = labels;
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
    Ok(declarations)
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
                        return Err(semantic_format!(
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
                        return Err(semantic_format!(
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
                    return Err(semantic_format!(
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
                    return Err(semantic_format!(
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
                    return Err(semantic_format!(
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
            Item::UnsafeThreadAnnotation { .. }
            | Item::LinearAnnotation { .. }
            | Item::ThreadTask { .. } => {}
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
                                return Err(semantic_format!(
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
            return Err(semantic_format!(
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
                    return Err(semantic_format!(
                        "thread task handle '{name}' must be immutable and consumed by join"
                    ));
                }
                let expected_spawn = format!("{task_type}-spawn");
                if !is_direct_thread_call(value, &expected_spawn) {
                    return Err(semantic_format!(
                        "thread task '{name}' must be initialized directly by '{expected_spawn}'"
                    ));
                }
                let Expr::List(items) = value else {
                    unreachable!()
                };
                check_task_expression_children(&items[1..], &handles, tasks)?;
                if handles.insert(name.clone(), task_type.clone()).is_some() {
                    return Err(semantic_format!("duplicate thread task binding '{name}'"));
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
                        return Err(semantic_format!(
                            "function '{}' may return while thread task '{}' is still running",
                            function.name,
                            pending.iter().next().unwrap()
                        ));
                    }
                }
            }
            Statement::Return(None) => {
                if !pending.is_empty() {
                    return Err(semantic_format!(
                        "function '{}' may return while thread task '{}' is still running",
                        function.name,
                        pending.iter().next().unwrap()
                    ));
                }
            }
            _ => {
                check_task_statement(statement, &handles, tasks)?;
                if !pending.is_empty() && is_control_statement(statement) {
                    return Err(semantic_format!(
                        "thread task handles cannot cross control flow; join '{}' before this statement",
                        pending.iter().next().unwrap()
                    ));
                }
            }
        }
    }
    if let Some(handle) = pending.iter().next() {
        return Err(semantic_format!(
            "thread task handle '{handle}' is not joined exactly once"
        ));
    }
    if let Some(handle) = handles.keys().find(|handle| !consumed.contains(*handle)) {
        return Err(semantic_format!(
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
        return Err(semantic_format!(
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
        Some(_) if consumed.contains(handle) => Err(semantic_format!(
            "thread task handle '{handle}' was joined more than once"
        )),
        Some(_) => Err(semantic_format!(
            "thread task handle '{handle}' is not active"
        )),
        None => Err(semantic_format!("'{handle}' is not a thread task handle")),
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
                return Err(semantic_format!(
                    "thread task handle '{name}' may only be used once as the direct argument to join"
                ));
            }
            Expr::List(items) => {
                if let Some(Expr::Symbol(name)) = items.first() {
                    if tasks.contains_key(name) && items.len() > 1 {
                        return Err(semantic_format!(
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
                    .collect::<Result<Vec<_>, SemanticError>>(),
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
                    .collect::<Result<Vec<_>, SemanticError>>(),
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
                return Err(semantic_format!(
                    "unknown type '{name}' while checking {property:?}"
                ));
            };
            active.remove(name);
            Ok(result)
        }
    }
}

fn reject_recursive_calls(
    program: &Program,
    functions: &FunctionTable,
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
    functions: &FunctionTable,
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
        last_type = result.map_err(|error: SemanticError| {
            let code = error.code;
            let statement_span = statement_spans
                .get(&(function.name.clone(), index))
                .copied();
            let source_expression = statement_expressions.get(&(function.name.clone(), index));
            let precise_span = source_expression
                .and_then(|expression| {
                    let source = source_files
                        .get(expression.span.source_id as usize)
                        .map(|file| file.source.as_str())?;
                    let origin = semantic_statement_source(
                        statement,
                        expression,
                        error.origin,
                        false,
                        functions,
                        structs,
                    );
                    semantic_error_span(origin.unwrap_or(expression), &error, source)
                })
                .or_else(|| source_expression.map(crate::source_value_span))
                .or(statement_span);
            FunctionTypeError {
                message: error.message,
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
            message: error.message,
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

impl From<SemanticError> for FunctionTypeError {
    fn from(error: SemanticError) -> Self {
        Self {
            message: error.message,
            span: None,
            code: error.code,
        }
    }
}

// Addresses are used only as identities while this immutable AST is borrowed;
// they are never dereferenced or retained beyond the diagnostic construction.
pub(crate) fn analysis_node_source(
    program: &Program,
    node: usize,
    statement: bool,
) -> Option<&crate::SpannedExpr> {
    let mut functions = FunctionTable::default();
    let mut structs = HashMap::new();
    for item in &program.items {
        match item {
            Item::Function(function) => {
                functions.insert(
                    function.name.clone(),
                    Signature {
                        type_parameters: Vec::new(),
                        parameters: Vec::new(),
                        parameter_names: function
                            .parameters
                            .iter()
                            .map(|p| p.name.clone())
                            .collect(),
                        return_type: Type::Unit,
                    },
                );
            }
            Item::ThreadTask {
                generated_functions,
                ..
            } => {
                for function in generated_functions {
                    functions.insert(
                        function.name.clone(),
                        Signature {
                            type_parameters: Vec::new(),
                            parameters: Vec::new(),
                            parameter_names: function
                                .parameters
                                .iter()
                                .map(|p| p.name.clone())
                                .collect(),
                            return_type: Type::Unit,
                        },
                    );
                }
            }
            Item::Struct { name, fields, .. } => {
                structs.insert(name.clone(), fields.clone());
            }
            _ => {}
        }
    }
    for item in &program.items {
        if let Item::Function(function) = item {
            for (index, value) in function.body.iter().enumerate() {
                if let Some(source) = program
                    .statement_expressions
                    .get(&(function.name.clone(), index))
                {
                    if let Some(found) = semantic_statement_source(
                        value,
                        source,
                        Some(node),
                        statement,
                        &functions,
                        &structs,
                    ) {
                        return Some(found);
                    }
                }
            }
        }
    }
    None
}

fn semantic_statement_source<'a>(
    statement: &Statement,
    source: &'a crate::SpannedExpr,
    origin: Option<usize>,
    statement_origin: bool,
    functions: &FunctionTable,
    structs: &HashMap<String, Vec<Field>>,
) -> Option<&'a crate::SpannedExpr> {
    if functions.collecting_sources.get() {
        functions
            .source_spans
            .borrow_mut()
            .insert(std::ptr::from_ref(statement) as usize, source.span);
    }
    if statement_origin && origin == Some(std::ptr::from_ref(statement) as usize) {
        return Some(source);
    }
    let locate = |value: &Expr, source: &'a crate::SpannedExpr| {
        semantic_expression_source(value, source, origin, statement_origin, functions, structs)
    };
    match statement {
        Statement::Let { value, .. } | Statement::Destructure { value, .. } => {
            locate(value, source.children.get(3)?)
        }
        Statement::LetElse {
            value, else_body, ..
        } => locate(value, source.children.get(3)?).or_else(|| {
            else_body
                .iter()
                .zip(source.children.iter().skip(4))
                .find_map(|(statement, source)| {
                    semantic_statement_source(
                        statement,
                        source,
                        origin,
                        statement_origin,
                        functions,
                        structs,
                    )
                })
        }),
        Statement::Return(Some(value)) | Statement::BreakValue(value) => {
            locate(value, source.children.get(1)?)
        }
        Statement::BreakToValue { value, .. } => locate(value, source.children.get(2)?),
        Statement::Labeled { statement, .. } => semantic_statement_source(
            statement,
            source.children.get(2)?,
            origin,
            statement_origin,
            functions,
            structs,
        ),
        Statement::For {
            init,
            condition,
            step,
            body,
        } => semantic_statement_source(
            init,
            source.children.get(1)?,
            origin,
            statement_origin,
            functions,
            structs,
        )
        .or_else(|| {
            source
                .children
                .get(2)
                .and_then(|source| locate(condition, source))
        })
        .or_else(|| {
            source.children.get(3).and_then(|source| {
                semantic_statement_source(
                    step,
                    source,
                    origin,
                    statement_origin,
                    functions,
                    structs,
                )
            })
        })
        .or_else(|| {
            body.iter()
                .zip(source.children.iter().skip(4))
                .find_map(|(statement, source)| {
                    semantic_statement_source(
                        statement,
                        source,
                        origin,
                        statement_origin,
                        functions,
                        structs,
                    )
                })
        }),
        Statement::Assign { value, .. } => locate(value, source.children.get(2)?),
        Statement::Expr(value) => locate(value, source),
        Statement::ArrayAssign { index, value, .. } => locate(index, source.children.get(2)?)
            .or_else(|| {
                source
                    .children
                    .get(3)
                    .and_then(|source| locate(value, source))
            }),
        Statement::FieldAssign { value, .. } | Statement::TupleAssign { value, .. } => {
            locate(value, source.children.get(3)?)
        }
        Statement::EnumPayloadAssign { value, .. } => locate(value, source.children.get(4)?),
        Statement::While { condition, body } => {
            locate(condition, source.children.get(1)?).or_else(|| {
                body.iter()
                    .zip(source.children.iter().skip(2))
                    .find_map(|(statement, source)| {
                        semantic_statement_source(
                            statement,
                            source,
                            origin,
                            statement_origin,
                            functions,
                            structs,
                        )
                    })
            })
        }
        Statement::Loop { body } => {
            body.iter()
                .zip(source.children.iter().skip(1))
                .find_map(|(statement, source)| {
                    semantic_statement_source(
                        statement,
                        source,
                        origin,
                        statement_origin,
                        functions,
                        structs,
                    )
                })
        }
        _ => None,
    }
}

fn semantic_expression_source<'a>(
    value: &Expr,
    source: &'a crate::SpannedExpr,
    origin: Option<usize>,
    statement_origin: bool,
    functions: &FunctionTable,
    structs: &HashMap<String, Vec<Field>>,
) -> Option<&'a crate::SpannedExpr> {
    let origin = origin?;
    if functions.collecting_sources.get() {
        functions
            .source_spans
            .borrow_mut()
            .insert(std::ptr::from_ref(value) as usize, source.span);
    }
    if !statement_origin && std::ptr::from_ref(value) as usize == origin {
        return Some(source);
    }
    match value {
        Expr::List(items) => {
            let source_head = source.children.first().and_then(|head| match &head.expr {
                Expr::Symbol(head) => Some(head.trim_start_matches('#')),
                _ => None,
            });
            let target_head = items.first().and_then(|head| match head {
                Expr::Symbol(head) => Some(head),
                _ => None,
            });
            // External imports prefix semantic identifiers but preserve the
            // original source labels. Recover that known prefix from the
            // callee/type head, never from diagnostic wording or token search.
            let label_matches = |label: &str, name: &str| {
                if label == name {
                    return true;
                }
                let original_head = source.children.get(1).and_then(|child| match &child.expr {
                    Expr::Symbol(name) => Some(name.as_str()),
                    _ => None,
                });
                target_head
                    .zip(original_head)
                    .and_then(|(target, original)| target.strip_suffix(original))
                    .is_some_and(|prefix| name.strip_prefix(prefix) == Some(label))
            };
            for (index, child) in items.iter().enumerate() {
                let corresponding = match (source_head, target_head) {
                    (Some("case"), _) => source.children.get(index + 1),
                    (Some("call"), Some(function)) => {
                        if index == 0 {
                            source.children.get(1)
                        } else {
                            let name = functions.get(function)?.parameter_names.get(index - 1)?;
                            source.children.get(2)?.children.iter().skip(1).find_map(|argument| {
                                matches!(&argument.children.first()?.expr, Expr::Symbol(label) if label_matches(label, name))
                                    .then(|| argument.children.get(1)).flatten()
                            })
                        }
                    }
                    (Some("struct-literal"), Some(structure)) => {
                        if index == 0 {
                            source.children.get(1)
                        } else {
                            let name = &structs.get(structure)?.get(index - 1)?.name;
                            source.children.get(2)?.children.iter().find_map(|field| {
                                matches!(&field.children.first()?.expr, Expr::Symbol(label) if label_matches(label, name))
                                    .then(|| field.children.get(1)).flatten()
                            })
                        }
                    }
                    _ => source.children.get(index),
                };
                if let Some(found) = corresponding.and_then(|source| {
                    semantic_expression_source(
                        child,
                        source,
                        Some(origin),
                        statement_origin,
                        functions,
                        structs,
                    )
                }) {
                    return Some(found);
                }
            }
            None
        }
        Expr::Block(statements) | Expr::Loop(statements) => statements
            .iter()
            .zip(source.children.iter().skip(1))
            .find_map(|(statement, source)| {
                semantic_statement_source(
                    statement,
                    source,
                    Some(origin),
                    statement_origin,
                    functions,
                    structs,
                )
            }),
        Expr::Labeled { expression, .. } => semantic_expression_source(
            expression,
            source.children.get(2)?,
            Some(origin),
            statement_origin,
            functions,
            structs,
        ),
        Expr::Quote(expression)
        | Expr::QuasiQuote(expression)
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => semantic_expression_source(
            expression,
            source.children.first()?,
            Some(origin),
            statement_origin,
            functions,
            structs,
        ),
        _ => None,
    }
}

fn semantic_error_span(
    statement: &crate::SpannedExpr,
    error: &SemanticError,
    source: &str,
) -> Option<crate::Span> {
    fn find_scope<'a>(
        node: &'a crate::SpannedExpr,
        scope: &Expr,
    ) -> Option<&'a crate::SpannedExpr> {
        let normalized = crate::normalize_keywords(node.expr.clone());
        if &normalized == scope {
            return Some(node);
        }
        if let (Expr::List(source), Expr::List(target)) = (&normalized, scope) {
            let actual = match source.first() {
                Some(Expr::Symbol(head)) if head == "call" => {
                    if source.get(1) == target.first() {
                        source.get(2).and_then(|args| match args {
                            Expr::List(args) => Some(
                                args.iter()
                                    .skip(1)
                                    .filter_map(|arg| match arg {
                                        Expr::List(pair) => pair.get(1).cloned(),
                                        _ => None,
                                    })
                                    .collect::<Vec<_>>(),
                            ),
                            _ => None,
                        })
                    } else {
                        None
                    }
                }
                Some(Expr::Symbol(head)) if head == "struct-literal" => {
                    if source.get(1) == target.first() {
                        source.get(2).and_then(|fields| match fields {
                            Expr::List(fields) => Some(
                                fields
                                    .iter()
                                    .filter_map(|field| match field {
                                        Expr::List(pair) => pair.get(1).cloned(),
                                        _ => None,
                                    })
                                    .collect::<Vec<_>>(),
                            ),
                            _ => None,
                        })
                    } else {
                        None
                    }
                }
                _ => None,
            };
            if let Some(mut actual) = actual {
                let mut matched = actual.len() + 1 == target.len();
                for value in target.iter().skip(1) {
                    if let Some(index) = actual.iter().position(|candidate| candidate == value) {
                        actual.remove(index);
                    } else {
                        matched = false;
                        break;
                    }
                }
                if matched {
                    return Some(node);
                }
            }
        }
        node.children
            .iter()
            .find_map(|child| find_scope(child, scope))
    }
    let statement = error
        .scope
        .as_ref()
        .and_then(|scope| find_scope(statement, scope))
        .unwrap_or(statement);
    let value = crate::source_value_expression(statement);
    let span = match error.site.as_ref() {
        ErrorSite::Value => None,
        ErrorSite::Symbol(name) => first_symbol_span(statement, name),
        ErrorSite::DeclaredType(name) => {
            declared_type_span(statement, name).or_else(|| first_symbol_span(statement, name))
        }
        ErrorSite::Operator(name) => source_operator_span(statement, name),
        ErrorSite::Argument(operator, index) => {
            find_operator_argument(value, &[operator.as_str()], *index)
        }
        ErrorSite::TupleElement(index) => tuple_element_span(value, *index),
        ErrorSite::ArrayElement(index) => array_element_span(value, *index),
        ErrorSite::ConstructorArity(operator, count) => {
            constructor_arity_span(value, operator, *count)
        }
        ErrorSite::Payload(variant, index) => enum_constructor_payload_span(value, variant, *index),
        ErrorSite::Field(field) => struct_literal_field_value_span(value, field),
        ErrorSite::NamedArgument(function, parameter) => {
            named_call_argument_span(statement, function, parameter)
        }
        ErrorSite::PatternSymbol(name) => last_match_pattern_symbol_span(statement, name)
            .or_else(|| type_pattern_symbol_span(statement, name)),
        ErrorSite::PatternInteger(number) => last_match_pattern_integer_span(statement, *number),
        ErrorSite::PatternCharacter => last_match_pattern_char_span(statement),
        ErrorSite::PatternRange(upper) => match_range_pattern_span(statement, *upper),
        ErrorSite::BranchMismatch(actual) => {
            control_flow_mismatch_span(value, &format!("{actual:?}"), source)
        }
        ErrorSite::Mismatch(actual, expected) => {
            if let Some(Type::Named(name)) = expected {
                if let Some(span) = declared_type_span(statement, name) {
                    return Some(span);
                }
            }
            expression_with_type_hint(value, &format!("{actual:?}"), source)
        }
    };
    span.or(Some(value.span))
}

fn tuple_element_span(expression: &crate::SpannedExpr, index: usize) -> Option<crate::Span> {
    if let Expr::List(items) = &expression.expr {
        if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#tuple" || head == "tuple")
        {
            let value_start = usize::from(items.get(1).is_some_and(|item| {
                parse_type(Some(&crate::normalize_keywords(item.clone())))
                    .is_ok_and(|ty| matches!(ty, Type::Tuple(_)))
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
                parse_type(Some(&crate::normalize_keywords(item.clone())))
                    .is_ok_and(|ty| matches!(ty, Type::Array(_, _)))
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
        "fn" | "unsafe-fn" | "extern-fn" => {
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

fn match_range_pattern_span(expression: &crate::SpannedExpr, upper: bool) -> Option<crate::Span> {
    fn collect(expression: &crate::SpannedExpr, upper: bool, spans: &mut Vec<crate::Span>) {
        if let Expr::List(items) = &expression.expr {
            if matches!(items.first(), Some(Expr::Symbol(operator)) if operator.strip_prefix('#').unwrap_or(operator) == "range")
            {
                let span = if upper {
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
            collect(child, upper, spans);
        }
    }
    let mut spans = Vec::new();
    collect(expression, upper, &mut spans);
    spans.into_iter().min_by_key(|span| span.start)
}

fn statement_type(
    statement: &Statement,
    variables: &mut HashMap<String, Type>,
    mutable: &mut HashSet<String>,
    functions: &FunctionTable,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    return_type: &Type,
    aliases: &HashMap<String, Type>,
    in_loop: bool,
) -> Result<Type, SemanticError> {
    match statement {
        Statement::Let {
            name,
            ty,
            value,
            mutable: is_mutable,
        } => {
            if variables.contains_key(name) {
                return Err(semantic_format!("duplicate local '{name}'"));
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
                return Err(semantic_format!("duplicate loop label '{label}'"));
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
                    return Err(semantic_format!("duplicate local '{name}'"));
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
                    return Err(semantic_format!("duplicate local '{name}'"));
                }
                variables.insert(name, field_type);
            }
            Ok(Type::Unit)
        }
        Statement::Assign { name, value } => {
            let ty = variables
                .get(name)
                .ok_or_else(|| {
                    semantic_at!(ErrorSite::Symbol(name.clone()), "unknown variable '{name}'")
                })?
                .clone();
            if !mutable.contains(name) {
                return Err(semantic_at!(
                    ErrorSite::Symbol(name.clone()),
                    "cannot assign to immutable variable '{name}'"
                ));
            }
            if contains_reference_type(&ty, structs, enums, &mut HashSet::new()) {
                return Err(semantic_format!(
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
                .ok_or_else(|| {
                    semantic_at!(ErrorSite::Symbol(name.clone()), "unknown variable '{name}'")
                })?
                .clone();
            if !mutable.contains(name) {
                return Err(semantic_at!(
                    ErrorSite::Symbol(name.clone()),
                    "cannot assign to immutable variable '{name}'"
                ));
            }
            let Type::Array(element, length) = ty else {
                return Err(semantic_at!(
                    ErrorSite::Symbol(name.clone()),
                    "'{name}' is not an array"
                ));
            };
            if contains_reference_type(&element, structs, enums, &mut HashSet::new()) {
                return Err(semantic_format!(
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
                .ok_or_else(|| {
                    semantic_at!(ErrorSite::Symbol(name.clone()), "unknown variable '{name}'")
                })?
                .clone();
            if !mutable.contains(name) {
                return Err(semantic_at!(
                    ErrorSite::Symbol(name.clone()),
                    "cannot assign to immutable variable '{name}'"
                ));
            }
            let Type::Named(struct_name) = ty else {
                return Err(semantic_at!(
                    ErrorSite::Symbol(name.clone()),
                    "'{name}' is not a struct"
                ));
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
                return Err(semantic_format!(
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
                .ok_or_else(|| {
                    semantic_at!(ErrorSite::Symbol(name.clone()), "unknown variable '{name}'")
                })?
                .clone();
            if !mutable.contains(name) {
                return Err(semantic_at!(
                    ErrorSite::Symbol(name.clone()),
                    "cannot assign to immutable variable '{name}'"
                ));
            }
            let Type::Named(enum_name) = ty else {
                return Err(semantic_at!(
                    ErrorSite::Symbol(name.clone()),
                    "'{name}' is not an enum"
                ));
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
                return Err(semantic_format!(
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
                .ok_or_else(|| {
                    semantic_at!(ErrorSite::Symbol(name.clone()), "unknown variable '{name}'")
                })?
                .clone();
            if !mutable.contains(name) {
                return Err(semantic_at!(
                    ErrorSite::Symbol(name.clone()),
                    "cannot assign to immutable variable '{name}'"
                ));
            }
            let Type::Tuple(fields) = ty else {
                return Err(semantic_at!(
                    ErrorSite::Symbol(name.clone()),
                    "'{name}' is not a tuple"
                ));
            };
            let field_type = fields
                .get(*index)
                .ok_or_else(|| format!("tuple field index {index} is out of bounds"))?;
            if contains_reference_type(field_type, structs, enums, &mut HashSet::new()) {
                return Err(semantic_format!(
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
                return Err(semantic_format!(
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
                Err(semantic_format!("unknown or inactive loop label '{label}'"))
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
) -> Result<Vec<(String, Type)>, SemanticError> {
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
        return Err(semantic_format!(
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
) -> Result<Vec<(String, Type)>, SemanticError> {
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
                            return Err(semantic_format!("unknown enum variant '{name}'"));
                        };
                        if !payload_patterns.is_empty()
                            && payload_patterns.len() != variant.fields.len()
                        {
                            return Err(semantic_at!(
                                ErrorSite::PatternSymbol(name.to_string()),
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
                .ok_or_else(|| {
                    semantic_at!(
                        ErrorSite::PatternSymbol(variant_name.to_string()),
                        "'{variant_name}' is not a variant of '{enum_name}'"
                    )
                })?;
            if payload_patterns.len() != variant.fields.len() {
                return Err(semantic_at!(
                    ErrorSite::PatternSymbol(variant_name.to_string()),
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
    expr: &Expr,
    variables: &HashMap<String, Type>,
    functions: &FunctionTable,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    mutable: &HashSet<String>,
    aliases: &HashMap<String, Type>,
    expected: Option<&Type>,
) -> Result<Type, SemanticError> {
    expression_inner(
        expr, variables, functions, structs, enums, mutable, aliases, expected,
    )
    .inspect(|ty| {
        functions
            .expression_types
            .borrow_mut()
            .insert(std::ptr::from_ref(expr) as usize, ty.clone());
    })
    .map_err(|mut error| {
        if error.scope.is_none() {
            error.scope = Some(Box::new(expr.clone()));
            error.origin = Some(std::ptr::from_ref(expr) as usize);
        }
        error
    })
}

fn expression_inner(
    value: &Expr,
    variables: &HashMap<String, Type>,
    functions: &FunctionTable,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    mutable: &HashSet<String>,
    aliases: &HashMap<String, Type>,
    expected: Option<&Type>,
) -> Result<Type, SemanticError> {
    match value {
        Expr::Integer(value) => {
            let ty = expected
                .filter(|ty| is_integer(ty))
                .cloned()
                .unwrap_or(Type::I64);
            if !fits_integer(*value, &ty) {
                return Err(semantic_format!(
                    "integer literal {value} does not fit in {ty:?}"
                ));
            }
            Ok(ty)
        }
        Expr::UnsignedInteger(value) => {
            let ty = expected
                .filter(|ty| is_integer(ty))
                .cloned()
                .unwrap_or(Type::U128);
            if !fits_unsigned_integer(*value, &ty) {
                return Err(semantic_format!(
                    "integer literal {value} does not fit in {ty:?}"
                ));
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
                return Err(semantic_format!(
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
            .ok_or_else(|| {
                SemanticError::from(format!("unknown variable or enum variant '{name}'"))
                    .at(ErrorSite::Symbol(name.clone()))
            }),
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
                return Err(semantic_format!("duplicate loop label '{label}'"));
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
    functions: &FunctionTable,
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
    functions: &FunctionTable,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    mutable: &HashSet<String>,
    aliases: &HashMap<String, Type>,
    expected: Option<&Type>,
) -> Result<Type, SemanticError> {
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
        "linux-syscall" => {
            if items.len() != 4 {
                return Err(
                    "#linux-syscall requires a result type, syscall number, and argument list"
                        .into(),
                );
            }
            let result_type = resolve_type(&crate::parse_type(items.get(1))?, aliases)
                .map_err(SemanticError::from)?;
            if !is_syscall_word_type(&result_type)
                && result_type != Type::Unit
                && !matches!(result_type, Type::RawPointer { .. })
            {
                return Err("#linux-syscall result must be unit or a scalar machine word".into());
            }
            let number_type = expression(
                &items[2], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            if !is_syscall_word_type(&number_type) {
                return Err("#linux-syscall number must be an integer machine word".into());
            }
            let Expr::List(arguments) = &items[3] else {
                return Err("#linux-syscall arguments must be a list".into());
            };
            if arguments.len() > 6 {
                return Err("Linux x86-64 syscalls accept at most six arguments".into());
            }
            for argument in arguments {
                let actual = expression(
                    argument, variables, functions, structs, enums, mutable, aliases, None,
                )?;
                if !is_syscall_word_type(&actual)
                    && !matches!(actual, Type::RawPointer { .. } | Type::Reference { .. })
                {
                    return Err(format!(
                        "#linux-syscall argument must be a scalar machine word or pointer, got {actual:?}"
                    )
                    .into());
                }
            }
            Ok(result_type)
        }
        "asm" => {
            if items.len() != 4 {
                return Err(
                    "#asm requires a result type, register operands, and assembly text".into(),
                );
            }
            let result_type = resolve_type(&crate::parse_type(items.get(1))?, aliases)
                .map_err(SemanticError::from)?;
            if !matches!(
                result_type,
                Type::Unit
                    | Type::I8
                    | Type::I16
                    | Type::I32
                    | Type::I64
                    | Type::Isize
                    | Type::U8
                    | Type::U16
                    | Type::U32
                    | Type::U64
                    | Type::Usize
                    | Type::Bool
                    | Type::RawPointer { .. }
            ) {
                return Err(
                    "#asm result must be unit, an integer up to 64 bits, or a raw pointer".into(),
                );
            }
            let Expr::List(operands) = &items[2] else {
                return Err("#asm operands must be a list of (register value) pairs".into());
            };
            if operands.len() > 6 {
                return Err("#asm supports at most six register operands".into());
            }
            let mut registers = HashSet::new();
            for operand in operands {
                let Expr::List(pair) = operand else {
                    return Err("#asm operand must be a (register value) pair".into());
                };
                if pair.len() != 2 {
                    return Err("#asm operand must contain one register and one value".into());
                }
                let Expr::Symbol(register) = &pair[0] else {
                    return Err("#asm register must be a symbol".into());
                };
                if !matches!(
                    register.as_str(),
                    "rax"
                        | "rbx"
                        | "rcx"
                        | "rdx"
                        | "rsi"
                        | "rdi"
                        | "r8"
                        | "r9"
                        | "r10"
                        | "r11"
                        | "r12"
                        | "r13"
                        | "r14"
                        | "r15"
                ) {
                    return Err(format!("unsupported #asm register '{register}'").into());
                }
                if !registers.insert(register) {
                    return Err(
                        format!("#asm register '{register}' is assigned more than once").into(),
                    );
                }
                let input_type = expression(
                    &pair[1], variables, functions, structs, enums, mutable, aliases, None,
                )?;
                if !matches!(
                    input_type,
                    Type::I8
                        | Type::I16
                        | Type::I32
                        | Type::I64
                        | Type::Isize
                        | Type::U8
                        | Type::U16
                        | Type::U32
                        | Type::U64
                        | Type::Usize
                        | Type::RawPointer { .. }
                        | Type::Reference { .. }
                ) {
                    return Err(format!(
                        "#asm register operand must be an integer up to 64 bits or raw pointer, got {input_type:?}"
                    )
                    .into());
                }
            }
            if !matches!(&items[3], Expr::String(_)) {
                return Err("#asm instruction body must be a string literal".into());
            }
            Ok(result_type)
        }
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
                    return Err(semantic_format!("thread task '{name}' cannot be cloned"));
                }
                if let Some(signature) = functions.get(&format!("{name}-clone")) {
                    if signature.parameters != [cloned.clone()] || signature.return_type != cloned {
                        return Err(semantic_format!(
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
                    return Err(semantic_format!(
                        "thread task '{name}' must be joined; it cannot be dropped or forgotten"
                    ));
                }
                let thread_result_task = name
                    .strip_suffix("-spawn-result")
                    .or_else(|| name.strip_suffix("-join-result"));
                if thread_result_task
                    .is_some_and(|task| functions.contains_key(&format!("{task}-spawn")))
                {
                    return Err(semantic_format!(
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
                return Err(semantic_format!(
                    "cell does not support values of type {inner:?}"
                ));
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
                return Err(semantic_at!(
                    ErrorSite::Argument("-".into(), 1),
                    "unary '-' requires a numeric operand"
                ));
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
            require_same(&left, &right, operator).map_err(|error| {
                error.at(ErrorSite::Argument(
                    raw_operator.into(),
                    if operator_type.as_ref() == Some(&right) {
                        1
                    } else {
                        2
                    },
                ))
            })?;
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
                return Err(semantic_format!(
                    "operator '{operator}' requires integer or boolean operands"
                ));
            }
            if matches!(operator, "<<" | ">>") {
                if let Expr::Integer(count) = &items[2] {
                    if *count < 0 || integer_width(&left).is_some_and(|width| *count >= width) {
                        return Err(semantic_at!(
                            ErrorSite::Argument(operator.into(), 2),
                            "shift count {count} is out of range for {left:?}"
                        ));
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
            require_same(&left, &right, operator).map_err(|error| {
                error.at(ErrorSite::Argument(
                    raw_operator.into(),
                    if operator_type.as_ref() == Some(&right) {
                        1
                    } else {
                        2
                    },
                ))
            })?;
            if let Some(qualifier) = qualifier {
                require_operator_type(qualifier, &left, raw_operator)?;
            }
            if !is_numeric(&left) && !matches!(left, Type::Bool | Type::Char) {
                return Err(semantic_format!(
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
                .map_err(|error| error.at(ErrorSite::BranchMismatch(else_type.clone())))
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
        "atomic-load"
        | "atomic-store"
        | "atomic-fetch-add"
        | "atomic-exchange"
        | "atomic-compare-exchange"
        | "atomic-compare-exchange-weak" => {
            let compare = matches!(
                operator,
                "atomic-compare-exchange" | "atomic-compare-exchange-weak"
            );
            let expected = if compare {
                6
            } else if operator == "atomic-load" {
                3
            } else {
                4
            };
            require_arity(operator, items, expected)?;
            let Type::Reference { target, .. } = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?
            else {
                return Err(semantic_format!(
                    "{operator} requires a shared reference to an atomic scalar"
                ));
            };
            let Type::Atomic(scalar) = *target else {
                return Err(semantic_format!(
                    "{operator} requires a reference to an atomic scalar"
                ));
            };
            let order_index = if compare {
                4
            } else if operator == "atomic-load" {
                2
            } else {
                3
            };
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
            if compare {
                let failure = atomic_memory_order(items.get(5)).ok_or_else(|| {
                    format!("{operator} requires an explicit failure #memory-* ordering")
                })?;
                let allowed = match failure {
                    "relaxed" => true,
                    "acquire" => matches!(order, "acquire" | "acq-rel" | "seq-cst"),
                    "seq-cst" => order == "seq-cst",
                    _ => false,
                };
                if !allowed {
                    return Err("compare-exchange failure ordering must be relaxed, acquire, or seq-cst and no stronger than success ordering".into());
                }
                let desired = expression(
                    &items[3],
                    variables,
                    functions,
                    structs,
                    enums,
                    mutable,
                    aliases,
                    Some(&scalar),
                )?;
                require_type(&desired, &scalar, "atomic desired operand")?;
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
            if compare {
                Ok(Type::Tuple(vec![Type::Bool, *scalar]))
            } else if operator == "atomic-store" {
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
                return Err(semantic_at!(
                    ErrorSite::Argument("slice-of".into(), 1),
                    "slice requires an immutable reference to an array"
                ));
            };
            let Type::Array(element, _) = *target else {
                return Err(semantic_at!(
                    ErrorSite::Argument("slice-of".into(), 1),
                    "slice requires a reference to an array"
                ));
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
                return Err(semantic_at!(
                    ErrorSite::Argument("slice-len".into(), 1),
                    "slice-len requires a slice"
                ));
            }
            Ok(Type::Usize)
        }
        "slice-idx" => {
            require_arity(operator, items, 3)?;
            let Type::Slice(element) = expression(
                &items[1], variables, functions, structs, enums, mutable, aliases, None,
            )?
            else {
                return Err(semantic_at!(
                    ErrorSite::Argument("slice-idx".into(), 1),
                    "slice-idx requires a slice"
                ));
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
                return Err(semantic_format!("{operator} requires a mutable slice"));
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
                            return Err(semantic_at!(ErrorSite::Argument(operator.into(), 1),
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
                            return Err(semantic_format!(
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
                        return Err(semantic_format!(
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
                    return Err(semantic_format!(
                        "{operator} cannot borrow a unit or never value"
                    ));
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
                        return Err(semantic_format!(
                            "{operator} refers to unknown variable '{owner}'"
                        ));
                    }
                    if operator == "borrow-mut" && !mutable.contains(owner) {
                        return Err(semantic_format!(
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
                        return Err(semantic_format!(
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
                    return Err(semantic_format!(
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
                return Err(semantic_at!(
                    ErrorSite::Argument("deref-set".into(), 1),
                    "deref-set requires a mutable reference"
                ));
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
                _ => return Err(semantic_format!("{operator} requires a variable name")),
            };
            let owner_type = variables
                .get(owner)
                .ok_or_else(|| format!("{operator} refers to unknown variable '{owner}'"))?;
            if !is_scalar_reference_target(owner_type, enums) {
                return Err(semantic_format!(
                    "{operator} currently supports scalar values only"
                ));
            }
            if operator == "addr-of-mut" && !mutable.contains(owner) {
                return Err(semantic_format!(
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
                return Err(semantic_format!(
                    "{operator} requires a reference lifetime anchor"
                ));
            };
            let pointer = expression(
                &items[2], variables, functions, structs, enums, mutable, aliases, None,
            )?;
            let Type::RawPointer {
                mutable: pointer_mutable,
                target,
            } = pointer
            else {
                return Err(semantic_format!("{operator} requires a raw pointer"));
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
                return Err(semantic_at!(
                    ErrorSite::ConstructorArity("#array", length),
                    "array constructor expects {length} elements"
                ));
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
                require_type(&actual, element.as_ref(), &format!("array element {index}"))
                    .map_err(|error| error.at(ErrorSite::ArrayElement(index)))?;
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
                return Err(semantic_at!(
                    ErrorSite::ConstructorArity("#tuple", fields.len()),
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
                require_type(&actual, field, &format!("tuple element {index}"))
                    .map_err(|error| error.at(ErrorSite::TupleElement(index)))?;
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
                return Err(semantic_at!(
                    ErrorSite::Argument("index".into(), 1),
                    "index requires an array"
                ));
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
                                            "enum or-pattern alternatives must be variants".into(),
                                        );
                                    };
                                    Ok((name.as_str(), items[1..].iter().collect()))
                                }
                                _ => Err(SemanticError::from(
                                    "enum or-pattern alternatives must be variants",
                                )),
                            })
                            .collect::<Result<Vec<(&str, Vec<&Expr>)>, SemanticError>>()?;
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
                            return Err(semantic_at!(
                                ErrorSite::PatternSymbol(alternative.to_string()),
                                "'{alternative}' is not a variant of '{enum_name}'"
                            ));
                        };
                        if !alternative_payloads.is_empty()
                            && alternative_payloads.len() != variant.fields.len()
                        {
                            return Err(semantic_at!(
                                ErrorSite::PatternSymbol(alternative.to_string()),
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
                        return Err(semantic_at!(
                            ErrorSite::PatternSymbol("_".into()),
                            "duplicate wildcard match pattern"
                        ));
                    }
                    if guard.is_none() {
                        wildcard = true;
                    }
                } else {
                    let Some(variant) = variants.iter().find(|variant| variant.name == pattern)
                    else {
                        return Err(semantic_at!(
                            ErrorSite::PatternSymbol(pattern.to_string()),
                            "'{pattern}' is not a variant of '{enum_name}'"
                        ));
                    };
                    if !payload_patterns.is_empty()
                        && payload_patterns.len() != variant.fields.len()
                    {
                        return Err(semantic_at!(
                            ErrorSite::PatternSymbol(pattern.to_string()),
                            "variant '{pattern}' expects {} payload patterns",
                            variant.fields.len()
                        ));
                    }
                    if guard.is_none() && seen.contains(&pattern) {
                        return Err(semantic_at!(
                            ErrorSite::PatternSymbol(pattern.to_string()),
                            "duplicate enum match pattern '{pattern}'"
                        ));
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
                    result_type = Some(
                        merge_types(previous, &arm_type, "match arms").map_err(|error| {
                            error.at(ErrorSite::BranchMismatch(arm_type.clone()))
                        })?,
                    );
                } else {
                    result_type = Some(arm_type);
                }
            }
            if !wildcard && seen.len() != variants.len() {
                return Err(semantic_at!(
                    ErrorSite::Operator("match".into()),
                    "match is not exhaustive; add '_' arm"
                ));
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
                return fields.get(index).cloned().ok_or_else(|| {
                    SemanticError::from(format!("tuple field index {index} is out of bounds"))
                        .at(ErrorSite::Argument("get".into(), 2))
                });
            }
            let Type::Named(struct_name) = value_type else {
                return Err(semantic_at!(
                    ErrorSite::Argument("get".into(), 1),
                    "get requires a struct or tuple value"
                ));
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
                .ok_or_else(|| {
                    SemanticError::from(format!(
                        "struct '{struct_name}' has no field '{field_name}'"
                    ))
                    .at(ErrorSite::Argument("get".into(), 2))
                })
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
                return Err(semantic_at!(
                    ErrorSite::Argument("get-payload".into(), 1),
                    "get-payload requires an enum value"
                ));
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
                .ok_or_else(|| {
                    SemanticError::from(format!(
                        "enum '{enum_name}' has no variant '{variant_name}'"
                    ))
                    .at(ErrorSite::Argument("get-payload".into(), 2))
                })?;
            variant.fields.get(index).cloned().ok_or_else(|| {
                SemanticError::from(format!(
                    "variant '{variant_name}' has no payload field at index {index}"
                ))
                .at(ErrorSite::Argument("get-payload".into(), 3))
            })
        }
        _ => {
            if let Some(fields) = structs.get(operator) {
                if items.len() - 1 != fields.len() {
                    return Err(semantic_format!(
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
                    )
                    .map_err(|error| error.at(ErrorSite::Field(field.name.clone())))?;
                }
                return Ok(Type::Named(operator.to_owned()));
            }
            for (enum_name, variants) in enums {
                let Some(variant) = variants.iter().find(|variant| variant.name == *operator)
                else {
                    continue;
                };
                if items.len() - 1 != variant.fields.len() {
                    return Err(semantic_format!(
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
                    )
                    .map_err(|error| {
                        error.at(ErrorSite::Payload(operator.into(), payload_index))
                    })?;
                }
                return Ok(Type::Named(enum_name.clone()));
            }
            let (function_name, type_arguments) = split_generic_call(operator)?;
            let signature = functions.get(&function_name).ok_or_else(|| {
                semantic_at!(
                    ErrorSite::Operator(operator.into()),
                    "unknown function '{operator}'"
                )
            })?;
            let substitutions = generic_substitutions(signature, &type_arguments, aliases)?;
            let parameter_types = signature
                .parameters
                .iter()
                .map(|parameter| substitute_type(parameter, &substitutions))
                .collect::<Vec<_>>();
            let return_type = substitute_type(&signature.return_type, &substitutions);
            if items.len() - 1 != signature.parameters.len() {
                return Err(semantic_at!(
                    ErrorSite::Operator(operator.into()),
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
                )
                .map_err(|error| {
                    error.at(ErrorSite::NamedArgument(operator.into(), parameter.clone()))
                })?;
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
    functions: &FunctionTable,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    mutable: &HashSet<String>,
    aliases: &HashMap<String, Type>,
    expected: Option<&Type>,
) -> Result<Type, SemanticError> {
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
                                return Err(semantic_at!(
                                    ErrorSite::PatternSymbol(name.to_string()),
                                    "duplicate boolean match pattern '{name}'"
                                ));
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
                    return Err(semantic_at!(
                        ErrorSite::PatternSymbol("_".into()),
                        "duplicate wildcard match pattern"
                    ));
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
                    return Err(semantic_at!(
                        ErrorSite::PatternSymbol(pattern.to_string()),
                        "duplicate boolean match pattern '{pattern}'"
                    ));
                }
                seen_bool[index] = true;
            }
            Expr::Integer(value) if is_integer(scrutinee) => {
                if !fits_integer(*value, scrutinee) {
                    return Err(semantic_at!(
                        ErrorSite::PatternInteger(*value as u128),
                        "integer match pattern {value} does not fit in {scrutinee:?}"
                    ));
                }
                if !seen_integers.insert(*value) {
                    return Err(semantic_at!(
                        ErrorSite::PatternInteger(*value as u128),
                        "duplicate integer match pattern {value}"
                    ));
                }
            }
            Expr::UnsignedInteger(value) if is_integer(scrutinee) => {
                if !fits_unsigned_integer(*value, scrutinee) {
                    return Err(semantic_at!(
                        ErrorSite::PatternInteger(*value as u128),
                        "unsigned integer match pattern {value} does not fit in {scrutinee:?}"
                    ));
                }
                if !seen_unsigned_integers.insert(*value) {
                    return Err(semantic_at!(
                        ErrorSite::PatternInteger(*value as u128),
                        "duplicate integer match pattern {value}"
                    ));
                }
            }
            Expr::Char(value) if matches!(scrutinee, Type::Char) => {
                if !seen_chars.insert(*value) {
                    return Err(semantic_at!(
                        ErrorSite::PatternCharacter,
                        "duplicate character match pattern {value:?}"
                    ));
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
            result_type = Some(
                merge_types(previous, &arm_type, "match arms")
                    .map_err(|error| error.at(ErrorSite::BranchMismatch(arm_type.clone())))?,
            );
        } else {
            result_type = Some(arm_type);
        }
    }
    if !wildcard && !(matches!(scrutinee, Type::Bool) && seen_bool.iter().all(|seen| *seen)) {
        return Err(semantic_at!(
            ErrorSite::Operator("match".into()),
            "match is not exhaustive; add '_' arm"
        ));
    }
    Ok(result_type.unwrap_or(Type::Unit))
}

fn check_scalar_pattern(pattern: &Expr, scrutinee: &Type) -> Result<(), SemanticError> {
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

fn check_scalar_range_pattern(parts: &[Expr], scrutinee: &Type) -> Result<(), SemanticError> {
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
                return Err(semantic_at!(
                    ErrorSite::PatternRange(false),
                    "integer range pattern does not fit its scrutinee type"
                ));
            }
            if lower > upper {
                return Err(semantic_at!(
                    ErrorSite::PatternRange(true),
                    "integer range pattern lower bound exceeds upper bound"
                ));
            }
        } else {
            let lower_expression = range_bound_expression(&parts[1], scrutinee)?;
            let upper_expression = range_bound_expression(&parts[2], scrutinee)?;
            let lower = unsigned_range_bound(lower_expression)?;
            let upper = unsigned_range_bound(upper_expression)?;
            if !fits_unsigned_integer(lower, scrutinee) || !fits_unsigned_integer(upper, scrutinee)
            {
                return Err(semantic_at!(
                    ErrorSite::PatternRange(false),
                    "unsigned range pattern does not fit its scrutinee type"
                ));
            }
            if lower > upper {
                return Err(semantic_at!(
                    ErrorSite::PatternRange(true),
                    "unsigned range pattern lower bound exceeds upper bound"
                ));
            }
        }
        return Ok(());
    }
    if matches!(scrutinee, Type::Char) {
        let Expr::Char(lower) = parts[1] else {
            return Err(semantic_at!(
                ErrorSite::PatternRange(false),
                "character range patterns require character bounds"
            ));
        };
        let Expr::Char(upper) = parts[2] else {
            return Err(semantic_at!(
                ErrorSite::PatternRange(false),
                "character range patterns require character bounds"
            ));
        };
        if lower > upper {
            return Err(semantic_at!(
                ErrorSite::PatternRange(true),
                "character range pattern lower bound exceeds upper bound"
            ));
        }
        return Ok(());
    }
    Err(semantic_at!(
        ErrorSite::PatternRange(false),
        "range patterns require an integer or char scrutinee"
    ))
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
) -> Result<Option<&'a Expr>, SemanticError> {
    let Expr::List(items) = pattern else {
        return Ok(None);
    };
    if !is_typed_integer_pattern(pattern) {
        return Ok(None);
    }
    let literal_type = parse_type(items.get(1))?;
    if literal_type != *scrutinee || !is_integer(&literal_type) {
        return Err(semantic_format!(
            "typed integer pattern has type {literal_type:?}, expected {scrutinee:?}"
        ));
    }
    if !matches!(items[2], Expr::Integer(_) | Expr::UnsignedInteger(_)) {
        return Err("typed integer pattern requires an integer literal".into());
    }
    Ok(Some(&items[2]))
}

fn range_bound_expression<'a>(
    expression: &'a Expr,
    scrutinee: &Type,
) -> Result<&'a Expr, SemanticError> {
    let Expr::List(items) = expression else {
        return Ok(expression);
    };
    if items.len() != 3 || !matches!(items.first(), Some(Expr::Symbol(name)) if name == "literal") {
        return Ok(expression);
    }
    let literal_type = parse_type(items.get(1))?;
    if &literal_type != scrutinee {
        return Err(semantic_format!(
            "typed range bound has type {literal_type:?}, expected {scrutinee:?}"
        ));
    }
    Ok(&items[2])
}

fn signed_range_bound(expression: &Expr) -> Result<i128, SemanticError> {
    match expression {
        Expr::Integer(value) => Ok(*value),
        Expr::UnsignedInteger(value) => {
            i128::try_from(*value).map_err(|_| "signed range bound is too large".into())
        }
        _ => Err("integer range patterns require integer bounds".into()),
    }
}

fn unsigned_range_bound(expression: &Expr) -> Result<u128, SemanticError> {
    match expression {
        Expr::Integer(value) if *value >= 0 => Ok(*value as u128),
        Expr::Integer(_) => Err("unsigned range bounds cannot be negative".into()),
        Expr::UnsignedInteger(value) => Ok(*value),
        _ => Err("integer range patterns require integer bounds".into()),
    }
}

fn match_arm_parts(arm: &Expr) -> Result<(&Expr, Option<&Expr>, &Expr), SemanticError> {
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
    functions: &FunctionTable,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    mutable: &HashSet<String>,
    aliases: &HashMap<String, Type>,
    expected: Option<&Type>,
) -> Result<Type, SemanticError> {
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
                    return Err(semantic_at!(
                        ErrorSite::PatternSymbol("_".into()),
                        "duplicate wildcard match pattern"
                    ));
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
                    return Err(semantic_format!(
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
            result_type = Some(
                merge_types(previous, &arm_type, "match arms")
                    .map_err(|error| error.at(ErrorSite::BranchMismatch(arm_type.clone())))?,
            );
        } else {
            result_type = Some(arm_type);
        }
    }
    if !wildcard {
        return Err(semantic_at!(
            ErrorSite::Operator("match".into()),
            "tuple match is not exhaustive; add '_' arm"
        ));
    }
    Ok(result_type.unwrap_or(Type::Unit))
}

fn check_aggregate_pattern(
    pattern: &Expr,
    ty: &Type,
    arm_variables: &mut HashMap<String, Type>,
    variables: &HashMap<String, Type>,
    structs: &HashMap<String, Vec<Field>>,
) -> Result<(), SemanticError> {
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
                return Err(semantic_format!("duplicate match binding '{name}'"));
            }
            arm_variables.insert(name.clone(), ty.clone());
            Ok(())
        }
        Expr::Integer(value) if is_integer(ty) => {
            if !fits_integer(*value, ty) {
                return Err(semantic_at!(
                    ErrorSite::PatternInteger(*value as u128),
                    "integer match pattern {value} does not fit in {ty:?}"
                ));
            }
            Ok(())
        }
        Expr::UnsignedInteger(value) if is_integer(ty) => {
            if !fits_unsigned_integer(*value, ty) {
                return Err(semantic_at!(
                    ErrorSite::PatternInteger(*value as u128),
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
                return Err(semantic_format!(
                    "aggregate pattern expects {} fields",
                    fields.len()
                ));
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
) -> Result<bool, SemanticError> {
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
    functions: &FunctionTable,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    mutable: &HashSet<String>,
    aliases: &HashMap<String, Type>,
    expected: Option<&Type>,
) -> Result<Type, SemanticError> {
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
                    return Err(semantic_at!(
                        ErrorSite::PatternSymbol("_".into()),
                        "duplicate wildcard match pattern"
                    ));
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
                    return Err(semantic_format!(
                        "array match pattern expects {} elements",
                        length
                    ));
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
            result_type = Some(
                merge_types(previous, &arm_type, "match arms")
                    .map_err(|error| error.at(ErrorSite::BranchMismatch(arm_type.clone())))?,
            );
        } else {
            result_type = Some(arm_type);
        }
    }
    if !wildcard {
        return Err(semantic_at!(
            ErrorSite::Operator("match".into()),
            "array match is not exhaustive; add '_' arm"
        ));
    }
    Ok(result_type.unwrap_or(Type::Unit))
}

fn check_enum_payload_pattern(
    pattern: &Expr,
    ty: &Type,
    arm_variables: &mut HashMap<String, Type>,
    variables: &HashMap<String, Type>,
    structs: &HashMap<String, Vec<Field>>,
) -> Result<(), SemanticError> {
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
                return Err(semantic_format!("duplicate match binding '{name}'"));
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
                return Err(semantic_format!(
                    "integer enum payload pattern {value} does not fit in {ty:?}"
                ));
            }
            Ok(())
        }
        Expr::UnsignedInteger(value) if is_integer(ty) => {
            if !fits_unsigned_integer(*value, ty) {
                return Err(semantic_format!(
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
    functions: &FunctionTable,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    mutable: &HashSet<String>,
    aliases: &HashMap<String, Type>,
    expected: Option<&Type>,
) -> Result<Type, SemanticError> {
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
                    return Err(semantic_at!(
                        ErrorSite::PatternSymbol("_".into()),
                        "duplicate wildcard match pattern"
                    ));
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
                    return Err(semantic_format!(
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
                return Err(semantic_format!(
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
            result_type = Some(
                merge_types(previous, &arm_type, "match arms")
                    .map_err(|error| error.at(ErrorSite::BranchMismatch(arm_type.clone())))?,
            );
        } else {
            result_type = Some(arm_type);
        }
    }
    if !wildcard {
        return Err(semantic_at!(
            ErrorSite::Operator("match".into()),
            "struct match is not exhaustive; add '_' arm"
        ));
    }
    Ok(result_type.unwrap_or(Type::Unit))
}

fn require_arity(operator: &str, items: &[Expr], expected: usize) -> Result<(), SemanticError> {
    if items.len() != expected {
        Err(semantic_at!(
            ErrorSite::Operator(operator.into()),
            "operator '{operator}' expects {} operands",
            expected - 1
        ))
    } else {
        Ok(())
    }
}

fn split_generic_call(operator: &str) -> Result<(String, Vec<String>), SemanticError> {
    let Some(open) = operator.find('<') else {
        return Ok((operator.to_owned(), Vec::new()));
    };
    if !operator.ends_with('>') || open == 0 {
        return Err(semantic_format!("malformed generic call '{operator}'"));
    }
    let name = operator[..open].to_owned();
    let arguments = &operator[open + 1..operator.len() - 1];
    if arguments.is_empty() {
        return Err(semantic_format!(
            "generic call '{operator}' has no type arguments"
        ));
    }
    let arguments = arguments
        .split(',')
        .map(str::trim)
        .map(|argument| {
            if argument.is_empty() {
                Err(semantic_format!(
                    "generic call '{operator}' has an empty type argument"
                ))
            } else {
                Ok::<_, SemanticError>(argument.to_owned())
            }
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok((name, arguments))
}

fn generic_substitutions(
    signature: &Signature,
    arguments: &[String],
    aliases: &HashMap<String, Type>,
) -> Result<HashMap<String, Type>, SemanticError> {
    if signature.type_parameters.len() != arguments.len() {
        if signature.type_parameters.is_empty() && arguments.is_empty() {
            return Ok(HashMap::new());
        }
        return Err(semantic_format!(
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
                return Err(semantic_format!(
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

fn resolve_type(ty: &Type, aliases: &HashMap<String, Type>) -> Result<Type, SemanticError> {
    crate::typed_ir::resolve_type(ty, aliases).map_err(SemanticError::from)
}

fn validate_layout_type(
    ty: &Type,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
) -> Result<(), SemanticError> {
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
        Type::Named(name) => Err(semantic_at!(
            ErrorSite::DeclaredType(name.clone()),
            "unknown type '{name}' in size-of"
        )),
        Type::Array(element, _) | Type::Slice(element) | Type::MutableSlice(element) => {
            validate_layout_type(element, structs, enums)
        }
        Type::Tuple(fields) => fields
            .iter()
            .try_for_each(|field| validate_layout_type(field, structs, enums)),
        Type::Generic(name) => Err(semantic_format!(
            "generic type '{name}' has no concrete size"
        )),
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
    functions: &FunctionTable,
    structs: &HashMap<String, Vec<Field>>,
    enums: &HashMap<String, Vec<EnumVariant>>,
    mutable: &HashSet<String>,
    aliases: &HashMap<String, Type>,
) -> Result<(), SemanticError> {
    let actual = expression(
        index, variables, functions, structs, enums, mutable, aliases, None,
    )?;
    if !is_integer(&actual) {
        return Err(semantic_at!(
            ErrorSite::Argument("index".into(), 2),
            "array index must be an integer"
        ));
    }
    if let Expr::Integer(value) = index {
        if *value < 0 || *value >= length as i128 {
            return Err(semantic_format!(
                "array index {value} is out of bounds for length {length}"
            ));
        }
    }
    Ok(())
}

fn require_type(actual: &Type, expected: &Type, context: &str) -> Result<(), SemanticError> {
    if actual == expected || matches!(actual, Type::Never) {
        Ok(())
    } else {
        Err(SemanticError::from(format!(
            "{context} has type {actual:?}, expected {expected:?}"
        ))
        .at(ErrorSite::Mismatch(actual.clone(), Some(expected.clone()))))
    }
}

fn merge_types(left: &Type, right: &Type, context: &str) -> Result<Type, SemanticError> {
    if matches!(left, Type::Never) {
        return Ok(right.clone());
    }
    if matches!(right, Type::Never) {
        return Ok(left.clone());
    }
    require_same(left, right, context)?;
    Ok(left.clone())
}

fn require_same(left: &Type, right: &Type, context: &str) -> Result<(), SemanticError> {
    if left == right {
        Ok(())
    } else {
        Err(SemanticError::from(format!(
            "{context} has mismatched types {left:?} and {right:?}"
        ))
        .at(ErrorSite::Mismatch(right.clone(), Some(left.clone()))))
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

fn is_syscall_word_type(ty: &Type) -> bool {
    matches!(
        ty,
        Type::I8
            | Type::I16
            | Type::I32
            | Type::I64
            | Type::Isize
            | Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::Usize
            | Type::Bool
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

fn require_operator_type(qualifier: &str, ty: &Type, operator: &str) -> Result<(), SemanticError> {
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
            return Err(semantic_format!(
                "operator '{operator}' has an unsupported operand type {ty:?}"
            ))
        }
    };
    if qualifier == expected {
        Ok(())
    } else {
        Err(semantic_format!(
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
) -> Result<(), SemanticError> {
    if !matches!(operation, "+" | "-" | "*" | "/" | "%") {
        if mode.is_some() {
            return Err(semantic_format!(
                "non-arithmetic operator '{operator}' cannot have a wrapping mode"
            ));
        }
        return Ok(());
    }
    if matches!(ty, Type::F32 | Type::F64) {
        if mode.is_some() {
            return Err(semantic_format!(
                "floating-point operator '{operator}' cannot have a wrapping mode"
            ));
        }
        return Ok(());
    }
    if !is_numeric(ty) {
        return Ok(());
    }
    let Some(mode) = mode else {
        return Err(semantic_format!(
            "arithmetic operator '{operator}' requires '.wrap' or '.saturate'"
        ));
    };
    if !matches!(mode, "wrap" | "saturate") {
        return Err(semantic_format!(
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
