//! Lexical borrow checking for Lim's first borrow model.
//!
//! References are explicit values, while expression-form borrows still provide
//! a scoped way to access an owner: `(#borrow owner body)` or
//! `(#borrow-mut owner body)`. The owner is borrowed for exactly the duration
//! of `body`, and two-expression borrows retain provenance in the surrounding
//! context for the lifetime of their binding.

use std::{
    collections::{HashMap, HashSet},
    sync::Arc,
};

use crate::{Expr, Function, Item, Program, Statement};

const PLACE_SEPARATOR: char = '\u{1f}';

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LoanKind {
    Shared(usize),
    Mutable,
}

#[derive(Clone, Default)]
struct Loans {
    active: HashMap<String, LoanKind>,
}

#[derive(Clone)]
struct Context {
    loans: Loans,
    returnable: HashSet<String>,
    mutable: HashSet<String>,
    mutable_references: HashSet<String>,
    reference_bindings: HashSet<String>,
    suspended_references: HashSet<String>,
    scoped_mutable_owners: HashSet<String>,
    reference_origins: HashMap<String, HashSet<String>>,
    reference_loans: HashMap<String, Vec<(String, String)>>,
    reference_fields:
        HashMap<String, HashMap<Vec<usize>, (HashSet<String>, Vec<(String, String)>)>>,
    reference_parents: HashMap<String, String>,
    allow_local_reference: bool,
    reference_types: HashSet<String>,
    reference_functions: HashSet<String>,
    function_names: HashSet<String>,
    thread_spawn_functions: HashMap<String, Vec<crate::Type>>,
    thread_join_functions: HashSet<String>,
    thread_task_loans: HashMap<String, Vec<(String, LoanKind)>>,
    thread_exclusive_owners: HashMap<String, usize>,
    return_contains_references: bool,
    mutable_reference_types: HashSet<String>,
    program_items: Arc<Vec<Item>>,
}

impl Loans {
    fn borrow(&mut self, place: &str, kind: LoanKind) -> Result<(), String> {
        if let Some(active) = self.active.iter().find_map(|(active, active_kind)| {
            (active.as_str() != place
                && places_conflict(active, place)
                && !matches!(
                    (active_kind, kind),
                    (LoanKind::Shared(_), LoanKind::Shared(_))
                ))
            .then_some(active.clone())
        }) {
            return Err(format!(
                "cannot borrow '{}' because '{}' is already borrowed",
                display_place(place),
                display_place(&active)
            ));
        }
        match (self.active.get(place).copied(), kind) {
            (None, kind) => {
                self.active.insert(place.to_owned(), kind);
                Ok(())
            }
            (Some(LoanKind::Shared(count)), LoanKind::Shared(_)) => {
                self.active
                    .insert(place.to_owned(), LoanKind::Shared(count + 1));
                Ok(())
            }
            (Some(LoanKind::Shared(_)), LoanKind::Mutable) => Err(format!(
                "cannot borrow '{}' mutably because it is already borrowed",
                display_place(place)
            )),
            (Some(LoanKind::Mutable), LoanKind::Shared(_)) => Err(format!(
                "cannot borrow '{}' because it is already borrowed mutably",
                display_place(place)
            )),
            (Some(LoanKind::Mutable), LoanKind::Mutable) => Err(format!(
                "cannot borrow '{}' mutably because it is already borrowed mutably",
                display_place(place)
            )),
        }
    }

    fn end(&mut self, place: &str) {
        match self.active.get_mut(place) {
            Some(LoanKind::Shared(count)) if *count > 1 => *count -= 1,
            Some(_) => {
                self.active.remove(place);
            }
            None => {}
        }
    }
}

fn places_conflict(left: &str, right: &str) -> bool {
    let left = left.split(PLACE_SEPARATOR).collect::<Vec<_>>();
    let right = right.split(PLACE_SEPARATOR).collect::<Vec<_>>();
    let common = left.len().min(right.len());
    left[..common]
        .iter()
        .zip(&right[..common])
        .all(|(left, right)| left == right || *left == "*" || *right == "*")
}

fn display_place(place: &str) -> String {
    place.split(PLACE_SEPARATOR).collect::<Vec<_>>().join(".")
}

fn has_child_loan(loans: &Loans, owner: &str) -> bool {
    loans
        .active
        .keys()
        .any(|active| active.starts_with(&format!("{owner}{PLACE_SEPARATOR}")))
}

impl Context {
    fn write(&self, owner: &str) -> Result<(), String> {
        self.write_place(owner, None)
    }

    fn write_place(&self, owner: &str, field: Option<&str>) -> Result<(), String> {
        if self.thread_exclusive_owners.contains_key(owner) {
            return Err(format!(
                "cannot mutate '{owner}' while it is mutably borrowed by a running thread"
            ));
        }
        let place = field.map_or_else(
            || owner.to_owned(),
            |field| format!("{owner}{PLACE_SEPARATOR}{field}"),
        );
        for (loan, kind) in &self.loans.active {
            if !places_conflict(loan, &place) {
                continue;
            }
            if matches!(kind, LoanKind::Shared(_)) {
                return Err(format!(
                    "cannot mutate '{}' while it is immutably borrowed",
                    if loan == owner {
                        owner.to_owned()
                    } else {
                        display_place(&place)
                    }
                ));
            }
            if !self.scoped_mutable_owners.contains(owner) {
                return Err(format!(
                    "cannot mutate '{}' while it is mutably borrowed",
                    if loan == owner {
                        owner.to_owned()
                    } else {
                        display_place(&place)
                    }
                ));
            }
        }
        Ok(())
    }

    fn read_place(
        &self,
        owner: &str,
        field: Option<&str>,
        through_mutable_reference: bool,
    ) -> Result<(), String> {
        if self.thread_exclusive_owners.contains_key(owner) {
            return Err(format!(
                "cannot access '{owner}' while it is mutably borrowed by a running thread"
            ));
        }
        let place = field.map_or_else(
            || owner.to_owned(),
            |field| format!("{owner}{PLACE_SEPARATOR}{field}"),
        );
        for (loan, kind) in &self.loans.active {
            if places_conflict(loan, &place)
                && *kind == LoanKind::Mutable
                && (!through_mutable_reference || loan != owner)
                && (!self.scoped_mutable_owners.contains(owner) || loan != owner)
            {
                return Err(format!(
                    "cannot access '{}' while it is mutably borrowed",
                    display_place(&place)
                ));
            }
        }
        Ok(())
    }
}

pub(crate) fn check_program(program: &Program) -> Result<(), String> {
    let globals = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Let { name, .. } | Item::Static { name, .. } => Some(name.clone()),
            _ => None,
        })
        .collect::<HashSet<_>>();
    let reference_types = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Struct { name, fields, .. }
                if fields.iter().any(|field| {
                    type_contains_reference(&field.ty, &program.items, &mut HashSet::new())
                }) =>
            {
                Some(name.clone())
            }
            Item::Enum { name, variants, .. }
                if variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|ty| type_contains_reference(ty, &program.items, &mut HashSet::new())) =>
            {
                Some(name.clone())
            }
            _ => None,
        })
        .collect::<HashSet<_>>();
    let mutable_reference_types = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Struct { name, .. } | Item::Enum { name, .. }
                if type_contains_mutable_reference(
                    &crate::Type::Named(name.clone()),
                    &program.items,
                    &mut HashSet::new(),
                ) =>
            {
                Some(name.clone())
            }
            _ => None,
        })
        .collect::<HashSet<_>>();
    let reference_functions = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Function(function)
                if contains_reference_type(&function.return_type, &reference_types) =>
            {
                Some(function.name.clone())
            }
            _ => None,
        })
        .collect::<HashSet<_>>();
    let function_names = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Function(function) => Some(function.name.clone()),
            _ => None,
        })
        .collect::<HashSet<_>>();
    let mut thread_spawn_functions = HashMap::new();
    let mut thread_join_functions = HashSet::new();
    for item in &program.items {
        let Item::ThreadTask { name, worker, .. } = item else {
            continue;
        };
        let parameters = program.items.iter().find_map(|item| match item {
            Item::Function(function) if function.name == *worker => Some(
                function
                    .parameters
                    .iter()
                    .map(|parameter| parameter.ty.clone())
                    .collect::<Vec<_>>(),
            ),
            _ => None,
        });
        if let Some(parameters) = parameters {
            thread_spawn_functions.insert(format!("{name}-spawn"), parameters);
        }
        thread_join_functions.insert(format!("{name}-join"));
    }
    let function_names = function_names
        .into_iter()
        .chain(thread_spawn_functions.keys().cloned())
        .chain(thread_join_functions.iter().cloned())
        .collect();
    for item in &program.items {
        if let Item::Function(function) = item {
            if !function.external {
                check_function(
                    function,
                    program,
                    &globals,
                    &reference_types,
                    &mutable_reference_types,
                    &reference_functions,
                    &function_names,
                    &thread_spawn_functions,
                    &thread_join_functions,
                    &program.statement_spans,
                    &program.statement_expressions,
                )?;
            }
        }
    }
    Ok(())
}

fn check_function(
    function: &Function,
    program: &Program,
    globals: &std::collections::HashSet<String>,
    reference_types: &HashSet<String>,
    mutable_reference_types: &HashSet<String>,
    reference_functions: &HashSet<String>,
    function_names: &HashSet<String>,
    thread_spawn_functions: &HashMap<String, Vec<crate::Type>>,
    thread_join_functions: &HashSet<String>,
    statement_spans: &HashMap<(String, usize), crate::Span>,
    statement_expressions: &HashMap<(String, usize), crate::SpannedExpr>,
) -> Result<(), String> {
    let mut returnable = globals.clone();
    let mut mutable = std::collections::HashSet::new();
    let mut mutable_references = HashSet::new();
    let mut reference_bindings = HashSet::new();
    let mut reference_origins = HashMap::new();
    for parameter in &function.parameters {
        returnable.insert(parameter.name.clone());
        if contains_reference_type(&parameter.ty, reference_types) {
            reference_origins.insert(
                parameter.name.clone(),
                HashSet::from([parameter.name.clone()]),
            );
            if matches!(parameter.ty, crate::Type::Reference { .. }) {
                reference_bindings.insert(parameter.name.clone());
            }
            if contains_mutable_reference(&parameter.ty, reference_types, mutable_reference_types) {
                mutable_references.insert(parameter.name.clone());
            }
        }
        if parameter.mutable {
            mutable.insert(parameter.name.clone());
        }
    }
    let mut context = Context {
        loans: Loans::default(),
        returnable,
        mutable,
        mutable_references,
        reference_bindings,
        suspended_references: HashSet::new(),
        scoped_mutable_owners: HashSet::new(),
        reference_origins,
        reference_loans: HashMap::new(),
        reference_fields: HashMap::new(),
        reference_parents: HashMap::new(),
        allow_local_reference: false,
        reference_types: reference_types.clone(),
        mutable_reference_types: mutable_reference_types.clone(),
        reference_functions: reference_functions.clone(),
        function_names: function_names.clone(),
        thread_spawn_functions: thread_spawn_functions.clone(),
        thread_join_functions: thread_join_functions.clone(),
        thread_task_loans: HashMap::new(),
        thread_exclusive_owners: HashMap::new(),
        return_contains_references: contains_reference_type(&function.return_type, reference_types),
        program_items: Arc::new(program.items.clone()),
    };
    for parameter in &function.parameters {
        if contains_reference_type(&parameter.ty, reference_types) {
            let kind = if contains_mutable_reference(
                &parameter.ty,
                reference_types,
                mutable_reference_types,
            ) {
                LoanKind::Mutable
            } else {
                LoanKind::Shared(1)
            };
            context.loans.borrow(&parameter.name, kind)?;
        }
    }
    for (statement_index, statement) in function.body.iter().enumerate() {
        if let Err(error) = check_statement(statement, &mut context) {
            return Err(format_borrow_diagnostic(
                error,
                function,
                statement_index,
                statement_spans
                    .get(&(function.name.clone(), statement_index))
                    .copied(),
                statement_expressions.get(&(function.name.clone(), statement_index)),
                statement_expressions,
            ));
        }
    }
    Ok(())
}

fn format_borrow_diagnostic(
    error: String,
    function: &Function,
    statement_index: usize,
    exact_conflict_span: Option<crate::Span>,
    statement_expression: Option<&crate::SpannedExpr>,
    function_expressions: &HashMap<(String, usize), crate::SpannedExpr>,
) -> String {
    let owner = error
        .split('\'')
        .nth(1)
        .filter(|name| !name.is_empty())
        .unwrap_or("<unknown>");
    let exact_conflict_span = exact_conflict_span.and_then(|statement_span| {
        statement_expression
            .and_then(|expression| conflict_operator_source_span(expression, owner, &error))
            .or_else(|| {
                statement_expression.and_then(|expression| {
                    find_accessed_source_symbol(expression, &place_name_candidates(owner))
                })
            })
            .or_else(|| statement_expression.map(crate::source_value_span))
            .or(Some(statement_span))
    });
    let spans = source_spans(
        function_expressions,
        &function.name,
        owner,
        exact_conflict_span,
    );
    let span_text = if let Some(span) = exact_conflict_span {
        format!(
            "original borrow site {}; conflicting access {}:{}; conflicting span {}:{}:{}",
            spans.first().map_or_else(
                || "unavailable".to_owned(),
                |site| format!("{}:{}", site.0, site.1)
            ),
            span.line,
            span.column,
            span.source_id,
            span.start,
            span.end
        )
    } else if spans.is_empty() {
        "source spans unavailable".to_owned()
    } else {
        let first = spans[0];
        let second = spans.get(1).copied().unwrap_or(first);
        format!(
            "original borrow site {}:{}; conflicting access {}:{}",
            first.0, first.1, second.0, second.1
        )
    };
    format!(
        "E4100 borrow-checker diagnostic in function '{}' statement {}: {}; {}",
        function.name, statement_index, error, span_text
    )
}

fn find_accessed_source_symbol(
    expression: &crate::SpannedExpr,
    names: &[&str],
) -> Option<crate::Span> {
    if matches!(&expression.expr, Expr::Symbol(name) if names.contains(&name.as_str())) {
        return Some(expression.span);
    }
    let Expr::List(items) = &expression.expr else {
        return expression
            .children
            .iter()
            .find_map(|child| find_accessed_source_symbol(child, names));
    };
    let head = match items.first() {
        Some(Expr::Symbol(name)) => name.as_str(),
        _ => "",
    };
    match head {
        "#get" | "get" | "#get-payload" | "get-payload" => expression
            .children
            .get(1)
            .and_then(|base| find_accessed_source_symbol(base, names)),
        "#call" | "call" => expression
            .children
            .get(2)
            .and_then(|arguments| find_accessed_source_symbol(arguments, names)),
        "#struct-literal" | "struct-literal" => expression
            .children
            .get(2)
            .into_iter()
            .flat_map(|fields| &fields.children)
            .filter_map(|field| field.children.get(1))
            .find_map(|value| find_accessed_source_symbol(value, names)),
        _ => expression
            .children
            .iter()
            .skip(1)
            .find_map(|child| find_accessed_source_symbol(child, names)),
    }
}

fn source_spans(
    expressions: &HashMap<(String, usize), crate::SpannedExpr>,
    function_name: &str,
    needle: &str,
    conflict: Option<crate::Span>,
) -> Vec<(usize, usize)> {
    let full_path = needle.trim_end_matches(".*").split('.').collect::<Vec<_>>();
    let mut statements = expressions
        .iter()
        .filter(|((name, _), _)| name == function_name)
        .collect::<Vec<_>>();
    statements.sort_by_key(|((_, index), _)| *index);

    let mut aliases = HashMap::<String, HashSet<String>>::new();
    let mut sites = Vec::new();
    for (_, statement) in statements {
        if conflict.is_some_and(|span| statement.span.start >= span.start) {
            break;
        }
        if let Expr::List(items) = &statement.expr {
            if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#let" | "#let-mut"))
            {
                if let (Some(Expr::Symbol(binding)), Some(value)) =
                    (items.get(1), statement.children.get(3))
                {
                    let mut borrow_forms = Vec::new();
                    collect_borrow_forms(value, &mut borrow_forms);
                    let mut origins = HashSet::new();
                    for form in borrow_forms {
                        if let Some(argument) = form.children.get(1) {
                            collect_source_symbols(argument, &mut origins);
                        }
                    }
                    if !origins.is_empty() {
                        aliases.insert(binding.clone(), origins);
                    }
                }
            }
        }
        let mut borrow_forms = Vec::new();
        collect_borrow_forms(statement, &mut borrow_forms);
        for form in borrow_forms {
            let Some(operator) = form.children.first() else {
                continue;
            };
            if conflict.is_some_and(|span| operator.span.start >= span.start) {
                continue;
            }
            let Some(argument) = form.children.get(1) else {
                continue;
            };
            let mut names = HashSet::new();
            collect_source_symbols(argument, &mut names);
            let mut expanded = names.clone();
            for name in &names {
                if let Some(origins) = aliases.get(name) {
                    expanded.extend(origins.iter().cloned());
                }
            }
            if names.contains(needle) || full_path.iter().all(|part| expanded.contains(*part)) {
                sites.push((
                    operator.span.line,
                    operator.span.column,
                    operator.span.start,
                ));
            }
        }
    }
    sites
        .into_iter()
        .max_by_key(|(_, _, start)| *start)
        .map(|(line, column, _)| vec![(line, column)])
        .unwrap_or_default()
}

fn collect_borrow_forms<'a>(
    expression: &'a crate::SpannedExpr,
    forms: &mut Vec<&'a crate::SpannedExpr>,
) {
    if let Expr::List(items) = &expression.expr {
        if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#borrow" | "#borrow-mut"))
        {
            forms.push(expression);
        }
    }
    for child in &expression.children {
        collect_borrow_forms(child, forms);
    }
}

fn collect_source_symbols(expression: &crate::SpannedExpr, names: &mut HashSet<String>) {
    if let Expr::Symbol(name) = &expression.expr {
        names.insert(name.clone());
    }
    for child in &expression.children {
        collect_source_symbols(child, names);
    }
}

fn conflict_operator_source_span(
    expression: &crate::SpannedExpr,
    owner: &str,
    error: &str,
) -> Option<crate::Span> {
    let owner_names = place_name_candidates(owner);
    if error.starts_with("cannot access") {
        return find_accessed_source_symbol(expression, &owner_names);
    }
    fn visit(expression: &crate::SpannedExpr, error: &str) -> Option<crate::Span> {
        let Expr::List(items) = &expression.expr else {
            return None;
        };
        let operator = match items.first() {
            Some(Expr::Symbol(name)) => name.as_str(),
            _ => "",
        };
        let matches_operator = if error.starts_with("cannot borrow") {
            matches!(operator, "#borrow" | "#borrow-mut")
        } else if error.starts_with("cannot mutate") || error.starts_with("cannot write") {
            operator.starts_with("#set") || operator == "#deref-set"
        } else {
            false
        };
        let own = matches_operator
            .then(|| expression.children.first().map(|head| head.span))
            .flatten();
        let nested = expression
            .children
            .iter()
            .filter_map(|child| visit(child, error))
            .max_by_key(|span| span.start);
        match (own, nested) {
            (Some(own), Some(nested)) => Some(if own.start > nested.start {
                own
            } else {
                nested
            }),
            (Some(span), None) | (None, Some(span)) => Some(span),
            (None, None) => None,
        }
    }
    visit(expression, error)
}

fn place_name_candidates(place: &str) -> Vec<&str> {
    let mut candidates = vec![place];
    if let Some((root, _)) = place.split_once('.') {
        candidates.push(root);
    }
    if let Some((root, _)) = place.split_once('[') {
        candidates.push(root);
    }
    candidates
}

fn check_statement(statement: &Statement, context: &mut Context) -> Result<(), String> {
    match statement {
        Statement::Let {
            name,
            ty,
            value,
            mutable,
        } => {
            let contains_references = contains_reference_type(ty, &context.reference_types);
            let origins = reference_origins(value, context, contains_references);
            let derived_parent = borrowed_field_parent(value);
            let contains_mutable_references = contains_mutable_reference(
                ty,
                &context.reference_types,
                &context.mutable_reference_types,
            );
            let is_reference_binding = matches!(ty, crate::Type::Reference { .. });
            let mut reference_fields = HashMap::new();
            if contains_references {
                collect_reference_fields(
                    ty,
                    value,
                    context,
                    &mut Vec::new(),
                    &mut reference_fields,
                );
            }
            let task_loans = thread_spawn_origins(value, context);
            context.allow_local_reference = true;
            let checked = check_expression(value, context);
            context.allow_local_reference = false;
            checked?;
            let moves_thread_task = if let Expr::Symbol(source) = value {
                context.thread_task_loans.contains_key(source).then(|| {
                    move_thread_task_loans(source, name, context);
                })
            } else {
                None
            }
            .is_some();
            if let Some(task_loans) = task_loans {
                for (owner, kind) in &task_loans {
                    context.loans.borrow(owner, *kind)?;
                    if *kind == LoanKind::Mutable {
                        *context
                            .thread_exclusive_owners
                            .entry(owner.clone())
                            .or_default() += 1;
                    }
                }
                context.reference_origins.insert(
                    name.clone(),
                    task_loans.iter().map(|(owner, _)| owner.clone()).collect(),
                );
                context.thread_task_loans.insert(name.clone(), task_loans);
            } else if !moves_thread_task {
                if let Some(parent) = derived_parent.as_ref() {
                    if context.mutable_references.contains(parent) {
                        context.suspended_references.insert(parent.clone());
                    }
                }
                let mut loans = if contains_references {
                    let mut paths = reference_fields.keys().collect::<Vec<_>>();
                    paths.sort();
                    paths
                        .into_iter()
                        .flat_map(|path| reference_fields[path].1.iter().cloned())
                        .collect::<Vec<_>>()
                } else {
                    Vec::new()
                };
                if loans.is_empty() && contains_references {
                    loans = borrow_place_loans(value, context);
                }
                if loans.is_empty() {
                    loans = origins
                        .iter()
                        .cloned()
                        .map(|owner| (owner.clone(), owner))
                        .collect();
                }
                for (owner, loan) in &loans {
                    if derived_parent
                        .as_ref()
                        .is_some_and(|parent| context.mutable_references.contains(parent))
                    {
                        if loan != owner
                            && matches!(context.loans.active.get(owner), Some(LoanKind::Mutable))
                        {
                            context.loans.active.remove(owner);
                        }
                        if contains_mutable_references {
                            context.loans.borrow(loan, LoanKind::Mutable)?;
                        } else {
                            context.loans.borrow(loan, LoanKind::Shared(1))?;
                        }
                    } else {
                        context.loans.borrow(
                            loan,
                            if contains_mutable_references {
                                LoanKind::Mutable
                            } else {
                                LoanKind::Shared(1)
                            },
                        )?;
                    }
                }
                if origins.is_empty() || !contains_references {
                    context.reference_origins.remove(name);
                } else {
                    context.reference_origins.insert(name.clone(), origins);
                }
                if !loans.is_empty() {
                    context.reference_loans.insert(name.clone(), loans);
                }
                if let Some(parent) = derived_parent {
                    context.reference_parents.insert(name.clone(), parent);
                }
            }
            if *mutable {
                context.mutable.insert(name.clone());
            }
            if contains_mutable_references {
                context.mutable_references.insert(name.clone());
            }
            if is_reference_binding {
                context.reference_bindings.insert(name.clone());
            }
            if !reference_fields.is_empty() {
                context
                    .reference_fields
                    .insert(name.clone(), reference_fields);
            }
        }
        Statement::Destructure {
            pattern,
            ty,
            value,
            mutable,
        } => {
            check_expression(value, context)?;
            bind_pattern_references(pattern, ty, value, context)?;
            if *mutable {
                let mut names = Vec::new();
                pattern_names(pattern, &mut names);
                context.mutable.extend(names);
            }
        }
        Statement::LetElse {
            pattern, ty, value, ..
        } => {
            check_expression(value, context)?;
            bind_pattern_references(pattern, ty, value, context)?;
        }
        Statement::Assign { name, value } => {
            if matches!(statement, Statement::Assign { .. })
                && context.reference_origins.contains_key(name)
            {
                return Err(format!(
                    "cannot replace '{name}' while it retains references"
                ));
            }
            check_expression(value, context)?;
            context.write(name)?;
        }
        Statement::FieldAssign { name, field, value } => {
            check_expression(value, context)?;
            context.write_place(name, Some(field))?;
        }
        Statement::TupleAssign { name, index, value } => {
            check_expression(value, context)?;
            context.write_place(name, Some(&index.to_string()))?;
        }
        Statement::EnumPayloadAssign {
            name,
            variant,
            index,
            value,
        } => {
            check_expression(value, context)?;
            context.write_place(name, Some(&format!("{variant}.{index}")))?;
        }
        Statement::ArrayAssign { name, index, value } => {
            check_expression(index, context)?;
            check_expression(value, context)?;
            if let Some(index) = static_index_segment(index) {
                context.write_place(name, Some(&index))?;
            } else {
                context.write(name)?;
            }
        }
        Statement::While { condition, body } => {
            check_expression(condition, context)?;
            check_loop_iteration(body, context)?;
        }
        Statement::Loop { body } => check_loop_iteration(body, context)?,
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            check_statement(init, context)?;
            check_expression(condition, context)?;
            let mut iteration = context.clone();
            check_statements(body, &mut iteration)?;
            check_statement(step, &mut iteration)?;
            ensure_loop_thread_state(context, &iteration)?;
        }
        Statement::Labeled { statement, .. } => check_statement(statement, context)?,
        Statement::Return(Some(value)) => {
            check_expression(value, context)?;
            for owner in reference_origins(value, context, context.return_contains_references) {
                if !context.returnable.contains(&owner) {
                    return Err(format!(
                        "cannot return a value retaining a reference to local '{owner}'"
                    ));
                }
            }
        }
        Statement::BreakValue(value) | Statement::BreakToValue { value, .. } => {
            check_expression(value, context)?
        }
        Statement::Expr(value) => {
            if thread_spawn_origins(value, context).is_some() {
                return Err(
                    "thread spawn results must be stored in a task binding and joined before the binding is discarded"
                        .into(),
                );
            }
            check_expression(value, context)?
        }
        Statement::Return(None)
        | Statement::Break
        | Statement::BreakTo(_)
        | Statement::Continue
        | Statement::ContinueTo(_) => {}
    }
    if let Statement::LetElse { else_body, .. } = statement {
        check_statements(else_body, context)?;
    }
    Ok(())
}

fn pattern_names(pattern: &Expr, names: &mut Vec<String>) {
    match pattern {
        Expr::Symbol(name) if name != "_" => names.push(name.clone()),
        Expr::List(items) => {
            for child in items.iter().skip(1) {
                pattern_names(child, names);
            }
        }
        _ => {}
    }
}

fn bind_pattern_references(
    pattern: &Expr,
    ty: &crate::Type,
    value: &Expr,
    context: &mut Context,
) -> Result<(), String> {
    let inherited_origins = reference_origins(value, context, true);
    let inherited_fields = match value {
        Expr::Symbol(name) => context
            .reference_fields
            .get(name)
            .cloned()
            .unwrap_or_default(),
        _ => HashMap::new(),
    };
    let inherited_loans = match value {
        Expr::Symbol(name) => context
            .reference_loans
            .get(name)
            .cloned()
            .unwrap_or_default(),
        _ => borrow_place_loans(value, context),
    };
    if matches!(value, Expr::Symbol(_)) {
        release_dropped_value(value, context);
    }
    if let Expr::Symbol(name) = value {
        context.reference_fields.remove(name);
    }
    bind_pattern_reference_fields(
        pattern,
        ty,
        value,
        context,
        &inherited_origins,
        &inherited_loans,
        &inherited_fields,
        &mut Vec::new(),
    )
}

fn collect_reference_fields(
    ty: &crate::Type,
    value: &Expr,
    context: &Context,
    path: &mut Vec<usize>,
    result: &mut HashMap<Vec<usize>, (HashSet<String>, Vec<(String, String)>)>,
) {
    if !type_contains_reference(ty, &context.program_items, &mut HashSet::new()) {
        return;
    }
    if let Expr::Symbol(name) = value {
        if let Some(existing) = context
            .reference_fields
            .get(name)
            .and_then(|fields| fields.get(path))
        {
            result.insert(path.clone(), existing.clone());
            return;
        }
    }
    let children = match ty {
        crate::Type::Tuple(fields) => fields.clone(),
        crate::Type::Array(element, count) => {
            std::iter::repeat_n((**element).clone(), *count).collect()
        }
        crate::Type::Named(name) => context
            .program_items
            .iter()
            .find_map(|item| match item {
                Item::Struct {
                    name: struct_name,
                    fields,
                    ..
                } if struct_name == name => Some(
                    fields
                        .iter()
                        .map(|field| field.ty.clone())
                        .collect::<Vec<_>>(),
                ),
                Item::Enum {
                    name: enum_name,
                    variants,
                    ..
                } if enum_name == name => {
                    let variant_name = match value {
                        Expr::List(items) => items.first().and_then(|head| match head {
                            Expr::Symbol(name) => Some(name.as_str()),
                            _ => None,
                        }),
                        _ => None,
                    }?;
                    variants
                        .iter()
                        .find(|variant| variant.name == variant_name)
                        .map(|variant| variant.fields.clone())
                }
                _ => None,
            })
            .unwrap_or_default(),
        _ => Vec::new(),
    };
    if !children.is_empty() {
        if let Expr::List(items) = value {
            let value_start = match ty {
                crate::Type::Array(_, _) => 2,
                crate::Type::Tuple(_) if items.len() == children.len() + 2 => 2,
                _ => 1,
            };
            for (index, child_type) in children.iter().enumerate() {
                if let Some(child_value) = items.get(index + value_start) {
                    path.push(index);
                    collect_reference_fields(child_type, child_value, context, path, result);
                    path.pop();
                }
            }
            return;
        }
    }
    let origins = reference_origins(value, context, true);
    if origins.is_empty() {
        return;
    }
    let mut loans = borrow_place_loans(value, context);
    if loans.is_empty() {
        if let Expr::Symbol(name) = value {
            loans = context
                .reference_loans
                .get(name)
                .cloned()
                .unwrap_or_default();
        }
    }
    if loans.is_empty() {
        loans.extend(origins.iter().cloned().map(|owner| (owner.clone(), owner)));
    }
    result.insert(path.clone(), (origins, loans));
}

fn bind_pattern_reference_fields(
    pattern: &Expr,
    ty: &crate::Type,
    value: &Expr,
    context: &mut Context,
    inherited_origins: &HashSet<String>,
    inherited_loans: &[(String, String)],
    inherited_fields: &HashMap<Vec<usize>, (HashSet<String>, Vec<(String, String)>)>,
    path: &mut Vec<usize>,
) -> Result<(), String> {
    if let Expr::Symbol(name) = pattern {
        if name == "_" || !type_contains_reference(ty, &context.program_items, &mut HashSet::new())
        {
            return Ok(());
        }
        let mut origins = reference_origins(value, context, true);
        if origins.is_empty() {
            origins.clone_from(inherited_origins);
        }
        let mut loans = borrow_place_loans(value, context);
        if let Some((field_origins, field_loans)) = inherited_fields.get(path) {
            origins.clone_from(field_origins);
            loans.clone_from(field_loans);
        }
        if loans.is_empty() {
            loans.extend_from_slice(inherited_loans);
        }
        if loans.is_empty() {
            loans.extend(origins.iter().cloned().map(|owner| (owner.clone(), owner)));
        }
        let mutable =
            type_contains_mutable_reference(ty, &context.program_items, &mut HashSet::new());
        let kind = if mutable {
            LoanKind::Mutable
        } else {
            LoanKind::Shared(1)
        };
        for (owner, loan) in &loans {
            context
                .loans
                .borrow(loan, kind)
                .map_err(|error| format!("cannot destructure reference into '{name}': {error}"))?;
            if mutable && loan != owner {
                context.loans.active.remove(owner);
            }
        }
        context.reference_origins.insert(name.clone(), origins);
        context.reference_loans.insert(name.clone(), loans);
        if matches!(ty, crate::Type::Reference { .. } | crate::Type::Slice(_)) {
            context.reference_bindings.insert(name.clone());
        }
        if mutable {
            context.mutable_references.insert(name.clone());
        }
        let nested_fields = inherited_fields
            .iter()
            .filter_map(|(field_path, state)| {
                field_path
                    .strip_prefix(path.as_slice())
                    .filter(|suffix| !suffix.is_empty())
                    .map(|suffix| (suffix.to_vec(), state.clone()))
            })
            .collect::<HashMap<_, _>>();
        if !nested_fields.is_empty() {
            context.reference_fields.insert(name.clone(), nested_fields);
        }
        return Ok(());
    }

    let Expr::List(pattern_items) = pattern else {
        return Ok(());
    };
    let Some(Expr::Symbol(pattern_head)) = pattern_items.first() else {
        return Ok(());
    };
    let value_items = match value {
        Expr::List(items) => Some(items),
        _ => None,
    };
    let pattern_children = &pattern_items[1..];
    let mut child_types = Vec::new();
    match ty {
        crate::Type::Tuple(fields) => child_types.extend(fields.iter().cloned()),
        crate::Type::Array(element, count) => {
            child_types.extend(std::iter::repeat_n((**element).clone(), *count));
        }
        crate::Type::Named(name) => {
            for item in context.program_items.iter() {
                match item {
                    Item::Struct {
                        name: struct_name,
                        fields,
                        ..
                    } if struct_name == name && pattern_head == name => {
                        child_types.extend(fields.iter().map(|field| field.ty.clone()));
                    }
                    Item::Enum {
                        name: enum_name,
                        variants,
                        ..
                    } if enum_name == name => {
                        if let Some(variant) = variants
                            .iter()
                            .find(|variant| variant.name == *pattern_head)
                        {
                            child_types.extend(variant.fields.iter().cloned());
                        }
                    }
                    _ => {}
                }
            }
        }
        _ => {}
    }
    let value_start = match ty {
        crate::Type::Array(_, _) => 2,
        crate::Type::Tuple(_)
            if value_items.is_some_and(|items| items.len() == child_types.len() + 2) =>
        {
            2
        }
        _ => 1,
    };
    for (index, (child_pattern, child_type)) in
        pattern_children.iter().zip(child_types.iter()).enumerate()
    {
        let child_value = value_items
            .and_then(|items| items.get(index + value_start))
            .unwrap_or(value);
        path.push(index);
        bind_pattern_reference_fields(
            child_pattern,
            child_type,
            child_value,
            context,
            inherited_origins,
            inherited_loans,
            inherited_fields,
            path,
        )?;
        path.pop();
    }
    Ok(())
}

fn check_statements(statements: &[Statement], context: &mut Context) -> Result<(), String> {
    for statement in statements {
        check_statement(statement, context)?;
    }
    Ok(())
}

fn check_loop_iteration(statements: &[Statement], context: &Context) -> Result<(), String> {
    let mut iteration = context.clone();
    check_statements(statements, &mut iteration)?;
    ensure_loop_thread_state(context, &iteration)
}

fn ensure_loop_thread_state(before: &Context, after: &Context) -> Result<(), String> {
    if before.thread_task_loans != after.thread_task_loans
        || before.thread_exclusive_owners != after.thread_exclusive_owners
    {
        return Err(
            "thread task borrows must be spawned and joined within the same loop iteration".into(),
        );
    }
    Ok(())
}

fn check_expression(expression: &Expr, context: &mut Context) -> Result<(), String> {
    match expression {
        Expr::List(items) => {
            if let Some(Expr::Symbol(operator)) = items.first() {
                if matches!(operator.as_str(), "drop" | "forget") && items.len() == 2 {
                    check_expression(&items[1], context)?;
                    release_dropped_value(&items[1], context);
                } else if operator == "if" && items.len() == 4 {
                    check_expression(&items[1], context)?;
                    let base = context.clone();
                    let mut then_context = base.clone();
                    let mut else_context = base.clone();
                    check_expression(&items[2], &mut then_context)?;
                    check_expression(&items[3], &mut else_context)?;
                    merge_branch_context(context, &[then_context, else_context]);
                } else if operator == "match" && items.len() >= 3 {
                    let thread_operation = thread_match_operation(&items[1], context);
                    check_expression(&items[1], context)?;
                    let base = context.clone();
                    let mut branches = Vec::with_capacity(items.len() - 2);
                    for arm in &items[2..] {
                        let Expr::List(parts) = arm else {
                            return Err("match arms must be lists".into());
                        };
                        if parts.len() != 2 && parts.len() != 3 {
                            return Err("match arms must contain a pattern and body".into());
                        }
                        let mut branch = base.clone();
                        if let Some(operation) = &thread_operation {
                            apply_thread_match_arm(
                                operation,
                                &parts[0],
                                parts.len() == 3,
                                &mut branch,
                            )?;
                        }
                        if parts.len() == 3 {
                            check_expression(&parts[1], &mut branch)?;
                        }
                        check_expression(parts.last().expect("validated match arm"), &mut branch)?;
                        branches.push(branch);
                    }
                    merge_branch_context(context, &branches);
                } else if matches!(operator.as_str(), "borrow" | "borrow-mut") {
                    if items.len() != 3 {
                        if items.len() == 2 {
                            let origins = borrow_place_origins(&items[1], context);
                            if origins.is_empty() {
                                return Err(format!("{operator} place has no tracked owner"));
                            }
                            if !context.allow_local_reference {
                                if let Some(owner) = origins
                                    .iter()
                                    .find(|owner| !context.returnable.contains(*owner))
                                {
                                    return Err(format!(
                                        "cannot return a reference to local variable '{owner}'"
                                    ));
                                }
                            }
                            if let Some((base, path)) = projection_path(&items[1]) {
                                if path.is_empty() {
                                    check_expression(&items[1], context)?;
                                } else {
                                    check_projection_base(base, context)?;
                                }
                            } else {
                                check_expression(&items[1], context)?;
                            }
                            return Ok(());
                        }
                        return Err(format!(
                            "{operator} requires a place, with an optional body"
                        ));
                    }
                    let origins = borrow_place_origins(&items[1], context);
                    if origins.is_empty() {
                        return Err(format!("{operator} place has no tracked owner"));
                    }
                    let loans = borrow_place_loans(&items[1], context);
                    let kind = if operator == "borrow" {
                        LoanKind::Shared(1)
                    } else {
                        LoanKind::Mutable
                    };
                    let parent = borrowed_field_parent(expression);
                    if let Some((base, path)) = projection_path(&items[1]) {
                        if path.is_empty() {
                            check_expression(&items[1], context)?;
                        } else {
                            check_projection_base(base, context)?;
                        }
                    } else {
                        check_expression(&items[1], context)?;
                    }
                    let reborrow_mutable_parent = parent
                        .as_ref()
                        .is_some_and(|parent| context.mutable_references.contains(parent));
                    for (owner, loan) in &loans {
                        if reborrow_mutable_parent {
                            // A field reborrow temporarily suspends the parent
                            // loan.  Keeping the whole-owner loan active would
                            // make an access to a disjoint field appear to
                            // overlap the reborrowed field.
                            if matches!(context.loans.active.get(owner), Some(LoanKind::Mutable)) {
                                context.loans.active.remove(owner);
                            }
                            context.loans.active.insert(loan.clone(), kind);
                        } else {
                            context.loans.borrow(loan, kind)?;
                        }
                        if operator == "borrow-mut" {
                            context.scoped_mutable_owners.insert(owner.clone());
                        }
                    }
                    if let Some(parent) = &parent {
                        if reborrow_mutable_parent {
                            context.suspended_references.insert(parent.clone());
                        }
                    }
                    let result = check_expression(&items[2], context);
                    for (owner, loan) in &loans {
                        if operator == "borrow-mut" {
                            context.scoped_mutable_owners.remove(owner);
                        }
                        if reborrow_mutable_parent {
                            context.loans.end(loan);
                            if !has_child_loan(&context.loans, owner) {
                                context
                                    .loans
                                    .active
                                    .insert(owner.clone(), LoanKind::Mutable);
                            }
                        } else {
                            context.loans.end(loan);
                        }
                    }
                    if let Some(parent) = &parent {
                        context.suspended_references.remove(parent);
                    }
                    result?
                } else if context.function_names.contains(operator) {
                    let previous = context.allow_local_reference;
                    context.allow_local_reference = true;
                    let checked = items[1..]
                        .iter()
                        .try_for_each(|item| check_expression(item, context));
                    context.allow_local_reference = previous;
                    checked?;
                } else if matches!(operator.as_str(), "get" | "index" | "get-payload") {
                    if let Some((base, path)) = projection_path(expression) {
                        let through_mutable_reference = matches!(base, Expr::Symbol(name)
                            if context.reference_bindings.contains(name));
                        let place = path.join(&PLACE_SEPARATOR.to_string());
                        if through_mutable_reference {
                            for source in reference_origins(base, context, true) {
                                context.read_place(&source, Some(&place), true)?;
                            }
                        } else if let Expr::Symbol(owner) = base {
                            context.read_place(owner, Some(&place), false)?;
                        } else {
                            check_expression(&items[1], context)?;
                        }
                    } else {
                        for item in &items[1..] {
                            check_expression(item, context)?;
                        }
                    }
                } else {
                    let arguments = if operator == "get" && items.len() >= 3 {
                        &items[1..items.len() - 1]
                    } else {
                        &items[1..]
                    };
                    for item in arguments {
                        check_expression(item, context)?;
                    }
                }
            } else {
                for item in items {
                    check_expression(item, context)?;
                }
            }
        }
        Expr::Block(statements) | Expr::Loop(statements) => {
            // Locals and loans created by a block cannot escape its lexical
            // scope. The enclosing let separately records the provenance of a
            // reference-valued block result, so the temporary context can be
            // discarded after checking the block.
            let mut scoped = context.clone();
            check_statements(statements, &mut scoped)?;
        }
        Expr::Labeled { expression, .. } => check_expression(expression, context)?,
        Expr::Quote(value) => check_expression(value, context)?,
        Expr::QuasiQuote(value) | Expr::Unquote(value) | Expr::UnquoteSplicing(value) => {
            check_expression(value, context)?
        }
        Expr::Symbol(name) => {
            if context.suspended_references.contains(name) {
                return Err(format!(
                    "cannot use reference '{name}' while a derived field reference is active"
                ));
            }
            if matches!(context.loans.active.get(name), Some(LoanKind::Mutable))
                && !context.scoped_mutable_owners.contains(name)
                && !context.reference_bindings.contains(name)
            {
                return Err(format!(
                    "cannot access '{name}' while it is mutably borrowed"
                ));
            }
            if context.thread_exclusive_owners.contains_key(name) {
                return Err(format!(
                    "cannot access '{name}' while it is mutably borrowed by a running thread"
                ));
            }
        }
        Expr::Integer(_)
        | Expr::UnsignedInteger(_)
        | Expr::Float(_)
        | Expr::Char(_)
        | Expr::String(_)
        | Expr::At => {}
    }
    Ok(())
}

/// Join the dynamic borrow state after control-flow branches. A loan that is
/// active on any branch must be considered active after the join; otherwise a
/// later write could be accepted even though one runtime path still holds the
/// borrow. Shared-loan counts use the maximum branch count because branches
/// are mutually exclusive.
fn merge_branch_context(context: &mut Context, branches: &[Context]) {
    let base = context.clone();
    let mut merged = base.clone();
    for branch in branches {
        for (owner, kind) in &branch.loans.active {
            let next = match (merged.loans.active.get(owner).copied(), *kind) {
                (Some(LoanKind::Mutable), _) | (_, LoanKind::Mutable) => LoanKind::Mutable,
                (Some(LoanKind::Shared(existing)), LoanKind::Shared(count)) => {
                    LoanKind::Shared(existing.max(count))
                }
                (None, LoanKind::Shared(count)) => LoanKind::Shared(count),
            };
            merged.loans.active.insert(owner.clone(), next);
        }
        for (name, origins) in &branch.reference_origins {
            if base.reference_origins.contains_key(name) {
                merged
                    .reference_origins
                    .entry(name.clone())
                    .or_default()
                    .extend(origins.iter().cloned());
            }
        }
        for (name, loans) in &branch.reference_loans {
            if base.reference_loans.contains_key(name) {
                merged
                    .reference_loans
                    .entry(name.clone())
                    .or_insert_with(|| loans.clone());
            }
        }
        for (name, fields) in &branch.reference_fields {
            if base.reference_fields.contains_key(name) {
                merged
                    .reference_fields
                    .entry(name.clone())
                    .or_insert_with(|| fields.clone());
            }
        }
        for (name, parent) in &branch.reference_parents {
            if base.reference_parents.contains_key(name) {
                merged
                    .reference_parents
                    .entry(name.clone())
                    .or_insert_with(|| parent.clone());
            }
        }
        for (name, loans) in &branch.thread_task_loans {
            merged
                .thread_task_loans
                .entry(name.clone())
                .or_insert_with(|| loans.clone());
        }
        for (owner, count) in &branch.thread_exclusive_owners {
            let entry = merged
                .thread_exclusive_owners
                .entry(owner.clone())
                .or_default();
            *entry = (*entry).max(*count);
        }
    }
    *context = merged;
}

fn release_dropped_value(expression: &Expr, context: &mut Context) {
    let Expr::Symbol(name) = expression else {
        return;
    };
    let name = name.clone();
    if let Some(parent) = context.reference_parents.remove(&name) {
        context.suspended_references.remove(&parent);
    }
    let origins = context.reference_origins.remove(&name).unwrap_or_default();
    context.reference_fields.remove(&name);
    if let Some(loans) = context.reference_loans.remove(&name) {
        for (owner, loan) in loans {
            context.loans.end(&loan);
            if loan != owner
                && !context.loans.active.keys().any(|active| {
                    active != &owner && active.starts_with(&format!("{owner}{PLACE_SEPARATOR}"))
                })
            {
                context.loans.active.insert(owner, LoanKind::Mutable);
            }
        }
    } else {
        for owner in origins {
            context.loans.end(&owner);
        }
    }
    if let Some(loans) = context.thread_task_loans.remove(&name) {
        for (owner, kind) in loans {
            context.loans.end(&owner);
            if kind == LoanKind::Mutable {
                let remove_owner =
                    if let Some(count) = context.thread_exclusive_owners.get_mut(&owner) {
                        *count -= 1;
                        *count == 0
                    } else {
                        false
                    };
                if remove_owner {
                    context.thread_exclusive_owners.remove(&owner);
                }
            }
        }
    }
    context.mutable_references.remove(&name);
    context.reference_bindings.remove(&name);
}

enum ThreadMatchOperation {
    Spawn {
        source: Option<String>,
        loans: Vec<(String, LoanKind)>,
    },
    Join {
        handle: String,
    },
}

fn thread_match_operation(expression: &Expr, context: &Context) -> Option<ThreadMatchOperation> {
    if let Expr::Symbol(source) = expression {
        if let Some(loans) = context.thread_task_loans.get(source) {
            return Some(ThreadMatchOperation::Spawn {
                source: Some(source.clone()),
                loans: loans.clone(),
            });
        }
    }
    let Expr::List(items) = expression else {
        return None;
    };
    let Expr::Symbol(function) = items.first()? else {
        return None;
    };
    if context.thread_join_functions.contains(function) {
        if let Some(Expr::Symbol(handle)) = items.get(1) {
            return Some(ThreadMatchOperation::Join {
                handle: handle.clone(),
            });
        }
    }
    context
        .thread_spawn_functions
        .get(function)
        .map(|_| ThreadMatchOperation::Spawn {
            source: None,
            loans: thread_spawn_origins(expression, context).unwrap_or_default(),
        })
}

fn apply_thread_match_arm(
    operation: &ThreadMatchOperation,
    pattern: &Expr,
    guarded: bool,
    context: &mut Context,
) -> Result<(), String> {
    if guarded {
        return Err("thread result matches cannot use guarded arms".into());
    }
    let Expr::List(parts) = pattern else {
        return Ok(());
    };
    let Some(Expr::Symbol(variant)) = parts.first() else {
        return Ok(());
    };
    match operation {
        ThreadMatchOperation::Spawn { source, loans } if variant.ends_with("-spawn-ok") => {
            let destination = parts.get(1).and_then(pattern_binding).ok_or_else(|| {
                "thread spawn success pattern must bind its task handle".to_owned()
            })?;
            if let Some(source) = source {
                move_thread_task_loans(source, &destination, context);
            } else {
                start_thread_task_loans(&destination, loans, context)?;
            }
        }
        ThreadMatchOperation::Spawn { source, .. } if variant.ends_with("-spawn-error") => {
            if let Some(source) = source {
                release_thread_task_loans(source, context);
            }
        }
        ThreadMatchOperation::Join { handle } if variant.ends_with("-join-ok") => {
            release_thread_task_loans(handle, context);
        }
        ThreadMatchOperation::Join { handle } if variant.ends_with("-join-error") => {
            let destination = parts.get(1).and_then(pattern_binding).ok_or_else(|| {
                "thread join error pattern must bind the returned task handle".to_owned()
            })?;
            move_thread_task_loans(handle, &destination, context);
        }
        _ => {}
    }
    Ok(())
}

fn pattern_binding(pattern: &Expr) -> Option<String> {
    match pattern {
        Expr::Symbol(name) if name != "_" && name != "tuple" => Some(name.clone()),
        Expr::List(items) => items.iter().find_map(pattern_binding),
        _ => None,
    }
}

fn start_thread_task_loans(
    destination: &str,
    loans: &[(String, LoanKind)],
    context: &mut Context,
) -> Result<(), String> {
    for (owner, kind) in loans {
        context.loans.borrow(owner, *kind)?;
        if *kind == LoanKind::Mutable {
            *context
                .thread_exclusive_owners
                .entry(owner.clone())
                .or_default() += 1;
        }
    }
    context.reference_origins.insert(
        destination.to_owned(),
        loans.iter().map(|(owner, _)| owner.clone()).collect(),
    );
    context
        .thread_task_loans
        .insert(destination.to_owned(), loans.to_vec());
    Ok(())
}

fn move_thread_task_loans(source: &str, destination: &str, context: &mut Context) {
    if let Some(loans) = context.thread_task_loans.remove(source) {
        context.reference_origins.remove(source);
        context.reference_origins.insert(
            destination.to_owned(),
            loans.iter().map(|(owner, _)| owner.clone()).collect(),
        );
        context
            .thread_task_loans
            .insert(destination.to_owned(), loans);
    }
}

fn release_thread_task_loans(source: &str, context: &mut Context) {
    if let Some(loans) = context.thread_task_loans.remove(source) {
        context.reference_origins.remove(source);
        for (owner, _) in &loans {
            context.loans.end(owner);
        }
        for (owner, kind) in loans {
            if kind == LoanKind::Mutable {
                let remove_owner =
                    if let Some(count) = context.thread_exclusive_owners.get_mut(&owner) {
                        *count -= 1;
                        *count == 0
                    } else {
                        false
                    };
                if remove_owner {
                    context.thread_exclusive_owners.remove(&owner);
                }
            }
        }
    }
}

fn thread_spawn_origins(expression: &Expr, context: &Context) -> Option<Vec<(String, LoanKind)>> {
    let Expr::List(items) = expression else {
        return None;
    };
    let Expr::Symbol(function) = items.first()? else {
        return None;
    };
    let parameters = context.thread_spawn_functions.get(function)?;
    let mut loans = Vec::new();
    for (argument, parameter) in items[1..].iter().zip(parameters) {
        if !contains_reference_type(parameter, &context.reference_types) {
            continue;
        }
        let kind = if contains_mutable_reference(
            parameter,
            &context.reference_types,
            &context.mutable_reference_types,
        ) {
            LoanKind::Mutable
        } else {
            LoanKind::Shared(1)
        };
        loans.extend(
            reference_origins(argument, context, true)
                .into_iter()
                .map(|owner| (owner, kind)),
        );
    }
    Some(loans)
}

fn contains_mutable_reference(
    ty: &crate::Type,
    reference_types: &HashSet<String>,
    mutable_reference_types: &HashSet<String>,
) -> bool {
    match ty {
        crate::Type::Reference { mutable, .. } => *mutable,
        crate::Type::Array(element, _) | crate::Type::Cell(element) => {
            contains_mutable_reference(element, reference_types, mutable_reference_types)
        }
        crate::Type::Tuple(fields) => fields.iter().any(|field| {
            contains_mutable_reference(field, reference_types, mutable_reference_types)
        }),
        crate::Type::Named(name) => {
            reference_types.contains(name) && mutable_reference_types.contains(name)
        }
        _ => false,
    }
}

fn static_index_segment(expression: &Expr) -> Option<String> {
    match expression {
        Expr::Integer(index) if *index >= 0 => Some(index.to_string()),
        Expr::UnsignedInteger(index) => Some(index.to_string()),
        _ => None,
    }
}

fn check_projection_base(base: &Expr, context: &mut Context) -> Result<(), String> {
    if matches!(base, Expr::Symbol(name) if context.suspended_references.contains(name)) {
        Ok(())
    } else {
        check_expression(base, context)
    }
}

fn projection_path(expression: &Expr) -> Option<(&Expr, Vec<String>)> {
    match expression {
        Expr::Symbol(_) => Some((expression, Vec::new())),
        Expr::List(items)
            if items.len() == 2
                && matches!(items.first(), Some(Expr::Symbol(name)) if matches!(name.as_str(), "borrow" | "borrow-mut")) =>
        {
            projection_path(&items[1])
        }
        Expr::List(items)
            if items.len() == 3
                && matches!(items.first(), Some(Expr::Symbol(name)) if name == "get" || name == "index") =>
        {
            let (base, mut path) = projection_path(&items[1])?;
            let is_index =
                matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "index");
            let segment = if is_index {
                static_index_segment(&items[2]).unwrap_or_else(|| "*".into())
            } else {
                match &items[2] {
                    Expr::Symbol(name) => name.clone(),
                    Expr::Integer(index) => index.to_string(),
                    Expr::UnsignedInteger(index) => index.to_string(),
                    _ => return None,
                }
            };
            path.push(segment);
            Some((base, path))
        }
        Expr::List(items)
            if items.len() == 4
                && matches!(items.first(), Some(Expr::Symbol(name)) if name == "get-payload") =>
        {
            let (base, mut path) = projection_path(&items[1])?;
            let Expr::Symbol(variant) = &items[2] else {
                return None;
            };
            path.push(variant.clone());
            path.push(static_index_segment(&items[3]).unwrap_or_else(|| "*".into()));
            Some((base, path))
        }
        _ => None,
    }
}

fn borrowed_field_parent(expression: &Expr) -> Option<String> {
    let Expr::List(items) = expression else {
        return None;
    };
    if !matches!(items.first(), Some(Expr::Symbol(operator)) if matches!(operator.as_str(), "borrow" | "borrow-mut"))
        || (items.len() != 2 && items.len() != 3)
    {
        return None;
    }
    let (base, path) = projection_path(&items[1])?;
    if path.is_empty() {
        return None;
    }
    let Expr::Symbol(name) = base else {
        return None;
    };
    Some(name.clone())
}

fn borrow_place_origins(place: &Expr, context: &Context) -> HashSet<String> {
    if let Expr::List(items) = place {
        if items.len() == 2 && matches!(items.first(), Some(Expr::Symbol(name)) if name == "unsafe")
        {
            return borrow_place_origins(&items[1], context);
        }
    }
    let Some((base, path)) = projection_path(place) else {
        return HashSet::new();
    };
    if let Expr::Symbol(owner) = base {
        if path.is_empty() {
            HashSet::from([owner.clone()])
        } else if context.reference_origins.contains_key(owner) {
            reference_origins(base, context, true)
        } else {
            HashSet::from([owner.clone()])
        }
    } else {
        HashSet::new()
    }
}

fn borrow_place_loans(place: &Expr, context: &Context) -> Vec<(String, String)> {
    let Some((base, path)) = projection_path(place) else {
        return Vec::new();
    };
    let owners = if let Expr::Symbol(owner) = base {
        if path.is_empty() {
            HashSet::from([owner.clone()])
        } else if context.reference_origins.contains_key(owner) {
            reference_origins(base, context, true)
        } else {
            HashSet::from([owner.clone()])
        }
    } else {
        HashSet::new()
    };
    owners
        .into_iter()
        .map(|owner| {
            let loan = if path.is_empty() {
                owner.clone()
            } else {
                format!(
                    "{owner}{PLACE_SEPARATOR}{}",
                    path.join(&PLACE_SEPARATOR.to_string())
                )
            };
            (owner, loan)
        })
        .collect()
}

fn reference_origins(
    expression: &Expr,
    context: &Context,
    result_contains_references: bool,
) -> HashSet<String> {
    if let Expr::List(items) = expression {
        if items.len() == 2 && matches!(items.first(), Some(Expr::Symbol(name)) if name == "unsafe")
        {
            return reference_origins(&items[1], context, result_contains_references);
        }
    }
    if !result_contains_references {
        return HashSet::new();
    }
    match expression {
        Expr::Symbol(name) => context
            .reference_origins
            .get(name)
            .cloned()
            .unwrap_or_default(),
        Expr::List(items) => {
            let Some(Expr::Symbol(operator)) = items.first() else {
                return HashSet::new();
            };
            if matches!(operator.as_str(), "borrow" | "borrow-mut") && items.len() == 2 {
                return borrow_place_origins(&items[1], context);
            }
            if matches!(operator.as_str(), "slice-of" | "slice-idx" | "slice-range")
                && items.len() >= 2
            {
                return reference_origins(&items[1], context, true);
            }
            if matches!(operator.as_str(), "ptr-borrow" | "ptr-borrow-mut") && items.len() == 3 {
                return reference_origins(&items[1], context, true);
            }
            if operator == "get" && items.len() == 3 {
                return reference_origins(&items[1], context, true);
            }
            if operator == "clone" && items.len() == 2 {
                return reference_origins(&items[1], context, true);
            }
            if operator == "match" && items.len() >= 3 {
                return items[2..]
                    .iter()
                    .filter_map(|arm| match arm {
                        Expr::List(parts) if parts.len() >= 2 => parts.last(),
                        _ => None,
                    })
                    .flat_map(|value| reference_origins(value, context, true))
                    .collect();
            }
            if operator == "as" && items.len() == 3 {
                return reference_origins(&items[1], context, true);
            }
            if operator == "index" && items.len() == 3 {
                return reference_origins(&items[1], context, true);
            }
            if operator == "deref" && items.len() == 2 {
                return reference_origins(&items[1], context, true);
            }
            if operator == "cell-get" && items.len() == 2 {
                return reference_origins(&items[1], context, true);
            }
            if matches!(operator.as_str(), "tuple" | "array" | "array-repeat") {
                return items
                    .iter()
                    .skip(1)
                    .flat_map(|item| reference_origins(item, context, true))
                    .collect();
            }
            if operator == "if" {
                return items
                    .iter()
                    .skip(2)
                    .flat_map(|item| reference_origins(item, context, true))
                    .collect();
            }
            if context.reference_types.contains(operator)
                || context.reference_functions.contains(operator)
            {
                return items
                    .iter()
                    .skip(1)
                    .flat_map(|item| reference_origins(item, context, true))
                    .collect();
            }
            HashSet::new()
        }
        Expr::Block(statements) | Expr::Loop(statements) => statements
            .iter()
            .rev()
            .find_map(|statement| match statement {
                Statement::Expr(value)
                | Statement::Return(Some(value))
                | Statement::BreakValue(value)
                | Statement::BreakToValue { value, .. } => {
                    Some(reference_origins(value, context, true))
                }
                _ => None,
            })
            .unwrap_or_default(),
        Expr::Labeled { expression, .. }
        | Expr::Quote(expression)
        | Expr::QuasiQuote(expression)
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => reference_origins(expression, context, true),
        _ => HashSet::new(),
    }
}

fn type_contains_reference(ty: &crate::Type, items: &[Item], seen: &mut HashSet<String>) -> bool {
    match ty {
        crate::Type::Reference { .. } | crate::Type::Slice(_) => true,
        crate::Type::Array(element, _) | crate::Type::Cell(element) => {
            type_contains_reference(element, items, seen)
        }
        crate::Type::Tuple(fields) => fields
            .iter()
            .any(|field| type_contains_reference(field, items, seen)),
        crate::Type::Named(name) if seen.insert(name.clone()) => {
            let result = items.iter().any(|item| match item {
                Item::Struct {
                    name: struct_name,
                    fields,
                    ..
                } if struct_name == name => fields
                    .iter()
                    .any(|field| type_contains_reference(&field.ty, items, seen)),
                Item::Enum {
                    name: enum_name,
                    variants,
                    ..
                } if enum_name == name => variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|field| type_contains_reference(field, items, seen)),
                _ => false,
            });
            seen.remove(name);
            result
        }
        _ => false,
    }
}

fn type_contains_mutable_reference(
    ty: &crate::Type,
    items: &[Item],
    seen: &mut HashSet<String>,
) -> bool {
    match ty {
        crate::Type::Reference { mutable: true, .. } => true,
        crate::Type::Slice(_) => false,
        crate::Type::Reference { mutable: false, .. } | crate::Type::RawPointer { .. } => false,
        crate::Type::Array(element, _) | crate::Type::Cell(element) => {
            type_contains_mutable_reference(element, items, seen)
        }
        crate::Type::Tuple(fields) => fields
            .iter()
            .any(|field| type_contains_mutable_reference(field, items, seen)),
        crate::Type::Named(name) if seen.insert(name.clone()) => {
            let result = items.iter().any(|item| match item {
                Item::Struct {
                    name: struct_name,
                    fields,
                    ..
                } if struct_name == name => fields
                    .iter()
                    .any(|field| type_contains_mutable_reference(&field.ty, items, seen)),
                Item::Enum {
                    name: enum_name,
                    variants,
                    ..
                } if enum_name == name => variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|field| type_contains_mutable_reference(field, items, seen)),
                _ => false,
            });
            seen.remove(name);
            result
        }
        _ => false,
    }
}

fn contains_reference_type(ty: &crate::Type, reference_types: &HashSet<String>) -> bool {
    match ty {
        crate::Type::Reference { .. } | crate::Type::Slice(_) => true,
        crate::Type::Array(element, _) | crate::Type::Cell(element) => {
            contains_reference_type(element, reference_types)
        }
        crate::Type::Tuple(fields) => fields
            .iter()
            .any(|field| contains_reference_type(field, reference_types)),
        crate::Type::Named(name) => reference_types.contains(name),
        _ => false,
    }
}
