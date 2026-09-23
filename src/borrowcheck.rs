//! Lexical borrow checking for Lim's first borrow model.
//!
//! References are explicit values, while expression-form borrows still provide
//! a scoped way to access an owner: `(#borrow owner body)` or
//! `(#borrow-mut owner body)`. The owner is borrowed for exactly the duration
//! of `body`, and two-expression borrows retain provenance in the surrounding
//! context for the lifetime of their binding.

use std::collections::{HashMap, HashSet};

use crate::{Expr, Function, Item, Program, Statement, TokenKind};

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
                    type_contains_reference(&field.ty, program, &mut HashSet::new())
                }) =>
            {
                Some(name.clone())
            }
            Item::Enum { name, variants, .. }
                if variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|ty| type_contains_reference(ty, program, &mut HashSet::new())) =>
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
                    program,
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
        let Item::ThreadTask { name, worker } = item else {
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
                    &globals,
                    &reference_types,
                    &mutable_reference_types,
                    &reference_functions,
                    &function_names,
                    &thread_spawn_functions,
                    &thread_join_functions,
                    program.source.as_deref(),
                    &program.statement_spans,
                )?;
            }
        }
    }
    Ok(())
}

fn check_function(
    function: &Function,
    globals: &std::collections::HashSet<String>,
    reference_types: &HashSet<String>,
    mutable_reference_types: &HashSet<String>,
    reference_functions: &HashSet<String>,
    function_names: &HashSet<String>,
    thread_spawn_functions: &HashMap<String, Vec<crate::Type>>,
    thread_join_functions: &HashSet<String>,
    source: Option<&str>,
    statement_spans: &HashMap<(String, usize), crate::Span>,
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
                source,
                statement_spans
                    .get(&(function.name.clone(), statement_index))
                    .copied(),
            ));
        }
    }
    Ok(())
}

fn format_borrow_diagnostic(
    error: String,
    function: &Function,
    statement_index: usize,
    source: Option<&str>,
    exact_conflict_span: Option<crate::Span>,
) -> String {
    let owner = error
        .split('\'')
        .nth(1)
        .filter(|name| !name.is_empty())
        .unwrap_or("<unknown>");
    let exact_conflict_span = exact_conflict_span.and_then(|statement_span| {
        source
            .and_then(|source| conflict_operator_span(source, statement_span, owner, &error))
            .or(Some(statement_span))
    });
    let spans = source
        .map(|source| source_spans(source, owner, &function.name, exact_conflict_span))
        .unwrap_or_default();
    let span_text = if let Some(span) = exact_conflict_span {
        format!(
            "original borrow site {}; conflicting access {}:{}; conflicting span {}:{}",
            spans.first().map_or_else(
                || "unavailable".to_owned(),
                |site| format!("{}:{}", site.0, site.1)
            ),
            span.line,
            span.column,
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

fn source_spans(
    source: &str,
    needle: &str,
    function_name: &str,
    conflict: Option<crate::Span>,
) -> Vec<(usize, usize)> {
    let Ok(tokens) = crate::lex(source) else {
        return Vec::new();
    };
    let Some(function_start) = tokens.windows(3).find_map(|window| {
        let [open, keyword, name] = window else {
            return None;
        };
        (open.kind == TokenKind::LParen
            && keyword.kind == TokenKind::Symbol("#fn".into())
            && name.kind == TokenKind::Symbol(function_name.into()))
        .then_some(open.span.start)
    }) else {
        return Vec::new();
    };
    let aliases = borrowed_source_aliases(&tokens, function_start, conflict.map(|span| span.start));
    let full_path = needle.trim_end_matches(".*").split('.').collect::<Vec<_>>();
    let mut sites = Vec::new();
    for index in 0..tokens.len().saturating_sub(2) {
        let (open, operator, argument) = (&tokens[index], &tokens[index + 1], index + 2);
        let TokenKind::Symbol(operator_name) = &operator.kind else {
            continue;
        };
        if open.kind != TokenKind::LParen
            || !matches!(
                operator_name.as_str(),
                "#borrow" | "#borrow-mut" | "borrow" | "borrow-mut"
            )
            || open.span.start < function_start
            || conflict.is_some_and(|conflict| operator.span.start >= conflict.start)
        {
            continue;
        }
        let Some(argument_end) = expression_end(&tokens, argument) else {
            continue;
        };
        let argument_names = tokens[argument..=argument_end]
            .iter()
            .filter_map(|token| match &token.kind {
                TokenKind::Symbol(name) => Some(name.as_str()),
                _ => None,
            })
            .collect::<HashSet<_>>();
        let expanded_names = argument_names
            .iter()
            .flat_map(|name| {
                std::iter::once(*name).chain(
                    aliases
                        .get(*name)
                        .into_iter()
                        .flat_map(|origins| origins.iter().map(String::as_str)),
                )
            })
            .collect::<HashSet<_>>();
        let matches_owner = argument_names.contains(needle)
            || full_path.iter().all(|part| expanded_names.contains(part));
        if matches_owner {
            sites.push((
                operator.span.line,
                operator.span.column,
                operator.span.start,
            ));
        }
    }
    sites
        .into_iter()
        .map(|(line, column, _)| vec![(line, column)])
        .last()
        .unwrap_or_default()
}

fn borrowed_source_aliases(
    tokens: &[crate::Token],
    function_start: usize,
    before: Option<usize>,
) -> HashMap<String, HashSet<String>> {
    let mut aliases = HashMap::new();
    for index in 0..tokens.len().saturating_sub(3) {
        if tokens[index].span.start < function_start
            || before.is_some_and(|before| tokens[index].span.start >= before)
            || tokens[index].kind != TokenKind::LParen
            || tokens[index + 1].kind != TokenKind::Symbol("#let".into())
        {
            continue;
        }
        let TokenKind::Symbol(binding) = &tokens[index + 2].kind else {
            continue;
        };
        let Some(type_end) = expression_end(tokens, index + 3) else {
            continue;
        };
        let value_start = type_end + 1;
        if !matches!(
            tokens.get(value_start).map(|token| &token.kind),
            Some(TokenKind::LParen)
        ) || !matches!(tokens.get(value_start + 1).map(|token| &token.kind), Some(TokenKind::Symbol(operator)) if matches!(operator.as_str(), "#borrow" | "#borrow-mut"))
        {
            continue;
        }
        let Some(value_end) = expression_end(tokens, value_start) else {
            continue;
        };
        let argument_start = value_start + 2;
        let Some(argument_end) = expression_end(tokens, argument_start) else {
            continue;
        };
        let origins = tokens[argument_start..=argument_end]
            .iter()
            .filter_map(|token| match &token.kind {
                TokenKind::Symbol(name) => Some(name.clone()),
                _ => None,
            })
            .collect::<HashSet<_>>();
        if argument_end < value_end && !origins.is_empty() {
            aliases.insert(binding.clone(), origins);
        }
    }
    aliases
}

fn expression_end(tokens: &[crate::Token], start: usize) -> Option<usize> {
    match tokens.get(start)?.kind {
        TokenKind::LParen => {
            let mut depth = 0usize;
            for (index, token) in tokens.iter().enumerate().skip(start) {
                match token.kind {
                    TokenKind::LParen => depth += 1,
                    TokenKind::RParen => {
                        depth = depth.checked_sub(1)?;
                        if depth == 0 {
                            return Some(index);
                        }
                    }
                    _ => {}
                }
            }
            None
        }
        _ => Some(start),
    }
}

fn conflict_operator_span(
    source: &str,
    statement: crate::Span,
    owner: &str,
    error: &str,
) -> Option<crate::Span> {
    let tokens = crate::lex(source).ok()?;
    let is_borrow_conflict = error.starts_with("cannot borrow");
    let owner_names = place_name_candidates(owner);
    let operator_span = tokens
        .windows(3)
        .filter_map(|window| {
            let [open, operator, target] = window else {
                return None;
            };
            let TokenKind::Symbol(operator_name) = &operator.kind else {
                return None;
            };
            let TokenKind::Symbol(target_name) = &target.kind else {
                return None;
            };
            let matching_operator = if is_borrow_conflict {
                matches!(
                    operator_name.as_str(),
                    "#borrow" | "#borrow-mut" | "borrow" | "borrow-mut"
                )
            } else if error.starts_with("cannot mutate") || error.starts_with("cannot write") {
                operator_name.starts_with("#set")
                    || operator_name.starts_with("set")
                    || operator_name == "#deref-set"
            } else {
                false
            };
            (open.kind == TokenKind::LParen
                && matching_operator
                && (owner_names.iter().any(|candidate| target_name == candidate)
                    || operator_name == "#deref-set")
                && operator.span.start >= statement.start
                && operator.span.end <= statement.end)
                .then_some(operator.span)
        })
        .last();
    operator_span.or_else(|| {
        tokens
            .into_iter()
            .filter(|token| {
                token.span.start >= statement.start
                    && token.span.end <= statement.end
                    && matches!(&token.kind, TokenKind::Symbol(symbol) if owner_names.iter().any(|candidate| symbol == candidate))
            })
            .last()
            .map(|token| token.span)
    })
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
            let task_loans = thread_spawn_origins(value, context);
            context.allow_local_reference = true;
            let checked = check_expression(value, context);
            context.allow_local_reference = false;
            checked?;
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
            } else {
                if let Some(parent) = derived_parent.as_ref() {
                    if context.mutable_references.contains(parent) {
                        context.suspended_references.insert(parent.clone());
                    }
                }
                let mut loans = if contains_references {
                    borrow_place_loans(value, context)
                } else {
                    Vec::new()
                };
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
        }
        Statement::Destructure { value, .. } | Statement::LetElse { value, .. } => {
            if !reference_origins(value, context, true).is_empty() {
                return Err("destructuring values that retain references is not supported".into());
            }
            check_expression(value, context)?;
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
                    if context.thread_join_functions.contains(operator) {
                        if let Some(Expr::Symbol(handle)) = items.get(1) {
                            if let Some(loans) = context.thread_task_loans.remove(handle) {
                                context.reference_origins.remove(handle);
                                for (owner, _) in &loans {
                                    context.loans.end(owner);
                                }
                                for (owner, kind) in loans {
                                    if kind == LoanKind::Mutable {
                                        let remove_owner = if let Some(count) =
                                            context.thread_exclusive_owners.get_mut(&owner)
                                        {
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
                    }
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

fn type_contains_reference(
    ty: &crate::Type,
    program: &Program,
    seen: &mut HashSet<String>,
) -> bool {
    match ty {
        crate::Type::Reference { .. } => true,
        crate::Type::Array(element, _) | crate::Type::Cell(element) => {
            type_contains_reference(element, program, seen)
        }
        crate::Type::Tuple(fields) => fields
            .iter()
            .any(|field| type_contains_reference(field, program, seen)),
        crate::Type::Named(name) if seen.insert(name.clone()) => {
            let result = program.items.iter().any(|item| match item {
                Item::Struct {
                    name: struct_name,
                    fields,
                    ..
                } if struct_name == name => fields
                    .iter()
                    .any(|field| type_contains_reference(&field.ty, program, seen)),
                Item::Enum {
                    name: enum_name,
                    variants,
                    ..
                } if enum_name == name => variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|field| type_contains_reference(field, program, seen)),
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
    program: &Program,
    seen: &mut HashSet<String>,
) -> bool {
    match ty {
        crate::Type::Reference { mutable: true, .. } => true,
        crate::Type::Reference { mutable: false, .. } | crate::Type::RawPointer { .. } => false,
        crate::Type::Array(element, _) | crate::Type::Cell(element) => {
            type_contains_mutable_reference(element, program, seen)
        }
        crate::Type::Tuple(fields) => fields
            .iter()
            .any(|field| type_contains_mutable_reference(field, program, seen)),
        crate::Type::Named(name) if seen.insert(name.clone()) => {
            let result = program.items.iter().any(|item| match item {
                Item::Struct {
                    name: struct_name,
                    fields,
                    ..
                } if struct_name == name => fields
                    .iter()
                    .any(|field| type_contains_mutable_reference(&field.ty, program, seen)),
                Item::Enum {
                    name: enum_name,
                    variants,
                    ..
                } if enum_name == name => variants
                    .iter()
                    .flat_map(|variant| &variant.fields)
                    .any(|field| type_contains_mutable_reference(field, program, seen)),
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
        crate::Type::Reference { .. } => true,
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
