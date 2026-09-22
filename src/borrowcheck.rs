//! Lexical borrow checking for Lim's first borrow model.
//!
//! Lim does not yet expose references as values.  A borrow is therefore an
//! expression scope: `(#borrow owner body)` or `(#borrow-mut owner body)`.
//! The owner is borrowed for exactly the duration of `body`.  This gives the
//! language useful, inferred borrow checking without inventing a runtime
//! representation before indirection is designed.

use std::collections::{HashMap, HashSet};

use crate::{Expr, Function, Item, Program, Statement};

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
    allow_local_reference: bool,
    reference_types: HashSet<String>,
    reference_functions: HashSet<String>,
    function_names: HashSet<String>,
    thread_spawn_functions: HashMap<String, Vec<crate::Type>>,
    thread_join_functions: HashSet<String>,
    thread_task_loans: HashMap<String, Vec<(String, LoanKind)>>,
    thread_exclusive_owners: HashMap<String, usize>,
    return_contains_references: bool,
}

impl Loans {
    fn borrow(&mut self, owner: &str, kind: LoanKind) -> Result<(), String> {
        match (self.active.get(owner).copied(), kind) {
            (None, _) => {
                self.active.insert(owner.to_owned(), kind);
                Ok(())
            }
            (Some(LoanKind::Shared(count)), LoanKind::Shared(_)) => {
                self.active
                    .insert(owner.to_owned(), LoanKind::Shared(count + 1));
                Ok(())
            }
            (Some(LoanKind::Shared(_)), LoanKind::Mutable) => Err(format!(
                "cannot borrow '{owner}' mutably because it is already borrowed"
            )),
            (Some(LoanKind::Mutable), _) => Err(format!(
                "cannot borrow '{owner}' because it is already borrowed mutably"
            )),
        }
    }

    fn end(&mut self, owner: &str) {
        match self.active.get_mut(owner) {
            Some(LoanKind::Shared(count)) if *count > 1 => *count -= 1,
            Some(_) => {
                self.active.remove(owner);
            }
            None => {}
        }
    }

    fn downgrade_mutable_to_shared(&mut self, owner: &str) -> Result<(), String> {
        match self.active.get(owner) {
            Some(LoanKind::Mutable) => {
                self.active.insert(owner.to_owned(), LoanKind::Shared(1));
                Ok(())
            }
            Some(LoanKind::Shared(_)) => Ok(()),
            None => self.borrow(owner, LoanKind::Shared(1)),
        }
    }

    fn upgrade_shared_to_mutable(&mut self, owner: &str) -> Result<(), String> {
        match self.active.get(owner) {
            Some(LoanKind::Shared(1)) => {
                self.active.insert(owner.to_owned(), LoanKind::Mutable);
                Ok(())
            }
            Some(LoanKind::Mutable) => Ok(()),
            Some(LoanKind::Shared(_)) => Err(format!(
                "cannot reborrow '{owner}' mutably while it has other shared borrows"
            )),
            None => self.borrow(owner, LoanKind::Mutable),
        }
    }
}

impl Context {
    fn write(&self, owner: &str) -> Result<(), String> {
        if self.thread_exclusive_owners.contains_key(owner) {
            return Err(format!(
                "cannot mutate '{owner}' while it is mutably borrowed by a running thread"
            ));
        }
        match self.loans.active.get(owner) {
            Some(LoanKind::Shared(_)) => Err(format!(
                "cannot mutate '{owner}' while it is immutably borrowed"
            )),
            Some(LoanKind::Mutable) if !self.scoped_mutable_owners.contains(owner) => Err(format!(
                "cannot mutate '{owner}' while it is mutably borrowed"
            )),
            Some(LoanKind::Mutable) | None => Ok(()),
        }
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
                    &reference_functions,
                    &function_names,
                    &thread_spawn_functions,
                    &thread_join_functions,
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
    reference_functions: &HashSet<String>,
    function_names: &HashSet<String>,
    thread_spawn_functions: &HashMap<String, Vec<crate::Type>>,
    thread_join_functions: &HashSet<String>,
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
            if contains_mutable_reference(&parameter.ty, reference_types) {
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
        allow_local_reference: false,
        reference_types: reference_types.clone(),
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
            let kind = if contains_mutable_reference(&parameter.ty, reference_types) {
                LoanKind::Mutable
            } else {
                LoanKind::Shared(1)
            };
            context.loans.borrow(&parameter.name, kind)?;
        }
    }
    for statement in &function.body {
        check_statement(statement, &mut context)?;
    }
    Ok(())
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
            let contains_mutable_references =
                contains_mutable_reference(ty, &context.reference_types);
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
                for owner in &origins {
                    if derived_parent
                        .as_ref()
                        .is_some_and(|parent| context.mutable_references.contains(parent))
                    {
                        if contains_mutable_references {
                            if !matches!(context.loans.active.get(owner), Some(LoanKind::Mutable)) {
                                context.loans.borrow(owner, LoanKind::Mutable)?;
                            }
                        } else if matches!(context.loans.active.get(owner), Some(LoanKind::Mutable))
                        {
                            context.loans.downgrade_mutable_to_shared(owner)?;
                        } else {
                            context.loans.borrow(owner, LoanKind::Shared(1))?;
                        }
                    } else {
                        context.loans.borrow(
                            owner,
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
        Statement::Assign { name, value }
        | Statement::FieldAssign { name, value, .. }
        | Statement::TupleAssign { name, value, .. }
        | Statement::EnumPayloadAssign { name, value, .. } => {
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
        Statement::ArrayAssign { name, index, value } => {
            check_expression(index, context)?;
            check_expression(value, context)?;
            context.write(name)?;
        }
        Statement::While { condition, body } => {
            check_expression(condition, context)?;
            check_statements(body, context)?;
        }
        Statement::Loop { body } => check_statements(body, context)?,
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            check_statement(init, context)?;
            check_expression(condition, context)?;
            check_statements(body, context)?;
            check_statement(step, context)?;
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

fn check_expression(expression: &Expr, context: &mut Context) -> Result<(), String> {
    match expression {
        Expr::List(items) => {
            if let Some(Expr::Symbol(operator)) = items.first() {
                if operator == "if" && items.len() == 4 {
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
                            if let Some(base) = borrowed_field_base(&items[1]) {
                                check_expression(base, context)?;
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
                    let kind = if operator == "borrow" {
                        LoanKind::Shared(1)
                    } else {
                        LoanKind::Mutable
                    };
                    let parent = borrowed_field_parent(&items[1]);
                    if let Some(base) = borrowed_field_base(&items[1]) {
                        check_expression(base, context)?;
                    }
                    let reborrow_mutable_parent = parent
                        .as_ref()
                        .is_some_and(|parent| context.mutable_references.contains(parent));
                    for owner in &origins {
                        if reborrow_mutable_parent
                            && matches!(context.loans.active.get(owner), Some(LoanKind::Mutable))
                        {
                            if kind == LoanKind::Shared(1) {
                                context.loans.downgrade_mutable_to_shared(owner)?;
                            }
                        } else {
                            context.loans.borrow(owner, kind)?;
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
                    for owner in &origins {
                        if operator == "borrow-mut" {
                            context.scoped_mutable_owners.remove(owner);
                        }
                        if reborrow_mutable_parent {
                            if kind == LoanKind::Shared(1) {
                                context.loans.upgrade_shared_to_mutable(owner)?;
                            }
                        } else {
                            context.loans.end(owner);
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
        let kind = if contains_mutable_reference(parameter, &context.reference_types) {
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

fn contains_mutable_reference(ty: &crate::Type, reference_types: &HashSet<String>) -> bool {
    match ty {
        crate::Type::Reference { mutable, .. } => *mutable,
        crate::Type::Array(element, _) | crate::Type::Cell(element) => {
            contains_mutable_reference(element, reference_types)
        }
        crate::Type::Tuple(fields) => fields
            .iter()
            .any(|field| contains_mutable_reference(field, reference_types)),
        crate::Type::Named(name) => reference_types.contains(name) && false,
        _ => false,
    }
}

fn borrowed_field_base(place: &Expr) -> Option<&Expr> {
    let Expr::List(items) = place else {
        return None;
    };
    if !matches!(items.first(), Some(Expr::Symbol(operator)) if operator == "get")
        || items.len() != 3
    {
        return None;
    }
    matches!(items.get(1), Some(Expr::Symbol(_))).then(|| &items[1])
}

fn borrowed_field_parent(expression: &Expr) -> Option<String> {
    let Expr::List(items) = expression else {
        return None;
    };
    if !matches!(items.first(), Some(Expr::Symbol(operator)) if matches!(operator.as_str(), "borrow" | "borrow-mut"))
        || items.len() != 2
    {
        return None;
    }
    let base = borrowed_field_base(&items[1])?;
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
    match place {
        Expr::Symbol(owner) => HashSet::from([owner.clone()]),
        Expr::List(items) if borrowed_field_base(place).is_some() => {
            reference_origins(&items[1], context, true)
        }
        _ => HashSet::new(),
    }
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
        Expr::Block(statements) | Expr::Loop(statements) => {
            let Some(Statement::Expr(value) | Statement::Return(Some(value))) = statements.last()
            else {
                return HashSet::new();
            };
            reference_origins(value, context, true)
        }
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
