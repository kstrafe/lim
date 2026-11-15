use super::*;

pub(super) fn base_type(ty: &Type, p: &Program) -> Option<Type> {
    let aliases = p
        .items
        .iter()
        .filter_map(|item| match item {
            Item::TypeAlias { name, target, .. } => Some((name.clone(), target.clone())),
            _ => None,
        })
        .collect();
    crate::typed_ir::resolve_type(ty, &aliases).ok()
}
pub(super) fn snapshot_type(ty: &Type, p: &Program) -> bool {
    matches!(
        base_type(ty, p),
        Some(
            Type::Unit
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
                | Type::F64
        )
    )
}

fn constrained(ty: &Type, p: &Program, seen: &mut std::collections::HashSet<String>) -> bool {
    if seen.len() >= 64 {
        return true;
    }
    match ty {
        Type::Named(name) => {
            if p.contracts.refinements.contains_key(name) {
                return true;
            }
            if !seen.insert(name.clone()) {
                return false;
            }
            p.items.iter().any(|item| match item {
                Item::TypeAlias {
                    name: n, target, ..
                } if n == name => constrained(target, p, seen),
                Item::Struct {
                    name: n, fields, ..
                } if n == name => fields.iter().any(|f| constrained(&f.ty, p, seen)),
                Item::Enum {
                    name: n, variants, ..
                } if n == name => variants
                    .iter()
                    .any(|v| v.fields.iter().any(|t| constrained(t, p, seen))),
                _ => false,
            })
        }
        Type::Reference { target, .. }
        | Type::PinnedReference { target, .. }
        | Type::RawPointer { target, .. }
        | Type::PinOwned(target)
        | Type::PinShared(target)
        | Type::Slice(target)
        | Type::MutableSlice(target)
        | Type::Atomic(target)
        | Type::Array(target, _) => constrained(target, p, seen),
        Type::Tuple(fields) => fields.iter().any(|t| constrained(t, p, seen)),
        _ => false,
    }
}

pub(super) fn predicates_for(
    ty: &Type,
    value: &Expr,
    program: &Program,
) -> Result<Vec<Expr>, String> {
    if !constrained(ty, program, &mut std::collections::HashSet::new()) {
        return Ok(Vec::new());
    }
    fn visit(
        ty: &Type,
        value: &Expr,
        p: &Program,
        seen: &mut Vec<String>,
        depth: usize,
    ) -> Result<Vec<Expr>, String> {
        if depth > 64 {
            return Err("contract type nesting exceeds 64".into());
        }
        match ty {
            Type::Named(name) => {
                if seen.contains(name) {
                    if constrained(ty, p, &mut std::collections::HashSet::new()) {
                        return Err("recursive nested constraints require a predicate on the enclosing type".into());
                    }
                    return Ok(Vec::new());
                }
                seen.push(name.clone());
                let mut out = Vec::new();
                if let Some(r) = p.contracts.refinements.get(name) {
                    let binding = HashMap::from([(r.binder.clone(), value.clone())]);
                    out.extend(r.predicates.iter().map(|e| substitute(e, &binding)));
                    out.extend(visit(&r.base, value, p, seen, depth + 1)?);
                } else if let Some(target) = p.items.iter().find_map(|i| match i {
                    Item::TypeAlias {
                        name: n, target, ..
                    } if n == name => Some(target),
                    _ => None,
                }) {
                    out.extend(visit(target, value, p, seen, depth + 1)?);
                } else if let Some(fields) = p.items.iter().find_map(|i| match i {
                    Item::Struct {
                        name: n, fields, ..
                    } if n == name => Some(fields),
                    _ => None,
                }) {
                    for field in fields {
                        out.extend(visit(
                            &field.ty,
                            &form("get", [value.clone(), symbol(&field.name)]),
                            p,
                            seen,
                            depth + 1,
                        )?);
                    }
                } else if p
                    .items
                    .iter()
                    .any(|i| matches!(i,Item::Enum{name:n,..}if n==name))
                    && constrained(ty, p, &mut std::collections::HashSet::new())
                {
                    return Err(
                        "constrained enum payloads require a predicate on the enclosing enum"
                            .into(),
                    );
                }
                seen.pop();
                Ok(out)
            }
            Type::Reference { target, .. } | Type::PinnedReference { target, .. } => {
                visit(target, &form("deref", [value.clone()]), p, seen, depth + 1)
            }
            Type::Tuple(fields) => {
                let mut out = Vec::new();
                for (index, field) in fields.iter().enumerate() {
                    out.extend(visit(
                        field,
                        &form("get", [value.clone(), Expr::Integer(index as i128)]),
                        p,
                        seen,
                        depth + 1,
                    )?);
                }
                Ok(out)
            }
            Type::Array(element, length) => {
                if visit(element, value, p, seen, depth + 1)?.is_empty() {
                    return Ok(Vec::new());
                }
                if *length > 1024 {
                    return Err("constrained array expansion exceeds 1024 elements; use a collection predicate".into());
                }
                let mut out = Vec::new();
                for index in 0..*length {
                    out.extend(visit(
                        element,
                        &form("index", [value.clone(), Expr::Integer(index as i128)]),
                        p,
                        seen,
                        depth + 1,
                    )?);
                }
                Ok(out)
            }
            Type::Slice(element)
            | Type::MutableSlice(element)
            | Type::RawPointer {
                target: element, ..
            }
            | Type::PinOwned(element)
            | Type::PinShared(element)
            | Type::Atomic(element) => {
                if constrained(element, p, &mut std::collections::HashSet::new()) {
                    Err("nested constraints in this container require a predicate on the enclosing type".into())
                } else {
                    Ok(Vec::new())
                }
            }
            _ => Ok(Vec::new()),
        }
    }
    visit(ty, value, program, &mut Vec::new(), 0)
}

fn assertion(predicate: Expr) -> Statement {
    Statement::Expr(form("if", [predicate, unit(), form("panic", [])]))
}
fn replace_special(expr: &Expr, result: &str, old: &HashMap<String, Expr>) -> Expr {
    if head(expr) == "result" {
        return symbol(result);
    }
    if head(expr) == "old" {
        return old
            .get(&format!("{:?}", parts(expr).get(1)))
            .cloned()
            .unwrap_or_else(|| expr.clone());
    }
    match expr {
        Expr::List(xs) => Expr::List(
            xs.iter()
                .map(|x| replace_special(x, result, old))
                .collect::<Vec<_>>()
                .into(),
        ),
        _ => expr.clone(),
    }
}
fn collect_old(expr: &Expr, output: &mut Vec<Expr>) -> Result<(), String> {
    if head(expr) == "old" {
        if parts(expr).len() != 2 {
            return Err("#old requires one entry observation".into());
        }
        if head(&parts(expr)[1]) == "old" {
            return Err("nested #old is not supported".into());
        }
        if !output.contains(&parts(expr)[1]) {
            output.push(parts(expr)[1].clone());
        }
        return Ok(());
    }
    if let Expr::List(xs) = expr {
        for x in xs {
            collect_old(x, output)?;
        }
    }
    Ok(())
}

// A contract observes a mutable argument through a temporary shared reborrow.
// Ordinary user calls still follow Lim's explicit borrowing rules.
fn observation(expr: &Expr, locals: &HashMap<String, Type>, program: &Program) -> Expr {
    let Expr::List(xs) = expr else {
        return expr.clone();
    };
    let mut xs = xs
        .iter()
        .map(|x| observation(x, locals, program))
        .collect::<Vec<_>>();
    if let Some(Expr::Function(name)) = xs.first() {
        if let Some(function) = program.contracts.originals.get(name) {
            for (argument, parameter) in xs.iter_mut().skip(1).zip(&function.parameters) {
                if matches!(
                    base_type(&parameter.ty, program),
                    Some(Type::Reference { mutable: false, .. })
                ) && matches!(
                    observation_type(argument, locals, program)
                        .and_then(|t| base_type(&t, program)),
                    Some(Type::Reference { mutable: true, .. })
                ) {
                    *argument = form("borrow", [form("deref", [argument.clone()])]);
                }
            }
        }
    }
    Expr::List(xs.into())
}

pub(super) fn observation_type(
    expr: &Expr,
    locals: &HashMap<String, Type>,
    program: &Program,
) -> Option<Type> {
    fn resolve(ty: &Type, p: &Program, depth: usize) -> Option<Type> {
        if depth > 64 {
            return None;
        }
        if let Type::Named(name) = ty {
            if let Some(target) = p.items.iter().find_map(|i| match i {
                Item::TypeAlias {
                    name: n, target, ..
                } if n == name => Some(target),
                _ => None,
            }) {
                return resolve(target, p, depth + 1);
            }
        }
        Some(ty.clone())
    }
    match expr {
        Expr::Symbol(s) => locals.get(s).cloned().or_else(|| {
            if matches!(s.as_str(), "true" | "false") {
                Some(Type::Bool)
            } else {
                None
            }
        }),
        Expr::List(xs) => {
            if let Some(Expr::Function(name)) = xs.first() {
                return program.items.iter().find_map(|i| match i {
                    Item::Function(f) if &f.name == name => Some(f.return_type.clone()),
                    _ => None,
                });
            }
            match head(expr) {
                "borrow" | "borrow-mut" => Some(Type::Reference {
                    mutable: head(expr) == "borrow-mut",
                    target: Box::new(observation_type(xs.get(1)?, locals, program)?),
                }),
                "deref" => {
                    match resolve(&observation_type(xs.get(1)?, locals, program)?, program, 0)? {
                        Type::Reference { target, .. } | Type::PinnedReference { target, .. } => {
                            Some(*target)
                        }
                        _ => None,
                    }
                }
                "get" => {
                    let mut ty =
                        resolve(&observation_type(xs.get(1)?, locals, program)?, program, 0)?;
                    if let Type::Reference { target, .. } | Type::PinnedReference { target, .. } =
                        ty
                    {
                        ty = resolve(&target, program, 0)?;
                    }
                    match ty {
                        Type::Named(name) => program.items.iter().find_map(|i| match i {
                            Item::Struct {
                                name: n, fields, ..
                            } if n == &name => fields
                                .iter()
                                .find(|f| matches!(xs.get(2),Some(Expr::Symbol(s))if s==&f.name))
                                .map(|f| f.ty.clone()),
                            _ => None,
                        }),
                        Type::Tuple(fields) => {
                            if let Expr::Integer(i) = xs.get(2)? {
                                fields.get(*i as usize).cloned()
                            } else {
                                None
                            }
                        }
                        _ => None,
                    }
                }
                "old" | "clone" => observation_type(xs.get(1)?, locals, program),
                "as" => crate::parse_type(xs.get(2)).ok(),
                "slice-len" | "slice-mut-len" => Some(Type::Usize),
                _ => {
                    let h = head(expr);
                    let prefix = h.split('.').next()?;
                    if h.contains('.') {
                        if matches!(
                            h.rsplit('.').next()?,
                            "<" | "<=" | ">" | ">=" | "==" | "!=" | "&&" | "||" | "!"
                        ) {
                            Some(Type::Bool)
                        } else {
                            Some(Type::from_name(&format!("#{prefix}")))
                        }
                    } else {
                        None
                    }
                }
            }
        }
        Expr::Integer(_) => Some(Type::I64),
        Expr::UnsignedInteger(_) => Some(Type::U64),
        _ => None,
    }
}

pub(super) fn lower(program: &mut Program) -> Result<(), crate::SourceError> {
    // Validate even unused declarations rather than silently dropping an
    // unsupported constraint inside an uninspected container.
    for item in &program.items {
        match item {
            Item::Struct { fields, .. } => {
                for field in fields {
                    predicates_for(&field.ty, &symbol("value"), program)?;
                }
            }
            Item::Enum { variants, .. } => {
                for variant in variants {
                    for ty in &variant.fields {
                        if constrained(ty, program, &mut std::collections::HashSet::new()) {
                            return Err("constrained enum payloads require a predicate on the enclosing enum".into());
                        }
                    }
                }
            }
            Item::TypeAlias { target, .. } => {
                predicates_for(target, &symbol("value"), program)?;
            }
            Item::Let { ty, .. } | Item::Static { ty, .. } => {
                if !predicates_for(ty, &symbol("value"), program)?.is_empty() {
                    return Err("constrained global storage requires validated construction inside a function".into());
                }
            }
            _ => {}
        }
    }
    // Build implicit contracts only from explicitly constrained signature types.
    // A plain base type does not acquire caller-specific predicate assumptions.
    let originals = program.contracts.originals.clone();
    for (name, f) in &originals {
        if name.starts_with("__lim_contract_")
            || format!("{:?}", f.parameters).contains("\"__lim_contract_")
            || format!("{:?}", f.body).contains("\"__lim_contract_")
        {
            return Err(
                "names beginning __lim_contract_ are reserved for contract instrumentation".into(),
            );
        }
        let mut rebindable = Vec::new();
        super::visit_body(&f.body, &mut |_| {}, &mut |statement| {
            if let Statement::Let {
                ty, mutable: true, ..
            }
            | Statement::Destructure {
                ty, mutable: true, ..
            } = statement
            {
                rebindable.push(ty.clone());
            }
        });
        for ty in rebindable {
            if matches!(
                base_type(&ty, program),
                Some(Type::Reference { .. } | Type::PinnedReference { .. })
            ) && !predicates_for(&ty, &symbol("value"), program)?.is_empty()
            {
                return Err("constrained reference handles must use an immutable binding; mutate their referent through #ref-mut".into());
            }
        }
        let mut additions = Clauses::default();
        for p in &f.parameters {
            let predicates = predicates_for(&p.ty, &symbol(&p.name), program)?;
            if p.mutable
                && !predicates.is_empty()
                && matches!(
                    base_type(&p.ty, program),
                    Some(Type::Reference { .. } | Type::PinnedReference { .. })
                )
            {
                return Err("constrained reference handles must use an immutable binding; mutate their referent through #ref-mut".into());
            }
            additions.requires.extend(predicates.clone());
            if matches!(
                base_type(&p.ty, program),
                Some(
                    Type::Reference { mutable: true, .. }
                        | Type::PinnedReference { mutable: true, .. }
                )
            ) {
                additions.restores.extend(predicates);
            }
        }
        additions.result_constraints.extend(predicates_for(
            &f.return_type,
            &form("result", []),
            program,
        )?);
        let clauses = program.contracts.clauses.get_mut(name).unwrap();
        clauses.requires.extend(additions.requires);
        clauses.restores.extend(additions.restores);
        clauses
            .result_constraints
            .extend(additions.result_constraints);
    }
    super::prerequisites::expand(program)?;
    let instrumented = program.contracts.instrumented;
    for (name, f) in originals {
        let clauses = program.contracts.clauses[&name].clone();
        let mut locals = f
            .parameters
            .iter()
            .map(|p| (p.name.clone(), p.ty.clone()))
            .collect::<HashMap<_, _>>();
        locals.insert("__lim_contract_result".into(), f.return_type.clone());
        let mut entry = Vec::new();
        let mut exits = Vec::new();
        let mut old_names = HashMap::new();
        let lends_mutably = matches!(
            base_type(&f.return_type, program),
            Some(
                Type::Reference { mutable: true, .. }
                    | Type::PinnedReference { mutable: true, .. }
                    | Type::MutableSlice(_)
            )
        );
        if instrumented {
            entry.extend(
                program.contracts.effective_requires[&name]
                    .ordered()
                    .map(|p| assertion(observation(p, &locals, program))),
            );
            let mut old = Vec::new();
            for p in clauses
                .ensures
                .iter()
                .chain(&clauses.restores)
                .chain(&clauses.result_constraints)
            {
                collect_old(p, &mut old)?;
            }
            for (index, expr) in old.into_iter().enumerate() {
                let ty = observation_type(&expr, &locals, program).ok_or(
                    "cannot determine #old observation type; use a typed scalar observation",
                )?;
                if !snapshot_type(&ty, program) {
                    return Err("#old requires a scalar entry observation; reference handles and aggregates are not snapshots".into());
                }
                let name = format!("__lim_contract_old_{index}");
                old_names.insert(format!("{:?}", Some(&expr)), symbol(&name));
                entry.push(Statement::Let {
                    name,
                    ty,
                    value: observation(&expr, &locals, program),
                    mutable: false,
                });
            }
            for (index, predicate) in clauses.preserves.iter().enumerate() {
                let name = format!("__lim_contract_preserves_{index}");
                entry.push(Statement::Let {
                    name: name.clone(),
                    ty: Type::Bool,
                    value: observation(predicate, &locals, program),
                    mutable: false,
                });
                exits.push(Statement::Expr(form(
                    "if",
                    [
                        symbol(&name),
                        Expr::Block(vec![assertion(observation(predicate, &locals, program))]),
                        unit(),
                    ],
                )));
            }
            exits.extend(
                clauses
                    .ensures
                    .iter()
                    .chain(clauses.restores.iter().filter(|_| !lends_mutably))
                    .chain(&clauses.result_constraints)
                    .map(|p| {
                        assertion(observation(
                            &replace_special(p, "__lim_contract_result", &old_names),
                            &locals,
                            program,
                        ))
                    }),
            );
        }
        let mut body = entry;
        for statement in &f.body {
            body.push(lower_statement(
                statement,
                &f.return_type,
                &exits,
                instrumented,
            )?);
        }
        if let Some(Item::Function(target)) = program
            .items
            .iter_mut()
            .find(|item| matches!(item,Item::Function(g)if g.name==name))
        {
            target.body = body;
        }
    }
    Ok(())
}
fn lower_statement(
    s: &Statement,
    ret: &Type,
    exits: &[Statement],
    instrumented: bool,
) -> Result<Statement, String> {
    let expr = |e: &Expr| lower_expression(e, ret, exits, instrumented);
    Ok(match s {
        Statement::Expr(e)
            if matches!(head(e), "requires" | "ensures" | "preserves" | "assume") =>
        {
            Statement::Expr(unit())
        }
        Statement::Return(e) if instrumented && !exits.is_empty() => {
            let mut body = vec![Statement::Let {
                name: "__lim_contract_result".into(),
                ty: ret.clone(),
                value: expr(e.as_ref().unwrap_or(&unit()))?,
                mutable: false,
            }];
            body.extend(exits.iter().cloned());
            body.push(Statement::Return(Some(symbol("__lim_contract_result"))));
            // A final explicit return is required by the original parser only;
            // ordinary checking recognizes the divergent block.
            Statement::Return(Some(Expr::Block(body)))
        }
        Statement::Return(e) => Statement::Return(e.as_ref().map(expr).transpose()?),
        Statement::Let {
            name,
            ty,
            value,
            mutable,
        } => Statement::Let {
            name: name.clone(),
            ty: ty.clone(),
            value: expr(value)?,
            mutable: *mutable,
        },
        Statement::Assign { name, value } => Statement::Assign {
            name: name.clone(),
            value: expr(value)?,
        },
        Statement::ArrayAssign { name, index, value } => Statement::ArrayAssign {
            name: name.clone(),
            index: expr(index)?,
            value: expr(value)?,
        },
        Statement::FieldAssign { name, field, value } => Statement::FieldAssign {
            name: name.clone(),
            field: field.clone(),
            value: expr(value)?,
        },
        Statement::TupleAssign { name, index, value } => Statement::TupleAssign {
            name: name.clone(),
            index: *index,
            value: expr(value)?,
        },
        Statement::EnumPayloadAssign {
            name,
            variant,
            index,
            value,
        } => Statement::EnumPayloadAssign {
            name: name.clone(),
            variant: variant.clone(),
            index: *index,
            value: expr(value)?,
        },
        Statement::While { condition, body } => Statement::While {
            condition: expr(condition)?,
            body: body
                .iter()
                .map(|s| lower_statement(s, ret, exits, instrumented))
                .collect::<Result<_, _>>()?,
        },
        Statement::Loop { body } => Statement::Loop {
            body: body
                .iter()
                .map(|s| lower_statement(s, ret, exits, instrumented))
                .collect::<Result<_, _>>()?,
        },
        Statement::Labeled { label, statement } => Statement::Labeled {
            label: label.clone(),
            statement: Box::new(lower_statement(statement, ret, exits, instrumented)?),
        },
        Statement::Expr(e) => Statement::Expr(expr(e)?),
        Statement::Destructure {
            pattern,
            ty,
            value,
            mutable,
        } => Statement::Destructure {
            pattern: pattern.clone(),
            ty: ty.clone(),
            value: expr(value)?,
            mutable: *mutable,
        },
        Statement::LetElse {
            pattern,
            ty,
            value,
            failure_pattern,
            else_body,
        } => Statement::LetElse {
            pattern: pattern.clone(),
            ty: ty.clone(),
            value: expr(value)?,
            failure_pattern: failure_pattern.clone(),
            else_body: else_body
                .iter()
                .map(|s| lower_statement(s, ret, exits, instrumented))
                .collect::<Result<_, _>>()?,
        },
        Statement::For {
            init,
            condition,
            step,
            body,
        } => Statement::For {
            init: Box::new(lower_statement(init, ret, exits, instrumented)?),
            condition: expr(condition)?,
            step: Box::new(lower_statement(step, ret, exits, instrumented)?),
            body: body
                .iter()
                .map(|s| lower_statement(s, ret, exits, instrumented))
                .collect::<Result<_, _>>()?,
        },
        _ => s.clone(),
    })
}
pub(super) fn planning_statement(s: &Statement, ret: &Type) -> Result<Statement, String> {
    // Planning has no evidence context. Use checked projections there; the
    // completed frontend checks the original proven accesses before emission.
    lower_statement(s, ret, &[], true)
}
fn lower_expression(
    e: &Expr,
    ret: &Type,
    exits: &[Statement],
    instrumented: bool,
) -> Result<Expr, String> {
    if head(e) == "assume" {
        return Ok(unit());
    }
    Ok(match e {
        Expr::Block(body) => Expr::Block(
            body.iter()
                .map(|s| lower_statement(s, ret, exits, instrumented))
                .collect::<Result<_, _>>()?,
        ),
        Expr::Loop(body) => Expr::Loop(
            body.iter()
                .map(|s| lower_statement(s, ret, exits, instrumented))
                .collect::<Result<_, _>>()?,
        ),
        Expr::Labeled { label, expression } => Expr::Labeled {
            label: label.clone(),
            expression: Box::new(lower_expression(expression, ret, exits, instrumented)?),
        },
        Expr::List(xs) => {
            let order = xs.argument_order().map(<[usize]>::to_vec);
            let mut xs = xs
                .iter()
                .map(|x| lower_expression(x, ret, exits, instrumented))
                .collect::<Result<Vec<_>, _>>()?;
            if matches!(xs.first(),Some(Expr::Symbol(h))if h=="if-valid") {
                if !matches!(xs.len(), 3 | 4) {
                    return Err("#if-valid requires a predicate, successful branch and optional failure branch".into());
                }
                xs[0] = symbol("if");
            }
            if instrumented && matches!(xs.first(),Some(Expr::Symbol(h))if h=="index-proven") {
                xs[0] = symbol("index");
            }
            let list = crate::ExprList::from(xs);
            Expr::List(if let Some(order) = order {
                list.with_argument_order(order)
            } else {
                list
            })
        }
        _ => e.clone(),
    })
}
