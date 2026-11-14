//! Predicate evidence checked by local dataflow. No symbolic execution or solver.
mod flow;
mod lowering;
mod summaries;

use crate::{Expr, Function, Item, Program, SourceExpression, Statement, Type};
use std::collections::{BTreeMap, HashMap};

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Clauses {
    pub requires: Vec<Expr>,
    pub ensures: Vec<Expr>,
    pub preserves: Vec<Expr>,
    pub restores: Vec<Expr>,
    pub result_constraints: Vec<Expr>,
}
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct Refinement {
    pub binder: String,
    pub base: Type,
    pub predicates: Vec<Expr>,
}
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct Metadata {
    pub originals: BTreeMap<String, Function>,
    pub clauses: BTreeMap<String, Clauses>,
    pub refinements: BTreeMap<String, Refinement>,
    pub instrumented: bool,
    pub lowered_items: Vec<Item>,
    pub planning_originals: BTreeMap<String, Function>,
}

pub(super) fn form(head: &str, args: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::List(
        std::iter::once(Expr::Symbol(head.into()))
            .chain(args)
            .collect::<Vec<_>>()
            .into(),
    )
}
pub(super) fn head(expr: &Expr) -> &str {
    match expr {
        Expr::List(xs) => match xs.first() {
            Some(Expr::Symbol(s)) => s,
            _ => "",
        },
        _ => "",
    }
}
pub(super) fn parts(expr: &Expr) -> &[Expr] {
    match expr {
        Expr::List(xs) => xs,
        _ => &[],
    }
}
pub(super) fn unit() -> Expr {
    Expr::List(Vec::new().into())
}
pub(super) fn symbol(name: &str) -> Expr {
    Expr::Symbol(name.into())
}
pub(super) fn substitute(expr: &Expr, bindings: &HashMap<String, Expr>) -> Expr {
    match expr {
        Expr::Symbol(name) => bindings.get(name).cloned().unwrap_or_else(|| expr.clone()),
        Expr::List(xs) => Expr::List(
            xs.iter()
                .enumerate()
                .map(|(index, x)| {
                    if index == 0
                        || (head(expr) == "get" && index == 2)
                        || (matches!(head(expr), "as" | "literal" | "array" | "tuple")
                            && index == if head(expr) == "as" { 2 } else { 1 })
                    {
                        x.clone()
                    } else {
                        substitute(x, bindings)
                    }
                })
                .collect::<Vec<_>>()
                .into(),
        ),
        _ => expr.clone(),
    }
}
pub(super) fn split_and(expr: &Expr) -> Vec<Expr> {
    if matches!(head(expr), "bool.&&" | "&&") {
        parts(expr)[1..].iter().flat_map(split_and).collect()
    } else {
        vec![expr.clone()]
    }
}
fn contains_form(expr: &Expr, name: &str) -> bool {
    head(expr) == name || matches!(expr, Expr::List(xs) if xs.iter().any(|x|contains_form(x,name)))
}
fn unfrozen_parameter(expr: &Expr, name: &str) -> bool {
    if head(expr) == "old" {
        return false;
    }
    match expr {
        Expr::Symbol(symbol) => symbol == name,
        Expr::List(xs) => xs.iter().enumerate().skip(1).any(|(i, e)| {
            !(head(expr) == "get" && i == 2
                || head(expr) == "as" && i == 2
                || matches!(head(expr), "literal" | "array" | "tuple") && i == 1)
                && unfrozen_parameter(e, name)
        }),
        _ => false,
    }
}
pub(super) fn visit_statement(statement: &Statement, visitor: &mut impl FnMut(&Expr)) {
    walk_statement(statement, visitor, &mut |_| {});
}
pub(super) fn visit_body(
    body: &[Statement],
    expressions: &mut impl FnMut(&Expr),
    statements: &mut impl FnMut(&Statement),
) {
    for statement in body {
        walk_statement(statement, expressions, statements);
    }
}
fn walk_expression(
    expr: &Expr,
    expressions: &mut dyn FnMut(&Expr),
    statements: &mut dyn FnMut(&Statement),
) {
    expressions(expr);
    match expr {
        Expr::List(xs) => {
            for expr in xs {
                walk_expression(expr, expressions, statements);
            }
        }
        Expr::Block(body) | Expr::Loop(body) => {
            for statement in body {
                walk_statement(statement, expressions, statements);
            }
        }
        Expr::Labeled { expression, .. } => walk_expression(expression, expressions, statements),
        _ => {}
    }
}
fn walk_statement(
    statement: &Statement,
    expressions: &mut dyn FnMut(&Expr),
    statements: &mut dyn FnMut(&Statement),
) {
    statements(statement);
    match statement {
        Statement::Let { value, .. }
        | Statement::Assign { value, .. }
        | Statement::FieldAssign { value, .. }
        | Statement::TupleAssign { value, .. }
        | Statement::EnumPayloadAssign { value, .. }
        | Statement::Destructure { value, .. }
        | Statement::Return(Some(value))
        | Statement::Expr(value)
        | Statement::BreakValue(value)
        | Statement::BreakToValue { value, .. } => walk_expression(value, expressions, statements),
        Statement::ArrayAssign { index, value, .. } => {
            walk_expression(index, expressions, statements);
            walk_expression(value, expressions, statements)
        }
        Statement::While { condition, body } => {
            walk_expression(condition, expressions, statements);
            for s in body {
                walk_statement(s, expressions, statements)
            }
        }
        Statement::Loop { body } => {
            for s in body {
                walk_statement(s, expressions, statements)
            }
        }
        Statement::For {
            init,
            condition,
            step,
            body,
        } => {
            walk_statement(init, expressions, statements);
            walk_expression(condition, expressions, statements);
            walk_statement(step, expressions, statements);
            for s in body {
                walk_statement(s, expressions, statements)
            }
        }
        Statement::LetElse {
            value, else_body, ..
        } => {
            walk_expression(value, expressions, statements);
            for s in else_body {
                walk_statement(s, expressions, statements)
            }
        }
        Statement::Labeled { statement, .. } => walk_statement(statement, expressions, statements),
        _ => {}
    }
}

pub(crate) fn parse_refined_type(xs: &[Expr]) -> Result<Type, String> {
    let Expr::List(binding) = xs
        .get(1)
        .ok_or("#where requires (value Type) and predicates")?
    else {
        return Err("#where requires an explicit (value Type) binder".into());
    };
    if binding.len() != 2 || xs.len() < 3 {
        return Err("#where requires (value Type) and at least one predicate".into());
    }
    let name = crate::expect_symbol(binding.first(), "#where binder")?;
    crate::names::require(name, "value")?;
    crate::parse_type(binding.get(1))?;
    // Content-derived internal aliases preserve the existing concrete type and
    // native layout machinery. Collisions are checked when collecting aliases.
    let mut hash = 0xcbf29ce484222325u64;
    for byte in format!("{xs:?}").bytes() {
        hash = (hash ^ u64::from(byte)).wrapping_mul(0x100000001b3);
    }
    Ok(Type::Named(format!("LimRefinement{hash:016x}")))
}
fn collect_refinements(
    expr: &Expr,
    output: &mut BTreeMap<String, Refinement>,
) -> Result<(), String> {
    if head(expr) == "where" {
        let xs = parts(expr);
        let Type::Named(name) = parse_refined_type(xs)? else {
            unreachable!()
        };
        let binding = parts(&xs[1]);
        let refinement = Refinement {
            binder: crate::expect_symbol(binding.first(), "#where binder")?.into(),
            base: crate::parse_type(binding.get(1))?,
            predicates: xs[2..].iter().flat_map(split_and).collect(),
        };
        if output
            .get(&name)
            .is_some_and(|previous| previous != &refinement)
        {
            return Err("#where identity collision".into());
        }
        output.insert(name, refinement);
    }
    if let Expr::List(xs) = expr {
        for x in xs {
            collect_refinements(x, output)?;
        }
    }
    Ok(())
}
fn source_refinements(
    sources: &HashMap<String, SourceExpression>,
) -> Result<BTreeMap<String, Refinement>, String> {
    let mut output = BTreeMap::new();
    for source in sources.values() {
        collect_refinements(&crate::normalize_keywords(source.expr.clone()), &mut output)?;
    }
    Ok(output)
}
pub(crate) fn refinement_aliases(
    sources: &HashMap<String, SourceExpression>,
) -> Result<Vec<Item>, crate::SourceError> {
    Ok(source_refinements(sources)?
        .into_iter()
        .map(|(name, refinement)| Item::TypeAlias {
            name,
            type_parameters: Vec::new(),
            target: refinement.base,
        })
        .collect())
}

pub(super) fn normalized(expr: &Expr, program: &Program) -> Result<Expr, String> {
    let mut value = expr.clone();
    let signatures = program
        .items
        .iter()
        .filter_map(|item| match item {
            Item::Function(f) => Some((f.name.clone(), crate::CallSignature::of(f))),
            _ => None,
        })
        .collect();
    crate::normalize_call_expr(&mut value, &signatures)?;
    Ok(value)
}

pub(crate) fn prepare(program: &mut Program, instrumented: bool) -> Result<(), crate::SourceError> {
    for item in &program.items {
        if let Item::Let { value, .. } | Item::Static { value, .. } = item {
            let mut proven_index = false;
            walk_expression(
                value,
                &mut |expression| proven_index |= head(expression) == "index-proven",
                &mut |_| {},
            );
            if proven_index {
                return Err("#index-proven requires function-local bounds evidence".into());
            }
        }
    }
    let mut metadata = Metadata {
        instrumented,
        refinements: source_refinements(&program.declaration_expressions)?,
        ..Metadata::default()
    };
    if metadata.refinements.is_empty()
        && !program.items.iter().any(|item| {
            let Item::Function(function) = item else {
                return false;
            };
            let mut found = false;
            for statement in &function.body {
                visit_statement(statement, &mut |e| {
                    found |= matches!(
                        head(e),
                        "requires"
                            | "ensures"
                            | "preserves"
                            | "if-valid"
                            | "assume"
                            | "index-proven"
                    )
                });
            }
            found
        })
    {
        return Ok(());
    }
    for refinement in metadata.refinements.values_mut() {
        for predicate in &mut refinement.predicates {
            *predicate = normalized(predicate, program)?;
        }
    }
    for item in &program.items {
        let Item::Function(function) = item else {
            continue;
        };
        // Runtime calls and aggregate constructors were normalized by the
        // completed frontend; only source predicates on types need the extra
        // normalization above.
        let original = function.clone();
        let mut clauses = Clauses::default();
        let mut body_started = false;
        for statement in &original.body {
            let Statement::Expr(expr) = statement else {
                body_started = true;
                continue;
            };
            let target = match head(expr) {
                "requires" => &mut clauses.requires,
                "ensures" => &mut clauses.ensures,
                "preserves" => &mut clauses.preserves,
                _ => {
                    body_started = true;
                    continue;
                }
            };
            if body_started {
                return Err(crate::SourceError::from(format!(
                    "contract clauses must precede the body of '{}'",
                    function.name
                )));
            }
            if parts(expr).len() != 2 {
                return Err(crate::SourceError::from(format!(
                    "#{} requires one predicate expression",
                    head(expr)
                )));
            }
            if head(expr) != "ensures"
                && (contains_form(expr, "old") || contains_form(expr, "result"))
            {
                return Err("#old and #result are only available in #ensures".into());
            }
            target.extend(split_and(&parts(expr)[1]));
        }
        metadata.clauses.insert(function.name.clone(), clauses);
        metadata.originals.insert(function.name.clone(), original);
    }
    for (name, function) in &metadata.originals {
        for parameter in function.parameters.iter().filter(|p| p.mutable) {
            let clauses = &metadata.clauses[name];
            if clauses
                .ensures
                .iter()
                .chain(&clauses.preserves)
                .any(|p| unfrozen_parameter(p, &parameter.name))
            {
                return Err(format!("postconditions cannot expose the final local binding of mutable parameter '{}'; use a scalar #old observation or return the value",parameter.name).into());
            }
        }
    }
    program.contracts = metadata;
    lowering::lower(program)?;
    program.contracts.lowered_items = program.items.clone();
    Ok(())
}

pub(crate) fn erase_planning(program: &mut Program) -> Result<(), crate::SourceError> {
    for item in &mut program.items {
        if let Item::Function(function) = item {
            let mut needed = false;
            for statement in &function.body {
                visit_statement(statement, &mut |e| {
                    needed |= matches!(
                        head(e),
                        "requires"
                            | "ensures"
                            | "preserves"
                            | "if-valid"
                            | "assume"
                            | "index-proven"
                    )
                });
            }
            if !needed {
                continue;
            }
            program
                .contracts
                .planning_originals
                .insert(function.name.clone(), function.clone());
            function.body = function
                .body
                .iter()
                .map(|s| lowering::planning_statement(s, &function.return_type))
                .collect::<Result<_, _>>()?;
        }
    }
    Ok(())
}

pub(crate) fn restore_planning(program: &mut Program) {
    let mut originals = std::mem::take(&mut program.contracts.planning_originals);
    for item in &mut program.items {
        if let Item::Function(function) = item {
            if let Some(original) = originals.remove(&function.name) {
                *function = original;
            }
        }
    }
}

pub(crate) fn check(
    checked: &crate::typecheck::CheckedProgram<'_>,
) -> Result<(), crate::typecheck::AnalysisError> {
    let p = checked.program();
    if p.contracts.originals.is_empty() {
        let mut proven_index = false;
        for item in &p.items {
            if let Item::Function(function) = item {
                for statement in &function.body {
                    visit_statement(statement, &mut |expression| {
                        proven_index |= head(expression) == "index-proven"
                    });
                }
            } else if let Item::Let { value, .. } | Item::Static { value, .. } = item {
                walk_expression(
                    value,
                    &mut |expression| proven_index |= head(expression) == "index-proven",
                    &mut |_| {},
                );
            }
        }
        if proven_index {
            return Err((
                "#index-proven requires checked contract metadata; reparse the program".into(),
                crate::DiagnosticCode::Contract,
                None,
                Vec::new(),
            ));
        }
    }
    if !active(p) {
        return Ok(());
    }
    if !p.contracts.lowered_items.is_empty() && p.items != p.contracts.lowered_items {
        return Err(("contract metadata does not match the program; reparse after modifying declarations or function bodies".into(), crate::DiagnosticCode::Contract, None, Vec::new()));
    }
    flow::check(checked)
}

fn active(p: &Program) -> bool {
    !p.contracts.refinements.is_empty()
        || p.contracts
            .clauses
            .values()
            .any(|c| !c.requires.is_empty() || !c.ensures.is_empty() || !c.preserves.is_empty())
        || p.contracts.originals.values().any(|f| {
            let mut found = false;
            for statement in &f.body {
                visit_statement(statement, &mut |e| {
                    found |= matches!(head(e), "if-valid" | "assume" | "index-proven")
                });
            }
            found
        })
}
