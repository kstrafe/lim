//! Validate redundant await contracts before syntactic state-machine lowering
//! Implementation detail of built-in code generation, not runtime semantics.
//! can erase them. Types come only from explicit declarations, not inference.
use std::collections::HashMap;

use crate::generator::async_types::AsyncTypeEnvironment;
use crate::{Expr, Span, SpannedExpr, Type};

pub(crate) struct Error {
    pub message: String,
    pub span: Span,
}

fn head(node: &SpannedExpr) -> &str {
    match node.children.first().map(|node| &node.expr) {
        Some(Expr::Symbol(head)) => head.strip_prefix('#').unwrap_or(head),
        _ => "",
    }
}

fn function(node: &SpannedExpr) -> Option<&SpannedExpr> {
    match head(node) {
        "fn" => Some(node),
        "quote" | "quasiquote" => None,
        _ => node.children.iter().find_map(function),
    }
}

fn explicit_type(expr: &Expr) -> Option<Type> {
    crate::parse_type(Some(&crate::normalize_keywords(expr.clone()))).ok()
}

fn has_explicit_await(node: &SpannedExpr) -> bool {
    match head(node) {
        "quote" | "quasiquote" => false,
        "await" if node.children.len() == 7 => true,
        _ => node.children.iter().any(has_explicit_await),
    }
}

pub(crate) fn check(source: &SpannedExpr, environment: &AsyncTypeEnvironment) -> Option<Error> {
    let function = function(source)?;
    if !has_explicit_await(function) {
        return None;
    }
    let result = explicit_type(&function.children.get(3)?.expr)?;
    let aliases = environment
        .aliases
        .iter()
        .filter_map(|(name, source)| {
            let ty = explicit_type(&crate::parse(source).ok()?.first()?.expr)?;
            Some((name.clone(), ty))
        })
        .collect();
    let checker = Checker {
        environment,
        aliases,
        result,
    };
    let mut scope = HashMap::new();
    for parameter in &function.children.get(2)?.children {
        let items = &parameter.children;
        let offset = usize::from(head(parameter) == "mut");
        if let (Some(name), Some(ty)) = (items.get(offset), items.get(offset + 1)) {
            if let (Expr::Symbol(name), Some(ty)) = (&name.expr, explicit_type(&ty.expr)) {
                scope.insert(name.clone(), ty);
            }
        }
    }
    for statement in function.children.iter().skip(4) {
        if let Some(error) = checker.visit(statement, &mut scope, None) {
            return Some(error);
        }
    }
    None
}

struct Checker<'a> {
    environment: &'a AsyncTypeEnvironment,
    aliases: HashMap<String, Type>,
    result: Type,
}

impl Checker<'_> {
    fn declared_value_type(
        &self,
        node: &SpannedExpr,
        scope: &HashMap<String, Type>,
    ) -> Option<Type> {
        if let Expr::Symbol(name) = &node.expr {
            return scope.get(name).cloned();
        }
        match head(node) {
            "await" if node.children.len() == 7 => explicit_type(&node.children[1].expr),
            "literal" | "struct-literal" | "tuple" | "array-of" => {
                explicit_type(&node.children.get(1)?.expr)
            }
            _ => None,
        }
    }
    fn bind(&self, pattern: &Expr, ty: &Type, scope: &mut HashMap<String, Type>) {
        let mut bindings = Vec::new();
        if crate::generator::async_types::collect_enum_pattern_bindings(
            pattern,
            &crate::type_source(ty),
            self.environment,
            &mut bindings,
        )
        .is_ok()
        {
            for (name, source) in bindings {
                if let Some(ty) = crate::parse(&source)
                    .ok()
                    .and_then(|nodes| explicit_type(&nodes.first()?.expr))
                {
                    scope.insert(name, ty);
                }
            }
        }
    }

    fn visit(
        &self,
        node: &SpannedExpr,
        scope: &mut HashMap<String, Type>,
        expected: Option<(&Type, &str)>,
    ) -> Option<Error> {
        let items = &node.children;
        match head(node) {
            "quote" | "quasiquote" | "literal" => None,
            "await" if matches!(items.len(), 6 | 7) => {
                if items.len() == 7 {
                    if let (Some(actual), Some((expected, label))) =
                        (explicit_type(&items[1].expr), expected)
                    {
                        if let (Ok(actual), Ok(expected)) = (
                            crate::typed_ir::resolve_type(&actual, &self.aliases),
                            crate::typed_ir::resolve_type(expected, &self.aliases),
                        ) {
                            if actual != expected {
                                return Some(Error { message: format!(
                                    "#generate #async-fn #await result type does not match {label} (found {}, expected {})",
                                    crate::type_source(&actual), crate::type_source(&expected)), span: items[0].span });
                            }
                        }
                    }
                }
                let task_index = items.len() - 1;
                let task_type = explicit_type(&items[if items.len() == 7 { 2 } else { 1 }].expr);
                self.visit(
                    &items[task_index],
                    scope,
                    task_type.as_ref().map(|ty| (ty, "child task")),
                )
            }
            "let" | "let-mut" | "let-else" if items.len() >= 4 => {
                let ty = explicit_type(&items[2].expr)?;
                let label = format!(
                    "binding '{}'",
                    crate::expression_source(&items[1].expr).ok()?
                );
                if let Some(error) = self.visit(&items[3], scope, Some((&ty, &label))) {
                    return Some(error);
                }
                if let Some(failure) = items.get(4) {
                    let mut failure_scope = scope.clone();
                    if head(failure) == "else" {
                        if let Some(pattern) = failure.children.get(1) {
                            self.bind(&pattern.expr, &ty, &mut failure_scope);
                        }
                        for statement in failure.children.iter().skip(2) {
                            if let Some(error) = self.visit(statement, &mut failure_scope, None) {
                                return Some(error);
                            }
                        }
                    } else if let Some(error) = self.visit(failure, &mut failure_scope, None) {
                        return Some(error);
                    }
                }
                self.bind(&items[1].expr, &ty, scope);
                None
            }
            "set" if items.len() == 3 => {
                let Expr::Symbol(name) = &items[1].expr else {
                    return None;
                };
                let ty = scope.get(name).cloned();
                let label = format!("binding '{name}'");
                self.visit(&items[2], scope, ty.as_ref().map(|ty| (ty, label.as_str())))
            }
            "return" if items.len() == 2 => {
                self.visit(&items[1], scope, Some((&self.result, "function result")))
            }
            "match" if items.len() >= 3 => {
                if let Some(error) = self.visit(&items[1], scope, None) {
                    return Some(error);
                }
                let ty = self.declared_value_type(&items[1], scope);
                for arm in items.iter().skip(2) {
                    if head(arm) != "case" || arm.children.len() < 3 {
                        continue;
                    }
                    let mut inner = scope.clone();
                    if let Some(ty) = &ty {
                        self.bind(&arm.children[1].expr, ty, &mut inner);
                    }
                    if let Some(guard) = arm.children.get(2).filter(|node| head(node) == "when") {
                        if let Some(value) = guard.children.get(1) {
                            if let Some(error) =
                                self.visit(value, &mut inner, Some((&Type::Bool, "match guard")))
                            {
                                return Some(error);
                            }
                        }
                    }
                    if let Some(error) = self.visit(arm.children.last()?, &mut inner, expected) {
                        return Some(error);
                    }
                }
                None
            }
            "while-let" if items.len() >= 4 => {
                if let Some(error) = self.visit(&items[2], scope, None) {
                    return Some(error);
                }
                let mut inner = scope.clone();
                if let Some(ty) = self.declared_value_type(&items[2], scope) {
                    self.bind(&items[1].expr, &ty, &mut inner);
                }
                items
                    .iter()
                    .skip(3)
                    .find_map(|node| self.visit(node, &mut inner, None))
            }
            "call" | "unsafe-call" if items.len() == 3 => {
                let Expr::Symbol(function) = &items[1].expr else {
                    return None;
                };
                let parameters = self.environment.functions.get(function);
                for argument in &items[2].children {
                    let [name, value] = argument.children.as_slice() else {
                        continue;
                    };
                    let Expr::Symbol(name) = &name.expr else {
                        continue;
                    };
                    let ty = parameters
                        .and_then(|parameters| parameters.get(name))
                        .and_then(|source| crate::parse(source).ok())
                        .and_then(|nodes| explicit_type(&nodes.first()?.expr));
                    let label = format!("argument '{name}'");
                    if let Some(error) =
                        self.visit(value, scope, ty.as_ref().map(|ty| (ty, label.as_str())))
                    {
                        return Some(error);
                    }
                }
                None
            }
            "for" if items.len() >= 5 => {
                let mut inner = scope.clone();
                self.visit(&items[1], &mut inner, None)
                    .or_else(|| {
                        self.visit(&items[2], &mut inner, Some((&Type::Bool, "loop condition")))
                    })
                    .or_else(|| self.visit(&items[3], &mut inner, None))
                    .or_else(|| {
                        items
                            .iter()
                            .skip(4)
                            .find_map(|node| self.visit(node, &mut inner, None))
                    })
            }
            "while" if items.len() >= 3 => self
                .visit(&items[1], scope, Some((&Type::Bool, "loop condition")))
                .or_else(|| {
                    let mut inner = scope.clone();
                    items
                        .iter()
                        .skip(2)
                        .find_map(|node| self.visit(node, &mut inner, None))
                }),
            "block" | "loop" => {
                let mut inner = scope.clone();
                for (index, child) in items.iter().enumerate().skip(1) {
                    let expected = if head(node) == "block" && index + 1 == items.len() {
                        expected
                    } else {
                        None
                    };
                    if let Some(error) = self.visit(child, &mut inner, expected) {
                        return Some(error);
                    }
                }
                None
            }
            "if" if items.len() == 4 => self
                .visit(&items[1], scope, Some((&Type::Bool, "if condition")))
                .or_else(|| self.visit(&items[2], &mut scope.clone(), expected))
                .or_else(|| self.visit(&items[3], &mut scope.clone(), expected)),
            _ => items
                .iter()
                .skip(1)
                .find_map(|child| self.visit(child, scope, None)),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check_source(source: &str) -> Option<Error> {
        let forms = crate::parse_source_unit(source).unwrap();
        let environment = crate::generator::frontend::async_type_environment(&forms);
        check(forms.last().unwrap(), &environment)
    }

    #[test]
    fn parameter_and_nested_pattern_contracts_keep_the_exact_await_span() {
        for source in [
            "#fn work { #params = ((#mut counter #u64)); #returns = #u64; #body = (
                (#set counter (#await #u32 Step Pending Ready poll task)) (#return counter) ); }\n",
            "#struct Bounds () ((z (#tuple #u8 #u16)) (a #u64))
#fn work { #params = ((bounds Bounds)); #returns = #u64; #body = (
                  (#for (#let-mut (Bounds (#tuple index limit) bias) Bounds bounds)
                    true (#set limit (#await #u8 Step Pending Ready poll task)) ())
                  (#return 0u64) ); }\n",
        ] {
            let error = check_source(source).expect("explicit destination mismatch");
            assert_eq!(error.span.start, source.find("#await").unwrap());
            assert_eq!(&source[error.span.start..error.span.end], "#await");
            assert!(error.message.contains("result type does not match binding"));
        }
    }

    #[test]
    fn independent_loop_and_branch_scopes_do_not_replace_outer_types() {
        let source = "#fn work { #params = ((#mut value #u64)); #returns = #u64; #body = (
            (#for (#let-mut index #u8 0u8) false ()
              (#set index (#await #u8 Step Pending Ready poll task)))
            (#for (#let-mut index #u16 0u16) false ()
              (#set index (#await #u16 Step Pending Ready poll task)))
            (#if true (#block (#let branch-only #u8 0u8) branch-only) 0u8)
            (#let-mut branch-only #u32 0u32)
            (#set branch-only (#await #u32 Step Pending Ready poll task))
            (#set value (#await #u64 Step Pending Ready poll task)) (#return value) ); }\n";
        assert!(check_source(source).is_none());
    }

    #[test]
    fn nested_aliases_compare_by_resolved_contracts() {
        let source = "#type Index #u64
#type View (#ref Index)
#fn work { #params = ((view View)); #returns = View; #body = (
              (#return (#await (#ref #u64) Step Pending Ready poll task)) ); }\n";
        assert!(check_source(source).is_none());
    }

    #[test]
    fn quoted_contracts_do_not_hide_a_real_later_mismatch() {
        let source = "#fn work { #params = (); #returns = #u64; #body = (
            (#quote (#fn fake () #u64 (#return (#await #u32 Step Pending Ready poll task))))
            (#let result #u64 (#await #u16 Step Pending Ready poll task)) (#return result) ); }\n";
        let error = check_source(source).expect("the real binding is checked");
        assert_eq!(error.span.start, source.find("#await #u16").unwrap());
        assert!(error.message.contains("binding 'result'"));
    }
}
