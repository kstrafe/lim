//! Nonowning tests of retained, checked async patterns.
//!
//! Only Copy scalar leaves are loaded. Aggregates remain in their tagged
//! cells until Commit; inspecting a variant never extracts its payload.
//! This is not a guard-alias or ownership proof. The caller must validate the
//! original body and the completed ordinary generated program.
#![allow(dead_code)]

use std::collections::HashSet;

use crate::{typed_ir::Declarations, Expr, Type};

fn symbol(name: impl Into<String>) -> Expr {
    Expr::Symbol(name.into())
}

fn form(name: &str, arguments: impl IntoIterator<Item = Expr>) -> Expr {
    Expr::List(std::iter::once(symbol(name)).chain(arguments).collect())
}

fn and(left: Expr, right: Expr) -> Expr {
    if left == symbol("true") {
        right
    } else if right == symbol("true") {
        left
    } else {
        form("#bool.&&", [left, right])
    }
}

struct Inspector<'a> {
    declarations: &'a Declarations,
    prefix: &'a str,
    reserved: &'a mut HashSet<String>,
    next: usize,
}

impl Inspector<'_> {
    fn test(&mut self, pattern: &Expr, ty: &Type, reference: Expr) -> Result<Expr, String> {
        if pattern == &symbol("_") {
            return Ok(symbol("true"));
        }
        if ty == &Type::Unit && pattern == &Expr::List(Vec::new()) {
            return Ok(symbol("true"));
        }
        let name = loop {
            let candidate = format!("{}.{}", self.prefix, self.next);
            self.next += 1;
            if self.reserved.insert(candidate.clone()) {
                break candidate;
            }
        };
        let handle = symbol(&name);
        let test = self.inspect(pattern, ty, &handle)?;
        let reference_type = crate::parse(&format!("(#pin-ref {})", crate::type_source(ty)))
            .map_err(|error| error.to_string())?
            .remove(0)
            .expr;
        Ok(form(
            "#block",
            [
                form("#let", [symbol(name), reference_type, reference]),
                test,
            ],
        ))
    }

    fn inspect(&mut self, pattern: &Expr, ty: &Type, handle: &Expr) -> Result<Expr, String> {
        if let Expr::List(parts) = pattern {
            if parts.first() == Some(&symbol("#or")) && parts.len() >= 2 {
                let mut alternatives = parts[1..].iter();
                let mut result = self.test(alternatives.next().unwrap(), ty, handle.clone())?;
                for alternative in alternatives {
                    result = form(
                        "#bool.||",
                        [result, self.test(alternative, ty, handle.clone())?],
                    );
                }
                return Ok(result);
            }
        }
        if matches!(
            ty,
            Type::Bool
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
        ) {
            return Ok(form(
                "#match",
                [
                    form("#deref", [handle.clone()]),
                    form("#case", [pattern.clone(), symbol("true")]),
                    form("#case", [symbol("_"), symbol("false")]),
                ],
            ));
        }
        if let Type::Named(owner) = ty {
            if let Some(variants) = self.declarations.enums.get(owner) {
                let (name, payload) = match pattern {
                    Expr::Symbol(name) => (name, &[][..]),
                    Expr::List(parts) => match parts.first() {
                        Some(Expr::Symbol(name)) => (name, &parts[1..]),
                        _ => return Err("checked enum pattern lost its constructor".into()),
                    },
                    _ => return Err("checked enum pattern has no constructor".into()),
                };
                let variant = variants
                    .iter()
                    .find(|variant| &variant.name == name)
                    .ok_or("checked enum pattern variant belongs to another owner")?;
                if payload.len() != variant.fields.len() {
                    return Err("checked enum pattern payload arity changed".into());
                }
                let fields = variant.fields.clone();
                let mut result = form("#variant-is", [handle.clone(), symbol(name)]);
                for (index, (nested, field)) in payload.iter().zip(&fields).enumerate() {
                    let projection = form(
                        "#pin-get-payload",
                        [handle.clone(), symbol(name), Expr::Integer(index as i128)],
                    );
                    // The short-circuit tag test must dominate every payload
                    // projection. A nonselected arm never touches that payload.
                    result = and(result, self.test(nested, field, projection)?);
                }
                return Ok(result);
            }
        }
        let Expr::List(parts) = pattern else {
            return Err("checked aggregate pattern has no constructor".into());
        };
        let Some(Expr::Symbol(constructor)) = parts.first() else {
            return Err("checked aggregate pattern lost its constructor".into());
        };
        let fields = match ty {
            Type::Tuple(fields) if constructor == "#tuple" => fields
                .iter()
                .enumerate()
                .map(|(index, ty)| (Expr::Integer(index as i128), ty.clone()))
                .collect::<Vec<_>>(),
            Type::Array(element, length) if constructor == "#array" => (0..*length)
                .map(|index| (symbol(format!("{index}usize")), element.as_ref().clone()))
                .collect(),
            Type::Named(owner) if constructor == owner => self
                .declarations
                .structs
                .get(owner)
                .ok_or("checked aggregate pattern owner has no struct layout")?
                .iter()
                .map(|field| (symbol(&field.name), field.ty.clone()))
                .collect(),
            _ => return Err("unsupported stationary pattern inspection type".into()),
        };
        if parts.len() - 1 != fields.len() {
            return Err("checked aggregate pattern arity changed".into());
        }
        let mut result = symbol("true");
        for (nested, (field, ty)) in parts[1..].iter().zip(&fields) {
            let access = form(
                if constructor == "#array" {
                    "#index"
                } else {
                    "#get"
                },
                [handle.clone(), field.clone()],
            );
            let projection = form("#pin-borrow", [access]);
            result = and(result, self.test(nested, ty, projection)?);
        }
        Ok(result)
    }
}

/// Pattern names have already been resolved and bindings replaced with `_`
/// by RenderContext. `prefix` is reserved by the dispatcher, not user syntax.
pub(crate) fn test(
    declarations: &Declarations,
    pattern: &Expr,
    ty: &Type,
    reference: Expr,
    prefix: &str,
    reserved: &mut HashSet<String>,
) -> Result<Expr, String> {
    Inspector {
        declarations,
        prefix,
        reserved,
        next: 0,
    }
    .test(pattern, ty, reference)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn borrowed_inspection_never_emits_an_owning_read_or_consumption() {
        let source = "(#struct Payload ((value #u64))) (#linear Payload)
          (#enum Choice ((Some Payload) Empty)) (#linear Choice)
          (#fn unused () () (#return ()))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let pattern = crate::parse("(Some (Payload 42u64))")
            .unwrap()
            .remove(0)
            .expr;
        let expression = test(
            checked.declarations(),
            &pattern,
            &Type::Named("Choice".into()),
            symbol("value"),
            "inspect",
            &mut HashSet::from(["inspect.0".into()]),
        )
        .unwrap();
        let text = crate::expression_source(&expression).unwrap();
        for prohibited in ["#unsafe", "#pin-read", "#forget", "#drop", "#clone"] {
            assert!(!text.contains(prohibited), "{text}");
        }
        assert!(text.contains("#variant-is"), "{text}");
        assert!(text.contains("#pin-get-payload"), "{text}");
        assert!(!text.contains("(#let inspect.0 "), "{text}");
        let checked_source = format!(
            "{source}
          (#fn inspect ((value (#pin-ref Choice))) #bool (#return {text}))"
        );
        crate::CheckedProgram::validate(&crate::parse_program(&checked_source).unwrap()).unwrap();
    }
}
