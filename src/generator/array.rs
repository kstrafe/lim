//! Concrete fixed-array APIs, emitted as ordinary functions and contracts.
use crate::*;

fn arguments(items: &[Expr]) -> Result<(Type, usize, String), String> {
    if items.len() != 5 {
        return Err(
            "#generate #array requires (: element Type : length N : name ArrayType)".into(),
        );
    }
    let element = parse_type(items.get(2))?;
    let length = match items.get(3) {
        Some(Expr::Integer(value)) => usize::try_from(*value).ok(),
        Some(Expr::UnsignedInteger(value)) => usize::try_from(*value).ok(),
        _ => None,
    }
    .ok_or("#generate #array length must be a nonnegative integer literal fitting #usize")?;
    let name = expect_symbol(items.get(4), "array type name")?.to_owned();
    crate::names::require(&name, "type")?;
    Ok((element, length, name))
}

pub(crate) fn type_alias(items: &[Expr]) -> Result<Item, String> {
    let (element, length, name) = arguments(items)?;
    Ok(Item::TypeAlias {
        name,
        type_parameters: Vec::new(),
        target: Type::Array(Box::new(element), length),
    })
}

pub(crate) fn source(items: &[Expr], copy_types: &HashSet<String>) -> Result<String, String> {
    let (element, length, name) = arguments(items)?;
    let element_source = type_source(&element);
    let bound = format!("(#call #usize::lt (: left index : right {length}usize))");
    let mut source = format!(
        r#"
(#type {name} (#array {element_source} {length}))
(#fn {name}::in-bounds ((index #usize)) #bool
  (#return {bound}))
(#fn {name}::prove-in-bounds ((index #usize)) ()
  (#requires (#call {name}::in-bounds (: index index)))
  (#ensures {bound})
  (#return ()))
(#fn {name}::borrow ((values (#ref {name})) (index #usize)) (#ref {element_source})
  (#requires {bound})
  (#return (#borrow (#index-proven values index))))
(#fn {name}::borrow-mut ((values (#ref-mut {name})) (index #usize)) (#ref-mut {element_source})
  (#requires {bound})
  (#return (#borrow-mut (#index-proven values index))))
"#
    );
    if builtin_payload_is_copy(&element, copy_types) {
        source.push_str(&format!(
            r#"
(#fn {name}::get ((values (#ref {name})) (index #usize)) {element_source}
  (#requires {bound})
  (#return (#deref (#borrow (#index-proven values index)))))
"#
        ));
    }
    Ok(source)
}
