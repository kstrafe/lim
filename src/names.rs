//! Source-level identifier conventions and scalar operation spellings.

pub(crate) const OPERATIONS: &[(&str, &str)] = &[
    ("+", "add"),
    ("-", "sub"),
    ("*", "mul"),
    ("/", "div"),
    ("%", "rem"),
    ("&", "bit-and"),
    ("|", "bit-or"),
    ("^", "bit-xor"),
    ("<<", "shl"),
    (">>", "shr"),
    ("<", "lt"),
    ("<=", "le"),
    (">", "gt"),
    (">=", "ge"),
    ("==", "eq"),
    ("!=", "ne"),
    ("!", "not"),
    ("&&", "and"),
    ("||", "or"),
];

/// Lower the public spelling to the numeric IR's existing operation encoding.
pub(crate) fn numeric_operation(name: &str) -> Option<String> {
    let (scalar, operation) = name.strip_prefix('#')?.split_once("::")?;
    if !crate::is_primitive_type_name(scalar) {
        return None;
    }
    let (operation, mode) = operation
        .strip_suffix("-wrap")
        .map(|op| (op, ".wrap"))
        .or_else(|| {
            operation
                .strip_suffix("-saturate")
                .map(|op| (op, ".saturate"))
        })
        .unwrap_or((operation, ""));
    let (symbol, _) = OPERATIONS.iter().find(|(_, word)| *word == operation)?;
    Some(format!("{scalar}.{symbol}{mode}"))
}

pub(crate) fn numeric_source(internal: &str) -> Option<String> {
    let (scalar, operation) = internal.trim_start_matches('#').split_once('.')?;
    if !crate::is_primitive_type_name(scalar) {
        return None;
    }
    let (operation, mode) = operation
        .split_once('.')
        .map(|(op, mode)| (op, format!("-{mode}")))
        .unwrap_or((operation, String::new()));
    let (_, word) = OPERATIONS.iter().find(|(symbol, _)| *symbol == operation)?;
    Some(format!("#{scalar}::{word}{mode}"))
}

pub(crate) fn type_name(name: &str) -> bool {
    let name = crate::file_access::local_name(name);
    if crate::gensym::reserved(name) {
        return true;
    }
    let name = name.rsplit_once('@').map_or(name, |(_, name)| name);
    !name.contains('.')
        && name.split("::").all(|part| {
            part.chars().next().is_some_and(|c| c.is_ascii_uppercase()) && !part.contains(':')
        })
}

pub(crate) fn value_name(name: &str) -> bool {
    let name = crate::file_access::local_name(name);
    if crate::gensym::reserved(name) {
        return true;
    }
    let name = name.rsplit_once('@').map_or(name, |(_, name)| name);
    let mut parts = name.rsplitn(2, "::");
    let last = parts.next().unwrap_or("");
    !last.contains(['.', ':'])
        && last
            .chars()
            .next()
            .is_some_and(|c| c.is_ascii_lowercase() || c == '_')
        && parts.next().is_none_or(type_name)
}

pub(crate) fn variant_name(name: &str) -> bool {
    name.rsplit_once('.').is_some_and(|(owner, variant)| {
        type_name(owner) && type_name(variant) && !variant.contains("::")
    })
}

pub(crate) fn require(name: &str, kind: &str) -> Result<(), String> {
    let valid = match kind {
        "type" => type_name(name),
        "variant" => variant_name(name),
        _ => value_name(name),
    };
    if valid {
        return Ok(());
    }
    let rule = match kind {
        "type" => "type names must start uppercase in every '::' component and cannot contain '.'",
        "variant" => "enum variants must use Type.Variant with uppercase type and variant names",
        _ => "value names must start lowercase (or '_'); '::' prefixes must be uppercase types and '.' is reserved for enum variants",
    };
    Err(format!(
        "identifier '{name}' violates {kind} naming: {rule}"
    ))
}

pub(crate) fn validate_declaration(expression: &crate::Expr) -> Result<(), String> {
    use crate::Expr;
    let Expr::List(items) = expression else {
        return Ok(());
    };
    let Some(Expr::Symbol(head)) = items.first() else {
        return Ok(());
    };
    if matches!(
        head.as_str(),
        "#let"
            | "#let-mut"
            | "#let-else"
            | "#if-let"
            | "#while-let"
            | "#case"
            | "#case-ref"
            | "#case-ref-mut"
            | "#case-pin"
            | "#case-pin-mut"
    ) {
        if let Some(value) = items.get(1) {
            pattern(value)?;
        }
    }
    if head == "#for-range" {
        if let Some(Expr::List(binding)) = items.get(1) {
            if let Some(Expr::Symbol(name)) = binding.first() {
                require(name, "value")?;
            }
        }
    }
    let kind = match head.as_str() {
        "#struct" | "#enum" | "#type" | "#thread-task" | "#distributed-enum" => "type",
        "#fn" | "#unsafe-fn" | "#extern-fn" | "#let" | "#let-mut" | "#static" | "#const"
        | "#gn-fn" => "value",
        _ => return Ok(()),
    };
    let index = if head == "#extern-fn" { 2 } else { 1 };
    if let Some(Expr::Symbol(name)) = items.get(index) {
        if !name.starts_with('#') {
            require(name, kind)?;
        }
    }
    if matches!(
        head.as_str(),
        "#fn" | "#unsafe-fn" | "#extern-fn" | "#struct"
    ) {
        let index = if matches!(head.as_str(), "#extern-fn" | "#struct") {
            3
        } else {
            2
        };
        if let Some(Expr::List(entries)) = items.get(index) {
            for entry in entries {
                if let Expr::List(parts) = entry {
                    let offset =
                        usize::from(matches!(parts.first(),Some(Expr::Symbol(s)) if s=="#mut"));
                    if let Some(Expr::Symbol(name)) = parts.get(offset) {
                        if !name.starts_with('#') {
                            require(name, "value")?;
                        }
                    }
                }
            }
        }
    }
    if head == "#enum" {
        if let Some(Expr::List(entries)) = items.get(3) {
            for entry in entries {
                let name = match entry {
                    Expr::Symbol(name) => Some(name),
                    Expr::List(parts) => parts.first().and_then(|p| {
                        if let Expr::Symbol(s) = p {
                            Some(s)
                        } else {
                            None
                        }
                    }),
                    _ => None,
                };
                if let Some(name) = name {
                    if !name.starts_with('#') {
                        require(name, "variant")?;
                        if let Some(Expr::Symbol(owner)) = items.get(1) {
                            if name.rsplit_once('.').map(|(prefix, _)| prefix)
                                != Some(owner.as_str())
                            {
                                return Err(format!("identifier '{name}' must name a variant of '{owner}' using {owner}.Variant"));
                            }
                        }
                    }
                }
            }
        }
    }
    Ok(())
}

fn pattern(expression: &crate::Expr) -> Result<(), String> {
    use crate::Expr;
    match expression {
        Expr::Symbol(name) if crate::gensym::reserved(name) => Ok(()),
        Expr::Symbol(name)
            if !name.starts_with('#') && !matches!(name.as_str(), "true" | "false") =>
        {
            if crate::file_access::local_name(name).contains('.') {
                require(name, "variant")
            } else {
                require(name, "value")
            }
        }
        Expr::List(items) => {
            if matches!(items.first(),Some(Expr::Symbol(head)) if matches!(head.as_str(),"#literal"|"#range"|"#range-inclusive"))
            {
                return Ok(());
            }
            for item in items.iter().skip(1) {
                pattern(item)?;
            }
            Ok(())
        }
        _ => Ok(()),
    }
}
