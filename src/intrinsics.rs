//! Compiler-generated callable declarations for strict scalar primitives.
//! Their implementations remain the existing typed backend operations.
use crate::{Parameter, Type};

pub(crate) struct Declaration {
    pub operator: String,
    pub parameters: Vec<Parameter>,
    pub return_type: Type,
}

pub(crate) fn declaration(name: &str) -> Result<Option<Declaration>, String> {
    let lowered = crate::names::numeric_operation(name);
    let name = lowered.as_deref().unwrap_or(name);
    let Some((scalar, operation)) = name.split_once('.') else {
        return Ok(None);
    };
    if !crate::is_primitive_type_name(scalar) {
        return Ok(None);
    }
    let (operation, mode) = operation
        .split_once('.')
        .map_or((operation, None), |(op, mode)| (op, Some(mode)));
    if matches!(operation, "&&" | "||") {
        return Err(
            "short-circuit Boolean operations use their direct control-flow forms, not #call"
                .into(),
        );
    }
    let ty = Type::from_name(scalar);
    let integer = matches!(
        ty,
        Type::U8
            | Type::U16
            | Type::U32
            | Type::U64
            | Type::U128
            | Type::Usize
            | Type::I8
            | Type::I16
            | Type::I32
            | Type::I64
            | Type::I128
            | Type::Isize
    );
    let float = matches!(ty, Type::F32 | Type::F64);
    let arithmetic = matches!(operation, "+" | "-" | "*" | "/" | "%");
    let comparison = matches!(operation, "<" | "<=" | ">" | ">=" | "==" | "!=");
    let valid = if comparison {
        integer
            || float
            || matches!(ty, Type::Char)
            || (ty == Type::Bool && matches!(operation, "==" | "!="))
    } else if arithmetic {
        integer || (float && operation != "%")
    } else if matches!(operation, "&" | "|" | "^" | "!") {
        integer || ty == Type::Bool
    } else {
        integer && matches!(operation, "<<" | ">>")
    };
    if !valid {
        return Err(format!("unsupported callable intrinsic '{name}'"));
    }
    if arithmetic && integer {
        if !matches!(mode, Some("wrap" | "saturate")) {
            return Err(crate::names::arithmetic_mode_error(name));
        }
    } else if mode.is_some() {
        return Err(format!(
            "intrinsic '{name}' does not accept an arithmetic mode"
        ));
    }
    let parameters = if operation == "!" {
        &["value"][..]
    } else {
        &["left", "right"][..]
    };
    Ok(Some(Declaration {
        operator: name.into(),
        parameters: parameters
            .iter()
            .map(|name| Parameter {
                name: (*name).into(),
                ty: ty.clone(),
                mutable: false,
            })
            .collect(),
        return_type: if comparison { Type::Bool } else { ty },
    }))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generated_scalar_declarations_agree_with_ordinary_type_checking() {
        let mut source = String::new();
        let mut count = 0;
        for scalar in [
            "bool", "char", "u8", "u16", "u32", "u64", "u128", "usize", "i8", "i16", "i32", "i64",
            "i128", "isize", "f32", "f64",
        ] {
            for (_, operation) in crate::names::OPERATIONS {
                for suffix in ["", "-wrap", "-saturate"] {
                    let name = format!("#{scalar}::{operation}{suffix}");
                    let Ok(Some(declaration)) = declaration(&name) else {
                        continue;
                    };
                    let parameters = declaration
                        .parameters
                        .iter()
                        .map(|parameter| {
                            format!("({} {})", parameter.name, crate::type_source(&parameter.ty))
                        })
                        .collect::<Vec<_>>()
                        .join(" ");
                    let arguments = declaration
                        .parameters
                        .iter()
                        .map(|parameter| format!("({0} {0})", parameter.name))
                        .collect::<Vec<_>>()
                        .join(" ");
                    source.push_str(&format!("#fn probe{count} {{ #params = ({parameters}); #returns = {}; #body = ( (#return (#call {name} ({arguments}))) ); }}\n", crate::type_source(&declaration.return_type)));
                    count += 1;
                }
            }
        }
        assert!(count > 200);
        crate::check_types(&crate::parse_program(&source).unwrap()).unwrap();
    }
}
