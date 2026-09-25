//! Retained semantic information. This is the first stage of the typed IR:
//! declarations are resolved once by validation, not rediscovered by emission.
use std::collections::{HashMap, HashSet};

use crate::{EnumVariant, Field, Span, Type};

#[derive(Clone, Debug)]
pub(crate) struct Signature {
    pub type_parameters: Vec<String>,
    pub parameters: Vec<Type>,
    pub parameter_names: Vec<String>,
    pub return_type: Type,
}

/// Dense identities are deterministic within a checked program. They are not
/// persistent cache keys and do not encode addresses of AST allocations.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash)]
pub(crate) struct FunctionId(usize);

pub(crate) struct FunctionDeclaration {
    pub signature: Signature,
    pub span: Option<Span>,
}

pub(crate) struct Declarations {
    pub bodies: HashMap<String, crate::typed_body::Body>,
    pub aliases: HashMap<String, Type>,
    pub structs: HashMap<String, Vec<Field>>,
    pub enums: HashMap<String, Vec<EnumVariant>>,
    pub globals: HashMap<String, Type>,
    functions: Vec<FunctionDeclaration>,
    function_ids: HashMap<String, FunctionId>,
}

impl Declarations {
    pub fn new(
        aliases: HashMap<String, Type>,
        structs: HashMap<String, Vec<Field>>,
        enums: HashMap<String, Vec<EnumVariant>>,
        globals: HashMap<String, Type>,
        functions: HashMap<String, Signature>,
        spans: &HashMap<String, Span>,
    ) -> Self {
        let mut functions: Vec<_> = functions.into_iter().collect();
        functions.sort_by(|a, b| a.0.cmp(&b.0));
        let function_ids = functions
            .iter()
            .enumerate()
            .map(|(index, (name, _))| (name.clone(), FunctionId(index)))
            .collect();
        let functions = functions
            .into_iter()
            .map(|(name, signature)| FunctionDeclaration {
                signature,
                span: spans.get(&name).copied(),
            })
            .collect();
        Self {
            bodies: HashMap::new(),
            aliases,
            structs,
            enums,
            globals,
            functions,
            function_ids,
        }
    }

    pub fn function_id(&self, name: &str) -> Option<FunctionId> {
        self.function_ids.get(name).copied()
    }

    pub fn function(&self, id: FunctionId) -> &FunctionDeclaration {
        &self.functions[id.0]
    }

    pub fn lower_bodies(
        &mut self,
        program: &crate::Program,
        types: &HashMap<usize, Type>,
        spans: &HashMap<usize, Span>,
    ) {
        self.bodies = program
            .items
            .iter()
            .filter_map(|item| match item {
                crate::Item::Function(function) if !function.external => Some((
                    function.name.clone(),
                    crate::typed_body::Body::lower(function, self, types, spans),
                )),
                _ => None,
            })
            .collect();
    }
}

/// Shared by validation and the not-yet-migrated AST lowering paths. In
/// particular, aliases must resolve inside *every* type constructor.
pub(crate) fn resolve_type(ty: &Type, aliases: &HashMap<String, Type>) -> Result<Type, String> {
    fn resolve(
        ty: &Type,
        aliases: &HashMap<String, Type>,
        seen: &mut HashSet<String>,
    ) -> Result<Type, String> {
        Ok(match ty {
            Type::Named(name) => {
                let Some(target) = aliases.get(name) else {
                    return Ok(ty.clone());
                };
                if !seen.insert(name.clone()) {
                    return Err(format!("type alias '{name}' is recursive"));
                }
                let result = resolve(target, aliases, seen);
                seen.remove(name);
                return result;
            }
            Type::Array(element, length) => {
                Type::Array(Box::new(resolve(element, aliases, seen)?), *length)
            }
            Type::Tuple(fields) => Type::Tuple(
                fields
                    .iter()
                    .map(|field| resolve(field, aliases, seen))
                    .collect::<Result<_, _>>()?,
            ),
            Type::Slice(element) => Type::Slice(Box::new(resolve(element, aliases, seen)?)),
            Type::MutableSlice(element) => {
                Type::MutableSlice(Box::new(resolve(element, aliases, seen)?))
            }
            Type::Atomic(element) => Type::Atomic(Box::new(resolve(element, aliases, seen)?)),
            Type::Cell(element) => Type::Cell(Box::new(resolve(element, aliases, seen)?)),
            Type::Reference { mutable, target } => Type::Reference {
                mutable: *mutable,
                target: Box::new(resolve(target, aliases, seen)?),
            },
            Type::RawPointer { mutable, target } => Type::RawPointer {
                mutable: *mutable,
                target: Box::new(resolve(target, aliases, seen)?),
            },
            _ => ty.clone(),
        })
    }
    resolve(ty, aliases, &mut HashSet::new())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn containers(ty: Type) -> Vec<Type> {
        vec![
            Type::Array(Box::new(ty.clone()), 2),
            Type::Tuple(vec![ty.clone(), ty.clone()]),
            Type::Slice(Box::new(ty.clone())),
            Type::MutableSlice(Box::new(ty.clone())),
            Type::Atomic(Box::new(ty.clone())),
            Type::Cell(Box::new(ty.clone())),
            Type::Reference {
                mutable: false,
                target: Box::new(ty.clone()),
            },
            Type::Reference {
                mutable: true,
                target: Box::new(ty.clone()),
            },
            Type::RawPointer {
                mutable: false,
                target: Box::new(ty.clone()),
            },
            Type::RawPointer {
                mutable: true,
                target: Box::new(ty),
            },
        ]
    }

    #[test]
    fn aliases_resolve_inside_every_container_and_reject_nested_cycles() {
        let alias = Type::Named("Word".into());
        let aliases = HashMap::from([
            ("Word".into(), Type::Named("Base".into())),
            ("Base".into(), Type::U64),
        ]);
        for (input, expected) in containers(alias.clone()).iter().zip(containers(Type::U64)) {
            assert_eq!(resolve_type(input, &aliases).unwrap(), expected);
        }
        for container in containers(alias.clone()) {
            let aliases = HashMap::from([("Word".into(), container)]);
            assert_eq!(
                resolve_type(&alias, &aliases).unwrap_err(),
                "type alias 'Word' is recursive"
            );
        }
    }

    #[test]
    fn checked_declarations_retain_types_spans_and_deterministic_function_ids() {
        let source = "(#type Word u64)
            (#struct Pair ((left Word) (right (#ref Word))))
            (#const Answer Word 42u64)
            (#fn z ((value (#ref Word))) Word (#return (#deref value)))
            (#fn main () Word (#return Answer))";
        let program = crate::parse_program(source).unwrap();
        let checked = crate::CheckedProgram::validate(&program).unwrap();
        let declarations = checked.declarations();
        assert_eq!(declarations.globals["Answer"], Type::U64);
        assert_eq!(declarations.structs["Pair"][0].ty, Type::U64);
        assert_eq!(
            declarations.structs["Pair"][1].ty,
            Type::Reference {
                mutable: false,
                target: Box::new(Type::U64)
            }
        );
        assert_eq!(declarations.function_id("main"), Some(FunctionId(0)));
        let id = declarations.function_id("z").unwrap();
        let function = declarations.function(id);
        assert_eq!(function.signature.return_type, Type::U64);
        assert_eq!(
            function.signature.parameters,
            vec![Type::Reference {
                mutable: false,
                target: Box::new(Type::U64)
            }]
        );
        let span = function.span.unwrap();
        assert!(source[span.start..span.end].contains("z"));
        let independent = crate::parse_program(source).unwrap();
        let checked_again = crate::CheckedProgram::validate(&independent).unwrap();
        assert_eq!(checked_again.declarations().function_id("z"), Some(id));
        let target = crate::TargetDescription::X86_64_SYSTEM_V;
        assert_eq!(
            checked.generate_assembly(target).unwrap(),
            checked_again.generate_assembly(target).unwrap()
        );
    }
}
