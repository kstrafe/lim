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

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct GlobalId(usize);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct AggregateId(usize);

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct FieldId {
    pub owner: AggregateId,
    pub index: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct VariantId {
    pub owner: AggregateId,
    pub index: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) enum DeclarationId {
    Global(GlobalId),
    Aggregate(AggregateId),
    Field(FieldId),
    Variant(VariantId),
}

/// Deterministic identity assigned by source-order traversal before checking.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct ExpressionId(pub usize);

pub(crate) fn expression_ids(program: &crate::Program) -> HashMap<usize, ExpressionId> {
    fn expression(value: &crate::Expr, ids: &mut HashMap<usize, ExpressionId>, next: &mut usize) {
        ids.insert(std::ptr::from_ref(value) as usize, ExpressionId(*next));
        *next += 1;
        match value {
            crate::Expr::List(items) => {
                for item in items {
                    expression(item, ids, next);
                }
            }
            crate::Expr::Block(statements) | crate::Expr::Loop(statements) => {
                for statement_value in statements {
                    statement(statement_value, ids, next);
                }
            }
            crate::Expr::Labeled {
                expression: inner, ..
            }
            | crate::Expr::Quote(inner)
            | crate::Expr::QuasiQuote(inner)
            | crate::Expr::Unquote(inner)
            | crate::Expr::UnquoteSplicing(inner) => expression(inner, ids, next),
            crate::Expr::Symbol(_)
            | crate::Expr::Integer(_)
            | crate::Expr::UnsignedInteger(_)
            | crate::Expr::Float(_)
            | crate::Expr::Char(_)
            | crate::Expr::String(_)
            | crate::Expr::At => {}
        }
    }

    fn statement(
        value: &crate::Statement,
        ids: &mut HashMap<usize, ExpressionId>,
        next: &mut usize,
    ) {
        use crate::Statement as S;
        match value {
            S::Let { value, .. }
            | S::Assign { value, .. }
            | S::FieldAssign { value, .. }
            | S::TupleAssign { value, .. }
            | S::EnumPayloadAssign { value, .. }
            | S::BreakValue(value)
            | S::Return(Some(value))
            | S::Expr(value) => expression(value, ids, next),
            S::Destructure { pattern, value, .. } => {
                expression(pattern, ids, next);
                expression(value, ids, next);
            }
            S::LetElse {
                pattern,
                value,
                else_body,
                ..
            } => {
                expression(pattern, ids, next);
                expression(value, ids, next);
                for statement_value in else_body {
                    statement(statement_value, ids, next);
                }
            }
            S::ArrayAssign { index, value, .. } => {
                expression(index, ids, next);
                expression(value, ids, next);
            }
            S::While { condition, body } => {
                expression(condition, ids, next);
                for statement_value in body {
                    statement(statement_value, ids, next);
                }
            }
            S::Loop { body } => {
                for statement_value in body {
                    statement(statement_value, ids, next);
                }
            }
            S::For {
                init,
                condition,
                step,
                body,
            } => {
                statement(init, ids, next);
                expression(condition, ids, next);
                statement(step, ids, next);
                for statement_value in body {
                    statement(statement_value, ids, next);
                }
            }
            S::Labeled {
                statement: inner, ..
            } => statement(inner, ids, next),
            S::BreakToValue { value, .. } => expression(value, ids, next),
            S::Break | S::BreakTo(_) | S::Continue | S::ContinueTo(_) | S::Return(None) => {}
        }
    }

    let mut ids = HashMap::new();
    let mut next = 0;
    for item in &program.items {
        match item {
            crate::Item::Function(function) => {
                for statement_value in &function.body {
                    statement(statement_value, &mut ids, &mut next);
                }
            }
            crate::Item::Let { value, .. } | crate::Item::Static { value, .. } => {
                expression(value, &mut ids, &mut next);
            }
            _ => {}
        }
    }
    ids
}

pub(crate) struct FunctionDeclaration {
    pub signature: Signature,
    pub span: Option<Span>,
}

pub(crate) struct Declarations {
    pub bodies: HashMap<String, crate::typed_body::Body>,
    pub flows: HashMap<String, crate::typed_flow::FlowGraph>,
    pub liveness: HashMap<String, crate::typed_flow::FlowLiveness>,
    pub aliases: HashMap<String, Type>,
    pub structs: HashMap<String, Vec<Field>>,
    pub enums: HashMap<String, Vec<EnumVariant>>,
    pub globals: HashMap<String, Type>,
    functions: Vec<FunctionDeclaration>,
    function_ids: HashMap<String, FunctionId>,
    global_names: Vec<String>,
    global_ids: HashMap<String, GlobalId>,
    aggregate_names: Vec<String>,
    aggregate_ids: HashMap<String, AggregateId>,
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
        let mut global_names: Vec<_> = globals.keys().cloned().collect();
        global_names.sort();
        let global_ids = global_names
            .iter()
            .enumerate()
            .map(|(index, name)| (name.clone(), GlobalId(index)))
            .collect();
        let mut aggregate_names: Vec<_> = structs.keys().chain(enums.keys()).cloned().collect();
        aggregate_names.sort();
        let aggregate_ids = aggregate_names
            .iter()
            .enumerate()
            .map(|(index, name)| (name.clone(), AggregateId(index)))
            .collect();
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
            flows: HashMap::new(),
            liveness: HashMap::new(),
            aliases,
            structs,
            enums,
            globals,
            functions,
            function_ids,
            global_names,
            global_ids,
            aggregate_names,
            aggregate_ids,
        }
    }

    pub fn global_id(&self, name: &str) -> Option<GlobalId> {
        self.global_ids.get(name).copied()
    }

    pub fn aggregate_id(&self, ty: &Type) -> Option<AggregateId> {
        let mut ty = resolve_type(ty, &self.aliases).ok()?;
        while let Type::Reference { target, .. } = ty {
            ty = *target;
        }
        let Type::Named(name) = ty else {
            return None;
        };
        self.aggregate_ids.get(&name).copied()
    }

    pub fn field_id(&self, ty: &Type, name: &str) -> Option<FieldId> {
        let owner = self.aggregate_id(ty)?;
        let index = self
            .structs
            .get(&self.aggregate_names[owner.0])?
            .iter()
            .position(|field| field.name == name)?;
        Some(FieldId { owner, index })
    }

    pub fn variant_id(&self, ty: &Type, name: &str) -> Option<VariantId> {
        let owner = self.aggregate_id(ty)?;
        let index = self
            .enums
            .get(&self.aggregate_names[owner.0])?
            .iter()
            .position(|variant| variant.name == name)?;
        Some(VariantId { owner, index })
    }

    pub fn declaration_name(&self, id: DeclarationId) -> &str {
        match id {
            DeclarationId::Global(id) => &self.global_names[id.0],
            DeclarationId::Aggregate(id) => &self.aggregate_names[id.0],
            DeclarationId::Field(id) => &self.field(id).name,
            DeclarationId::Variant(id) => &self.variant(id).name,
        }
    }

    pub fn global_type(&self, id: GlobalId) -> &Type {
        &self.globals[&self.global_names[id.0]]
    }

    pub fn field(&self, id: FieldId) -> &Field {
        &self.structs[&self.aggregate_names[id.owner.0]][id.index]
    }

    pub fn variant(&self, id: VariantId) -> &EnumVariant {
        &self.enums[&self.aggregate_names[id.owner.0]][id.index]
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
        types: &HashMap<ExpressionId, Type>,
        expression_ids: &HashMap<usize, ExpressionId>,
        spans: &HashMap<usize, Span>,
    ) -> Result<(), String> {
        self.bodies = program
            .items
            .iter()
            .filter_map(|item| match item {
                crate::Item::Function(function) if !function.external => Some((
                    function.name.clone(),
                    crate::typed_body::Body::lower(function, self, types, expression_ids, spans),
                )),
                _ => None,
            })
            .collect();
        self.flows = self
            .bodies
            .iter()
            .map(|(name, body)| {
                crate::typed_flow::FlowGraph::lower(body).map(|flow| (name.clone(), flow))
            })
            .collect::<Result<_, _>>()?;
        self.liveness = self
            .flows
            .iter()
            .map(|(name, flow)| (name.clone(), flow.liveness(&self.bodies[name])))
            .collect();
        for item in &program.items {
            if let crate::Item::Function(function) = item {
                if !function.external {
                    self.flows[&function.name].check_definite_bindings(
                        &self.bodies[&function.name],
                        function.parameters.len(),
                    )?;
                }
            }
        }
        Ok(())
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

    #[test]
    fn expression_ids_are_dense_and_stable_across_fresh_parses() {
        let source = "(#fn main () u64
          (#let value u64 1u64)
          (#return (#u64.+.wrap value 2u64)))";
        let first = crate::parse_program(source).unwrap();
        let second = crate::parse_program(source).unwrap();
        let first_ids = expression_ids(&first);
        let second_ids = expression_ids(&second);
        fn returned(program: &crate::Program) -> &crate::Expr {
            let crate::Item::Function(function) = &program.items[0] else {
                unreachable!()
            };
            let crate::Statement::Return(Some(value)) = function.body.last().unwrap() else {
                unreachable!()
            };
            value
        }
        let first_return = returned(&first);
        let second_return = returned(&second);
        assert_eq!(
            first_ids[&(std::ptr::from_ref(first_return) as usize)],
            second_ids[&(std::ptr::from_ref(second_return) as usize)]
        );
        let mut dense = first_ids.values().map(|id| id.0).collect::<Vec<_>>();
        dense.sort_unstable();
        assert_eq!(dense, (0..dense.len()).collect::<Vec<_>>());
    }

    #[test]
    fn declaration_ids_resolve_metadata_and_ignore_top_level_declaration_order() {
        let forms = [
            "(#struct Z ((z u64) (a u32)))",
            "(#struct A.Type ((a u8)))",
            "(#enum M ((Second u16) First))",
            "(#const Zed u64 7u64)",
            "(#const Alpha.answer u64 42u64)",
            "(#type ZAlias Z)",
        ];
        for forms in [forms.to_vec(), forms.into_iter().rev().collect()] {
            let source = format!(
                "{} (#fn main () u64 (#return Alpha.answer))",
                forms.join(" ")
            );
            let program = crate::parse_program(&source).unwrap();
            let checked = crate::CheckedProgram::validate(&program).unwrap();
            let declarations = checked.declarations();
            assert_eq!(declarations.global_id("Alpha.answer"), Some(GlobalId(0)));
            assert_eq!(declarations.global_id("Zed"), Some(GlobalId(1)));
            assert_eq!(declarations.global_type(GlobalId(0)), &Type::U64);
            let alias = Type::Reference {
                mutable: true,
                target: Box::new(Type::Named("ZAlias".into())),
            };
            let field = declarations.field_id(&alias, "a").unwrap();
            assert_eq!(
                field,
                FieldId {
                    owner: AggregateId(2),
                    index: 1
                }
            );
            assert_eq!(declarations.field(field).ty, Type::U32);
            assert_eq!(
                declarations.declaration_name(DeclarationId::Field(field)),
                "a"
            );
            let other = declarations
                .field_id(&Type::Named("A.Type".into()), "a")
                .unwrap();
            assert_ne!(field, other);
            assert_eq!(declarations.field(other).ty, Type::U8);
            let variant = declarations
                .variant_id(&Type::Named("M".into()), "Second")
                .unwrap();
            assert_eq!(
                variant,
                VariantId {
                    owner: AggregateId(1),
                    index: 0
                }
            );
            assert_eq!(declarations.variant(variant).fields, vec![Type::U16]);
            assert_eq!(
                declarations.declaration_name(DeclarationId::Variant(variant)),
                "Second"
            );
        }
    }

    fn containers(ty: Type) -> Vec<Type> {
        vec![
            Type::Array(Box::new(ty.clone()), 2),
            Type::Tuple(vec![ty.clone(), ty.clone()]),
            Type::Slice(Box::new(ty.clone())),
            Type::MutableSlice(Box::new(ty.clone())),
            Type::Atomic(Box::new(ty.clone())),
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
