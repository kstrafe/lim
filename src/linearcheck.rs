use std::collections::HashSet;

use crate::analysis_error::{failure, Error, Site};

use crate::{Expr, Item, Program, Statement, Type};

// Local renaming assigns each binding a unique name before this pass. Keep
// that opaque identity separate from projections; punctuation is never syntax.
#[derive(Clone, Debug, Eq, Hash, PartialEq, Ord, PartialOrd)]
struct BindingId(String);

#[derive(Clone, Debug, Eq, Hash, PartialEq, Ord, PartialOrd)]
enum Projection {
    Field(String),
    Tuple(usize),
    Variant(String),
    Index(String),
    UnknownIndex,
}

#[derive(Clone, Debug, Eq, Hash, PartialEq, Ord, PartialOrd)]
struct Place {
    binding: BindingId,
    projections: Vec<Projection>,
}

impl Place {
    fn root(name: &str) -> Self {
        Self {
            binding: BindingId(name.to_owned()),
            projections: Vec::new(),
        }
    }

    fn project(mut self, projection: Projection) -> Self {
        self.projections.push(projection);
        self
    }

    fn covers(&self, other: &Self) -> bool {
        self.binding == other.binding && other.projections.starts_with(&self.projections)
    }

    fn conflicts(&self, other: &Self) -> bool {
        self.binding == other.binding
            && self
                .projections
                .iter()
                .zip(&other.projections)
                .all(|(a, b)| {
                    a == b
                        || matches!(a, Projection::UnknownIndex)
                        || matches!(b, Projection::UnknownIndex)
                })
    }
}

impl std::fmt::Display for Place {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(out, "{}", self.binding.0)?;
        for projection in &self.projections {
            match projection {
                Projection::Field(name) | Projection::Variant(name) => write!(out, ".{name}")?,
                Projection::Tuple(index) => write!(out, ".{index}")?,
                Projection::Index(index) => write!(out, "[{index}]")?,
                Projection::UnknownIndex => write!(out, "[*]")?,
            }
        }
        Ok(())
    }
}

#[derive(Clone, Default)]
struct Moves {
    places: HashSet<Place>,
    sites: std::collections::HashMap<Place, Site>,
}
impl PartialEq for Moves {
    fn eq(&self, other: &Self) -> bool {
        self.places == other.places
    }
}
impl std::ops::Deref for Moves {
    type Target = HashSet<Place>;
    fn deref(&self) -> &Self::Target {
        &self.places
    }
}
impl std::ops::DerefMut for Moves {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.places
    }
}
impl Moves {
    fn insert(&mut self, place: Place) -> bool {
        if self.places.insert(place.clone()) {
            if let Some(site) = Site::current() {
                self.sites.insert(place, site);
            }
            true
        } else {
            false
        }
    }
    fn prior(&self, place: &Place) -> Option<Site> {
        self.places
            .iter()
            .filter(|prior| prior.conflicts(place))
            .min()
            .and_then(|prior| self.sites.get(prior).copied())
    }
    fn merged(&self, other: &Self) -> Self {
        let mut result = self.clone();
        result.places.extend(other.places.iter().cloned());
        result.sites.extend(
            other
                .sites
                .iter()
                .map(|(place, site)| (place.clone(), *site)),
        );
        result
    }
}

#[derive(Default)]
pub(crate) struct LinearTypes {
    explicitly_linear: HashSet<String>,
    binding_sites: std::cell::RefCell<std::collections::HashMap<String, Site>>,
    binding_types: std::cell::RefCell<std::collections::HashMap<String, Type>>,
    aliases: std::collections::HashMap<String, Type>,
    structs: std::collections::HashMap<String, Vec<Type>>,
    struct_fields: std::collections::HashMap<String, Vec<(String, Type)>>,
    enums: std::collections::HashMap<String, std::collections::HashMap<String, Vec<Type>>>,
    checked_expressions:
        Option<std::sync::Arc<std::collections::HashMap<crate::typed_ir::ExpressionId, Type>>>,
    checked_expression_ids:
        Option<std::sync::Arc<std::collections::HashMap<usize, crate::typed_ir::ExpressionId>>>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum LinearProjection {
    Field(String),
    Tuple(usize),
    Payload(String, usize),
    Index(usize),
}

impl LinearTypes {
    pub(crate) fn from_program(program: &Program) -> Self {
        let mut types = Self::default();
        for item in &program.items {
            match item {
                Item::LinearAnnotation { type_name } => {
                    types.explicitly_linear.insert(type_name.clone());
                }
                Item::TypeAlias { name, target, .. } => {
                    types.aliases.insert(name.clone(), target.clone());
                }
                Item::Struct { name, fields, .. } => {
                    types.structs.insert(
                        name.clone(),
                        fields.iter().map(|field| field.ty.clone()).collect(),
                    );
                    types.struct_fields.insert(
                        name.clone(),
                        fields
                            .iter()
                            .map(|field| (field.name.clone(), field.ty.clone()))
                            .collect(),
                    );
                }
                Item::Enum { name, variants, .. } => {
                    types.enums.insert(
                        name.clone(),
                        variants
                            .iter()
                            .map(|variant| (variant.name.clone(), variant.fields.clone()))
                            .collect(),
                    );
                }
                _ => {}
            }
        }
        types
    }

    pub(crate) fn is_linear(&self, ty: &Type) -> bool {
        is_linear(ty, self, &mut HashSet::new())
    }

    /// Return the indivisible linear leaves which must be consumed from a
    /// value. Enum payload alternatives are all retained here; typed match
    /// flow makes inactive alternatives vacuously consumed on each arm.
    pub(crate) fn linear_obligation_paths(&self, ty: &Type) -> Vec<Vec<LinearProjection>> {
        fn walk(
            types: &LinearTypes,
            ty: &Type,
            path: &mut Vec<LinearProjection>,
            seen: &mut HashSet<String>,
            output: &mut Vec<Vec<LinearProjection>>,
        ) {
            match ty {
                Type::Atomic(_) | Type::MutableSlice(_) => output.push(path.clone()),
                Type::Named(name) => {
                    if let Some(alias) = types.aliases.get(name) {
                        if seen.insert(name.clone()) {
                            walk(types, alias, path, seen, output);
                            seen.remove(name);
                        }
                    } else if types.explicitly_linear.contains(name) {
                        output.push(path.clone());
                    } else if let Some(fields) = types.struct_fields.get(name) {
                        for (field, field_ty) in fields {
                            if types.is_linear(field_ty) {
                                path.push(LinearProjection::Field(field.clone()));
                                walk(types, field_ty, path, seen, output);
                                path.pop();
                            }
                        }
                    } else if let Some(variants) = types.enums.get(name) {
                        let mut variants = variants.iter().collect::<Vec<_>>();
                        variants.sort_by(|left, right| left.0.cmp(right.0));
                        for (variant, fields) in variants {
                            for (index, field_ty) in fields.iter().enumerate() {
                                if types.is_linear(field_ty) {
                                    path.push(LinearProjection::Payload(variant.clone(), index));
                                    walk(types, field_ty, path, seen, output);
                                    path.pop();
                                }
                            }
                        }
                    } else {
                        output.push(path.clone());
                    }
                }
                Type::Tuple(items) => {
                    for (index, item) in items.iter().enumerate() {
                        if types.is_linear(item) {
                            path.push(LinearProjection::Tuple(index));
                            walk(types, item, path, seen, output);
                            path.pop();
                        }
                    }
                }
                Type::Array(element, count) if types.is_linear(element) => {
                    for index in 0..*count {
                        path.push(LinearProjection::Index(index));
                        walk(types, element, path, seen, output);
                        path.pop();
                    }
                }
                _ => {}
            }
        }

        let mut output = Vec::new();
        walk(self, ty, &mut Vec::new(), &mut HashSet::new(), &mut output);
        output
    }

    /// A value can be repeated only when no element requires unique ownership
    /// or exclusive reference identity. References need no explicit cleanup,
    /// but mutable references still cannot be duplicated.
    pub(crate) fn can_repeat(&self, ty: &Type) -> bool {
        !self.is_linear(ty) && !contains_exclusive_reference(ty, self, &mut HashSet::new())
    }

    fn binding_consumed(&self, name: &str, moved: &Moves) -> bool {
        let root = Place::root(name);
        if moved.contains(&root) {
            return true;
        }
        let binding_types = self.binding_types.borrow();
        let Some(ty) = binding_types.get(name) else {
            return false;
        };
        self.value_consumed(&root, ty, moved, &mut HashSet::new())
    }

    fn place_type(&self, place: &Place) -> Option<Type> {
        let mut ty = self.binding_types.borrow().get(&place.binding.0)?.clone();
        for projection in &place.projections {
            ty = self.resolve_aliases(ty)?;
            while let Type::Reference { target, .. } = ty {
                ty = self.resolve_aliases(*target)?;
            }
            ty = match (ty, projection) {
                (Type::Named(name), Projection::Field(field)) => self
                    .struct_fields
                    .get(&name)?
                    .iter()
                    .find(|(candidate, _)| candidate == field)?
                    .1
                    .clone(),
                (Type::Named(name), Projection::Variant(variant)) => {
                    Type::Tuple(self.enums.get(&name)?.get(variant)?.clone())
                }
                (Type::Tuple(items), Projection::Tuple(index)) => items.get(*index)?.clone(),
                (Type::Array(element, _), Projection::Index(_) | Projection::UnknownIndex) => {
                    *element
                }
                _ => return None,
            };
        }
        self.resolve_aliases(ty)
    }

    fn resolve_aliases(&self, mut ty: Type) -> Option<Type> {
        let mut seen = HashSet::new();
        while let Type::Named(name) = &ty {
            let Some(target) = self.aliases.get(name) else {
                break;
            };
            if !seen.insert(name.clone()) {
                return None;
            }
            ty = target.clone();
        }
        Some(ty)
    }

    fn value_consumed(
        &self,
        place: &Place,
        ty: &Type,
        moved: &Moves,
        seen: &mut HashSet<String>,
    ) -> bool {
        if moved.iter().any(|prior| prior.covers(place)) {
            return true;
        }
        match ty {
            Type::Named(name) => {
                if self.explicitly_linear.contains(name) || !seen.insert(name.clone()) {
                    return false;
                }
                let complete = if let Some(alias) = self.aliases.get(name) {
                    self.value_consumed(place, alias, moved, seen)
                } else if let Some(fields) = self.struct_fields.get(name) {
                    let linear_fields = fields
                        .iter()
                        .filter(|(_, ty)| self.is_linear(ty))
                        .collect::<Vec<_>>();
                    !linear_fields.is_empty()
                        && linear_fields.iter().all(|(field, ty)| {
                            self.value_consumed(
                                &place.clone().project(Projection::Field(field.clone())),
                                ty,
                                moved,
                                seen,
                            )
                        })
                } else {
                    false
                };
                seen.remove(name);
                complete
            }
            Type::Tuple(items) => {
                let linear = items
                    .iter()
                    .enumerate()
                    .filter(|(_, ty)| self.is_linear(ty))
                    .collect::<Vec<_>>();
                !linear.is_empty()
                    && linear.iter().all(|(index, ty)| {
                        self.value_consumed(
                            &place.clone().project(Projection::Tuple(*index)),
                            ty,
                            moved,
                            seen,
                        )
                    })
            }
            Type::Array(element, count) if self.is_linear(element) => {
                *count <= moved.len()
                    && (0..*count).all(|index| {
                        self.value_consumed(
                            &place.clone().project(Projection::Index(index.to_string())),
                            element,
                            moved,
                            seen,
                        )
                    })
            }
            _ => false,
        }
    }
}

/// Enforce linear use of owned values. Non-Copy values must be consumed exactly
/// once; Copy values and references do not create an ownership obligation.
pub(crate) fn check_program_with_span(
    program: &Program,
    checked_expressions: std::sync::Arc<
        std::collections::HashMap<crate::typed_ir::ExpressionId, Type>,
    >,
    checked_expression_ids: std::sync::Arc<
        std::collections::HashMap<usize, crate::typed_ir::ExpressionId>,
    >,
) -> Result<(), (String, Option<crate::Span>, Vec<(crate::Span, String)>)> {
    let mut types = LinearTypes::from_program(program);
    types.checked_expressions = Some(checked_expressions);
    types.checked_expression_ids = Some(checked_expression_ids);
    for item in &program.items {
        let Item::Function(function) = item else {
            continue;
        };
        if function.external {
            continue;
        }
        types.binding_types.borrow_mut().clear();
        types.binding_sites.borrow_mut().clear();
        let mut bindings = function
            .parameters
            .iter()
            .filter(|parameter| is_linear(&parameter.ty, &types, &mut HashSet::new()))
            .map(|p| p.name.clone())
            .collect::<HashSet<_>>();
        for parameter in &function.parameters {
            types
                .binding_types
                .borrow_mut()
                .insert(parameter.name.clone(), parameter.ty.clone());
        }
        let mut moved = Moves::default();
        for (index, statement) in function.body.iter().enumerate() {
            if let Err(error) = check_statements(
                std::slice::from_ref(statement),
                &mut bindings,
                &mut moved,
                &HashSet::new(),
                &types,
            ) {
                let key = (function.name.clone(), index);
                let span = error
                    .site
                    .and_then(|site| site.span(program))
                    .or_else(|| program.statement_spans.get(&key).copied());
                let labels = error
                    .related
                    .into_iter()
                    .filter_map(|site| site.span(program))
                    .map(|span| (span, "value consumed here".into()))
                    .collect();
                return Err((error.message, span, labels));
            }
        }
    }
    Ok(())
}

fn check_statements(
    statements: &[Statement],
    bindings: &mut HashSet<String>,
    moved: &mut Moves,
    globals: &HashSet<String>,
    types: &LinearTypes,
) -> Result<(), Error> {
    for statement in statements {
        let _site = Site::statement(statement).enter();
        match statement {
            Statement::Let {
                name, ty, value, ..
            } => {
                check_expr(value, bindings, moved, globals, false, types)?;
                types
                    .binding_types
                    .borrow_mut()
                    .insert(name.clone(), ty.clone());
                if is_linear(ty, types, &mut HashSet::new()) {
                    bindings.insert(name.clone());
                    types
                        .binding_sites
                        .borrow_mut()
                        .insert(name.clone(), Site::statement(statement));
                }
                moved.retain(|place| place_root(place) != name);
            }
            Statement::Destructure {
                pattern, ty, value, ..
            } => {
                check_expr(value, bindings, moved, globals, false, types)?;
                collect_typed_pattern_names(pattern, ty, types, bindings);
            }
            Statement::LetElse {
                pattern,
                ty,
                value,
                else_body,
                ..
            } => {
                check_expr(value, bindings, moved, globals, false, types)?;
                let mut else_bindings = bindings.clone();
                let mut else_moved = moved.clone();
                check_scoped_statements(
                    else_body,
                    &mut else_bindings,
                    &mut else_moved,
                    globals,
                    types,
                )?;
                collect_typed_pattern_names(pattern, ty, types, bindings);
            }
            Statement::Assign { name, value } => {
                check_expr(value, bindings, moved, globals, false, types)?;
                if bindings.contains(name) {
                    if !types.binding_consumed(name, moved) {
                        return Err(failure!("assignment would destroy live linear value '{name}'; consume it explicitly first"));
                    }
                    moved.retain(|place| place_root(place) != name);
                }
            }
            Statement::ArrayAssign { name, index, value } => {
                check_expr(index, bindings, moved, globals, false, types)?;
                check_expr(value, bindings, moved, globals, false, types)?;
                check_expr(
                    &Expr::Symbol(name.clone()),
                    bindings,
                    moved,
                    globals,
                    true,
                    types,
                )?;
                if let Some(index) = literal_index(index) {
                    moved.remove(&Place::root(name).project(Projection::Index(index)));
                }
                // A dynamic write cannot prove which moved element it restores.
            }
            Statement::FieldAssign { name, field, value } => {
                check_expr(value, bindings, moved, globals, false, types)?;
                moved.remove(&Place::root(name).project(Projection::Field(field.clone())));
            }
            Statement::TupleAssign { name, index, value } => {
                check_expr(value, bindings, moved, globals, false, types)?;
                moved.remove(&Place::root(name).project(Projection::Tuple(*index)));
            }
            Statement::EnumPayloadAssign {
                name,
                variant,
                index,
                value,
            } => {
                check_expr(value, bindings, moved, globals, false, types)?;
                moved.remove(
                    &Place::root(name)
                        .project(Projection::Variant(variant.clone()))
                        .project(Projection::Tuple(*index)),
                );
            }
            Statement::Return(value) => {
                if let Some(value) = value {
                    check_expr(value, bindings, moved, globals, false, types)?;
                }
                if let Some(name) = bindings
                    .iter()
                    .find(|name| !types.binding_consumed(name, moved))
                {
                    let mut error = failure!("linear value '{name}' must be consumed before returning; use it, pass it to a destruction function, or explicitly (#forget {name})");
                    if let Some(site) = types.binding_sites.borrow().get(name) {
                        error = error.at(*site);
                    }
                    return Err(error);
                }
            }
            Statement::Expr(expr) | Statement::BreakValue(expr) => {
                check_expr(expr, bindings, moved, globals, false, types)?
            }
            Statement::BreakToValue { value, .. } => {
                check_expr(value, bindings, moved, globals, false, types)?
            }
            Statement::While { condition, body } => {
                let before_condition = moved.clone();
                if let Expr::List(parts) = condition {
                    if matches!(parts.first(), Some(Expr::Symbol(head)) if head == "match") {
                        if let Some(owner) = parts.get(1) {
                            check_expr(owner, bindings, moved, globals, true, types)?;
                        }
                    } else {
                        check_expr(condition, bindings, moved, globals, false, types)?;
                    }
                } else {
                    check_expr(condition, bindings, moved, globals, false, types)?;
                }
                if *moved != before_condition {
                    return Err("a loop condition cannot consume an outer value; use #clone".into());
                }
                let mut body_moved = moved.clone();
                check_scoped_statements(body, bindings, &mut body_moved, globals, types)?;
                let moved_by_body = body_moved
                    .difference(moved)
                    .cloned()
                    .collect::<HashSet<_>>();
                for name in &moved_by_body {
                    if !assigned_before_read(body, place_root(name)) {
                        return Err(failure!("loop body moves '{name}' before the next iteration can restore it; clone the value"));
                    }
                }
                *moved = moved.merged(&body_moved);
            }
            Statement::Loop { body } => {
                let mut body_moved = moved.clone();
                check_scoped_statements(body, bindings, &mut body_moved, globals, types)?;
                if body_moved != *moved {
                    return Err(
                        "a loop body cannot move an outer value; clone it before use".into(),
                    );
                }
            }
            Statement::For {
                init,
                condition,
                step,
                body,
            } => {
                check_statements(std::slice::from_ref(init), bindings, moved, globals, types)?;
                let before_condition = moved.clone();
                check_expr(condition, bindings, moved, globals, false, types)?;
                if *moved != before_condition {
                    return Err("a loop condition cannot consume an outer value; use #clone".into());
                }
                let before = moved.clone();
                let mut inner = before.clone();
                check_scoped_statements(body, bindings, &mut inner, globals, types)?;
                check_statements(
                    std::slice::from_ref(step),
                    bindings,
                    &mut inner,
                    globals,
                    types,
                )?;
                if inner != before {
                    return Err(
                        "a loop body cannot move an outer value; clone it before use".into(),
                    );
                }
            }
            Statement::Labeled { statement, .. } => check_statements(
                std::slice::from_ref(statement),
                bindings,
                moved,
                globals,
                types,
            )?,
            _ => {}
        }
    }
    Ok(())
}

fn is_linear(ty: &Type, types: &LinearTypes, seen: &mut HashSet<String>) -> bool {
    match ty {
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
        | Type::Reference { .. }
        | Type::PinnedReference { .. }
        | Type::RawPointer { .. }
        | Type::Slice(_) => false,
        Type::MutableSlice(_) | Type::Atomic(_) => true,
        Type::Tuple(items) => items.iter().any(|item| is_linear(item, types, seen)),
        Type::Array(element, _) => is_linear(element, types, seen),
        Type::Named(name) => {
            if types.explicitly_linear.contains(name) {
                return true;
            }
            if let Some(alias) = types.aliases.get(name) {
                if !seen.insert(name.clone()) {
                    return true;
                }
                let result = is_linear(alias, types, seen);
                seen.remove(name);
                result
            } else if let Some(fields) = types.structs.get(name) {
                if !seen.insert(name.clone()) {
                    return true;
                }
                let result = fields.iter().any(|field| is_linear(field, types, seen));
                seen.remove(name);
                result
            } else if let Some(variants) = types.enums.get(name) {
                if !seen.insert(name.clone()) {
                    return true;
                }
                let result = variants
                    .values()
                    .flatten()
                    .any(|field| is_linear(field, types, seen));
                seen.remove(name);
                result
            } else {
                true
            }
        }
        Type::Generic(_) | Type::Never => true,
    }
}

fn contains_exclusive_reference(
    ty: &Type,
    types: &LinearTypes,
    seen: &mut HashSet<String>,
) -> bool {
    match ty {
        Type::Reference { mutable: true, .. } | Type::PinnedReference { mutable: true, .. } => true,
        Type::Tuple(items) => items
            .iter()
            .any(|item| contains_exclusive_reference(item, types, seen)),
        Type::Array(element, _) => contains_exclusive_reference(element, types, seen),
        Type::Named(name) => {
            if !seen.insert(name.clone()) {
                return true;
            }
            let result = if let Some(alias) = types.aliases.get(name) {
                contains_exclusive_reference(alias, types, seen)
            } else if let Some(fields) = types.structs.get(name) {
                fields
                    .iter()
                    .any(|field| contains_exclusive_reference(field, types, seen))
            } else if let Some(variants) = types.enums.get(name) {
                variants
                    .values()
                    .flatten()
                    .any(|field| contains_exclusive_reference(field, types, seen))
            } else {
                true
            };
            seen.remove(name);
            result
        }
        Type::Generic(_) => true,
        // Raw pointers and shared references/slices carry no exclusive loan;
        // the target type does not change whether the handle can be copied.
        _ => false,
    }
}

fn contains_reference(ty: &Type, types: &LinearTypes, seen: &mut HashSet<String>) -> bool {
    match ty {
        Type::Reference { .. }
        | Type::PinnedReference { .. }
        | Type::Slice(_)
        | Type::MutableSlice(_) => true,
        Type::Tuple(items) => items
            .iter()
            .any(|item| contains_reference(item, types, seen)),
        Type::Array(element, _) | Type::Atomic(element) => contains_reference(element, types, seen),
        Type::Named(name) => {
            if !seen.insert(name.clone()) {
                return true;
            }
            let contains = types
                .aliases
                .get(name)
                .map(|ty| contains_reference(ty, types, seen))
                .or_else(|| {
                    types
                        .structs
                        .get(name)
                        .map(|fields| fields.iter().any(|ty| contains_reference(ty, types, seen)))
                })
                .or_else(|| {
                    types.enums.get(name).map(|variants| {
                        variants
                            .values()
                            .flatten()
                            .any(|ty| contains_reference(ty, types, seen))
                    })
                })
                .unwrap_or(false);
            seen.remove(name);
            contains
        }
        _ => false,
    }
}

fn collect_typed_pattern_names(
    pattern: &Expr,
    ty: &Type,
    types: &LinearTypes,
    bindings: &mut HashSet<String>,
) {
    if let Type::Named(name) = ty {
        if let Some(target) = types.aliases.get(name) {
            collect_typed_pattern_names(pattern, target, types, bindings);
            return;
        }
    }
    match pattern {
        Expr::Symbol(name) if name != "_" => {
            types
                .binding_types
                .borrow_mut()
                .insert(name.clone(), ty.clone());
            if is_linear(ty, types, &mut HashSet::new()) {
                bindings.insert(name.clone());
            }
        }
        Expr::List(parts) if !parts.is_empty() => {
            let head = match &parts[0] {
                Expr::Symbol(name) => name.as_str(),
                _ => "",
            };
            if head == "or" {
                for alternative in parts.iter().skip(1) {
                    collect_typed_pattern_names(alternative, ty, types, bindings);
                }
                return;
            }
            let child_types: Vec<Type> = match (head, ty) {
                ("tuple", Type::Tuple(items)) => items.clone(),
                ("array", Type::Array(element, count)) => vec![(**element).clone(); *count],
                (_, Type::Named(name)) => types
                    .structs
                    .get(name)
                    .cloned()
                    .or_else(|| {
                        types
                            .enums
                            .get(name)
                            .and_then(|variants| variants.get(head).cloned())
                    })
                    .unwrap_or_default(),
                _ => Vec::new(),
            };
            if child_types.is_empty() && parts.len() > 1 {
                // Unknown pattern forms keep the old conservative behavior;
                // never silently drop a possible linear binding.
                collect_pattern_names(pattern, bindings);
                return;
            }
            for (child, child_ty) in parts.iter().skip(1).zip(child_types.iter()) {
                collect_typed_pattern_names(child, child_ty, types, bindings);
            }
        }
        _ => {}
    }
}

fn collect_pattern_names(pattern: &Expr, bindings: &mut HashSet<String>) {
    match pattern {
        Expr::Symbol(name) if name != "_" => {
            bindings.insert(name.clone());
        }
        Expr::List(items) => {
            if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "literal" | "range" | "range-inclusive"))
            {
                return;
            }
            for item in items.iter().skip(1) {
                collect_pattern_names(item, bindings);
            }
        }
        _ => {}
    }
}

fn check_expr(
    expr: &Expr,
    bindings: &HashSet<String>,
    moved: &mut Moves,
    globals: &HashSet<String>,
    place: bool,
    types: &LinearTypes,
) -> Result<(), Error> {
    let _site = Site::expression(expr).enter();
    match expr {
        Expr::Symbol(name) if types.binding_types.borrow().contains_key(name) => {
            let key = Place::root(name);
            let linear = types.place_type(&key).is_none_or(|ty| types.is_linear(&ty));
            let conflicts = if place {
                moved.iter().any(|prior| prior.covers(&key))
            } else {
                has_move_conflict(moved, &key)
            };
            if conflicts && (!place || !linear) {
                return Err(if linear {
                    failure!("linear value '{name}' was used more than once; use (#clone {name}) to make an explicit copy")
                        .related(moved.prior(&key))
                } else {
                    failure!("value '{name}' was used after it was consumed")
                        .related(moved.prior(&key))
                });
            }
            if !place && linear {
                moved.insert(key);
            }
        }
        Expr::List(items) if !items.is_empty() => {
            let head = match &items[0] {
                Expr::Symbol(s) => s.as_str(),
                _ => "",
            };
            if head == "clone" {
                if items.len() != 2 {
                    return Err("clone requires exactly one value".into());
                }
                check_clone(&items[1], bindings, moved, types)?;
            } else if matches!(head, "forget" | "drop") && items.len() == 2 {
                if let Some(key) = place_key(&items[1]) {
                    let root = place_root(&key);
                    if types.binding_types.borrow().contains_key(root) {
                        if moved.iter().any(|existing| existing.covers(&key)) {
                            return Err(failure!("linear value '{key}' was already consumed")
                                .related(moved.prior(&key)));
                        }
                        if types.place_type(&key).is_none_or(|ty| {
                            types.is_linear(&ty)
                                || contains_reference(&ty, types, &mut HashSet::new())
                        }) {
                            moved.retain(|existing| !key.covers(existing));
                            moved.insert(key);
                        }
                    } else {
                        check_expr(&items[1], bindings, moved, globals, false, types)?;
                    }
                } else {
                    check_expr(&items[1], bindings, moved, globals, false, types)?;
                }
            } else if head == "if" && items.len() == 4 {
                check_expr(&items[1], bindings, moved, globals, false, types)?;
                let mut left = moved.clone();
                let mut right = moved.clone();
                check_expr(&items[2], bindings, &mut left, globals, false, types)?;
                check_expr(&items[3], bindings, &mut right, globals, false, types)?;
                require_same_consumption(bindings, &left, &right, types)?;
                // Both branches have consumed exactly the same outer places,
                // so the union now also represents definite consumption.
                *moved = left.merged(&right);
            } else if head == "match" && items.len() >= 3 {
                check_expr(&items[1], bindings, moved, globals, false, types)?;
                let after_scrutinee = moved.clone();
                let scrutinee_type =
                    place_key(&items[1]).and_then(|place| types.place_type(&place));
                let mut exits = Vec::new();
                for arm in &items[2..] {
                    let Expr::List(parts) = arm else { continue };
                    if parts.len() < 2 {
                        continue;
                    }
                    let mut arm_bindings = bindings.clone();
                    if let Some(ty) = &scrutinee_type {
                        collect_typed_pattern_names(&parts[0], ty, types, &mut arm_bindings);
                    } else {
                        collect_pattern_names(&parts[0], &mut arm_bindings);
                    }
                    let mut arm_moved = after_scrutinee.clone();
                    let guard = parts.get(1).and_then(|expr| match expr {
                        Expr::List(when) if matches!(when.first(), Some(Expr::Symbol(head)) if head == "when") => Some(when),
                        _ => None,
                    });
                    if let Some(when) = guard {
                        let before_guard = arm_moved.clone();
                        for part in when.iter().skip(1) {
                            check_expr(part, &arm_bindings, &mut arm_moved, globals, false, types)?;
                        }
                        // Pattern payloads are inspected by guards, then
                        // consumed by the selected arm body.
                        for name in &arm_bindings {
                            if bindings.contains(name) {
                                continue;
                            }
                            if before_guard.contains(&Place::root(name)) {
                                arm_moved.insert(Place::root(name));
                            } else {
                                arm_moved.remove(&Place::root(name));
                            }
                        }
                        if let Some(body) = parts.get(2) {
                            check_expr(body, &arm_bindings, &mut arm_moved, globals, false, types)?;
                        }
                    } else {
                        for part in &parts[1..] {
                            check_expr(part, &arm_bindings, &mut arm_moved, globals, false, types)?;
                        }
                    }
                    arm_moved.retain(|name| bindings.contains(place_root(name)));
                    exits.push(arm_moved);
                }
                if let Some(first) = exits.first() {
                    for exit in exits.iter().skip(1) {
                        require_same_consumption(bindings, first, exit, types)?;
                    }
                    *moved = exits
                        .into_iter()
                        .reduce(|a, b| a.merged(&b))
                        .unwrap_or_default();
                }
            } else if head == "while-let" && items.len() >= 4 {
                check_expr(&items[2], bindings, moved, globals, true, types)?;
                let before = moved.clone();
                let mut body_state = before.clone();
                for body in &items[3..] {
                    check_expr(body, bindings, &mut body_state, globals, false, types)?;
                }
                if body_state != before {
                    return Err(
                        "a #while-let body must restore outer values before the next iteration"
                            .into(),
                    );
                }
            } else if head == "if-let" && (items.len() == 4 || items.len() == 5) {
                check_expr(&items[2], bindings, moved, globals, true, types)?;
                let mut branch_bindings = bindings.clone();
                collect_pattern_names(&items[1], &mut branch_bindings);
                let mut then_state = moved.clone();
                check_expr(
                    &items[3],
                    &branch_bindings,
                    &mut then_state,
                    globals,
                    false,
                    types,
                )?;
                then_state.retain(|name| bindings.contains(place_root(name)));
                let mut else_state = moved.clone();
                if let Some(otherwise) = items.get(4) {
                    check_expr(otherwise, bindings, &mut else_state, globals, false, types)?;
                }
                require_same_consumption(bindings, &then_state, &else_state, types)?;
                *moved = then_state.merged(&else_state);
            } else if matches!(head, "&&" | "||") && items.len() == 3 {
                check_expr(&items[1], bindings, moved, globals, false, types)?;
                let mut taken = moved.clone();
                check_expr(&items[2], bindings, &mut taken, globals, false, types)?;
                require_same_consumption(bindings, moved, &taken, types)?;
                *moved = moved.merged(&taken);
            } else if head == "unsafe" || head == "block" {
                for arg in items.iter().skip(1) {
                    check_expr(arg, bindings, moved, globals, false, types)?;
                }
            } else if matches!(head, "get" | "get-payload" | "index") {
                if head == "index" && items.len() == 3 {
                    check_expr(&items[2], bindings, moved, globals, false, types)?;
                }
                if !place {
                    if let Some(key) = place_key(expr) {
                        if moved.iter().any(|existing| existing.covers(&key)) {
                            return Err(failure!("linear projection '{key}' was used more than once; clone it explicitly").related(moved.prior(&key)));
                        }
                        if types.place_type(&key).is_none_or(|ty| types.is_linear(&ty)) {
                            if has_move_conflict(moved, &key) {
                                return Err(failure!("linear projection '{key}' was used more than once; clone it explicitly").related(moved.prior(&key)));
                            }
                            moved.insert(key);
                        }
                    } else if let Some(base) = items.get(1) {
                        check_expr(base, bindings, moved, globals, false, types)?;
                    }
                } else if let Some(base) = items.get(1) {
                    if let Some(key) = place_key(expr) {
                        if moved.iter().any(|prior| prior.covers(&key))
                            && types
                                .place_type(&key)
                                .is_some_and(|ty| !types.is_linear(&ty))
                        {
                            return Err(failure!("value '{key}' was used after it was consumed")
                                .related(moved.prior(&key)));
                        }
                    }
                    check_expr(base, bindings, moved, globals, true, types)?;
                }
            } else if head == "slice-mut-split" && items.len() == 3 {
                check_expr(&items[1], bindings, moved, globals, false, types)?;
                check_expr(&items[2], bindings, moved, globals, false, types)?;
            } else if head == "slice-mut-idx" && items.len() == 3 {
                check_expr(&items[1], bindings, moved, globals, true, types)?;
                check_expr(&items[2], bindings, moved, globals, false, types)?;
            } else if head == "slice-mut-len" && items.len() == 2 {
                check_expr(&items[1], bindings, moved, globals, true, types)?;
            } else if head == "tuple" || head == "array" {
                let checked_type = types
                    .checked_expressions
                    .as_ref()
                    .and_then(|checked| {
                        let id = types
                            .checked_expression_ids
                            .as_ref()?
                            .get(&(std::ptr::from_ref(expr) as usize))?;
                        checked.get(id)
                    })
                    .and_then(|ty| types.resolve_aliases(ty.clone()));
                let arity = match checked_type {
                    Some(Type::Array(_, length)) => Some(length),
                    Some(Type::Tuple(fields)) => Some(fields.len()),
                    _ => None,
                };
                let value_start = if arity.is_some_and(|count| items.len() == count + 1) {
                    1
                } else {
                    2
                };
                for arg in items.iter().skip(value_start) {
                    check_expr(arg, bindings, moved, globals, false, types)?;
                }
            } else if head == "array-repeat" {
                let value_index = if items.len() == 3
                    && matches!(items.get(1), Some(Expr::List(parts))
                        if matches!(parts.first(), Some(Expr::Symbol(name)) if name == "array"))
                {
                    2
                } else {
                    1
                };
                if let Some(value) = items.get(value_index) {
                    check_expr(value, bindings, moved, globals, false, types)?;
                }
            } else if matches!(
                head,
                "borrow" | "borrow-mut" | "pin-borrow" | "pin-borrow-mut"
            ) {
                if items.len() == 3 {
                    let owner = simple_place_name(&items[1]);
                    if let Some(owner) = owner {
                        check_expr(&items[1], bindings, moved, globals, true, types)?;
                        check_expr_with_place(
                            &items[2],
                            bindings,
                            moved,
                            globals,
                            Some(owner),
                            types,
                        )?;
                    } else {
                        check_expr(&items[1], bindings, moved, globals, false, types)?;
                        check_expr(&items[2], bindings, moved, globals, false, types)?;
                    }
                } else {
                    for arg in items.iter().skip(1) {
                        check_expr(arg, bindings, moved, globals, true, types)?;
                    }
                }
            } else if head == "ptr-offset" {
                if let Some(pointer) = items.get(1) {
                    check_expr(pointer, bindings, moved, globals, false, types)?;
                }
                if let Some(index) = items.get(2) {
                    check_expr(index, bindings, moved, globals, false, types)?;
                }
            } else if head == "addr-of"
                || head == "addr-of-mut"
                || head == "deref"
                || head == "ptr-read"
                || head == "ptr-is-null"
                || head == "ptr-borrow"
                || head == "ptr-borrow-mut"
                || head == "pin-ptr-borrow"
                || head == "pin-ptr-borrow-mut"
                || head == "ptr-write"
            {
                for arg in items.iter().skip(1) {
                    check_expr(arg, bindings, moved, globals, true, types)?;
                }
            } else {
                for arg in items.iter().skip(1) {
                    check_expr(arg, bindings, moved, globals, false, types)?;
                }
            }
        }
        Expr::List(items) => {
            for item in items {
                check_expr(item, bindings, moved, globals, false, types)?;
            }
        }
        Expr::Block(body) | Expr::Loop(body) => {
            check_scoped_statements(body, &mut bindings.clone(), moved, globals, types)?
        }
        Expr::Labeled { expression, .. }
        | Expr::Quote(expression)
        | Expr::QuasiQuote(expression)
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => {
            check_expr(expression, bindings, moved, globals, place, types)?
        }
        _ => {}
    }
    let _ = globals;
    Ok(())
}

fn simple_place_name(expr: &Expr) -> Option<&str> {
    match expr {
        Expr::Symbol(name) => Some(name),
        Expr::List(parts) if matches!(parts.first(), Some(Expr::Symbol(head)) if head == "get" || head == "get-payload") => {
            parts.get(1).and_then(|base| simple_place_name(base))
        }
        _ => None,
    }
}

fn check_clone(
    expr: &Expr,
    bindings: &HashSet<String>,
    moved: &Moves,
    types: &LinearTypes,
) -> Result<(), Error> {
    if let Some(key) = place_key(expr) {
        if (bindings.contains(place_root(&key))
            || types.binding_types.borrow().contains_key(place_root(&key)))
            && has_move_conflict(moved, &key)
        {
            return Err(
                failure!("cannot clone moved linear value '{key}'").related(moved.prior(&key))
            );
        }
    }
    Ok(())
}

fn place_key(expr: &Expr) -> Option<Place> {
    match expr {
        Expr::Symbol(name) => Some(Place::root(name)),
        Expr::List(items) if items.len() >= 3 => {
            let Expr::Symbol(head) = &items[0] else {
                return None;
            };
            let base = place_key(&items[1])?;
            match head.as_str() {
                "get" if items.len() == 3 => Some(base.project(match &items[2] {
                    Expr::Symbol(field) => Projection::Field(field.clone()),
                    Expr::Integer(index) => Projection::Tuple((*index).try_into().ok()?),
                    _ => return None,
                })),
                "index" if items.len() == 3 => Some(
                    base.project(
                        literal_index(&items[2])
                            .map(Projection::Index)
                            .unwrap_or(Projection::UnknownIndex),
                    ),
                ),
                "get-payload" if items.len() == 4 => {
                    let Expr::Symbol(variant) = &items[2] else {
                        return None;
                    };
                    Some(
                        base.project(Projection::Variant(variant.clone()))
                            .project(Projection::Tuple(literal_index(&items[3])?.parse().ok()?)),
                    )
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn literal_index(expr: &Expr) -> Option<String> {
    match expr {
        Expr::Integer(index) => Some(index.to_string()),
        Expr::UnsignedInteger(index) => Some(index.to_string()),
        Expr::List(parts) if matches!(parts.first(), Some(Expr::Symbol(head)) if head == "literal") => {
            match parts.get(2) {
                Some(Expr::Integer(index)) => Some(index.to_string()),
                Some(Expr::UnsignedInteger(index)) => Some(index.to_string()),
                _ => None,
            }
        }
        _ => None,
    }
}

fn has_move_conflict(moved: &Moves, key: &Place) -> bool {
    moved.iter().any(|existing| existing.conflicts(key))
}

fn check_scoped_statements(
    statements: &[Statement],
    bindings: &mut HashSet<String>,
    moved: &mut Moves,
    globals: &HashSet<String>,
    types: &LinearTypes,
) -> Result<(), Error> {
    let outer = bindings.clone();
    check_statements(statements, bindings, moved, globals, types)?;
    if let Some(name) = bindings
        .iter()
        .find(|name| !outer.contains(*name) && !types.binding_consumed(name, moved))
    {
        return Err(failure!("linear value '{name}' must be consumed before leaving its scope; use it, pass it to a destruction function, or explicitly (#forget {name})"));
    }
    bindings.retain(|name| outer.contains(name));
    moved.retain(|name| outer.contains(place_root(name)));
    Ok(())
}

fn require_same_consumption(
    bindings: &HashSet<String>,
    left: &Moves,
    right: &Moves,
    types: &LinearTypes,
) -> Result<(), Error> {
    for binding in bindings {
        let left_complete = types.binding_consumed(binding, left);
        let right_complete = types.binding_consumed(binding, right);
        if left_complete && right_complete {
            continue;
        }
        if left_complete != right_complete {
            return Err(failure!(
                "linear value '{binding}' must be consumed consistently on every control-flow path"
            ));
        }
        let left_places = left
            .iter()
            .filter(|place| place_root(place) == binding)
            .collect::<HashSet<_>>();
        let right_places = right
            .iter()
            .filter(|place| place_root(place) == binding)
            .collect::<HashSet<_>>();
        if left_places != right_places {
            return Err(failure!(
                "linear value '{binding}' must be consumed consistently on every control-flow path"
            ));
        }
    }
    Ok(())
}

fn place_root(place: &Place) -> &str {
    &place.binding.0
}

fn assigned_before_read(statements: &[Statement], name: &str) -> bool {
    for statement in statements {
        match statement {
            Statement::Assign {
                name: target,
                value,
            } if target == name => {
                return !expression_mentions(value, name);
            }
            Statement::Let { value, .. }
            | Statement::Destructure { value, .. }
            | Statement::LetElse { value, .. }
            | Statement::Expr(value)
            | Statement::Return(Some(value)) => {
                if expression_mentions(value, name) {
                    return false;
                }
            }
            _ => {}
        }
    }
    false
}

fn expression_mentions(expression: &Expr, name: &str) -> bool {
    match expression {
        Expr::Symbol(found) => found == name,
        Expr::List(items) => items.iter().any(|item| expression_mentions(item, name)),
        Expr::Block(statements) | Expr::Loop(statements) => {
            statements.iter().any(|statement| match statement {
                Statement::Assign {
                    name: target,
                    value,
                } => target == name || expression_mentions(value, name),
                Statement::Expr(value) | Statement::Return(Some(value)) => {
                    expression_mentions(value, name)
                }
                _ => false,
            })
        }
        Expr::Labeled { expression, .. }
        | Expr::Quote(expression)
        | Expr::QuasiQuote(expression)
        | Expr::Unquote(expression)
        | Expr::UnquoteSplicing(expression) => expression_mentions(expression, name),
        _ => false,
    }
}

fn check_expr_with_place(
    expr: &Expr,
    bindings: &HashSet<String>,
    moved: &mut Moves,
    globals: &HashSet<String>,
    borrowed_place: Option<&str>,
    types: &LinearTypes,
) -> Result<(), Error> {
    let _site = Site::expression(expr).enter();
    if let (Expr::Symbol(name), Some(place)) = (expr, borrowed_place) {
        if name == place {
            return Ok(());
        }
    }
    match expr {
        Expr::List(items) => {
            for (index, item) in items.iter().enumerate() {
                if index == 0 {
                    continue;
                }
                check_expr_with_place(item, bindings, moved, globals, borrowed_place, types)?;
            }
            Ok(())
        }
        Expr::Block(statements) => {
            check_statements(statements, &mut bindings.clone(), moved, globals, types)
        }
        Expr::Symbol(name) if bindings.contains(name) => {
            if !moved.insert(Place::root(name)) {
                Err(failure!("linear value '{name}' was used more than once; use (#clone {name}) to make an explicit copy"))
            } else {
                Ok(())
            }
        }
        _ => Ok(()),
    }
}

#[cfg(test)]
mod tests {
    use crate::{check_types, parse_program};

    #[test]
    fn places_keep_identifier_punctuation_and_dynamic_indices_structural() {
        use super::{Place, Projection};
        let dotted = Place::root("a.b");
        let field = Place::root("a").project(Projection::Field("b".into()));
        assert!(!dotted.conflicts(&field));
        let dotted_field = Place::root("a").project(Projection::Field("b.c".into()));
        let nested = field.clone().project(Projection::Field("c".into()));
        assert!(!dotted_field.conflicts(&nested));
        assert!(field.conflicts(&nested));
        let unknown = Place::root("a").project(Projection::UnknownIndex);
        let zero = Place::root("a").project(Projection::Index("0".into()));
        let one = Place::root("a").project(Projection::Index("1".into()));
        assert!(unknown.conflicts(&zero));
        assert!(!zero.conflicts(&one));
        assert!(!unknown.covers(&zero));
    }

    #[test]
    fn dotted_bindings_move_independently_of_fields_and_shadowing() {
        let source = "(#struct R ((b u64))) (#linear R)
          (#fn main () u64
            (#let a R (#struct-literal R ((b 1u64))))
            (#let a.b R (#struct-literal R ((b 2u64))))
            (#forget (#get a b)) (#forget a.b) (#forget a)
            (#let a.b-again R (#struct-literal R ((b 3u64))))
            (#forget a.b-again) (#return 0u64))";
        check_types(&parse_program(source).unwrap()).unwrap();
        let duplicate = source.replace(
            "(#forget a.b-again) (#return",
            "(#forget a.b-again) (#forget a.b-again) (#return",
        );
        assert!(check_types(&parse_program(&duplicate).unwrap()).is_err());
    }

    #[test]
    fn values_are_linear_and_clone_is_explicit() {
        let duplicate = parse_program(
            "(#struct Resource ((value u64))) (#linear Resource) (#fn consume ((value Resource)) () (#forget value) (#return ())) (#fn main () u64 (#let value Resource (#struct-literal Resource ((value 20u64)))) (#call consume (: value value)) (#call consume (: value value)) (#return 0u64))",
        ).unwrap();
        assert!(check_types(&duplicate)
            .unwrap_err()
            .contains("linear value 'value' was used more than once"));

        let cloned = parse_program(
            "(#struct Resource ((value u64))) (#fn main () u64 (#let value Resource (#struct-literal Resource ((value 20u64)))) (#forget (#clone value)) (#forget value) (#return 0u64))",
        )
        .unwrap();
        assert!(check_types(&cloned).is_ok());
    }

    #[test]
    fn cloning_a_moved_value_is_rejected() {
        let program = parse_program(
            "(#struct Resource ((value u64))) (#linear Resource) (#fn consume ((value Resource)) Resource (#return value)) (#fn inspect ((value Resource)) u64 (#forget value) (#return 0u64)) (#fn main () u64 (#let value Resource (#struct-literal Resource ((value 1u64)))) (#let moved Resource (#call consume (: value value))) (#forget moved) (#return (#call inspect (: value (#clone value)))))",
        )
        .unwrap();
        let error = check_types(&program).unwrap_err();
        assert!(
            error.contains("cannot clone moved linear value 'value'"),
            "{error}"
        );
    }

    #[test]
    fn mutable_references_cannot_be_cloned() {
        let program = parse_program(
            "(#fn main () (#ref-mut u64) (#let-mut value u64 1) (#let reference (#ref-mut u64) (#borrow-mut value)) (#return (#clone reference)))",
        )
        .unwrap();
        assert!(check_types(&program)
            .unwrap_err()
            .contains("a mutable reference cannot be cloned"));
    }

    #[test]
    fn loop_conditions_must_clone_values_that_are_reused() {
        let valid = parse_program(
            "(#fn main () u64 (#let-mut count u64 0) (#while (#u64.< (#clone count) 1) (#set count 1)) (#return count))",
        )
        .unwrap();
        assert!(check_types(&valid).is_ok());
    }

    #[test]
    fn explicit_clone_codegen_handles_aggregates() {
        let program = parse_program(
            "(#struct Pair ((left u64) (right u64))) (#fn main () u64 (#let value Pair (#struct-literal Pair ((left 20) (right 22)))) (#let duplicate Pair (#clone value)) (#let result u64 (#u64.+.wrap (#get duplicate left) (#get duplicate right))) (#forget duplicate) (#forget value) (#return result))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(crate::generate_assembly(&program).is_ok());
    }

    #[test]
    fn named_clone_functions_define_deep_clone_behavior() {
        let program = parse_program(
            "(#struct Point ((x u64))) (#fn Point-clone ((source Point)) Point (#return source)) (#fn consume ((point Point)) u64 (#let result u64 (#get point x)) (#forget point) (#return result)) (#fn main () u64 (#let value Point (#struct-literal Point ((x 4)))) (#let result u64 (#call consume (: point (#clone value)))) (#forget value) (#return result))",
        )
        .unwrap();
        assert!(check_types(&program).is_ok());
        assert!(crate::generate_assembly(&program)
            .unwrap()
            .contains("call Point_x2d_clone"));
    }

    #[test]
    fn field_values_are_moved_independently_and_can_be_cloned() {
        let duplicate = parse_program(
            "(#struct Resource ((value u64))) (#linear Resource) (#fn use ((resource Resource)) () (#forget resource) (#return ())) (#fn main () u64 (#let resource Resource (#struct-literal Resource ((value 20u64)))) (#call use (: resource resource)) (#call use (: resource resource)) (#return 0u64))",
        )
        .unwrap();
        assert!(check_types(&duplicate)
            .unwrap_err()
            .contains("linear value 'resource' was used more than once"));

        let cloned = parse_program(
            "(#struct Resource ((value u64))) (#linear Resource) (#struct Point ((x Resource) (y u64))) (#fn main () u64 (#let point Point (#struct-literal Point ((x (#struct-literal Resource ((value 20u64)))) (y 22u64)))) (#forget (#clone (#get point x))) (#forget point) (#return 0u64))",
        )
        .unwrap();
        assert!(check_types(&cloned).is_ok());
    }

    #[test]
    fn repeated_linear_field_move_highlights_the_repeated_projection() {
        let source = "(#struct Resource ((value u64)))\n(#linear Resource)\n(#struct Pair ((item Resource) (other u64)))\n(#fn main () u64\n  (#let pair Pair (#struct-literal Pair ((item (#struct-literal Resource ((value 1u64)))) (other 0u64))))\n  (#let first Resource (#get pair item))\n  (#let second Resource (#get pair item))\n  (#forget first)\n  (#forget second)\n  (#forget pair)\n  (#return 0u64))";
        let program = parse_program(source).unwrap();
        let (error, _, span, _) = crate::typecheck::check_types_with_span(&program).unwrap_err();
        assert!(error.contains("linear projection 'pair.item' was used more than once"));
        let span = span.expect("repeated projection has a structured span");
        assert_eq!(&source[span.start..span.end], "(#get pair item)");
    }

    #[test]
    fn repeated_linear_array_move_highlights_the_repeated_index() {
        let source = "(#struct Resource ((value u64)))\n(#linear Resource)\n(#fn main () u64\n  (#let values (#array Resource 2) (#array-of (#array Resource 2) (#struct-literal Resource ((value 1u64))) (#struct-literal Resource ((value 2u64)))))\n  (#let first Resource (#index values 0))\n  (#let second Resource (#index values 0))\n  (#forget first)\n  (#forget second)\n  (#forget values)\n  (#return 0u64))";
        let program = parse_program(source).unwrap();
        let (error, _, span, _) = crate::typecheck::check_types_with_span(&program).unwrap_err();
        assert!(error.contains("linear projection 'values[0]' was used more than once"));
        let span = span.expect("repeated index has a structured span");
        assert_eq!(&source[span.start..span.end], "(#index values 0)");
    }

    #[test]
    fn linear_values_must_be_consumed_before_return() {
        let leaked = parse_program(
            "(#struct Resource ((value u64))) (#linear Resource) (#fn main () u64 (#let resource Resource (#struct-literal Resource ((value 1u64)))) (#return 0u64))",
        ).unwrap();
        assert!(check_types(&leaked)
            .unwrap_err()
            .contains("must be consumed before returning"));

        let forgotten = parse_program(
            "(#struct Resource ((value u64))) (#linear Resource) (#fn main () u64 (#let resource Resource (#struct-literal Resource ((value 1u64)))) (#forget resource) (#return 0u64))",
        ).unwrap();
        assert!(check_types(&forgotten).is_ok());

        let copied =
            parse_program("(#fn main () u64 (#let number u64 1u64) (#return 0u64))").unwrap();
        assert!(check_types(&copied).is_ok());
    }

    #[test]
    fn linearity_diagnostics_point_to_the_exact_binding() {
        let source = "(#struct Resource ((value u64)))\n(#linear Resource)\n(#fn main () u64\n  (#let resource Resource (#struct-literal Resource ((value 1u64))))\n  (#return 0u64))";
        let program = parse_program(source).unwrap();
        let (_, _, span, _) = crate::typecheck::check_types_with_span(&program).unwrap_err();
        let span = span.expect("unconsumed local has a structured span");
        assert_eq!(&source[span.start..span.end], "resource");
    }

    #[test]
    fn linearity_is_checked_at_scope_exits_and_control_flow_joins() {
        let escaping = parse_program(
            "(#struct Resource ((value u64))) (#linear Resource) (#fn main () u64 (#return (#block (#let resource Resource (#struct-literal Resource ((value 1u64)))) 0u64)))",
        ).unwrap();
        assert!(check_types(&escaping)
            .unwrap_err()
            .contains("before leaving its scope"));

        let branch_leak = parse_program(
            "(#struct Resource ((value u64))) (#linear Resource) (#fn consume ((value Resource)) u64 (#forget value) (#return 1u64)) (#fn main () u64 (#let resource Resource (#struct-literal Resource ((value 1u64)))) (#return (#if true (#call consume (: value resource)) 0u64)))",
        ).unwrap();
        assert!(check_types(&branch_leak)
            .unwrap_err()
            .contains("consumed consistently on every control-flow path"));

        let both_branches_consume = parse_program(
            "(#struct Resource ((value u64))) (#linear Resource) (#fn consume ((value Resource)) u64 (#forget value) (#return 1u64)) (#fn main () u64 (#let resource Resource (#struct-literal Resource ((value 1u64)))) (#return (#if true (#call consume (: value resource)) (#call consume (: value resource)))))",
        ).unwrap();
        assert!(check_types(&both_branches_consume).is_ok());

        let different_fields = parse_program(
            "(#struct Resource ((value u64))) (#linear Resource) (#struct Pair ((left Resource) (right Resource))) (#fn main () u64 (#let pair Pair (#struct-literal Pair ((left (#struct-literal Resource ((value 1u64)))) (right (#struct-literal Resource ((value 2u64))))))) (#return (#if true (#block (#forget (#get pair left)) 1u64) (#block (#forget (#get pair right)) 2u64))))",
        ).unwrap();
        let error = check_types(&different_fields).unwrap_err();
        assert!(
            error.contains("consumed consistently on every control-flow path"),
            "{error}"
        );
    }

    #[test]
    fn consuming_all_linear_fields_discharges_struct_owner() {
        let source = "(#struct Resource ((value u64)))
          (#linear Resource)
          (#struct Pair ((item Resource) (other u64)))
          (#fn main () u64
            (#let pair Pair (#struct-literal Pair
              ((item (#struct-literal Resource ((value 1u64)))) (other 0u64))))
            (#forget (#get pair item))
            (#return 0u64))";
        let program = parse_program(source).unwrap();
        check_types(&program).unwrap();
    }

    #[test]
    fn partial_consumption_keeps_remaining_linear_fields_live() {
        let source = "(#struct Resource ((value u64)))
          (#linear Resource)
          (#struct Pair ((left Resource) (right Resource)))
          (#fn main () u64
            (#let pair Pair (#struct-literal Pair
              ((left (#struct-literal Resource ((value 1u64))))
               (right (#struct-literal Resource ((value 2u64)))))))
            (#forget (#get pair left))
            (#return 0u64))";
        let error = check_types(&parse_program(source).unwrap()).unwrap_err();
        assert!(
            error.contains("must be consumed before returning"),
            "{error}"
        );
        let complete = source.replace(
            "(#forget (#get pair left))",
            "(#forget (#get pair left)) (#forget (#get pair right))",
        );
        check_types(&parse_program(&complete).unwrap()).unwrap();
    }

    #[test]
    fn explicitly_linear_owner_is_not_discharged_by_its_fields() {
        let source = "(#struct Resource ((value u64)))
          (#linear Resource)
          (#struct Wrapper ((item Resource)))
          (#linear Wrapper)
          (#fn main () u64
            (#let wrapper Wrapper (#struct-literal Wrapper
              ((item (#struct-literal Resource ((value 1u64)))))))
            (#forget (#get wrapper item))
            (#return 0u64))";
        let error = check_types(&parse_program(source).unwrap()).unwrap_err();
        assert!(
            error.contains("must be consumed before returning"),
            "{error}"
        );
    }

    #[test]
    fn replacing_fully_consumed_owner_revives_all_fields() {
        let source = "(#struct Resource ((value u64)))
          (#linear Resource)
          (#struct Wrapper ((item Resource)))
          (#fn main () u64
            (#let-mut wrapper Wrapper (#struct-literal Wrapper
              ((item (#struct-literal Resource ((value 1u64)))))))
            (#forget (#get wrapper item))
            (#set wrapper (#struct-literal Wrapper
              ((item (#struct-literal Resource ((value 2u64)))))))
            (#forget (#get wrapper item))
            (#return 0u64))";
        check_types(&parse_program(source).unwrap()).unwrap();
    }

    #[test]
    fn nested_block_uses_same_linear_type_metadata() {
        let source = "(#struct Resource ((value u64)))
          (#linear Resource)
          (#struct Wrapper ((item Resource)))
          (#fn main () u64
            (#return (#block
              (#let wrapper Wrapper (#struct-literal Wrapper
                ((item (#struct-literal Resource ((value 1u64)))))))
              (#forget (#get wrapper item))
              0u64)))";
        check_types(&parse_program(source).unwrap()).unwrap();
    }

    #[test]
    fn copy_field_of_linear_owner_can_be_read_repeatedly() {
        let source = "(#struct Resource ((value u64)))
          (#linear Resource)
          (#struct Pair ((item Resource) (other u64)))
          (#fn main () u64
            (#let pair Pair (#struct-literal Pair
              ((item (#struct-literal Resource ((value 1u64)))) (other 2u64))))
            (#let sum u64 (#u64.+.wrap (#get pair other) (#get pair other)))
            (#forget (#get pair other))
            (#forget (#get pair other))
            (#forget (#get pair item))
            (#return sum))";
        check_types(&parse_program(source).unwrap()).unwrap();
    }

    #[test]
    fn tuple_and_array_owners_complete_by_linear_elements() {
        let tuple = "(#struct Resource ((value u64)))
          (#linear Resource)
          (#fn main () u64
            (#let pair (#tuple Resource u64)
              (#tuple (#tuple Resource u64)
                (#struct-literal Resource ((value 1u64))) 2u64))
            (#forget (#get pair 0))
            (#return 0u64))";
        check_types(&parse_program(tuple).unwrap()).unwrap();
        let array = "(#struct Resource ((value u64)))
          (#linear Resource)
          (#fn main () u64
            (#let items (#array Resource 2)
              (#array-of (#array Resource 2)
                (#struct-literal Resource ((value 1u64)))
                (#struct-literal Resource ((value 2u64)))))
            (#forget (#index items 0))
            (#forget (#index items 1))
            (#return 0u64))";
        check_types(&parse_program(array).unwrap()).unwrap();
    }

    #[test]
    fn copy_field_cannot_be_read_after_owner_is_consumed() {
        let source = "(#struct Resource ((value u64)))
          (#linear Resource)
          (#struct Pair ((item Resource) (other u64)))
          (#fn main () u64
            (#let pair Pair (#struct-literal Pair
              ((item (#struct-literal Resource ((value 1u64)))) (other 2u64))))
            (#forget pair)
            (#return (#get pair other)))";
        let error = check_types(&parse_program(source).unwrap()).unwrap_err();
        assert!(error.contains("used more than once"), "{error}");
    }

    #[test]
    fn copy_match_payload_can_be_read_repeatedly() {
        let source = "(#enum Choice ((Value u64)))
          (#fn main () u64
            (#let choice Choice (Value 3u64))
            (#return (#match choice
              (#case (Value payload) (#u64.+.wrap payload payload)))))";
        check_types(&parse_program(source).unwrap()).unwrap();
    }

    #[test]
    fn branch_join_accepts_equivalent_whole_and_fieldwise_consumption() {
        let source = "(#struct Resource ((value u64)))
          (#linear Resource)
          (#struct Wrapper ((item Resource) (copy u64)))
          (#fn main () u64
            (#let wrapper Wrapper (#struct-literal Wrapper
              ((item (#struct-literal Resource ((value 1u64)))) (copy 2u64))))
            (#return (#if true
              (#block (#forget wrapper) 1u64)
              (#block (#forget (#get wrapper item)) 2u64))))";
        check_types(&parse_program(source).unwrap()).unwrap();
    }

    #[test]
    fn branch_join_rejects_whole_against_incomplete_fields() {
        let source = "(#struct Resource ((value u64)))
          (#linear Resource)
          (#struct Pair ((left Resource) (right Resource)))
          (#fn main () u64
            (#let pair Pair (#struct-literal Pair
              ((left (#struct-literal Resource ((value 1u64))))
               (right (#struct-literal Resource ((value 2u64)))))))
            (#return (#if true
              (#block (#forget pair) 1u64)
              (#block (#forget (#get pair left)) 2u64))))";
        let error = check_types(&parse_program(source).unwrap()).unwrap_err();
        assert!(error.contains("consumed consistently"), "{error}");
    }

    #[test]
    fn branch_join_keeps_explicitly_linear_owner_obligation() {
        let source = "(#struct Resource ((value u64)))
          (#linear Resource)
          (#struct Wrapper ((item Resource)))
          (#linear Wrapper)
          (#fn main () u64
            (#let wrapper Wrapper (#struct-literal Wrapper
              ((item (#struct-literal Resource ((value 1u64)))))))
            (#return (#if true
              (#block (#forget wrapper) 1u64)
              (#block (#forget (#get wrapper item)) 2u64))))";
        let error = check_types(&parse_program(source).unwrap()).unwrap_err();
        assert!(error.contains("consumed consistently"), "{error}");
    }

    #[test]
    fn match_join_accepts_equivalent_whole_and_fieldwise_consumption() {
        let source = "(#struct Resource ((value u64)))
          (#linear Resource)
          (#struct Wrapper ((item Resource)))
          (#fn main () u64
            (#let wrapper Wrapper (#struct-literal Wrapper
              ((item (#struct-literal Resource ((value 1u64)))))))
            (#return (#match true
              (#case true (#block (#forget wrapper) 1u64))
              (#case false (#block (#forget (#get wrapper item)) 2u64)))))";
        check_types(&parse_program(source).unwrap()).unwrap();
    }

    #[test]
    fn thread_tasks_cannot_be_forgotten_instead_of_joined() {
        let program = parse_program(
            "(#fn worker ((value u64)) u64 (#return value)) (@thread-spawn (: task Task : worker worker)) (#fn main () u64 (#let result Task-spawn-result (#call Task-spawn (: value 1u64))) (#forget result) (#return 0u64))",
        ).unwrap();
        let error = check_types(&program).unwrap_err();
        assert!(
            error.contains("cannot be dropped or forgotten; match and join them"),
            "{error}"
        );
    }
}
