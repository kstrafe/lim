//! Explicit structural records, erased to ordinary fixed-layout structs before
//! semantic analysis. No value expression participates in type discovery.
use std::collections::{BTreeMap, HashMap, HashSet};

use crate::{Expr, Field, Item, Program, SourceError, SourceFile, Span, SpannedExpr as Node, Type};

const PREFIX: &str = "lim.gensym.record.";
const TEMPORARY: &str = "LimAnonymousRecordPending";

pub(crate) fn is_record(name: &str) -> bool {
    name.starts_with(PREFIX) || crate::file_access::local_name(name).starts_with(TEMPORARY)
}
/// Recognize only explicit parameter type syntax, including constructors whose
/// nested record fields have not yet been lowered. This never inspects values.
pub(crate) fn positional_type_syntax(node: &Node) -> bool {
    crate::positional_parameter_type(&node.expr).is_some()
        || matches!(
            head(node),
            "#ref"
                | "#ref-mut"
                | "#pin-ref"
                | "#pin-ref-mut"
                | "#ptr"
                | "#ptr-mut"
                | "#pin-own"
                | "#pin-shared-own"
                | "#slice"
                | "#slice-mut"
                | "#atomic"
                | "#array"
                | "#tuple"
                | "#where"
        )
}

fn symbol(node: &Node) -> &str {
    match &node.expr {
        Expr::Symbol(name) => name,
        _ => "",
    }
}
fn head(node: &Node) -> &str {
    node.children.first().map_or("", symbol)
}
fn atom(name: impl Into<String>, span: Span) -> Node {
    Node {
        expr: Expr::Symbol(name.into()),
        span,
        children: vec![].into(),
    }
}
fn list(children: Vec<Node>, span: Span) -> Node {
    Node {
        expr: Expr::List(children.iter().map(|n| n.expr.clone()).collect()),
        span,
        children: children.into(),
    }
}
fn sync(node: &mut Node) {
    if !node.children.is_empty() && matches!(node.expr, Expr::List(_)) {
        node.expr = Expr::List(node.children.iter().map(|n| n.expr.clone()).collect());
    }
}
fn error(message: impl Into<String>, span: Span) -> SourceError {
    SourceError::new(message, crate::DiagnosticCode::Type).at(span)
}
fn pairs(node: &Node) -> Result<BTreeMap<String, Node>, SourceError> {
    if !matches!(node.expr, Expr::List(_)) {
        return Err(error("anonymous record requires a field record", node.span));
    }
    let mut fields = BTreeMap::new();
    for entry in &node.children {
        if entry.children.len() != 2 {
            return Err(error(
                "record fields require explicit key/value pairs",
                entry.span,
            ));
        }
        let key = &entry.children[0];
        let name = symbol(key);
        crate::names::require(name, "value").map_err(|e| error(e, key.span))?;
        if name.starts_with('#') || name == "_" || crate::gensym::reserved(name) {
            return Err(error(
                "record fields require ordinary named identifiers; no rest patterns",
                key.span,
            ));
        }
        if fields.insert(name.into(), entry.clone()).is_some() {
            return Err(error(format!("duplicate record field '{name}'"), key.span));
        }
    }
    Ok(fields)
}

struct Lower<'a> {
    files: &'a [SourceFile],
    declarations: BTreeMap<String, Node>,
}
impl Lower<'_> {
    fn shape(&self, node: &Node) -> bool {
        matches!(node.expr, Expr::List(_))
            && !is_record(head(node))
            && (self
                .files
                .get(node.span.source_id as usize)
                .and_then(|f| f.source.as_bytes().get(node.span.start))
                == Some(&b'{')
                || node
                    .children
                    .first()
                    .is_some_and(|n| matches!(n.expr, Expr::List(_))))
    }
    fn ty(&mut self, node: &mut Node) -> Result<(), SourceError> {
        if self.shape(node) {
            let fields = pairs(node)?;
            // The empty structural product is unit. This keeps {} and ()
            // equivalent when generator syntax is represented as plain lists.
            if fields.is_empty() {
                *node = list(vec![], node.span);
                return Ok(());
            }
            let mut entries = Vec::new();
            for (_, mut field) in fields {
                self.ty(&mut field.children[1])?;
                sync(&mut field);
                entries.push(field);
            }
            let fields = list(entries, node.span);
            let spelling =
                crate::expression_source(&fields.expr).map_err(|e| error(e, node.span))?;
            // File IDs keep unresolved aliases in different source scopes apart.
            // After resolution, canonicalize() replaces this temporary identity.
            let name = format!(
                "{TEMPORARY}{}N{:032x}",
                node.span.source_id,
                crate::generator::stable_hash(spelling.as_bytes())
            );
            let declaration = list(
                vec![
                    atom("#struct", node.span),
                    atom(&name, node.span),
                    list(vec![], node.span),
                    fields,
                ],
                node.span,
            );
            if let Some(previous) = self.declarations.get(&name) {
                if previous.expr != declaration.expr {
                    return Err(error("anonymous record identity collision", node.span));
                }
            } else {
                self.declarations.insert(name.clone(), declaration);
            }
            *node = atom(name, node.span);
        } else {
            // Type constructors carry only types, except array lengths and
            // refinement predicates. Leave predicates in their own value scope.
            if head(node) == "#where" {
                if let Some(binding) = node.children.get_mut(1) {
                    if let Some(ty) = binding.children.get_mut(1) {
                        self.ty(ty)?;
                    }
                    sync(binding);
                }
            } else {
                for child in node.children.iter_mut().skip(1) {
                    self.ty(child)?;
                }
            }
            sync(node);
        }
        Ok(())
    }
    fn walk(&mut self, node: &mut Node) -> Result<(), SourceError> {
        if matches!(node.expr, Expr::Quote(_) | Expr::QuasiQuote(_))
            || matches!(head(node), "#gn" | "#gn-fn")
        {
            return Ok(());
        }
        let kind = head(node).to_owned();
        if kind == "#record-literal" {
            if node.children.len() != 3
                || !(self.shape(&node.children[1])
                    || matches!(&node.children[1].expr, Expr::List(fields) if fields.is_empty()))
            {
                return Err(error("#record-literal requires an explicit field-type record and a separate value record", node.children.first().map_or(node.span, |head| head.span)));
            }
            let declared = pairs(&node.children[1])?;
            let supplied = pairs(&node.children[2])?;
            check_field_names(
                &declared,
                &supplied,
                "literal",
                node.children[2].span,
                |name| supplied[name].children[0].span,
            )?;
            if declared.is_empty() {
                *node = list(vec![], node.span);
                return Ok(());
            }
            self.ty(&mut node.children[1])?;
            for field in &mut node.children[2].children {
                self.walk(&mut field.children[1])?;
                sync(field);
            }
            sync(&mut node.children[2]);
            node.children[0].expr = Expr::Symbol("#struct-literal".into());
            sync(node);
            return Ok(());
        }
        if matches!(kind.as_str(), "#let" | "#let-mut")
            && node.children.get(1).is_some_and(|n| {
                self.shape(n)
                    || node
                        .children
                        .get(2)
                        .is_some_and(|equal| symbol(equal) == "=")
                        && matches!(&n.expr, Expr::List(fields) if fields.is_empty())
            })
        {
            if node.children.len() != 4 || symbol(&node.children[2]) != "=" {
                return Err(error("record binding requires (#let { field = (#bind local Type); other = (#ignore Type); } = value)", node.span));
            }
            let fields = pairs(&node.children[1])?;
            if fields.is_empty() {
                let mut rhs = node.children[3].clone();
                self.walk(&mut rhs)?;
                node.children = vec![
                    node.children[0].clone(),
                    atom("_", node.children[1].span),
                    list(vec![], node.children[1].span),
                    rhs,
                ]
                .into();
                sync(node);
                return Ok(());
            }
            let mut types = Vec::new();
            let mut bindings = Vec::new();
            let mut names = HashSet::new();
            for (_, entry) in fields {
                let spec = &entry.children[1];
                let (binding, ty) = match (head(spec), spec.children.len()) {
                    ("#bind", 3) => {
                        let binding = spec.children[1].clone();
                        let name = symbol(&binding);
                        crate::names::require(name, "value").map_err(|e| error(e, binding.span))?;
                        if name == "_" || name.starts_with('#') || crate::gensym::reserved(name) {
                            return Err(error("#bind requires an ordinary local name; use #ignore explicitly", binding.span));
                        }
                        if !names.insert(name.to_owned()) {
                            return Err(error(format!("duplicate record binding '{name}'"), binding.span));
                        }
                        (binding, spec.children[2].clone())
                    }
                    ("#ignore", 2) => (atom("_", spec.span), spec.children[1].clone()),
                    _ => return Err(error("every record field requires (#bind local Type) or (#ignore Type); no defaults or rest patterns", spec.children.first().map_or(spec.span, |head| head.span))),
                };
                types.push(list(vec![entry.children[0].clone(), ty], entry.span));
                bindings.push(binding);
            }
            let mut ty = list(types, node.children[1].span);
            self.ty(&mut ty)?;
            let mut pattern = vec![ty.clone()];
            pattern.extend(bindings);
            let mut rhs = node.children[3].clone();
            self.walk(&mut rhs)?;
            node.children = vec![
                node.children[0].clone(),
                list(pattern, node.children[1].span),
                ty,
                rhs,
            ]
            .into();
            sync(node);
            return Ok(());
        }
        match kind.as_str() {
            "#dispatch-fn" => {
                if let Some(fields) = node.children.get_mut(2) {
                    for field in &mut fields.children {
                        match head(field) {
                            "#params" => {
                                if let Some(parameters) = field.children.get_mut(1) {
                                    for parameter in &mut parameters.children {
                                        if let Some(ty) = parameter.children.last_mut() {
                                            self.ty(ty)?;
                                        }
                                        sync(parameter);
                                    }
                                    sync(parameters);
                                }
                            }
                            "#returns" => {
                                if let Some(ty) = field.children.get_mut(1) {
                                    self.ty(ty)?;
                                }
                            }
                            _ => {}
                        }
                        sync(field);
                    }
                    sync(fields);
                }
            }
            "#enum-contribute" => {
                if let Some(variant) = node.children.get_mut(2) {
                    for ty in variant.children.iter_mut().skip(1) {
                        self.ty(ty)?;
                    }
                    sync(variant);
                }
            }
            "#fn" | "#unsafe-fn" | "#extern-fn" => {
                let params = if kind == "#extern-fn" { 3 } else { 2 };
                if let Some(parameters) = node.children.get_mut(params) {
                    if positional_type_syntax(parameters) {
                        self.ty(parameters)?;
                        if crate::positional_parameter_type(&parameters.expr).is_none() {
                            return Err(error(
                                "invalid explicit positional parameter type",
                                parameters.span,
                            ));
                        }
                    } else {
                        for parameter in &mut parameters.children {
                            if let Some(ty) = parameter.children.last_mut() {
                                self.ty(ty)?;
                            }
                            sync(parameter);
                        }
                        sync(parameters);
                    }
                }
                if let Some(ty) = node.children.get_mut(params + 1) {
                    self.ty(ty)?;
                }
                for child in node.children.iter_mut().skip(params + 2) {
                    self.walk(child)?;
                }
            }
            "#struct" => {
                if let Some(fields) = node.children.get_mut(3) {
                    for field in &mut fields.children {
                        if let Some(ty) = field.children.get_mut(1) {
                            self.ty(ty)?;
                        }
                        sync(field);
                    }
                    sync(fields);
                }
            }
            "#enum" => {
                if let Some(variants) = node.children.get_mut(3) {
                    for variant in &mut variants.children {
                        for ty in variant.children.iter_mut().skip(1) {
                            self.ty(ty)?;
                        }
                        sync(variant);
                    }
                    sync(variants);
                }
            }
            "#type" => {
                if let Some(ty) = node.children.get_mut(2) {
                    self.ty(ty)?;
                }
            }
            "#let" | "#let-mut" | "#const" | "#static" => {
                if node.children.len() == 4 {
                    self.ty(&mut node.children[2])?;
                    self.walk(&mut node.children[3])?;
                } else if node.children.len() == 3 && node.children[2].children.len() == 3 {
                    self.ty(&mut node.children[2].children[0])?;
                    self.walk(&mut node.children[2].children[2])?;
                    sync(&mut node.children[2]);
                }
            }
            "#array-repeat" => {
                for value in node.children.iter_mut().skip(1) {
                    self.walk(value)?;
                }
            }
            "#as" => {
                if let Some(value) = node.children.get_mut(1) {
                    self.walk(value)?;
                }
                if let Some(ty) = node.children.get_mut(2) {
                    self.ty(ty)?;
                }
            }
            "#tuple" => {
                // A contextual tuple starts with a value. Recognize an explicit
                // tuple type syntactically before lowering any of its schemas;
                // a nested tuple value must remain in expression position too.
                fn type_skeleton(lower: &Lower<'_>, node: &Node) -> Expr {
                    if lower.shape(node) {
                        Expr::Symbol("AnonymousRecordSchema".into())
                    } else if matches!(node.expr, Expr::List(_)) {
                        Expr::List(
                            node.children
                                .iter()
                                .map(|child| type_skeleton(lower, child))
                                .collect(),
                        )
                    } else {
                        node.expr.clone()
                    }
                }
                let explicit = node.children.get(1).is_some_and(|node| {
                    matches!(
                        crate::parse_type(Some(&crate::normalize_keywords(type_skeleton(
                            self, node
                        )))),
                        Ok(Type::Tuple(_))
                    )
                });
                let start = if explicit {
                    self.ty(&mut node.children[1])?;
                    2
                } else {
                    1
                };
                for value in node.children.iter_mut().skip(start) {
                    self.walk(value)?;
                }
            }
            "#size-of" | "#align-of" | "#array-of" | "#ptr-null" | "#atomic-init" | "#asm"
            | "#linux-syscall" | "#literal" => {
                if let Some(ty) = node.children.get_mut(1) {
                    self.ty(ty)?;
                }
                for value in node.children.iter_mut().skip(2) {
                    self.walk(value)?;
                }
            }
            _ => {
                for child in &mut node.children {
                    self.walk(child)?;
                }
            }
        }
        sync(node);
        Ok(())
    }
}
fn check_field_names<T, U>(
    declared: &BTreeMap<String, T>,
    supplied: &BTreeMap<String, U>,
    context: &str,
    span: Span,
    extra_span: impl Fn(&str) -> Span,
) -> Result<(), SourceError> {
    for name in declared.keys() {
        if !supplied.contains_key(name) {
            return Err(error(
                format!("record {context} is missing field '{name}'"),
                span,
            ));
        }
    }
    for name in supplied.keys() {
        if !declared.contains_key(name) {
            return Err(error(
                format!("unknown record {context} field '{name}'"),
                extra_span(name),
            ));
        }
    }
    Ok(())
}

/// Lower before file resolution so labels remain syntax and local bindings
/// enter the existing scope/alias checks in their ordinary destructuring form.
fn lower(forms: &mut Vec<Node>, files: &[SourceFile]) -> Result<(), SourceError> {
    let mut lower = Lower {
        files,
        declarations: BTreeMap::new(),
    };
    for form in forms.iter_mut() {
        lower.walk(form)?;
    }
    forms.extend(lower.declarations.into_values());
    Ok(())
}

/// The temporary namespace is checked before lowering, including quoted input.
/// Only names actually emitted by this pass may survive generator expansion.
fn temporary_symbols(node: &Node, output: &mut HashSet<String>) {
    fn visit(expr: &Expr, output: &mut HashSet<String>) {
        match expr {
            Expr::Symbol(name) if crate::file_access::local_name(name).starts_with(TEMPORARY) => {
                output.insert(name.clone());
            }
            Expr::List(parts) => {
                for part in parts {
                    visit(part, output);
                }
            }
            Expr::Quote(value)
            | Expr::QuasiQuote(value)
            | Expr::Unquote(value)
            | Expr::UnquoteSplicing(value) => visit(value, output),
            _ => {}
        }
    }
    visit(&node.expr, output);
}

pub(crate) fn temporary_names(forms: &[Node]) -> HashSet<String> {
    let mut names = HashSet::new();
    for form in forms {
        temporary_symbols(form, &mut names);
    }
    names
}

pub(crate) fn lower_source(forms: &mut Vec<Node>, files: &[SourceFile]) -> Result<(), SourceError> {
    for form in forms.iter() {
        let mut names = HashSet::new();
        temporary_symbols(form, &mut names);
        if !names.is_empty() {
            return Err(error(
                "the LimAnonymousRecordPending namespace is compiler-owned",
                form.span,
            ));
        }
    }
    lower(forms, files)
}

pub(crate) fn lower_generated(
    forms: &mut Vec<Node>,
    files: &[SourceFile],
    issued: &HashSet<String>,
) -> Result<(), SourceError> {
    for form in forms.iter() {
        let mut names = HashSet::new();
        temporary_symbols(form, &mut names);
        if !names.is_subset(issued) {
            return Err(error(
                "generator output cannot forge anonymous record type identities",
                form.span,
            ));
        }
    }
    lower(forms, files)
}

struct Canonical {
    aliases: HashMap<String, Type>,
    shapes: HashMap<String, Vec<Field>>,
    names: HashMap<String, String>,
    fields: HashMap<String, Vec<Field>>,
    active: HashSet<String>,
}
impl Canonical {
    fn ty(&mut self, ty: &Type) -> Result<Type, String> {
        Ok(match ty {
            Type::Named(name)
                if self.aliases.contains_key(name) || self.shapes.contains_key(name) =>
            {
                if !self.active.insert(name.clone()) {
                    return Err("recursive anonymous record type or alias".into());
                }
                let result = if let Some(target) = self.aliases.get(name).cloned() {
                    self.ty(&target)?
                } else if let Some(canonical) = self.names.get(name) {
                    Type::Named(canonical.clone())
                } else {
                    let mut fields = self.shapes[name].clone();
                    for field in &mut fields {
                        field.ty = self.ty(&field.ty)?;
                    }
                    let shape = format!("{fields:?}");
                    let canonical = format!(
                        "{PREFIX}{:032x}",
                        crate::generator::stable_hash(shape.as_bytes())
                    );
                    if self
                        .fields
                        .get(&canonical)
                        .is_some_and(|previous| previous != &fields)
                    {
                        return Err("anonymous record identity collision".into());
                    }
                    self.fields.insert(canonical.clone(), fields);
                    self.names.insert(name.clone(), canonical.clone());
                    Type::Named(canonical)
                };
                self.active.remove(name);
                result
            }
            Type::Reference { mutable, target } => Type::Reference {
                mutable: *mutable,
                target: Box::new(self.ty(target)?),
            },
            Type::PinnedReference { mutable, target } => Type::PinnedReference {
                mutable: *mutable,
                target: Box::new(self.ty(target)?),
            },
            Type::RawPointer { mutable, target } => Type::RawPointer {
                mutable: *mutable,
                target: Box::new(self.ty(target)?),
            },
            Type::PinOwned(t) => Type::PinOwned(Box::new(self.ty(t)?)),
            Type::PinShared(t) => Type::PinShared(Box::new(self.ty(t)?)),
            Type::Slice(t) => Type::Slice(Box::new(self.ty(t)?)),
            Type::MutableSlice(t) => Type::MutableSlice(Box::new(self.ty(t)?)),
            Type::Atomic(t) => Type::Atomic(Box::new(self.ty(t)?)),
            Type::Array(t, n) => Type::Array(Box::new(self.ty(t)?), *n),
            Type::Tuple(ts) => {
                Type::Tuple(ts.iter().map(|t| self.ty(t)).collect::<Result<_, _>>()?)
            }
            other => other.clone(),
        })
    }
}

/// Intern by sorted field names and recursively resolved field types, after
/// file aliases have acquired declaration identities. Check all occurrences
/// for private field-type access before retaining one layout declaration.
pub(crate) fn canonicalize(
    forms: &mut Vec<Node>,
    files: &[SourceFile],
    origins: &HashMap<u32, Span>,
    definitions: &HashMap<u32, Span>,
) -> Result<(), SourceError> {
    let mut canonical = Canonical {
        aliases: HashMap::new(),
        shapes: HashMap::new(),
        names: HashMap::new(),
        fields: HashMap::new(),
        active: HashSet::new(),
    };
    for form in forms.iter() {
        if !matches!(head(form), "#type" | "#struct") {
            continue;
        }
        let item = crate::parse_item(&crate::normalize_keywords(form.expr.clone()));
        match item {
            Ok(Item::TypeAlias { name, target, .. }) => {
                canonical.aliases.insert(name, target);
            }
            Ok(Item::Struct { name, fields, .. }) if is_record(&name) => {
                canonical.shapes.insert(name, fields);
            }
            _ => {}
        }
    }
    if canonical.shapes.is_empty() {
        return Ok(());
    }
    let mut names = canonical.shapes.keys().cloned().collect::<Vec<_>>();
    names.sort();
    for name in names {
        canonical.ty(&Type::Named(name.clone())).map_err(|e| {
            error(
                e,
                forms
                    .iter()
                    .find(|f| f.children.get(1).is_some_and(|n| symbol(n) == name))
                    .unwrap()
                    .span,
            )
        })?;
    }
    fn replace(node: &mut Node, names: &HashMap<String, String>) {
        if let Expr::Symbol(name) = &mut node.expr {
            if let Some(resolved) = names.get(name) {
                *name = resolved.clone();
            }
        }
        for child in &mut node.children {
            replace(child, names);
        }
        sync(node);
    }
    let mut seen = HashSet::new();
    for form in forms.iter_mut() {
        replace(form, &canonical.names);
    }
    // Check every authored type occurrence before coalescing equal layouts.
    // Otherwise an inaccessible private type could disappear with a duplicate.
    crate::library::check_record_types(forms, files, origins, definitions)?;
    forms.retain(|form| {
        if head(form) == "#struct" && form.children.get(1).is_some_and(|n| is_record(symbol(n))) {
            seen.insert(symbol(&form.children[1]).to_owned())
        } else {
            true
        }
    });
    Ok(())
}

/// Structural layouts have no private representation. Their field types still
/// pass the ordinary file capability and exported-signature visibility checks.
pub(crate) fn signature_types<'a>(
    ty: &'a Type,
    structs: &'a HashMap<String, Vec<Field>>,
) -> Vec<&'a Type> {
    match ty {
        Type::Named(name) if is_record(name) => structs
            .get(name)
            .into_iter()
            .flatten()
            .flat_map(|field| signature_types(&field.ty, structs))
            .collect(),
        Type::Reference { target, .. }
        | Type::PinnedReference { target, .. }
        | Type::RawPointer { target, .. }
        | Type::PinOwned(target)
        | Type::PinShared(target)
        | Type::Slice(target)
        | Type::MutableSlice(target)
        | Type::Atomic(target)
        | Type::Array(target, _) => signature_types(target, structs),
        Type::Tuple(types) => types
            .iter()
            .flat_map(|ty| signature_types(ty, structs))
            .collect(),
        _ => vec![ty],
    }
}

/// Recover authored annotations only for an error. Lowered patterns retain
/// their source range; interned layout declarations can come from another
/// equivalent shape, so they cannot supply a use-site diagnostic span.
fn authored_pattern(program: &Program, span: Span) -> Option<Node> {
    fn find(node: &Node, span: Span) -> Option<Node> {
        if node.span.start == span.start && node.span.end == span.end {
            return Some(node.clone());
        }
        node.children.iter().find_map(|child| find(child, span))
    }
    let file = program.source_files.get(span.source_id as usize)?;
    let mut pattern = crate::parse_source_unit(&file.source)
        .ok()?
        .iter()
        .find_map(|node| find(node, span))?;
    crate::set_source_id(&mut pattern, span.source_id);
    Some(pattern)
}
fn authored_field(program: &Program, pattern: Span, field: &str) -> Option<Node> {
    authored_pattern(program, pattern)?
        .children
        .iter()
        .find(|entry| {
            entry
                .children
                .first()
                .is_some_and(|key| symbol(key) == field)
        })
        .cloned()
}
fn annotation_span(program: &Program, pattern: Span, field: &str) -> Span {
    authored_field(program, pattern, field)
        .and_then(|entry| entry.children.get(1).cloned())
        .and_then(|spec| spec.children.last().cloned())
        .map_or(pattern, |kind| kind.span)
}

/// Enforce exhaustive, explicitly typed use of every returned field, and reject
/// wildcard destruction before the ordinary ownership passes see the pattern.
pub(crate) fn validate(program: &Program) -> Result<(), SourceError> {
    let mut aliases = HashMap::new();
    let mut structs = HashMap::new();
    for item in &program.items {
        match item {
            Item::TypeAlias { name, target, .. } => {
                aliases.insert(name.clone(), target.clone());
            }
            Item::Struct { name, fields, .. } => {
                structs.insert(name.clone(), fields.clone());
            }
            _ => {}
        }
    }
    if !structs.keys().any(|name| is_record(name)) {
        return Ok(());
    }
    let returns = program
        .items
        .iter()
        .filter_map(|item| {
            let Item::Function(function) = item else {
                return None;
            };
            let ty = crate::typed_ir::resolve_type(&function.return_type, &aliases).ok()?;
            match ty {
                Type::Named(name) if is_record(&name) => Some((function.name.clone(), name)),
                _ => None,
            }
        })
        .collect::<HashMap<_, _>>();
    let linear = crate::linearcheck::LinearTypes::from_program(program);
    fn walk(
        node: &Node,
        expected: Option<(&str, Span)>,
        program: &Program,
        aliases: &HashMap<String, Type>,
        returns: &HashMap<String, String>,
        structs: &HashMap<String, Vec<Field>>,
        linear: &crate::linearcheck::LinearTypes,
    ) -> Result<(), SourceError> {
        if matches!(node.expr, Expr::Quote(_) | Expr::QuasiQuote(_)) {
            return Ok(());
        }
        if matches!(head(node), "#let" | "#let-mut") && node.children.len() == 4 {
            let pattern = &node.children[1];
            let owner = head(pattern);
            if is_record(owner) {
                let fields = &structs[owner];
                for (binding, field) in pattern.children.iter().skip(1).zip(fields) {
                    if symbol(binding) == "_" && linear.is_linear(&field.ty) {
                        return Err(SourceError::new(format!("cannot ignore linear record field '{}'; bind and explicitly consume it", field.name), crate::DiagnosticCode::Linear).at(
                            authored_field(program, pattern.span, &field.name)
                                .and_then(|entry| entry.children.get(1).cloned())
                                .and_then(|spec| spec.children.first().cloned())
                                .map_or(binding.span, |marker| marker.span)));
                    }
                }
                return walk(
                    &node.children[3],
                    Some((owner, pattern.span)),
                    program,
                    aliases,
                    returns,
                    structs,
                    linear,
                );
            }
        }
        if head(node) == "#unsafe" && node.children.len() == 2 {
            return walk(
                &node.children[1],
                expected,
                program,
                aliases,
                returns,
                structs,
                linear,
            );
        }
        if matches!(head(node), "#call" | "#unsafe-call") {
            if let Some(actual) = node.children.get(1).and_then(|n| returns.get(symbol(n))) {
                let Some((expected, pattern_span)) = expected else {
                    return Err(error(
                        "anonymous record call results require an exhaustive typed record binding",
                        node.span,
                    ));
                };
                let wanted = structs[actual]
                    .iter()
                    .map(|f| (f.name.clone(), f))
                    .collect::<BTreeMap<_, _>>();
                let bound = structs[expected]
                    .iter()
                    .map(|f| (f.name.clone(), f))
                    .collect::<BTreeMap<_, _>>();
                check_field_names(&wanted, &bound, "pattern", pattern_span, |name| {
                    authored_field(program, pattern_span, name)
                        .and_then(|entry| entry.children.first().cloned())
                        .map_or(pattern_span, |key| key.span)
                })?;
                for (name, declared) in &bound {
                    let actual = crate::typed_ir::resolve_type(&wanted[name].ty, aliases)
                        .map_err(|message| error(message, node.span))?;
                    let declared = crate::typed_ir::resolve_type(&declared.ty, aliases).map_err(
                        |message| error(message, annotation_span(program, pattern_span, name)),
                    )?;
                    if actual != declared {
                        return Err(error(format!("record pattern field '{name}' declares {}, but the call returns {}",
                            crate::type_source(&declared), crate::type_source(&actual)),
                            annotation_span(program, pattern_span, name)));
                    }
                }
            }
        }
        for child in &node.children {
            walk(child, None, program, aliases, returns, structs, linear)?;
        }
        Ok(())
    }
    for source in program.declaration_expressions.values() {
        walk(source, None, program, &aliases, &returns, &structs, &linear)
            .map_err(|e| e.attach(&program.source_files))?;
    }
    Ok(())
}
