//! Source-role navigation. Bindings are lexical; member names are resolved
//! through explicit types, never by searching for a matching spelling.

use crate::{Expr, Program, Span, SpannedExpr as Node, Type};
use std::cell::{OnceCell, RefCell};
use std::collections::{HashMap, HashSet};

#[derive(Clone)]
struct Binding {
    spans: Vec<Span>,
    ty: Option<Type>,
}
type Scope = HashMap<String, Binding>;

fn symbol(node: &Node) -> Option<&str> {
    if let Expr::Symbol(name) | Expr::Function(name) = &node.expr {
        Some(name)
    } else {
        None
    }
}
fn head(node: &Node) -> &str {
    node.children
        .first()
        .and_then(symbol)
        .unwrap_or("")
        .trim_start_matches('#')
}
fn name_index(node: &Node) -> usize {
    if head(node) == "extern-fn" {
        2
    } else {
        1
    }
}
fn ty(node: &Node) -> Option<Type> {
    crate::parse_type(Some(&crate::normalize_keywords(node.expr.clone()))).ok()
}

pub(crate) struct Index<'a> {
    program: Option<&'a Program>,
    forms: &'a [Node],
    globals: HashMap<String, Vec<&'a Node>>,
    variants: HashMap<String, Vec<(&'a Node, &'a Node)>>,
    file: u32,
    byte: usize,
    explicit_locals: RefCell<HashSet<Span>>,
    checked_types: OnceCell<HashMap<Span, Vec<Type>>>,
}

impl<'a> Index<'a> {
    pub fn new(program: Option<&'a Program>, forms: &'a [Node], file: u32, byte: usize) -> Self {
        let mut index = Self {
            program,
            forms,
            globals: HashMap::new(),
            variants: HashMap::new(),
            file,
            byte,
            explicit_locals: RefCell::new(HashSet::new()),
            checked_types: OnceCell::new(),
        };
        if let Some(program) = program {
            for (name, nodes) in &program.declaration_occurrences {
                for node in nodes {
                    index.globals.entry(name.clone()).or_default().push(node);
                }
            }
        }
        for node in forms {
            if let Some(name) = node.children.get(name_index(node)).and_then(symbol) {
                if matches!(head(node), "gn" | "gn-fn" | "syntax" | "capability")
                    || (program.is_none()
                        && matches!(
                            head(node),
                            "theorem"
                                | "math-definition"
                                | "math-inductive"
                                | "fn"
                                | "unsafe-fn"
                                | "extern-fn"
                                | "struct"
                                | "enum"
                                | "distributed-enum"
                                | "type"
                                | "let"
                                | "let-mut"
                                | "const"
                                | "static"
                                | "thread-task"
                        ))
                {
                    index.globals.entry(name.to_owned()).or_default().push(node);
                }
            }
        }
        let signatures = index
            .globals
            .values()
            .flatten()
            .filter(|node| head(node) == "thread-task")
            .flat_map(|node| node.children.iter().skip(3))
            .filter(|node| matches!(head(node), "thread-task-spawn" | "thread-task-join"))
            .collect::<Vec<_>>();
        for signature in signatures {
            if let Some(name) = signature.children.get(1).and_then(symbol) {
                index
                    .globals
                    .entry(name.to_owned())
                    .or_insert_with(|| vec![signature]);
            }
        }
        for nodes in index.globals.values() {
            for node in nodes {
                if head(node) == "enum" {
                    if let Some(variants) = node.children.get(3) {
                        for variant in &variants.children {
                            let name = symbol(variant)
                                .or_else(|| variant.children.first().and_then(symbol));
                            if let Some(name) = name {
                                index
                                    .variants
                                    .entry(name.to_owned())
                                    .or_default()
                                    .push((node, variant));
                            }
                        }
                    }
                }
            }
        }
        index
    }

    fn contains(&self, node: &Node) -> bool {
        node.span.source_id == self.file
            && node.span.start <= self.byte
            && self.byte < node.span.end
    }
    fn scoped_name<'b>(&'b self, name: &'b str) -> &'b str {
        self.program
            .and_then(|program| program.source_files.get(self.file as usize))
            .and_then(|file| file.file_scope.as_ref())
            .and_then(|scope| scope.names.get(name))
            .map_or(name, String::as_str)
    }
    fn declaration(&self, name: &str) -> Option<&'a Node> {
        let nodes = self.globals.get(self.scoped_name(name))?;
        (nodes.len() == 1).then_some(nodes[0])
    }
    fn global(&self, name: &str) -> Vec<Span> {
        self.declaration(name)
            .and_then(|node| node.children.get(name_index(node)))
            .map(|node| vec![node.span])
            .unwrap_or_default()
    }
    fn variant(&self, name: &str) -> Option<(&'a Node, &'a Node)> {
        let nodes = self.variants.get(self.scoped_name(name))?;
        (nodes.len() == 1).then_some(nodes[0])
    }
    fn variant_target(&self, name: &str) -> Vec<Span> {
        self.variant(name)
            .map(|(_, node)| vec![node.children.first().unwrap_or(node).span])
            .unwrap_or_default()
    }
    fn variant_type(&self, name: &str) -> Option<Type> {
        let (owner, _) = self.variant(name)?;
        Some(Type::Named(symbol(owner.children.get(1)?)?.to_owned()))
    }
    fn variant_payload(&self, name: &str) -> Option<Type> {
        let (_, variant) = self.variant(name)?;
        // Explicit discriminants precede the single payload type.
        variant.children.iter().skip(1).find_map(ty)
    }
    fn expanded(&self, mut value: Type) -> Option<Type> {
        let mut seen = HashSet::new();
        loop {
            match value {
                Type::Reference { target, .. }
                | Type::PinnedReference { target, .. }
                | Type::RawPointer { target, .. }
                | Type::PinOwned(target)
                | Type::PinShared(target) => value = *target,
                Type::Named(ref name) => {
                    if !seen.insert(name.clone()) {
                        return None;
                    }
                    let alias = self.declaration(name).filter(|node| head(node) == "type");
                    if let Some(alias) = alias {
                        value = ty(alias.children.get(2)?)?;
                    } else {
                        return Some(value);
                    }
                }
                _ => return Some(value),
            }
        }
    }
    fn field(&self, owner: Type, field: &str) -> Option<(Span, Type)> {
        let Type::Named(name) = self.expanded(owner)? else {
            return None;
        };
        let declaration = self
            .declaration(&name)
            .filter(|node| head(node) == "struct")?;
        let mut found = declaration
            .children
            .get(3)?
            .children
            .iter()
            .filter(|node| node.children.first().and_then(symbol) == Some(field));
        let node = found.next()?;
        if found.next().is_some() {
            return None;
        }
        Some((node.children.first()?.span, ty(node.children.get(1)?)?))
    }
    fn field_types(&self, owner: Type) -> Vec<Type> {
        match self.expanded(owner) {
            Some(Type::Tuple(fields)) => fields,
            Some(Type::Named(name)) => self
                .declaration(&name)
                .and_then(|node| node.children.get(3))
                .map(|fields| {
                    fields
                        .children
                        .iter()
                        .filter_map(|field| field.children.get(1).and_then(ty))
                        .collect()
                })
                .unwrap_or_default(),
            _ => vec![],
        }
    }
    fn field_type_at(&self, owner: Type, index: usize) -> Option<Type> {
        match self.expanded(owner.clone())? {
            Type::Array(element, length) => (index < length).then_some(*element),
            _ => self.field_types(owner).get(index).cloned(),
        }
    }
    fn parameter(&self, callee: &str, label: &str) -> Vec<Span> {
        let Some(declaration) = self.declaration(callee) else {
            return vec![];
        };
        let Some(args) = declaration.children.get(name_index(declaration) + 1) else {
            return vec![];
        };
        let mut found = args.children.iter().filter_map(|arg| {
            let index = usize::from(head(arg) == "mut");
            let node = arg.children.get(index)?;
            (symbol(node) == Some(label)).then_some(node.span)
        });
        let Some(span) = found.next() else {
            return vec![];
        };
        if found.next().is_some() {
            vec![]
        } else {
            vec![span]
        }
    }
    fn value_type(&self, node: &Node, scope: &Scope) -> Option<Type> {
        if let Some(name) = symbol(node) {
            if let Some(binding) = scope.get(name) {
                return binding.ty.clone().or_else(|| self.checked_type(node));
            }
            if let Some(declaration) = self.declaration(name) {
                if matches!(head(declaration), "let" | "let-mut" | "const" | "static") {
                    return ty(declaration.children.get(2)?);
                }
            }
            return self.variant_type(name);
        }
        let xs = &node.children;
        let at = |i| xs.get(i).and_then(|node| self.value_type(node, scope));
        let result = match head(node) {
            "call" | "unsafe-call" => {
                let declaration = self.declaration(symbol(xs.get(1)?)?)?;
                ty(declaration.children.get(name_index(declaration) + 2)?)
            }
            "struct-literal" => Some(Type::Named(symbol(xs.get(1)?)?.to_owned())),
            "enum-literal" => self.variant_type(symbol(xs.get(1)?)?),
            "as" => ty(xs.get(2)?),
            "literal" | "array-of" | "tuple" | "ptr-null" | "word-read" | "word-take" | "asm"
            | "linux-syscall" | "atomic-init" => ty(xs.get(1)?),
            "get" => {
                let owner = at(1)?;
                if let Some(field) = xs.get(2).and_then(symbol) {
                    self.field(owner, field).map(|(_, ty)| ty)
                } else if let Expr::Integer(index) = xs.get(2)?.expr {
                    usize::try_from(index)
                        .ok()
                        .and_then(|index| self.field_type_at(owner, index))
                } else {
                    None
                }
            }
            "get-payload"
            | "pin-get-payload"
            | "pin-get-payload-mut"
            | "pin-get-payload-unchecked"
            | "pin-get-payload-unchecked-mut" => self.variant_payload(symbol(xs.get(2)?)?),
            "proof-result" => at(1).or_else(|| scope.get("\0proof-result")?.ty.clone()),
            "proof-old"
            | "deref"
            | "pin-read"
            | "ptr-read"
            | "clone"
            | "borrow"
            | "borrow-mut"
            | "pin"
            | "pin-shared"
            | "pin-borrow"
            | "pin-borrow-mut"
            | "pin-own-borrow"
            | "pin-own-borrow-mut"
            | "pin-shared-borrow"
            | "pin-shared-borrow-mut"
            | "pin-own-of"
            | "pin-share"
            | "pin-share-clone"
            | "ref-ptr"
            | "addr-of"
            | "addr-of-mut"
            | "borrow-slice"
            | "borrow-slice-mut"
            | "slice-of"
            | "slice-mut-of"
            | "slice-range"
            | "slice-mut-range" => at(1),
            "ptr-borrow" | "ptr-borrow-mut" | "pin-ptr-borrow" | "pin-ptr-borrow-mut" => at(2),
            "slice-mut-split" => {
                let kind = at(1)?;
                Some(Type::Tuple(vec![kind.clone(), kind]))
            }
            "word-view" => ty(xs.get(1)?),
            "index" | "slice-idx" | "slice-mut-idx" => match self.expanded(at(1)?)? {
                Type::Array(element, _) | Type::Slice(element) | Type::MutableSlice(element) => {
                    Some(*element)
                }
                _ => None,
            },
            "unsafe" | "block" => {
                let mut inner = scope.clone();
                for statement in xs.iter().skip(1).take(xs.len().saturating_sub(2)) {
                    self.bind_statement(statement, &mut inner);
                }
                self.value_type(xs.last()?, &inner)
            }
            "if" => {
                let left = at(2);
                let right = at(3);
                match (left, right) {
                    (Some(Type::Never), right) => right,
                    (left, Some(Type::Never)) => left,
                    (Some(left), Some(right))
                        if self.expanded(left.clone()) == self.expanded(right.clone()) =>
                    {
                        Some(left)
                    }
                    _ => None,
                }
            }
            "unreachable" | "panic" | "return" | "break" | "break-to" => Some(Type::Never),
            name => self.variant_type(name),
        };
        result.or_else(|| self.checked_type(node))
    }

    fn checked_type(&self, source: &Node) -> Option<Type> {
        let types = self.checked_types.get_or_init(|| {
            let mut types: HashMap<Span, Vec<Type>> = HashMap::new();
            if let Some(program) = self.program {
                if let Ok(declarations) =
                    crate::typecheck::resolve_program_for_analysis(program, false)
                {
                    for body in declarations.bodies.values() {
                        for node in &body.nodes {
                            if let (Some(span), Some(ty)) = (node.span, node.ty.as_ref()) {
                                let values = types.entry(span).or_default();
                                if !values.contains(ty) {
                                    values.push(ty.clone());
                                }
                            }
                        }
                    }
                }
            }
            types
        });
        let candidates = types.get(&source.span)?;
        (candidates.len() == 1).then(|| candidates[0].clone())
    }

    fn bind_pattern(
        &self,
        pattern: &Node,
        value_type: Option<Type>,
        scope: &mut Scope,
    ) -> Vec<Span> {
        if let Some(name) = symbol(pattern) {
            if name == "_" || name.starts_with('#') || matches!(name, "true" | "false") {
                return vec![];
            }
            if self.variants.contains_key(name) {
                return if self.contains(pattern) {
                    self.variant_target(name)
                } else {
                    vec![]
                };
            }
            scope
                .entry(name.to_owned())
                .and_modify(|binding| {
                    // An invalid duplicate binding must not silently select one.
                    binding.spans.clear();
                    binding.ty = None;
                })
                .or_insert(Binding {
                    spans: vec![pattern.span],
                    ty: value_type,
                });
            return if self.contains(pattern) {
                vec![pattern.span]
            } else {
                vec![]
            };
        }
        let Some(first) = pattern.children.first() else {
            return vec![];
        };
        let name = symbol(first).unwrap_or("");
        if let Some(mode) = crate::borrow_case::Mode::from_keyword(name) {
            let Some(inner) = pattern.children.get(1) else {
                return vec![];
            };
            let variant = inner
                .children
                .first()
                .and_then(symbol)
                .or_else(|| symbol(inner));
            if let Some(variant) = variant {
                if let Some(payload) = inner.children.get(1) {
                    let found = self.bind_pattern(
                        payload,
                        self.variant_payload(variant).map(|ty| mode.reference(ty)),
                        scope,
                    );
                    if !found.is_empty() {
                        return found;
                    }
                }
                if inner
                    .children
                    .first()
                    .is_some_and(|node| self.contains(node))
                    || self.contains(inner) && inner.children.is_empty()
                {
                    return self.variant_target(variant);
                }
            }
            return vec![];
        }
        if name == "#or" {
            let outer = scope.clone();
            let mut merged: Scope = Scope::new();
            let mut counts: HashMap<String, usize> = HashMap::new();
            for branch in pattern.children.iter().skip(1) {
                let mut inner = outer.clone();
                let found = self.bind_pattern(branch, value_type.clone(), &mut inner);
                if !found.is_empty() {
                    return found;
                }
                for (name, binding) in inner
                    .into_iter()
                    .filter(|(name, _)| !outer.contains_key(name))
                {
                    *counts.entry(name.clone()).or_default() += 1;
                    merged
                        .entry(name)
                        .and_modify(|existing| {
                            if existing.ty == binding.ty {
                                existing.spans.extend(&binding.spans);
                            } else {
                                existing.spans.clear();
                                existing.ty = None;
                            }
                        })
                        .or_insert(binding);
                }
            }
            let branches = pattern.children.len().saturating_sub(1);
            for (name, mut binding) in merged {
                if counts.get(&name).copied() != Some(branches) {
                    binding.spans.clear();
                    binding.ty = None;
                }
                scope.insert(name, binding);
            }
            return vec![];
        }
        if matches!(name, "#range" | "#literal") {
            return vec![];
        }
        let variant = self.variant(name);
        if self.contains(first) {
            return if variant.is_some() {
                self.variant_target(name)
            } else {
                self.global(name)
            };
        }
        for (index, child) in pattern.children.iter().skip(1).enumerate() {
            let kind = if variant.is_some() {
                (index == 0).then(|| self.variant_payload(name)).flatten()
            } else {
                value_type
                    .clone()
                    .and_then(|ty| self.field_type_at(ty, index))
            };
            let found = self.bind_pattern(child, kind, scope);
            if !found.is_empty() {
                return found;
            }
        }
        vec![]
    }
    fn bind_statement(&self, node: &Node, scope: &mut Scope) {
        if matches!(head(node), "let" | "let-mut" | "const" | "let-else") {
            if let Some(pattern) = node.children.get(1) {
                if !head(node).starts_with("let-else") && symbol(pattern).is_some() {
                    self.explicit_locals.borrow_mut().insert(pattern.span);
                }
                self.bind_let_pattern(node, pattern, scope);
            }
        }
    }
    fn bind_let_pattern(&self, node: &Node, pattern: &Node, scope: &mut Scope) -> Vec<Span> {
        let kind = node.children.get(2).and_then(ty);
        self.bind_pattern(pattern, kind, scope)
    }
    fn sequence(&self, nodes: &[Node], scope: &mut Scope, labels: &Scope) -> Vec<Span> {
        for node in nodes {
            if self.contains(node) {
                return self.walk(node, scope, labels);
            }
            if node.span.source_id == self.file && node.span.end <= self.byte {
                self.bind_statement(node, scope);
            }
        }
        vec![]
    }
    fn type_reference(&self, node: &Node) -> Vec<Span> {
        if !self.contains(node) {
            return vec![];
        }
        if let Some(name) = symbol(node) {
            return self.global(name);
        }
        for child in &node.children {
            if self.contains(child) {
                return self.type_reference(child);
            }
        }
        vec![]
    }
    fn value(&self, node: &Node, scope: &Scope) -> Vec<Span> {
        let Some(name) = symbol(node) else {
            return vec![];
        };
        if name.starts_with('#') || matches!(name, "_" | "true" | "false") {
            return vec![];
        }
        if let Some(binding) = scope.get(name) {
            return binding.spans.clone();
        }
        let global = self.global(name);
        if !global.is_empty() {
            global
        } else {
            self.variant_target(name)
        }
    }
    fn function(&self, node: &Node) -> Vec<Span> {
        let ni = name_index(node);
        let mut scope = Scope::new();
        if let Some(name) = node.children.get(ni).filter(|node| self.contains(node)) {
            return vec![name.span];
        }
        if let Some(args) = node.children.get(ni + 1) {
            for arg in &args.children {
                let index = usize::from(head(arg) == "mut");
                if let Some(name) = arg.children.get(index) {
                    self.explicit_locals.borrow_mut().insert(name.span);
                    let target = self.bind_pattern(
                        name,
                        arg.children.get(index + 1).and_then(ty),
                        &mut scope,
                    );
                    if !target.is_empty() {
                        return target;
                    }
                }
                if let Some(kind) = arg
                    .children
                    .get(index + 1)
                    .filter(|kind| self.contains(kind))
                {
                    return self.type_reference(kind);
                }
            }
        }
        if let Some(kind) = node.children.get(ni + 2).filter(|node| self.contains(node)) {
            return self.type_reference(kind);
        }
        self.sequence(
            node.children.get(ni + 3..).unwrap_or_default(),
            &mut scope,
            &Scope::new(),
        )
    }
    // Proof function operands use the canonical declaration table, never a
    // same-spelled lexical value or an arbitrary global declaration.
    fn proof_function(&self, node: &Node) -> Option<&'a Node> {
        let name = symbol(node)?;
        self.declaration(name.strip_prefix('@').unwrap_or(name))
            .filter(|node| matches!(head(node), "fn" | "unsafe-fn" | "extern-fn"))
    }
    fn proof_parameters(&self, function: &Node) -> Scope {
        let mut scope = Scope::new();
        if let Some(args) = function.children.get(name_index(function) + 1) {
            for arg in &args.children {
                let index = usize::from(head(arg) == "mut");
                if let Some(name) = arg.children.get(index) {
                    self.explicit_locals.borrow_mut().insert(name.span);
                    self.bind_pattern(name, arg.children.get(index + 1).and_then(ty), &mut scope);
                }
            }
        }
        // Result projections in contract predicates carry the function's
        // declared return type; this key cannot be a source identifier.
        scope.insert(
            "\0proof-result".to_owned(),
            Binding {
                spans: vec![],
                ty: function.children.get(name_index(function) + 2).and_then(ty),
            },
        );
        scope
    }
    // Reconstruct the lexical environment at a label without using the proof
    // cursor's byte offset: the function can live in another source file.
    fn proof_loop_scopes(
        &self,
        nodes: &[Node],
        mut scope: Scope,
        label: &str,
        found: &mut Vec<(Span, Scope)>,
    ) {
        for node in nodes {
            let xs = &node.children;
            match head(node) {
                "label" => {
                    if let Some(name) = xs.get(1).filter(|name| symbol(name) == Some(label)) {
                        found.push((name.span, scope.clone()));
                    }
                    self.proof_loop_scopes(
                        xs.get(2..).unwrap_or_default(),
                        scope.clone(),
                        label,
                        found,
                    );
                }
                "block" | "unsafe" | "loop" => {
                    self.proof_loop_scopes(&xs[1..], scope.clone(), label, found);
                }
                "while" => {
                    self.proof_loop_scopes(
                        xs.get(2..).unwrap_or_default(),
                        scope.clone(),
                        label,
                        found,
                    );
                }
                "for" => {
                    let mut inner = scope.clone();
                    if let Some(initializer) = xs.get(1) {
                        self.bind_statement(initializer, &mut inner);
                    }
                    self.proof_loop_scopes(xs.get(4..).unwrap_or_default(), inner, label, found);
                }
                "for-range" => {
                    let mut inner = scope.clone();
                    if let Some(binding) = xs.get(1) {
                        if let Some(name) = binding.children.first() {
                            self.explicit_locals.borrow_mut().insert(name.span);
                            self.bind_pattern(
                                name,
                                binding.children.get(1).and_then(ty),
                                &mut inner,
                            );
                        }
                    }
                    self.proof_loop_scopes(xs.get(4..).unwrap_or_default(), inner, label, found);
                }
                "if-let" | "while-let" => {
                    let explicit = head(node) == "if-let";
                    let mut inner = scope.clone();
                    if let Some(pattern) = xs.get(1) {
                        let kind = if explicit {
                            xs.get(2).and_then(ty)
                        } else {
                            xs.get(2).and_then(|value| self.value_type(value, &scope))
                        };
                        self.bind_pattern(pattern, kind, &mut inner);
                    }
                    let start = if explicit { 4 } else { 3 };
                    let end = if explicit { xs.len().min(5) } else { xs.len() };
                    self.proof_loop_scopes(
                        xs.get(start..end).unwrap_or_default(),
                        inner,
                        label,
                        found,
                    );
                    if explicit {
                        self.proof_loop_scopes(
                            xs.get(5..).unwrap_or_default(),
                            scope.clone(),
                            label,
                            found,
                        );
                    }
                }
                "match" => {
                    for arm in xs.iter().skip(2) {
                        let mut inner = scope.clone();
                        if let Some(pattern) = arm.children.get(1) {
                            let kind = xs.get(1).and_then(|value| self.value_type(value, &scope));
                            if matches!(
                                head(arm),
                                "case-ref" | "case-ref-mut" | "case-pin" | "case-pin-mut"
                            ) {
                                let mut wrapper = arm.clone();
                                wrapper.children = vec![arm.children[0].clone(), pattern.clone()];
                                self.bind_pattern(&wrapper, kind, &mut inner);
                            } else {
                                self.bind_pattern(pattern, kind, &mut inner);
                            }
                        }
                        self.proof_loop_scopes(
                            arm.children.get(2..).unwrap_or_default(),
                            inner,
                            label,
                            found,
                        );
                    }
                }
                "fn" | "unsafe-fn" | "extern-fn" => {}
                _ => {
                    // Each expression operand gets a fresh scope. Its own
                    // block/branch walker controls statement visibility.
                    for child in xs.iter().skip(1) {
                        self.proof_loop_scopes(
                            std::slice::from_ref(child),
                            scope.clone(),
                            label,
                            found,
                        );
                    }
                }
            }
            self.bind_statement(node, &mut scope);
        }
    }
    // Kernel terms have their own namespaces. Their types are terms, not
    // runtime Types, and bare names never fall back to global declarations.
    fn kernel_local_name<'n>(&self, node: &'n Node) -> Option<&'n str> {
        let name = symbol(node)?;
        // Source qualification may already have replaced @u with Symbol("u").
        // Preserve the authored distinction for lexical term/universe roles.
        let authored = self
            .program
            .and_then(|program| program.source_files.get(node.span.source_id as usize))
            .and_then(|file| file.source.get(node.span.start..node.span.end));
        if name.starts_with(['#', '@']) || authored.is_some_and(|text| text.starts_with(['#', '@']))
        {
            return None;
        }
        Some(name)
    }
    fn kernel_bind(&self, node: &Node, scope: &mut Scope) -> Vec<Span> {
        let Some(name) = self.kernel_local_name(node) else {
            return vec![];
        };
        self.explicit_locals.borrow_mut().insert(node.span);
        scope.insert(
            name.to_owned(),
            Binding {
                spans: vec![node.span],
                ty: None,
            },
        );
        if self.contains(node) {
            vec![node.span]
        } else {
            vec![]
        }
    }
    fn kernel_binders(&self, node: &Node, scope: &mut Scope, levels: &Scope) -> Option<Vec<Span>> {
        for binding in &node.children {
            // A binder is not in scope in its own type. Earlier binders are.
            if let Some(kind) = binding.children.get(1).filter(|kind| self.contains(kind)) {
                return Some(self.kernel_term(kind, scope, levels));
            }
            if let Some(name) = binding.children.first() {
                let found = self.kernel_bind(name, scope);
                if self.contains(name) {
                    return Some(found);
                }
            }
        }
        None
    }
    fn kernel_level(&self, node: &Node, levels: &Scope) -> Vec<Span> {
        if !self.contains(node) {
            return vec![];
        }
        if symbol(node).is_some() {
            return self
                .kernel_local_name(node)
                .and_then(|name| levels.get(name))
                .map(|binding| binding.spans.clone())
                .unwrap_or_default();
        }
        if head(node) == "pt-level-imax" && node.children.len() != 3 {
            return vec![];
        }
        if matches!(
            head(node),
            "pt-level-succ" | "pt-level-max" | "pt-level-imax"
        ) {
            for level in node
                .children
                .iter()
                .skip(1)
                .filter(|level| self.contains(level))
            {
                return self.kernel_level(level, levels);
            }
        }
        vec![]
    }
    fn kernel_levels(&self, node: &Node, levels: &Scope) -> Vec<Span> {
        node.children
            .iter()
            .find(|level| self.contains(level))
            .map(|level| self.kernel_level(level, levels))
            .unwrap_or_default()
    }
    fn kernel_proof(&self, node: &Node) -> Option<&'a Node> {
        let name = symbol(node)?;
        if name.starts_with('#') {
            return None;
        }
        self.declaration(name.strip_prefix('@').unwrap_or(name))
            .filter(|node| matches!(head(node), "theorem" | "math-definition" | "math-inductive"))
    }
    fn is_kernel_declaration(node: &Node) -> bool {
        matches!(head(node), "math-definition" | "math-inductive")
            || (head(node) == "theorem"
                && node.children.iter().skip(2).any(|clause| {
                    matches!(
                        head(clause),
                        "universes" | "parameters" | "statement" | "proof"
                    )
                }))
    }
    fn kernel_reference(&self, node: &Node, procedural: bool) -> Vec<Span> {
        self.kernel_proof(node)
            .filter(|node| Self::is_kernel_declaration(node) != procedural)
            .and_then(|node| node.children.get(1))
            .map(|name| vec![name.span])
            .unwrap_or_default()
    }
    fn kernel_constructor(&self, datatype: &Node, label: &Node) -> Vec<Span> {
        let Some(declaration) = self.kernel_proof(datatype) else {
            return vec![];
        };
        if head(declaration) != "math-inductive" {
            return vec![];
        }
        let indexed = declaration
            .children
            .get(4)
            .is_some_and(|node| head(node) == "indices");
        if indexed && !Self::kernel_indexed_shape_valid(declaration) {
            return vec![];
        }
        let constructors = if indexed {
            declaration.children.get(6)
        } else {
            declaration.children.get(5)
        };
        let Some(constructors) = constructors else {
            return vec![];
        };
        let Some(label) = symbol(label).filter(|name| !name.starts_with('#')) else {
            return vec![];
        };
        let mut found = constructors
            .children
            .iter()
            .filter_map(|ctor| ctor.children.first())
            .filter(|name| symbol(name) == Some(label));
        let Some(target) = found.next() else {
            return vec![];
        };
        if found.next().is_some() {
            vec![]
        } else {
            vec![target.span]
        }
    }
    fn kernel_identifier(name: &Node) -> Option<&str> {
        let name = symbol(name)?;
        (!name.starts_with(['#', '@'])
            && !name.contains([':', '/', '.', '@'])
            && name
                .chars()
                .next()
                .is_some_and(|c| c.is_alphabetic() || c == '_'))
        .then_some(name)
    }
    fn kernel_indexed_shape_valid(declaration: &Node) -> bool {
        let xs = &declaration.children;
        let Some(indices) = xs.get(4).filter(|n| head(n) == "indices") else {
            return false;
        };
        if xs.len() != 7 {
            return false;
        }
        let index_count = indices.children.len().saturating_sub(1);
        if !(1..=64).contains(&index_count) {
            return false;
        }
        let mut bound = std::collections::HashSet::new();
        if let Some(universes) = xs.get(2) {
            for universe in &universes.children {
                if let Some(name) = Self::kernel_identifier(universe) {
                    bound.insert(name);
                }
            }
        }
        if let Some(parameters) = xs.get(3) {
            for parameter in &parameters.children {
                if let Some(name) = parameter.children.first().and_then(Self::kernel_identifier) {
                    bound.insert(name);
                }
            }
        }
        let base = bound.clone();
        for binder in indices.children.iter().skip(1) {
            if head(binder) != "parameter" || binder.children.len() != 3 {
                return false;
            }
            let Some(name) = binder.children.get(1).and_then(Self::kernel_identifier) else {
                return false;
            };
            if !bound.insert(name) {
                return false;
            }
        }
        let Some(constructors) = xs.get(6) else {
            return false;
        };
        for ctor in &constructors.children {
            if ctor.children.len() != 3 {
                return false;
            }
            let Some(fields) = ctor.children.get(1) else {
                return false;
            };
            let mut visible = base.clone();
            for field in &fields.children {
                if field.children.len() != 2 {
                    return false;
                }
                let Some(name) = field.children.first().and_then(Self::kernel_identifier) else {
                    return false;
                };
                if !visible.insert(name) {
                    return false;
                }
            }
            if ctor.children[2].children.len() != index_count {
                return false;
            }
        }
        true
    }
    fn kernel_terms(&self, node: &Node, scope: &Scope, levels: &Scope) -> Vec<Span> {
        node.children
            .iter()
            .find(|term| self.contains(term))
            .map(|term| self.kernel_term(term, scope, levels))
            .unwrap_or_default()
    }
    fn kernel_term(&self, node: &Node, scope: &Scope, levels: &Scope) -> Vec<Span> {
        if !self.contains(node) {
            return vec![];
        }
        if symbol(node).is_some() {
            return self
                .kernel_local_name(node)
                .and_then(|name| scope.get(name))
                .map(|binding| binding.spans.clone())
                .unwrap_or_default();
        }
        let xs = &node.children;
        match head(node) {
            "pt-let" => {
                // A malformed let must not fall through to generic term roles.
                if xs.len() != 4 || head(&xs[1]) != "parameter" || xs[1].children.len() != 3 {
                    return vec![];
                }
                let parameter = &xs[1];
                let Some(name) = parameter.children.get(1) else {
                    return vec![];
                };
                let Some(identifier) = self.kernel_local_name(name).filter(|identifier| {
                    !identifier.starts_with('#')
                        && !identifier.contains([':', '/', '.', '@'])
                        && identifier
                            .chars()
                            .next()
                            .is_some_and(|character| character.is_alphabetic() || character == '_')
                }) else {
                    return vec![];
                };
                // A let binder cannot replace an existing term or universe
                // binding. Keep the declaration and body from acquiring a
                // synthetic navigation target for an invalid shadow.
                if scope.contains_key(identifier) || levels.contains_key(identifier) {
                    return vec![];
                }
                if self.contains(name) {
                    return self.kernel_bind(name, &mut scope.clone());
                }
                if let Some(ty) = parameter.children.get(2).filter(|ty| self.contains(ty)) {
                    return self.kernel_term(ty, scope, levels);
                }
                if let Some(value) = xs.get(2).filter(|value| self.contains(value)) {
                    return self.kernel_term(value, scope, levels);
                }
                let mut inner = scope.clone();
                self.kernel_bind(name, &mut inner);
                if let Some(body) = xs.get(3) {
                    return self.kernel_term(body, &inner, levels);
                }
            }
            "pt-type" | "pt-sort" => {
                if head(node) == "pt-sort" && xs.len() != 2 {
                    return vec![];
                }
                if let Some(level) = xs.get(1) {
                    return self.kernel_level(level, levels);
                }
            }
            "pt-pi" | "pt-lambda" | "pt-sigma" => {
                let mut inner = scope.clone();
                if let Some(binders) = xs.get(1) {
                    if let Some(found) = self.kernel_binders(binders, &mut inner, levels) {
                        return found;
                    }
                }
                if let Some(body) = xs.get(2) {
                    return self.kernel_term(body, &inner, levels);
                }
            }
            "pt-use" => {
                if let Some(name) = xs.get(1).filter(|name| self.contains(name)) {
                    return self.kernel_reference(name, false);
                }
                if let Some(arguments) = xs.get(2) {
                    return self.kernel_levels(arguments, levels);
                }
            }
            "pt-program" | "pt-certificate" => {
                if let Some(name) = xs.get(1).filter(|name| self.contains(name)) {
                    return self.kernel_reference(name, true);
                }
            }
            "pt-construct" | "pt-induct" => {
                if head(node) == "pt-induct"
                    && !((xs.len() == 7 && head(&xs[4]) != "indices")
                        || (xs.len() == 8 && head(&xs[4]) == "indices"))
                {
                    return vec![];
                }
                if head(node) == "pt-induct"
                    && xs.len() == 8
                    && !(2..=65).contains(&xs[4].children.len())
                {
                    return vec![];
                }
                if let Some(name) = xs.get(1).filter(|name| self.contains(name)) {
                    return self
                        .kernel_proof(name)
                        .filter(|declaration| head(declaration) == "math-inductive")
                        .and_then(|declaration| declaration.children.get(1))
                        .map(|name| vec![name.span])
                        .unwrap_or_default();
                }
                if let Some(arguments) = xs.get(2).filter(|node| self.contains(node)) {
                    return self.kernel_levels(arguments, levels);
                }
                if let Some(arguments) = xs.get(3).filter(|node| self.contains(node)) {
                    return self.kernel_terms(arguments, scope, levels);
                }
                if head(node) == "pt-construct" {
                    if let (Some(datatype), Some(label)) =
                        (xs.get(1), xs.get(4).filter(|node| self.contains(node)))
                    {
                        return self.kernel_constructor(datatype, label);
                    }
                    if let Some(fields) = xs.get(5) {
                        return self.kernel_terms(fields, scope, levels);
                    }
                } else {
                    let indexed = xs.len() == 8;
                    let (indices, motive_at, branches_at, subject_at) = if indexed {
                        (xs.get(4), 5, 6, 7)
                    } else {
                        (None, 4, 5, 6)
                    };
                    if let Some(indices) = indices.filter(|node| self.contains(node)) {
                        return self.kernel_terms(indices, scope, levels);
                    }
                    if let Some(motive) = xs.get(motive_at).filter(|node| self.contains(node)) {
                        return self.kernel_term(motive, scope, levels);
                    }
                    if let Some(branches) = xs.get(branches_at).filter(|node| self.contains(node)) {
                        return self.kernel_terms(branches, scope, levels);
                    }
                    if let Some(subject) = xs.get(subject_at) {
                        return self.kernel_term(subject, scope, levels);
                    }
                }
            }
            "pt-self-at" => {
                if xs.len() == 2 && symbol(&xs[1]).is_none() {
                    return self.kernel_terms(&xs[1], scope, levels);
                }
            }
            "pt-app" | "pt-eq" | "pt-refl" | "pt-eq-elim" | "pt-pair" | "pt-first"
            | "pt-second" | "pt-succ" | "pt-nat-induct" => {
                for operand in xs.iter().skip(1).filter(|node| self.contains(node)) {
                    return self.kernel_term(operand, scope, levels);
                }
            }
            // Numerals, builtin symbols, unknown forms and malformed operands
            // deliberately have no runtime/global navigation fallback.
            _ => {}
        }
        vec![]
    }
    fn kernel_declaration(&self, node: &Node) -> Vec<Span> {
        let xs = &node.children;
        if let Some(name) = xs.get(1).filter(|name| self.contains(name)) {
            return vec![name.span];
        }
        let mut levels = Scope::new();
        if let Some(universes) = xs.get(2) {
            for universe in &universes.children {
                let found = self.kernel_bind(universe, &mut levels);
                if self.contains(universe) {
                    return found;
                }
            }
        }
        let mut scope = Scope::new();
        if head(node) == "math-inductive" {
            let indexed = xs.get(4).is_some_and(|node| head(node) == "indices");
            if indexed && !Self::kernel_indexed_shape_valid(node) {
                return vec![];
            }
            if let Some(parameters) = xs.get(3) {
                if let Some(found) = self.kernel_binders(parameters, &mut scope, &levels) {
                    return found;
                }
            }
            if indexed {
                let mut indices = scope.clone();
                if let Some(declared) = xs.get(4) {
                    for binder in declared.children.iter().skip(1) {
                        if head(binder) != "parameter" || binder.children.len() != 3 {
                            continue;
                        }
                        if let Some(ty) = binder.children.get(2).filter(|ty| self.contains(ty)) {
                            return self.kernel_term(ty, &indices, &levels);
                        }
                        if let Some(name) = binder.children.get(1) {
                            let found = self.kernel_bind(name, &mut indices);
                            if self.contains(name) {
                                return found;
                            }
                        }
                    }
                }
            }
            let sort_at = if indexed { 5 } else { 4 };
            let constructors_at = if indexed { 6 } else { 5 };
            let mut indices = scope.clone();
            if indexed {
                if let Some(declared) = xs.get(4) {
                    for binder in declared.children.iter().skip(1) {
                        if head(binder) == "parameter" && binder.children.len() == 3 {
                            if let Some(name) = binder.children.get(1) {
                                self.kernel_bind(name, &mut indices);
                            }
                        }
                    }
                }
            }
            if let Some(sort) = xs.get(sort_at).filter(|node| self.contains(node)) {
                return self.kernel_term(sort, &indices, &levels);
            }
            if let Some(constructors) = xs.get(constructors_at) {
                for ctor in constructors
                    .children
                    .iter()
                    .filter(|node| self.contains(node))
                {
                    if let Some(name) = ctor.children.first().filter(|node| self.contains(node)) {
                        return vec![name.span];
                    }
                    let mut fields = scope.clone();
                    if let Some(binders) = ctor.children.get(1) {
                        if let Some(found) = self.kernel_binders(binders, &mut fields, &levels) {
                            return found;
                        }
                    }
                    if indexed {
                        if let Some(outputs) =
                            ctor.children.get(2).filter(|node| self.contains(node))
                        {
                            return self.kernel_terms(outputs, &fields, &levels);
                        }
                    }
                }
            }
        } else {
            for term in xs.iter().skip(3).filter(|node| self.contains(node)) {
                return self.kernel_term(term, &scope, &levels);
            }
        }
        vec![]
    }
    fn theorem(&self, node: &Node) -> Vec<Span> {
        let xs = &node.children;
        if let Some(name) = xs.get(1).filter(|name| self.contains(name)) {
            return vec![name.span];
        }
        if !Self::is_kernel_declaration(node) {
            return xs
                .get(2)
                .map(|claim| self.walk(claim, &mut Scope::new(), &Scope::new()))
                .unwrap_or_default();
        }
        let mut levels = Scope::new();
        if let Some(universes) = xs.iter().skip(2).find(|clause| head(clause) == "universes") {
            for universe in universes.children.iter().skip(1) {
                let found = self.kernel_bind(universe, &mut levels);
                if self.contains(universe) {
                    return found;
                }
            }
        }
        let mut scope = Scope::new();
        if let Some(parameters) = xs
            .iter()
            .skip(2)
            .find(|clause| head(clause) == "parameters")
        {
            for parameter in parameters
                .children
                .iter()
                .skip(1)
                .filter(|node| head(node) == "parameter")
            {
                if let Some(kind) = parameter.children.get(2).filter(|node| self.contains(node)) {
                    return self.kernel_term(kind, &scope, &levels);
                }
                if let Some(name) = parameter.children.get(1) {
                    let found = self.kernel_bind(name, &mut scope);
                    if self.contains(name) {
                        return found;
                    }
                }
            }
        }
        for clause in xs.iter().skip(2).filter(|node| self.contains(node)) {
            if matches!(head(clause), "statement" | "proof") {
                if let Some(term) = clause.children.get(1) {
                    return self.kernel_term(term, &scope, &levels);
                }
            }
        }
        vec![]
    }
    fn proof(&self, node: &Node, scope: &Scope, labels: &Scope) -> Vec<Span> {
        let xs = &node.children;
        let form = head(node);
        if form == "proof-for-all" {
            let mut inner = scope.clone();
            if let Some(bindings) = xs.get(1) {
                for binding in &bindings.children {
                    if let Some(kind) = binding.children.get(1).filter(|kind| self.contains(kind)) {
                        return self.type_reference(kind);
                    }
                    if let Some(name) = binding.children.first() {
                        self.explicit_locals.borrow_mut().insert(name.span);
                        let target = self.bind_pattern(
                            name,
                            binding.children.get(1).and_then(ty),
                            &mut inner,
                        );
                        if !target.is_empty() {
                            return target;
                        }
                    }
                }
            }
            return xs
                .get(2)
                .map(|body| self.walk(body, &mut inner, labels))
                .unwrap_or_default();
        }
        if form == "proof-with-invariants" {
            if let Some(entries) = xs.get(1).filter(|entries| self.contains(entries)) {
                for entry in &entries.children {
                    if !self.contains(entry) {
                        continue;
                    }
                    let Some(function) = entry
                        .children
                        .first()
                        .and_then(|name| self.proof_function(name))
                    else {
                        return vec![];
                    };
                    if self.contains(&entry.children[0]) {
                        return vec![function.children[name_index(function)].span];
                    }
                    let Some(label) = entry.children.get(1).and_then(symbol) else {
                        return vec![];
                    };
                    let mut found = Vec::new();
                    self.proof_loop_scopes(
                        function
                            .children
                            .get(name_index(function) + 3..)
                            .unwrap_or_default(),
                        self.proof_parameters(function),
                        label,
                        &mut found,
                    );
                    if found.len() != 1 {
                        return vec![];
                    }
                    let (span, mut inner) = found.pop().unwrap();
                    if self.contains(&entry.children[1]) {
                        return vec![span];
                    }
                    for predicate in entry
                        .children
                        .iter()
                        .skip(2)
                        .filter(|node| self.contains(node))
                    {
                        return self.walk(predicate, &mut inner, &Scope::new());
                    }
                }
                return vec![];
            }
            return xs
                .get(2)
                .map(|body| self.walk(body, &mut scope.clone(), labels))
                .unwrap_or_default();
        }
        let functions = match form {
            "proof-calls-directly" | "proof-calls-transitively" => 2,
            "proof-calls-before" | "proof-calls-when" => 3,
            "proof-no-effects" | "proof-only-unsafe" | "proof-stack-at-most" | "proof-contract" => {
                1
            }
            _ => 0,
        };
        if form == "proof-requires-validation" {
            if let Some(entry) = xs.get(1).filter(|node| self.contains(node)) {
                return self
                    .proof_function(entry)
                    .map(|function| vec![function.children[name_index(function)].span])
                    .unwrap_or_default();
            }
            for descriptor in xs.iter().skip(2).filter(|node| self.contains(node)) {
                if descriptor.children.len() != 3
                    || descriptor.children.first().and_then(symbol) != Some("#parameter-of")
                {
                    return vec![];
                }
                let Some(function) = descriptor
                    .children
                    .get(1)
                    .and_then(|name| self.proof_function(name))
                else {
                    return vec![];
                };
                if self.contains(&descriptor.children[1]) {
                    return vec![function.children[name_index(function)].span];
                }
                if self.contains(&descriptor.children[2]) {
                    let parameters = self.proof_parameters(function);
                    return symbol(&descriptor.children[2])
                        .and_then(|name| parameters.get(name))
                        .map(|binding| binding.spans.clone())
                        .unwrap_or_default();
                }
            }
            return vec![];
        }
        // calls-when's observed boolean is between its second and third functions.
        for index in 1..=functions {
            let index = if form == "proof-calls-when" && index == 3 {
                4
            } else {
                index
            };
            if let Some(operand) = xs.get(index).filter(|node| self.contains(node)) {
                return self
                    .proof_function(operand)
                    .map(|function| vec![function.children[name_index(function)].span])
                    .unwrap_or_default();
            }
        }
        match form {
            "proof-only-unsafe" => {
                if let Some(allowed) = xs.get(2).filter(|node| self.contains(node)) {
                    for entry in allowed.children.iter().filter(|node| self.contains(node)) {
                        // Builtin spellings are metadata. Unprefixed entries
                        // are canonical function boundaries, not lexical values.
                        if symbol(entry).is_some_and(|name| name.starts_with('#')) {
                            return vec![];
                        }
                        return self
                            .proof_function(entry)
                            .map(|function| vec![function.children[name_index(function)].span])
                            .unwrap_or_default();
                    }
                }
            }
            "proof-contract" => {
                let Some(function) = xs.get(1).and_then(|name| self.proof_function(name)) else {
                    return vec![];
                };
                let mut inner = self.proof_parameters(function);
                for predicate in xs.iter().skip(2).filter(|node| self.contains(node)) {
                    return self.walk(predicate, &mut inner, &Scope::new());
                }
            }
            "proof-calls-directly"
            | "proof-calls-transitively"
            | "proof-calls-before"
            | "proof-calls-when"
            | "proof-requires-validation"
            | "proof-no-effects"
            | "proof-stack-at-most"
            | "proof-allocation"
            | "proof-io"
            | "proof-global-write"
            | "proof-unsafe"
            | "proof-external"
            | "proof-asm"
            | "proof-mutation" => {}
            "proof-sorted" => {
                if let Some(comparator) = xs.get(2).filter(|node| self.contains(node)) {
                    return self
                        .proof_function(comparator)
                        .map(|function| vec![function.children[name_index(function)].span])
                        .unwrap_or_default();
                }
                if let Some(array) = xs.get(1) {
                    return self.walk(array, &mut scope.clone(), labels);
                }
            }
            _ => {
                let start = if matches!(form, "proof-no-overflow" | "proof-loop-limit") {
                    2
                } else {
                    1
                };
                for operand in xs.iter().skip(start).filter(|node| self.contains(node)) {
                    return self.walk(operand, &mut scope.clone(), labels);
                }
            }
        }
        vec![]
    }
    fn walk(&self, node: &Node, scope: &mut Scope, labels: &Scope) -> Vec<Span> {
        if !self.contains(node) {
            return vec![];
        }
        if symbol(node).is_some() {
            return self.value(node, scope);
        }
        if matches!(node.expr, Expr::Quote(_) | Expr::QuasiQuote(_)) {
            return vec![];
        }
        let xs = &node.children;
        match head(node) {
            "theorem" => return self.theorem(node),
            "math-definition" | "math-inductive" => return self.kernel_declaration(node),
            "universes" | "parameters" | "parameter" | "statement" | "proof" => return vec![],
            "proof-and"
            | "proof-or"
            | "proof-not"
            | "proof-implies"
            | "proof-calls-directly"
            | "proof-calls-transitively"
            | "proof-calls-before"
            | "proof-calls-when"
            | "proof-no-effects"
            | "proof-only-unsafe"
            | "proof-stack-at-most"
            | "proof-for-all"
            | "proof-eq"
            | "proof-requires-validation"
            | "proof-contract"
            | "proof-result"
            | "proof-old"
            | "proof-no-overflow"
            | "proof-with-invariants"
            | "proof-loop-limit"
            | "proof-sorted"
            | "proof-permutation"
            | "proof-allocation"
            | "proof-io"
            | "proof-global-write"
            | "proof-unsafe"
            | "proof-external"
            | "proof-asm"
            | "proof-mutation" => return self.proof(node, scope, labels),
            "fn" | "unsafe-fn" | "extern-fn" | "thread-task-spawn" | "thread-task-join" => {
                return self.function(node)
            }
            "gn" | "gn-fn" => return self.generator(node),
            "export" => {
                for name in xs.iter().skip(1).filter(|name| self.contains(name)) {
                    if let Some(name) = symbol(name) {
                        let target = self.global(name);
                        return if target.is_empty() {
                            self.variant_target(name)
                        } else {
                            target
                        };
                    }
                }
                return vec![];
            }
            "alias" => {
                for name in xs.iter().skip(1).filter(|name| self.contains(name)) {
                    if let Some(name) = symbol(name) {
                        let target = self.global(name);
                        return if target.is_empty() {
                            self.variant_target(name)
                        } else {
                            target
                        };
                    }
                }
                return vec![];
            }
            "syntax" => {
                if let Some(name) = xs.get(1).filter(|name| self.contains(name)) {
                    return vec![name.span];
                }
                return self.bundle(xs.get(2).unwrap_or(node));
            }
            "let" | "let-mut" | "const" | "static" | "let-else" => {
                if head(node) == "let-else" && xs.len() == 4 && head(&xs[3]) == "else" {
                    if self.contains(&xs[2]) {
                        return self.walk(&xs[2], scope, labels);
                    }
                    if self.contains(&xs[3]) {
                        return self.sequence(&xs[3].children[1..], &mut scope.clone(), labels);
                    }
                    return self.bind_let_pattern(node, &xs[1], scope);
                }
                if let Some(kind) = xs.get(2).filter(|kind| self.contains(kind)) {
                    return self.type_reference(kind);
                }
                if let Some(initializer) = xs.get(3).filter(|value| self.contains(value)) {
                    return self.walk(initializer, scope, labels);
                }
                if head(node).starts_with("let-else") {
                    if let Some(fallback) = xs
                        .get(4)
                        .filter(|node| head(node) == "else" && self.contains(node))
                    {
                        let mut inner = scope.clone();
                        if let Some(pattern) = fallback.children.get(1) {
                            let found = self.bind_let_pattern(node, pattern, &mut inner);
                            if !found.is_empty() {
                                return found;
                            }
                        }
                        return self.sequence(
                            fallback.children.get(2..).unwrap_or_default(),
                            &mut inner,
                            labels,
                        );
                    }
                    if xs
                        .get(4..)
                        .is_some_and(|nodes| nodes.iter().any(|node| self.contains(node)))
                    {
                        return self.sequence(&xs[4..], &mut scope.clone(), labels);
                    }
                }
                if let Some(pattern) = xs.get(1) {
                    if !head(node).starts_with("let-else") && symbol(pattern).is_some() {
                        self.explicit_locals.borrow_mut().insert(pattern.span);
                    }
                    return self.bind_let_pattern(node, pattern, scope);
                }
            }
            "match" => {
                if let Some(value) = xs.get(1).filter(|value| self.contains(value)) {
                    return self.walk(value, scope, labels);
                }
                for arm in xs.iter().skip(2).filter(|arm| self.contains(arm)) {
                    let raw = matches!(
                        head(arm),
                        "case" | "case-ref" | "case-ref-mut" | "case-pin" | "case-pin-mut"
                    );
                    let index = usize::from(raw);
                    let Some(pattern) = arm.children.get(index) else {
                        return vec![];
                    };
                    let mut inner = scope.clone();
                    let found = if raw && head(arm) != "case" {
                        let mut wrapper = arm.clone();
                        wrapper.children = vec![arm.children[0].clone(), pattern.clone()];
                        self.bind_pattern(
                            &wrapper,
                            xs.get(1).and_then(|node| self.value_type(node, scope)),
                            &mut inner,
                        )
                    } else {
                        self.bind_pattern(
                            pattern,
                            xs.get(1).and_then(|node| self.value_type(node, scope)),
                            &mut inner,
                        )
                    };
                    if !found.is_empty() {
                        return found;
                    }
                    return self.sequence(&arm.children[index + 1..], &mut inner, labels);
                }
                return vec![];
            }
            "if-let" | "while-let" => {
                let explicit = head(node) == "if-let";
                let value_index = if explicit { 3 } else { 2 };
                if explicit && xs.get(2).is_some_and(|node| self.contains(node)) {
                    return self.type_reference(&xs[2]);
                }
                if let Some(value) = xs.get(value_index).filter(|value| self.contains(value)) {
                    return self.walk(value, scope, labels);
                }
                let mut inner = scope.clone();
                let kind = if explicit {
                    xs.get(2).and_then(ty)
                } else {
                    xs.get(2).and_then(|value| self.value_type(value, scope))
                };
                if let Some(pattern) = xs.get(1) {
                    let found = self.bind_pattern(pattern, kind, &mut inner);
                    if !found.is_empty() {
                        return found;
                    }
                }
                if explicit {
                    if let Some(yes) = xs.get(4).filter(|node| self.contains(node)) {
                        return self.walk(yes, &mut inner, labels);
                    }
                    if let Some(no) = xs.get(5) {
                        return self.walk(no, &mut scope.clone(), labels);
                    }
                    return vec![];
                }
                return self.sequence(xs.get(3..).unwrap_or_default(), &mut inner, labels);
            }
            "for" => {
                let mut inner = scope.clone();
                if let Some(initializer) = xs.get(1) {
                    if self.contains(initializer) {
                        return self.walk(initializer, &mut inner, labels);
                    }
                    self.bind_statement(initializer, &mut inner);
                }
                for control in xs.iter().skip(2).take(2).filter(|node| self.contains(node)) {
                    return self.walk(control, &mut inner.clone(), labels);
                }
                return self.sequence(xs.get(4..).unwrap_or_default(), &mut inner, labels);
            }
            "for-range" => {
                let mut inner = scope.clone();
                if let Some(binding) = xs.get(1) {
                    if let Some(kind) = binding.children.get(1).filter(|node| self.contains(node)) {
                        return self.type_reference(kind);
                    }
                    if let Some(name) = binding.children.first() {
                        self.explicit_locals.borrow_mut().insert(name.span);
                        let found = self.bind_pattern(
                            name,
                            binding.children.get(1).and_then(ty),
                            &mut inner,
                        );
                        if !found.is_empty() {
                            return found;
                        }
                    }
                }
                for bound in xs.iter().skip(2).take(2).filter(|node| self.contains(node)) {
                    return self.walk(bound, scope, labels);
                }
                return self.sequence(xs.get(4..).unwrap_or_default(), &mut inner, labels);
            }
            "if" => {
                for child in xs.iter().skip(1).filter(|node| self.contains(node)) {
                    return self.walk(child, &mut scope.clone(), labels);
                }
                return vec![];
            }
            "while" => {
                if let Some(condition) = xs.get(1).filter(|node| self.contains(node)) {
                    return self.walk(condition, &mut scope.clone(), labels);
                }
                return self.sequence(xs.get(2..).unwrap_or_default(), &mut scope.clone(), labels);
            }
            "block" | "unsafe" | "loop" => {
                return self.sequence(&xs[1..], &mut scope.clone(), labels)
            }
            "label" => {
                let mut inner = labels.clone();
                if let Some(name) = xs.get(1).and_then(symbol) {
                    self.explicit_locals.borrow_mut().insert(xs[1].span);
                    inner.insert(
                        name.to_owned(),
                        Binding {
                            spans: vec![xs[1].span],
                            ty: None,
                        },
                    );
                }
                if xs.get(1).is_some_and(|node| self.contains(node)) {
                    return vec![xs[1].span];
                }
                return self.sequence(xs.get(2..).unwrap_or_default(), scope, &inner);
            }
            "break-to" | "continue-to" => {
                if let Some(name) = xs
                    .get(1)
                    .filter(|node| self.contains(node))
                    .and_then(symbol)
                {
                    return labels
                        .get(name)
                        .map(|binding| binding.spans.clone())
                        .unwrap_or_default();
                }
            }
            "call" | "unsafe-call" => {
                let Some(callee) = xs.get(1).and_then(symbol) else {
                    return vec![];
                };
                if self.contains(&xs[1]) {
                    return self.global(callee);
                }
                if let Some(arguments) = xs.get(2) {
                    for pair in arguments.children.iter().filter(|pair| self.contains(pair)) {
                        if let Some(value) =
                            pair.children.get(1).filter(|value| self.contains(value))
                        {
                            return self.walk(value, scope, labels);
                        }
                        if let Some(label) = pair.children.first().and_then(symbol) {
                            return self.parameter(callee, label);
                        }
                    }
                }
                return vec![];
            }
            "enum-literal" => {
                if let Some(variant) = xs.get(1).filter(|variant| self.contains(variant)) {
                    return symbol(variant)
                        .map(|name| self.variant_target(name))
                        .unwrap_or_default();
                }
                if let Some(payload) = xs.get(2).filter(|payload| self.contains(payload)) {
                    return self.walk(payload, scope, labels);
                }
                return vec![];
            }
            "struct-literal" => {
                if xs.get(1).is_some_and(|kind| self.contains(kind)) {
                    return self.type_reference(&xs[1]);
                }
                let kind = xs
                    .get(1)
                    .and_then(|node| symbol(node).map(|name| Type::Named(name.to_owned())));
                if let Some(fields) = xs.get(2) {
                    for pair in fields.children.iter().filter(|pair| self.contains(pair)) {
                        if let Some(value) =
                            pair.children.get(1).filter(|value| self.contains(value))
                        {
                            return self.walk(value, scope, labels);
                        }
                        if let (Some(kind), Some(label)) =
                            (kind.clone(), pair.children.first().and_then(symbol))
                        {
                            return self
                                .field(kind, label)
                                .map(|(span, _)| vec![span])
                                .unwrap_or_default();
                        }
                    }
                }
                return vec![];
            }
            "get" | "set-field" | "pin-set-field" | "offset-of" => {
                if let Some(field) = xs
                    .get(2)
                    .filter(|node| self.contains(node))
                    .and_then(symbol)
                {
                    let kind = if head(node) == "offset-of" {
                        xs.get(1).and_then(ty)
                    } else {
                        xs.get(1).and_then(|value| self.value_type(value, scope))
                    };
                    return kind
                        .and_then(|kind| self.field(kind, field))
                        .map(|(span, _)| vec![span])
                        .unwrap_or_default();
                }
            }
            "get-payload"
            | "set-payload"
            | "variant-is"
            | "pin-get-payload"
            | "pin-get-payload-mut"
            | "pin-get-payload-unchecked"
            | "pin-get-payload-unchecked-mut" => {
                if let Some(name) = xs
                    .get(2)
                    .filter(|node| self.contains(node))
                    .and_then(symbol)
                {
                    return self.variant_target(name);
                }
            }
            "enum-contribute" => {
                if let Some(owner) = xs
                    .get(1)
                    .filter(|node| self.contains(node))
                    .and_then(symbol)
                {
                    return self.global(owner);
                }
                if let Some(variant) = xs.get(2) {
                    if let Some(name) = symbol(variant).filter(|_| self.contains(variant)) {
                        return self.variant_target(name);
                    }
                    if let Some(name) = variant
                        .children
                        .first()
                        .filter(|node| self.contains(node))
                        .and_then(symbol)
                    {
                        return self.variant_target(name);
                    }
                    for kind in variant
                        .children
                        .iter()
                        .skip(1)
                        .filter(|node| self.contains(node))
                    {
                        return self.type_reference(kind);
                    }
                }
                return vec![];
            }
            "struct" | "enum" => {
                if xs.get(1).is_some_and(|node| self.contains(node)) {
                    return vec![xs[1].span];
                }
                if let Some(fields) = xs.get(3) {
                    for field in fields.children.iter().filter(|node| self.contains(node)) {
                        if symbol(field).is_some() {
                            return vec![field.span];
                        }
                        if field
                            .children
                            .first()
                            .is_some_and(|node| self.contains(node))
                        {
                            return vec![field.children[0].span];
                        }
                        for kind in field
                            .children
                            .iter()
                            .skip(1)
                            .filter(|node| self.contains(node))
                        {
                            return self.type_reference(kind);
                        }
                    }
                }
                return vec![];
            }
            "type" | "distributed-enum" => {
                if xs.get(1).is_some_and(|node| self.contains(node)) {
                    return vec![xs[1].span];
                }
                if let Some(kind) = xs.get(2) {
                    return self.type_reference(kind);
                }
                return vec![];
            }
            "syntax-splice" | "await" => {
                if let Some(name) = xs
                    .get(1)
                    .filter(|node| self.contains(node))
                    .and_then(symbol)
                {
                    return self.global(name);
                }
            }
            "require-generated" => {
                if let Some(producer) = xs
                    .get(2)
                    .filter(|node| self.contains(node))
                    .and_then(symbol)
                {
                    return self.global(producer);
                }
                for names in xs.iter().skip(1).take(1).chain(xs.iter().skip(3)) {
                    if self.contains(names) {
                        return self.references(names, scope);
                    }
                }
                return vec![];
            }
            "cfg-is" => return vec![],
            "capability" => {
                if xs.get(1).is_some_and(|node| self.contains(node)) {
                    return vec![xs[1].span];
                }
                for value in xs.iter().skip(2).filter(|node| self.contains(node)) {
                    return self.type_reference(value);
                }
                return vec![];
            }
            "linux-syscall" => {
                if let Some(args) = xs.get(3).filter(|node| self.contains(node)) {
                    for argument in &args.children {
                        if self.contains(argument) {
                            return self.walk(argument, scope, labels);
                        }
                    }
                    return vec![];
                }
            }
            "asm" => {
                if let Some(registers) = xs.get(2).filter(|node| self.contains(node)) {
                    for register in &registers.children {
                        if let Some(value) =
                            register.children.get(1).filter(|node| self.contains(node))
                        {
                            return self.walk(value, scope, labels);
                        }
                    }
                    return vec![];
                }
            }
            "thread-task" => {
                if xs.get(1).is_some_and(|node| self.contains(node)) {
                    return self.global(symbol(&xs[1]).unwrap_or(""));
                }
                if xs.get(2).is_some_and(|node| self.contains(node)) {
                    return self.global(symbol(&xs[2]).unwrap_or(""));
                }
            }
            _ => {}
        }
        let type_index = match head(node) {
            "as" => Some(2),
            "size-of" | "align-of" | "offset-of" | "literal" | "array-of" | "tuple"
            | "atomic-init" | "ptr-null" | "word-read" | "word-take" | "word-write"
            | "word-view" | "word-forget" | "asm" | "linux-syscall" => Some(1),
            _ => None,
        };
        if let Some(kind) = type_index
            .and_then(|index| xs.get(index))
            .filter(|node| self.contains(node))
        {
            return self.type_reference(kind);
        }
        // A constructor head is an enum variant, not an implicit function call.
        if xs.first().is_some_and(|node| self.contains(node)) {
            return self.variant_target(symbol(&xs[0]).unwrap_or(""));
        }
        let start = usize::from(xs.first().and_then(symbol).is_some());
        for child in xs.iter().skip(start).filter(|node| self.contains(node)) {
            return self.walk(child, scope, labels);
        }
        vec![]
    }

    fn references(&self, node: &Node, scope: &Scope) -> Vec<Span> {
        if !self.contains(node) {
            return vec![];
        }
        if symbol(node).is_some() {
            return self.value(node, scope);
        }
        node.children
            .iter()
            .find(|node| self.contains(node))
            .map(|node| self.references(node, scope))
            .unwrap_or_default()
    }
    fn bundle(&self, node: &Node) -> Vec<Span> {
        if !self.contains(node) || matches!(node.expr, Expr::Quote(_) | Expr::QuasiQuote(_)) {
            return vec![];
        }
        if head(node) == "syntax-splice" {
            return node
                .children
                .get(1)
                .and_then(symbol)
                .map(|name| self.global(name))
                .unwrap_or_default();
        }
        for child in &node.children {
            if self.contains(child) {
                return self.bundle(child);
            }
        }
        vec![]
    }
    fn generator(&self, node: &Node) -> Vec<Span> {
        if let Some(name) = node.children.get(1).filter(|node| self.contains(node)) {
            return vec![name.span];
        }
        let mut scope = Scope::new();
        if let Some(args) = node.children.get(2) {
            for arg in &args.children {
                let name = if symbol(arg).is_some() {
                    arg
                } else {
                    arg.children.first().unwrap_or(arg)
                };
                if let Some(name_string) = symbol(name) {
                    scope.insert(
                        name_string.to_owned(),
                        Binding {
                            spans: vec![name.span],
                            ty: None,
                        },
                    );
                }
                self.explicit_locals.borrow_mut().insert(name.span);
                if self.contains(name) {
                    return vec![name.span];
                }
                for contract in arg
                    .children
                    .iter()
                    .skip(1)
                    .filter(|node| self.contains(node))
                {
                    return self.references(contract, &scope);
                }
            }
        }
        node.children
            .get(3)
            .map(|body| self.generator_expr(body, &scope))
            .unwrap_or_default()
    }
    fn generator_expr(&self, node: &Node, scope: &Scope) -> Vec<Span> {
        if !self.contains(node) {
            return vec![];
        }
        if let Some(name) = symbol(node) {
            return scope
                .get(name)
                .map(|binding| binding.spans.clone())
                .unwrap_or_default();
        }
        if matches!(node.expr, Expr::Quote(_)) {
            return vec![];
        }
        if matches!(node.expr, Expr::QuasiQuote(_)) {
            return node
                .children
                .first()
                .map(|node| self.template(node, scope, 1))
                .unwrap_or_default();
        }
        if head(node) == "gn-for-each" {
            if let Some(input) = node.children.get(2).filter(|node| self.contains(node)) {
                return self.generator_expr(input, scope);
            }
            let mut inner = scope.clone();
            if let Some(name) = node.children.get(1) {
                self.explicit_locals.borrow_mut().insert(name.span);
                if self.contains(name) {
                    return vec![name.span];
                }
                if let Some(key) = symbol(name) {
                    inner.insert(
                        key.to_owned(),
                        Binding {
                            spans: vec![name.span],
                            ty: None,
                        },
                    );
                }
            }
            return node
                .children
                .get(3)
                .map(|node| self.generator_expr(node, &inner))
                .unwrap_or_default();
        }
        if head(node) == "gn-call" {
            if let Some(name) = node
                .children
                .get(1)
                .filter(|node| self.contains(node))
                .and_then(symbol)
            {
                return self.global(name);
            }
        }
        if !head(node).starts_with("gn-") {
            return vec![];
        }
        for child in node
            .children
            .iter()
            .skip(1)
            .filter(|node| self.contains(node))
        {
            return self.generator_expr(child, scope);
        }
        vec![]
    }
    fn template(&self, node: &Node, scope: &Scope, depth: usize) -> Vec<Span> {
        if !self.contains(node) {
            return vec![];
        }
        match node.expr {
            Expr::Unquote(_) | Expr::UnquoteSplicing(_) if depth == 1 => {
                return node
                    .children
                    .first()
                    .map(|node| self.generator_expr(node, scope))
                    .unwrap_or_default()
            }
            Expr::Unquote(_) | Expr::UnquoteSplicing(_) => {
                return node
                    .children
                    .first()
                    .map(|node| self.template(node, scope, depth - 1))
                    .unwrap_or_default()
            }
            Expr::QuasiQuote(_) => {
                return node
                    .children
                    .first()
                    .map(|node| self.template(node, scope, depth + 1))
                    .unwrap_or_default()
            }
            Expr::Quote(_) => return vec![],
            _ => {}
        }
        for child in &node.children {
            if self.contains(child) {
                return self.template(child, scope, depth);
            }
        }
        vec![]
    }
    fn source_form(&self, node: &Node) -> Vec<Span> {
        if !self.contains(node) {
            return vec![];
        }
        if matches!(node.expr, Expr::Quote(_) | Expr::QuasiQuote(_)) {
            return vec![];
        }
        if matches!(
            node.children.first().map(|node| &node.expr),
            Some(Expr::Generate)
        ) {
            // Literal generator arguments are data. Explicit function syntax
            // inside them still has lexical binding/type roles of its own.
            for child in node.children.iter().skip(2) {
                let found = self.nested_function(child);
                if !found.is_empty() {
                    return found;
                }
            }
            return vec![];
        }
        self.walk(node, &mut Scope::new(), &Scope::new())
    }
    fn nested_function(&self, node: &Node) -> Vec<Span> {
        if !self.contains(node) || matches!(node.expr, Expr::Quote(_) | Expr::QuasiQuote(_)) {
            return vec![];
        }
        if matches!(head(node), "fn" | "unsafe-fn") {
            return self.function(node);
        }
        for child in &node.children {
            let found = self.nested_function(child);
            if !found.is_empty() {
                return found;
            }
        }
        vec![]
    }
    pub fn resolve(&self) -> Vec<Span> {
        // Qualification is a source operation, even inside otherwise literal
        // generator arguments and templates. Navigate the resolved identifier,
        // not a same-spelled generator parameter or runtime local.
        fn qualified(index: &Index<'_>, node: &Node) -> Option<Vec<Span>> {
            if Index::is_kernel_declaration(node) || head(node) == "proof-requires-validation" {
                // Validation selectors have exact contextual roles too. An
                // @name inside a malformed selector must not bypass them.
                return None;
            }
            if !index.contains(node) {
                return None;
            }
            if let Some(name) = symbol(node) {
                if index
                    .program
                    .and_then(|program| program.source_files.get(node.span.source_id as usize))
                    .and_then(|file| file.source.get(node.span.start..node.span.end))
                    .is_some_and(|text| text.starts_with('@'))
                {
                    return Some(index.global(name.strip_prefix('@').unwrap_or(name)));
                }
            }
            node.children
                .iter()
                .find_map(|child| qualified(index, child))
        }
        for node in self.forms {
            if let Some(targets) = qualified(self, node) {
                return targets;
            }
        }
        let mut result = vec![];
        for node in self.forms {
            result.extend(self.source_form(node));
        }
        if let Some(program) = self.program {
            // Generated editor snapshots have no corresponding handwritten form.
            if result.is_empty() {
                for node in program.declaration_expressions.values() {
                    if node.span.source_id == self.file {
                        result.extend(self.source_form(node));
                    }
                }
            }
        }
        result.sort_by_key(|span| (span.source_id, span.start, span.end));
        result.dedup();
        result
    }

    /// Explicit lexical binders need no generation or whole-program analysis.
    /// Pattern symbols may denote generated fieldless variants, so those stay
    /// on the semantic path rather than guessing they are local bindings.
    pub fn resolve_lexical(&self) -> Vec<Span> {
        self.resolve()
            .into_iter()
            .filter(|span| self.explicit_locals.borrow().contains(span))
            .collect()
    }
}
