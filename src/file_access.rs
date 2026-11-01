//! File-local spellings resolve to canonical file/declaration identities.
//! This changes syntax in memory, never copies or rewrites library source.
use crate::{Expr, SourceError, SourceFile, Span, SpannedExpr as Node};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::sync::Arc;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct FileScope {
    pub names: HashMap<String, String>,
    pub exports: HashSet<String>,
    pub declaration_access: HashSet<String>,
    pub declared: HashSet<String>,
    pub required: HashMap<String, Span>,
}

pub(crate) fn split(name: &str) -> Option<(&str, &str)> {
    if crate::gensym::reserved(name) {
        return None;
    }
    let index = name.find(".lim::")?;
    let (path, suffix) = name.split_at(index + 4);
    let name = &suffix[2..];
    (!path.is_empty() && !name.is_empty()).then_some((path, name))
}

pub(crate) fn local_name(name: &str) -> &str {
    split(name).map_or(name, |(_, name)| name)
}

fn symbol(node: &Node) -> Option<&str> {
    match &node.expr {
        Expr::Symbol(name) | Expr::String(name) => Some(name),
        _ => None,
    }
}
fn head(node: &Node) -> &str {
    node.children.first().and_then(symbol).unwrap_or("")
}

pub(crate) fn target(node: &Node) -> Result<Option<(String, String, bool)>, SourceError> {
    if head(node) == "#unstable" {
        if node.children.len() != 2 {
            return Err(SourceError::from(
                "#unstable requires exactly one file declaration target",
            )
            .at(node.span));
        }
        let Some((path, name, _)) = target(&node.children[1])? else {
            return Err(
                SourceError::from("#unstable requires a path.lim::declaration target")
                    .at(node.span),
            );
        };
        return Ok(Some((path, name, true)));
    }
    Ok(symbol(node).and_then(|name| {
        let name = name.strip_prefix('@').unwrap_or(name);
        split(name).map(|(path, name)| (path.to_owned(), name.to_owned(), false))
    }))
}

fn alias(node: &Node) -> Result<Option<(&str, &Node)>, SourceError> {
    if head(node) != "#alias" {
        return Ok(None);
    }
    if node.children.len() != 4 || symbol(&node.children[2]) != Some("=") {
        return Err(SourceError::from(
            "#alias expects (#alias local-name = path.lim::declaration)",
        )
        .at(node.span));
    }
    let name = match &node.children[1].expr {
        Expr::Symbol(name) if !name.starts_with(['#', '@']) && name != "_" && name != "=" => {
            name.as_str()
        }
        _ => {
            return Err(
                SourceError::from("#alias requires an ordinary local identifier")
                    .at(node.children[1].span),
            )
        }
    };
    if target(&node.children[3])?.is_none() {
        return Err(SourceError::from(
            "#alias target must be path.lim::declaration, optionally wrapped in #unstable",
        )
        .at(node.children[3].span));
    }
    Ok(Some((name, &node.children[3])))
}

pub(crate) fn check_path(from: &Path, to: &Path) -> Result<(), String> {
    if crate::library::owner(from) != crate::library::owner(to) {
        crate::library::check_import(from, to, true)?;
    }
    Ok(())
}

pub(crate) fn dependencies(
    node: &Node,
    result: &mut Vec<(String, bool, Span)>,
) -> Result<(), SourceError> {
    if matches!(
        node.children.first().map(|node| &node.expr),
        Some(Expr::Generate)
    ) && !node
        .children
        .get(1)
        .and_then(symbol)
        .is_some_and(|name| crate::generator::builtins::named_builtin_keys(name).is_some())
    {
        if let Some(generator) = node.children.get(1) {
            dependencies(generator, result)?;
        }
        fn marked(node: &Node, result: &mut Vec<(String, bool, Span)>) -> Result<(), SourceError> {
            if matches!(&node.expr, Expr::Symbol(name) if name.starts_with('@')) {
                return dependencies(node, result);
            }
            for child in &node.children {
                marked(child, result)?;
            }
            Ok(())
        }
        for input in node.children.iter().skip(2) {
            marked(input, result)?;
        }
        return Ok(());
    }
    if head(node) == "#alias" {
        if let Some(value) = node.children.get(3) {
            if let Some((path, _, unstable)) = target(value)? {
                result.push((path, unstable, value.span));
            }
        }
        return Ok(());
    }
    if let Some((path, _, unstable)) = target(node)? {
        // String literals are data except in the explicitly declared alias target.
        if !matches!(node.expr, Expr::String(_)) || head(node) == "#unstable" {
            result.push((path, unstable, node.span));
        }
        return Ok(());
    }
    for child in &node.children {
        dependencies(child, result)?;
    }
    Ok(())
}

pub(crate) fn with_dependencies(forms: Vec<Node>) -> Result<Vec<Node>, SourceError> {
    let mut result = Vec::new();
    for form in forms {
        let mut dependencies = Vec::new();
        if let Some((_, value)) = alias(&form)? {
            let (path, _, unstable) = target(value)?.unwrap();
            dependencies.push((path, unstable, value.span));
        } else {
            self::dependencies(&form, &mut dependencies)?;
        }
        for (path, unstable, span) in dependencies {
            let mut parts = vec![Expr::Symbol("$lim-file-import".into()), Expr::String(path)];
            if unstable {
                parts.push(Expr::Symbol("#unstable".into()));
            }
            result.push(Node {
                expr: Expr::List(parts),
                span,
                children: vec![],
            });
        }
        result.push(form);
    }
    Ok(result)
}

fn identity(file: &SourceFile, name: &str, root: bool) -> String {
    if root && name == "main" || name.starts_with('#') || crate::gensym::reserved(name) {
        return name.into();
    }
    let mut path = String::new();
    for byte in crate::editor::path_key(&file.path)
        .to_string_lossy()
        .bytes()
    {
        if byte.is_ascii_alphanumeric() || b"/._-".contains(&byte) {
            path.push(byte as char);
        } else {
            path.push_str(&format!("%{byte:02X}"));
        }
    }
    if !path.ends_with(".lim") {
        path.push_str(".lim");
    }
    format!("{path}::{name}")
}

fn original_id(mut source: u32, origins: &HashMap<u32, Span>) -> u32 {
    for _ in 0..=origins.len() {
        match origins.get(&source) {
            Some(parent) => source = parent.source_id,
            None => return source,
        }
    }
    source
}

struct Resolver<'a> {
    files: &'a [SourceFile],
    names: Vec<HashMap<String, String>>,
    aliases: Vec<HashMap<String, (usize, String, Span, bool)>>,
    imports: Vec<Vec<usize>>,
    exports: Vec<Vec<String>>,
    declared: Vec<HashSet<String>>,
    memo: RefCell<HashMap<(usize, String), Option<String>>>,
}

impl Resolver<'_> {
    fn file(&self, from: usize, path: &str) -> Result<usize, String> {
        let mut decoded = Vec::new();
        let bytes = path.as_bytes();
        let mut at = 0;
        while at < bytes.len() {
            if bytes[at] == b'%' && at + 2 < bytes.len() {
                if let (Some(high), Some(low)) = (
                    (bytes[at + 1] as char).to_digit(16),
                    (bytes[at + 2] as char).to_digit(16),
                ) {
                    decoded.push((high * 16 + low) as u8);
                    at += 3;
                    continue;
                }
            }
            decoded.push(bytes[at]);
            at += 1;
        }
        let decoded = String::from_utf8(decoded).unwrap_or_else(|_| path.into());
        for path in [path, decoded.as_str()] {
            let candidate = crate::editor::path_key(
                &self.files[from]
                    .path
                    .parent()
                    .unwrap_or(Path::new("."))
                    .join(path),
            );
            let same_library =
                crate::library::owner(&candidate) == crate::library::owner(&self.files[from].path);
            let prefix = if same_library {
                self.files[from].import_prefix.as_str()
            } else {
                ""
            };
            if let Some(id) = self.files.iter().position(|file| {
                crate::editor::path_key(&file.path) == candidate && file.import_prefix == prefix
            }) {
                return Ok(id);
            }
        }
        Err(format!(
            "file reference '{path}' was not loaded before generation"
        ))
    }

    fn lookup(
        &self,
        file: usize,
        name: &str,
        active: &mut Vec<(usize, String)>,
    ) -> Result<Option<String>, String> {
        if active.len() >= 128 {
            return Err("file alias resolution exceeds maximum depth of 128".into());
        }
        let key = (file, name.to_owned());
        if active.contains(&key) {
            return Err(format!("cyclic file alias involving '{name}'"));
        }
        if let Some(value) = self.names[file].get(name) {
            return Ok(Some(value.clone()));
        }
        if let Some(value) = self.memo.borrow().get(&key).cloned() {
            return Ok(value);
        }
        active.push(key.clone());
        let result = if let Some((target, name, _, _)) = self.aliases[file].get(name) {
            self.lookup(*target, name, active)?
                .or_else(|| Some(identity(&self.files[*target], name, *target == 0)))
        } else if let Some((owner, variant)) = name.split_once('.') {
            self.lookup(file, owner, active)?
                .map(|owner| format!("{owner}.{variant}"))
        } else if let Some((owner, suffix)) = name.split_once("::") {
            self.lookup(file, owner, active)?
                .map(|owner| format!("{owner}::{suffix}"))
        } else {
            let mut found = None;
            for imported in &self.imports[file] {
                if let Some(value) = self.lookup(*imported, name, active)? {
                    if found.as_ref().is_some_and(|previous| previous != &value) {
                        return Err(format!(
                            "ambiguous imported name '{name}'; use an explicit #alias"
                        ));
                    }
                    found = Some(value);
                }
            }
            found
        };
        self.memo.borrow_mut().insert(key, result.clone());
        active.pop();
        Ok(result)
    }

    fn reference(&self, file: usize, node: &Node) -> Result<Option<String>, SourceError> {
        let Some((path, name, unstable)) = target(node)? else {
            return Ok(None);
        };
        let to = self
            .file(file, &path)
            .map_err(|message| SourceError::from(message).at(node.span))?;
        let resolved_generated =
            node.span.source_id as usize != file && Path::new(&path).is_absolute();
        if !unstable && !resolved_generated {
            check_path(&self.files[file].path, &self.files[to].path)
                .map_err(|message| SourceError::from(message).at(node.span))?;
            if crate::library::owner(&self.files[file].path)
                != crate::library::owner(&self.files[to].path)
                && crate::library::owner(&self.files[to].path).is_some()
                && !self.exports[to]
                    .iter()
                    .any(|export| export == name.split('.').next().unwrap_or(&name))
            {
                return Err(SourceError::from(format!(
                    "'{name}' is private; it is not exported by '{}'",
                    self.files[to].path.display()
                ))
                .at(node.span));
            }
        }
        self.lookup(to, &name, &mut Vec::new())
            .map(|value| Some(value.unwrap_or_else(|| identity(&self.files[to], &name, to == 0))))
            .map_err(|message| SourceError::from(message).at(node.span))
    }

    fn rewrite(
        &self,
        node: &mut Node,
        file: usize,
        locals: &HashSet<String>,
    ) -> Result<(), SourceError> {
        if matches!(node.expr, Expr::String(_)) {
            return Ok(());
        }
        if node.children.is_empty() {
            if let Expr::List(items) = &node.expr {
                node.children = items
                    .iter()
                    .map(|expr| Node {
                        expr: expr.clone(),
                        span: node.span,
                        children: vec![],
                    })
                    .collect();
            }
        }
        if matches!(&node.expr, Expr::Symbol(name) if split(name.trim_start_matches('@')).is_some_and(|(path, _)| Path::new(path).is_absolute()))
            && self.files.iter().any(|file| file.file_scope.is_some())
        {
            return Ok(());
        }
        if let Some(name) = self.reference(file, node)? {
            let marked = matches!(&node.expr, Expr::Symbol(name) if name.starts_with('@'));
            if head(node) == "#unstable" {
                node.span = node.children[1].span;
            }
            node.expr = Expr::Symbol(if marked { format!("@{name}") } else { name });
            node.children.clear();
            return Ok(());
        }
        if let Expr::Symbol(name) = &mut node.expr {
            if name.starts_with('#') {
                return Ok(());
            }
            let marked = name.starts_with('@');
            let plain = name.strip_prefix('@').unwrap_or(name);
            if marked || !locals.contains(plain) {
                if let Some(value) = self
                    .lookup(file, plain, &mut Vec::new())
                    .map_err(|message| SourceError::from(message).at(node.span))?
                {
                    *name = if marked { format!("@{value}") } else { value };
                }
            }
            return Ok(());
        }
        if head(node) == "#alias" && locals.contains("#file-template") {
            if let Some(value) = node.children.get_mut(3) {
                if let Some(name) = self.reference(file, value)? {
                    value.expr = Expr::Symbol(name);
                    value.children.clear();
                }
            }
            return rebuild(node);
        }
        if let Some((name, value)) = alias(node)? {
            if split(name).is_some() {
                return Ok(());
            }
            let value = self.reference(file, value)?.unwrap();
            let mut key = node.children[1].clone();
            if !locals.contains("#file-template") {
                key.expr = Expr::Symbol(value.clone());
            }
            let mut target = node.children[3].clone();
            if head(&target) == "#unstable" {
                target.span = target.children[1].span;
            }
            target.expr = Expr::Symbol(value);
            target.children.clear();
            node.children[1] = key;
            node.children[3] = target;
            return rebuild(node);
        }
        let kind = head(node).to_owned();
        let mut inner = locals.clone();
        if matches!(
            kind.as_str(),
            "#fn" | "#unsafe-fn" | "#extern-fn" | "#gn" | "#gn-fn"
        ) {
            if matches!(kind.as_str(), "#gn" | "#gn-fn") {
                inner.insert("#file-template".into());
            }
            let args = if kind == "#extern-fn" { 3 } else { 2 };
            if let Some(arguments) = node.children.get_mut(args) {
                for argument in &mut arguments.children {
                    let binder = if argument.children.is_empty() {
                        symbol(argument)
                    } else {
                        argument.children.first().and_then(symbol)
                    };
                    if let Some(name) = binder {
                        inner.insert(name.into());
                    }
                    if let Some(name) = binder {
                        if self
                            .lookup(file, name, &mut Vec::new())
                            .map_err(SourceError::from)?
                            .is_some()
                        {
                            return Err(SourceError::from(format!(
                                "parameter '{name}' would shadow a file-local declaration or alias"
                            ))
                            .at(argument.span));
                        }
                    }
                    for ty in argument.children.iter_mut().skip(1) {
                        self.rewrite(ty, file, locals)?;
                    }
                    rebuild(argument)?;
                }
                rebuild(arguments)?;
            }
            for (index, child) in node.children.iter_mut().enumerate().skip(1) {
                if index != args {
                    self.rewrite(child, file, if index == 1 { locals } else { &inner })?;
                }
            }
            return rebuild(node);
        }
        if kind == "#struct" {
            for child in node.children.iter_mut().take(3).skip(1) {
                self.rewrite(child, file, locals)?;
            }
            if let Some(fields) = node.children.get_mut(3) {
                for field in &mut fields.children {
                    for ty in field.children.iter_mut().skip(1) {
                        self.rewrite(ty, file, locals)?;
                    }
                    rebuild(field)?;
                }
                rebuild(fields)?;
            }
            return rebuild(node);
        }
        if matches!(kind.as_str(), "#call" | "#unsafe-call" | "#struct-literal") {
            if let Some(name) = node.children.get_mut(1) {
                self.rewrite(name, file, locals)?;
            }
            if let Some(args) = node.children.get_mut(2) {
                for argument in &mut args.children {
                    for value in argument.children.iter_mut().skip(1) {
                        self.rewrite(value, file, locals)?;
                    }
                    rebuild(argument)?;
                }
                rebuild(args)?;
            }
            return rebuild(node);
        }
        if matches!(node.expr, Expr::List(_))
            && matches!(node.children.first().map(|n| &n.expr), Some(Expr::Generate))
        {
            if let Some(name) = node.children.get_mut(1) {
                self.rewrite(name, file, locals)?;
            }
            let builtin =
                node.children.get(1).and_then(symbol).is_some_and(|name| {
                    crate::generator::builtins::named_builtin_keys(name).is_some()
                });
            if builtin {
                if let Some(args) = node.children.get_mut(2) {
                    for argument in &mut args.children {
                        for value in argument.children.iter_mut().skip(1) {
                            self.rewrite(value, file, locals)?;
                        }
                        rebuild(argument)?;
                    }
                    rebuild(args)?;
                }
            } else {
                for child in node.children.iter_mut().skip(2) {
                    self.marked(child, file, locals)?;
                }
            }
            return rebuild(node);
        }
        for (index, child) in node.children.iter_mut().enumerate() {
            if kind == "#get" && index == 2 {
                continue;
            }
            self.rewrite(child, file, locals)?;
        }
        rebuild(node)
    }

    fn marked(
        &self,
        node: &mut Node,
        file: usize,
        locals: &HashSet<String>,
    ) -> Result<(), SourceError> {
        if matches!(&node.expr, Expr::Symbol(name) if name.starts_with('@')) {
            return self.rewrite(node, file, locals);
        }
        for child in &mut node.children {
            self.marked(child, file, locals)?;
        }
        rebuild(node)
    }
}

fn rebuild(node: &mut Node) -> Result<(), SourceError> {
    if node.children.is_empty() {
        return Ok(());
    }
    match &mut node.expr {
        Expr::List(items) => {
            *items = node
                .children
                .iter()
                .map(|child| child.expr.clone())
                .collect()
        }
        Expr::Quote(value)
        | Expr::QuasiQuote(value)
        | Expr::Unquote(value)
        | Expr::UnquoteSplicing(value) => {
            if let Some(child) = node.children.first() {
                **value = child.expr.clone();
            }
        }
        _ => {}
    }
    Ok(())
}

pub(crate) fn resolve(
    forms: &mut [Node],
    files: &mut [SourceFile],
    origins: &HashMap<u32, Span>,
    definitions: &HashMap<u32, Span>,
    config: &crate::CompileConfig,
) -> Result<(), SourceError> {
    if !files.iter().any(|file| {
        file.file_scope.is_some()
            || file.source.contains(".lim::")
            || file.source.contains("#alias")
    }) {
        return Ok(());
    }
    if !files.iter().any(|file| file.file_scope.is_some())
        && !forms.iter().any(|form| {
            fn has(node: &Node) -> bool {
                head(node) == "#alias"
                    || ((matches!(node.expr, Expr::Symbol(_)) || head(node) == "#unstable")
                        && target(node).ok().flatten().is_some())
                    || node.children.iter().any(has)
            }
            has(form)
        })
    {
        return Ok(());
    }
    let mut resolver = Resolver {
        files,
        names: vec![HashMap::new(); files.len()],
        aliases: vec![HashMap::new(); files.len()],
        imports: vec![vec![]; files.len()],
        exports: vec![vec![]; files.len()],
        declared: vec![HashSet::new(); files.len()],
        memo: RefCell::new(HashMap::new()),
    };
    for (id, file) in files.iter().enumerate() {
        if let Some(scope) = &file.file_scope {
            resolver.names[id] = scope.names.clone();
        }
        let raw = crate::expand_cfg_forms(crate::parse(&file.source)?, config)?;
        for form in raw {
            if let Some(names) = crate::library::export_names(&form)? {
                resolver.exports[id].extend(names);
            }
            if let Some(spec) = crate::import_form(&form.expr)? {
                let candidate = crate::import_candidate(
                    file.path.parent().unwrap_or(Path::new(".")),
                    spec.path,
                    config,
                );
                let prefix = match spec.prefix {
                    Some(prefix) if !file.import_prefix.is_empty() => {
                        crate::names::imported(&file.import_prefix, prefix)
                    }
                    Some(prefix) => prefix.into(),
                    None if crate::standard_library::source(&candidate).is_some() => String::new(),
                    None => file.import_prefix.clone(),
                };
                if let Some(to) = files.iter().position(|other| {
                    crate::editor::path_key(&other.path) == crate::editor::path_key(&candidate)
                        && other.import_prefix == prefix
                }) {
                    resolver.imports[id].push(to);
                }
            }
        }
    }
    for form in forms.iter() {
        let id = original_id(form.span.source_id, origins) as usize;
        if id >= files.len() {
            continue;
        }
        let mut declarations = crate::generator_provenance::declared_names(&form.expr);
        if matches!(head(form), "#gn" | "#gn-fn" | "#capability") {
            declarations.extend(form.children.get(1).and_then(symbol));
        }
        for name in declarations {
            if let Some((_, local)) = split(name) {
                if files[id].file_scope.is_none() || identity(&files[id], local, id == 0) != name {
                    return Err(SourceError::from("a declaration must belong to its own source file; pass a fresh local name to a generator instead of declaring a file reference").at(form.span).attach(files));
                }
            }
            resolver.declared[id].insert(if split(name).is_some() {
                name.into()
            } else {
                identity(&files[id], name, id == 0)
            });
            if split(name).is_none() {
                if resolver.aliases[id].contains_key(name) {
                    return Err(
                        SourceError::from(format!("duplicate file-local alias '{name}'"))
                            .at(form.span)
                            .attach(files),
                    );
                }
                resolver.names[id].insert(name.into(), identity(&files[id], name, id == 0));
            }
        }
        if matches!(
            form.children.first().map(|node| &node.expr),
            Some(Expr::Generate)
        ) {
            if let Some(kind) = form.children.get(1).and_then(symbol) {
                if crate::generator::builtins::named_builtin_keys(kind).is_some() {
                    if let Some(arguments) = form.children.get(2) {
                        for argument in &arguments.children {
                            if argument.children.first().and_then(symbol) == Some("cancel") {
                                if let Some(name) = argument
                                    .children
                                    .get(1)
                                    .and_then(|value| value.children.first())
                                    .and_then(symbol)
                                {
                                    resolver.names[id]
                                        .entry(name.into())
                                        .or_insert_with(|| identity(&files[id], name, id == 0));
                                }
                            }
                            if matches!(
                                argument.children.first().and_then(symbol),
                                Some("name" | "task" | "protocol" | "cancel" | "destroy")
                            ) || (kind == "#vec-alloc"
                                && argument.children.first().and_then(symbol) == Some("vector"))
                            {
                                if let Some(name) = argument.children.get(1).and_then(symbol) {
                                    resolver.names[id]
                                        .entry(name.into())
                                        .or_insert_with(|| identity(&files[id], name, id == 0));
                                }
                            }
                            if matches!(kind, "#async-fn" | "#async-fn-pinned")
                                && argument.children.first().and_then(symbol) == Some("function")
                            {
                                if let Some(name) = argument
                                    .children
                                    .get(1)
                                    .and_then(|function| function.children.get(1))
                                    .and_then(symbol)
                                {
                                    resolver.names[id]
                                        .entry(name.into())
                                        .or_insert_with(|| identity(&files[id], name, id == 0));
                                    let family =
                                        crate::generator::builtins::capitalized_type_name(name);
                                    resolver.names[id]
                                        .entry(family.clone())
                                        .or_insert_with(|| identity(&files[id], &family, id == 0));
                                }
                            }
                        }
                    }
                }
            }
        }
        if let Some((name, value)) = alias(form)? {
            if split(name).is_some() {
                continue;
            }
            let (path, target, unstable) = target(value)?.unwrap();
            let to = resolver
                .file(id, &path)
                .map_err(|message| SourceError::from(message).at(value.span))?;
            if resolver.names[id].contains_key(name)
                || resolver.aliases[id]
                    .insert(name.into(), (to, target, value.span, unstable))
                    .is_some()
            {
                return Err(
                    SourceError::from(format!("duplicate file-local alias '{name}'"))
                        .at(form.children[1].span)
                        .attach(files),
                );
            }
        }
    }
    let mut scopes = Vec::new();
    for id in 0..files.len() {
        let mut scope = files[id].file_scope.as_deref().cloned().unwrap_or_default();
        for key in resolver.names[id].keys().chain(resolver.aliases[id].keys()) {
            let value = resolver
                .lookup(id, key, &mut Vec::new())
                .map_err(|message| SourceError::from(message))?
                .unwrap();
            scope.names.insert(key.clone(), value.clone());
            if resolver.aliases[id].get(key).is_some_and(|entry| entry.3) {
                scope.declaration_access.insert(value);
            }
            if let Some((_, _, span, _)) = resolver.aliases[id].get(key) {
                scope.required.insert(scope.names[key].clone(), *span);
                let target = local_name(&scope.names[key]);
                let kind = if crate::names::type_name(target) || crate::names::variant_name(target)
                {
                    "type"
                } else {
                    "value"
                };
                crate::names::require(key, kind)
                    .map_err(|message| SourceError::from(message).at(*span))?;
            }
        }
        for name in &resolver.exports[id] {
            let name = if files[id].import_prefix.is_empty() {
                name.clone()
            } else {
                crate::names::imported(&files[id].import_prefix, name)
            };
            scope.exports.insert(
                resolver
                    .lookup(id, &name, &mut Vec::new())
                    .map_err(SourceError::from)?
                    .unwrap_or_else(|| identity(&files[id], &name, id == 0)),
            );
        }
        scope.declared.extend(resolver.declared[id].iter().cloned());
        scopes.push(scope);
    }
    fn references(
        node: &Node,
        file: usize,
        resolver: &Resolver<'_>,
        scope: &mut FileScope,
    ) -> Result<(), SourceError> {
        if matches!(
            node.children.first().map(|node| &node.expr),
            Some(Expr::Generate)
        ) && !node
            .children
            .get(1)
            .and_then(symbol)
            .is_some_and(|name| crate::generator::builtins::named_builtin_keys(name).is_some())
        {
            if let Some(generator) = node.children.get(1) {
                references(generator, file, resolver, scope)?;
            }
            fn marked(
                node: &Node,
                file: usize,
                resolver: &Resolver<'_>,
                scope: &mut FileScope,
            ) -> Result<(), SourceError> {
                if matches!(&node.expr, Expr::Symbol(name) if name.starts_with('@')) {
                    return references(node, file, resolver, scope);
                }
                for child in &node.children {
                    marked(child, file, resolver, scope)?;
                }
                Ok(())
            }
            for input in node.children.iter().skip(2) {
                marked(input, file, resolver, scope)?;
            }
            return Ok(());
        }
        if matches!(node.expr, Expr::Symbol(_)) || head(node) == "#unstable" {
            if let Some((_, _, unstable)) = target(node)? {
                let name = resolver.reference(file, node)?.unwrap();
                if unstable {
                    scope.declaration_access.insert(name.clone());
                }
                scope.required.insert(name, node.span);
                return Ok(());
            }
        }
        if head(node) == "#alias" {
            // Alias targets were already checked with their explicit bypass.
            if let Some(value) = node
                .children
                .get(3)
                .filter(|value| head(value) == "#unstable")
            {
                return references(value, file, resolver, scope);
            }
            return Ok(());
        }
        for child in &node.children {
            references(child, file, resolver, scope)?;
        }
        Ok(())
    }
    for form in forms.iter() {
        let id = original_id(form.span.source_id, origins) as usize;
        if files[id].file_scope.is_none() {
            references(form, id, &resolver, &mut scopes[id])?;
        }
        if let Some((name, value)) = alias(form)? {
            if split(name).is_none() {
                if form.span.source_id as usize != id {
                    let (path, _, unstable) = target(value)?.unwrap();
                    let to = resolver.file(id, &path).map_err(SourceError::from)?;
                    let target = resolver.reference(id, value)?.unwrap();
                    let owner = crate::library::owner(&files[to].path);
                    let author_access =
                        definitions.get(&form.span.source_id).is_some_and(|author| {
                            let author = &files[original_id(author.source_id, origins) as usize];
                            (crate::library::owner(&author.path) == owner
                                && author.import_prefix == files[to].import_prefix)
                                || author
                                    .file_scope
                                    .as_ref()
                                    .is_some_and(|scope| scope.declaration_access.contains(&target))
                        });
                    let caller_access = crate::library::owner(&files[id].path) == owner
                        && files[id].import_prefix == files[to].import_prefix;
                    let public = owner.as_ref().is_none_or(|owner| {
                        files.iter().zip(&scopes).any(|(file, scope)| {
                            crate::editor::path_key(&file.path) == *owner
                                && scope.exports.contains(&target)
                        })
                    });
                    if !unstable && !author_access && !caller_access && !public {
                        return Err(SourceError::from(format!("generated alias cannot expose private declaration '{target}' outside its authorized definition and invocation libraries")).at(value.span).attach(files));
                    }
                    if unstable || author_access {
                        scopes[id].declaration_access.insert(target);
                    }
                }
            }
        }
    }
    // Validate all alias targets even when their local spelling is unused.
    for form in forms.iter() {
        let id = original_id(form.span.source_id, origins) as usize;
        if let Some((name, value)) = alias(form)? {
            if split(name).is_none() {
                resolver
                    .reference(id, value)
                    .map_err(|error| error.attach(files))?;
            }
        }
    }
    for form in forms.iter_mut() {
        let id = original_id(form.span.source_id, origins) as usize;
        resolver
            .rewrite(form, id, &HashSet::new())
            .map_err(|error| error.attach(files))?;
    }
    for (file, scope) in files.iter_mut().zip(scopes) {
        file.file_scope = Some(Arc::new(scope));
    }
    Ok(())
}

pub(crate) fn validate(program: &crate::Program) -> Result<(), SourceError> {
    if !program
        .source_files
        .iter()
        .any(|file| file.file_scope.is_some())
    {
        return Ok(());
    }
    let mut declared = program
        .source_files
        .iter()
        .filter_map(|file| file.file_scope.as_ref())
        .flat_map(|scope| scope.declared.iter().cloned())
        .collect::<HashSet<_>>();
    for item in &program.items {
        declared.extend(crate::item_declared_names(item));
        if let crate::Item::Enum { variants, .. } = item {
            declared.extend(variants.iter().map(|variant| variant.name.clone()));
        }
    }
    for file in &program.source_files {
        if let Some(scope) = &file.file_scope {
            for (name, span) in &scope.required {
                if !declared.contains(name) {
                    return Err(SourceError::from(format!(
                        "file alias target '{name}' does not exist"
                    ))
                    .at(*span)
                    .attach(&program.source_files));
                }
            }
        }
    }
    Ok(())
}
