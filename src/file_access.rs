//! File-local spellings resolve to canonical file/declaration identities.
//! This changes syntax in memory, never copies or rewrites library source.
use crate::{Expr, SourceError, SourceFile, Span, SpannedExpr as Node};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(crate) struct FileScope {
    pub names: HashMap<String, String>,
    pub exports: HashSet<String>,
    pub declaration_access: HashSet<String>,
    pub declared: HashSet<String>,
    pub required: HashMap<String, Span>,
}

pub(crate) fn project_root(entry: &Path) -> PathBuf {
    let entry = crate::editor::path_key(entry);
    let base = if entry.is_dir() {
        entry.as_path()
    } else {
        entry.parent().unwrap_or(Path::new("."))
    };
    base.ancestors()
        .find(|directory| {
            directory.join("lim.project").is_file()
                || crate::editor::source(&directory.join("lim.project")).is_some()
        })
        .unwrap_or(base)
        .to_owned()
}

pub(crate) fn reference_path(base: &Path, name: &str, root: &Path) -> PathBuf {
    if let Some(relative) = name.strip_prefix("//") {
        root.join(relative)
    } else {
        base.join(name)
    }
}

pub(crate) fn validate_path(name: &str) -> Result<(), String> {
    if let Some(relative) = name.strip_prefix("//") {
        if Path::new(relative).components().any(|part| {
            matches!(
                part,
                std::path::Component::ParentDir | std::path::Component::RootDir
            )
        }) {
            return Err("project-root references cannot contain '..' or another root".into());
        }
    }
    Ok(())
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
    if let (Expr::Symbol(name), Expr::Function(_)) =
        (&node.children[1].expr, &node.children[3].expr)
    {
        return Ok(Some((name, &node.children[3])));
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
    if !matches!(node.children[3].expr, Expr::Function(_)) && target(&node.children[3])?.is_none() {
        return Err(SourceError::from(
            "#alias target must be path.lim::declaration, optionally wrapped in #unstable",
        )
        .at(node.children[3].span));
    }
    Ok(Some((name, &node.children[3])))
}

pub(crate) fn check_path(from: &Path, to: &Path) -> Result<(), String> {
    if crate::library::owner(from) != crate::library::owner(to) {
        crate::library::check_entry(from, to)?;
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
    if crate::standard_library::source(&file.path).is_some() {
        return name.into();
    }
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

fn proof_children(node: &mut Node) {
    if node.children.is_empty() {
        if let Expr::List(items) = &node.expr {
            node.children = items
                .iter()
                .map(|expr| Node {
                    expr: expr.clone(),
                    span: node.span,
                    children: Vec::new(),
                })
                .collect();
        }
    }
    for child in &mut node.children {
        proof_children(child);
    }
}

#[derive(Default)]
struct ProofFunctionScope {
    parameters: HashSet<String>,
    locals: HashSet<String>,
}

fn proof_pattern_names(expression: &Expr, names: &mut HashSet<String>) {
    match expression {
        Expr::Symbol(name)
            if !name.starts_with('#')
                && !name.contains('.')
                && !matches!(name.as_str(), "true" | "false" | "_") =>
        {
            names.insert(name.clone());
        }
        Expr::List(parts) => {
            if matches!(parts.first(), Some(Expr::Symbol(head))
                if matches!(head.as_str(), "#literal" | "#range" | "#range-inclusive"))
            {
                return;
            }
            for part in parts.iter().skip(1) {
                proof_pattern_names(part, names);
            }
        }
        _ => {}
    }
}

fn proof_local_names(expression: &Expr, names: &mut HashSet<String>) {
    match expression {
        Expr::List(parts) => {
            if let Some(Expr::Symbol(head)) = parts.first() {
                if matches!(
                    head.as_str(),
                    "#let"
                        | "#let-mut"
                        | "#const"
                        | "#let-else"
                        | "#if-let"
                        | "#while-let"
                        | "#case"
                        | "#case-ref"
                        | "#case-ref-mut"
                        | "#case-pin"
                        | "#case-pin-mut"
                ) {
                    if let Some(pattern) = parts.get(1) {
                        proof_pattern_names(pattern, names);
                    }
                }
                if head == "#for-range" {
                    if let Some(Expr::List(binding)) = parts.get(1) {
                        if let Some(Expr::Symbol(name)) = binding.first() {
                            names.insert(name.clone());
                        }
                    }
                }
            }
            for part in parts {
                proof_local_names(part, names);
            }
        }
        Expr::Labeled { expression, .. } => proof_local_names(expression, names),
        _ => {}
    }
}

struct Resolver<'a> {
    files: &'a [SourceFile],
    names: Vec<HashMap<String, String>>,
    aliases: Vec<HashMap<String, (usize, String, Span, bool)>>,
    imports: Vec<Vec<usize>>,
    exports: Vec<Vec<String>>,
    declared: Vec<HashSet<String>>,
    memo: RefCell<HashMap<(usize, String), Option<String>>>,
    root: PathBuf,
    proof_functions: HashMap<String, ProofFunctionScope>,
}

impl Resolver<'_> {
    fn proof_term_child(
        &self,
        node: &mut Node,
        index: usize,
        file: usize,
        locals: &HashSet<String>,
    ) -> Result<(), SourceError> {
        if let Some(child) = node.children.get_mut(index) {
            self.proof_term(child, file, locals)?;
        }
        Ok(())
    }
    fn proof_term_list(
        &self,
        node: &mut Node,
        index: usize,
        file: usize,
        locals: &HashSet<String>,
    ) -> Result<(), SourceError> {
        if let Some(list) = node.children.get_mut(index) {
            for term in &mut list.children {
                self.proof_term(term, file, locals)?;
            }
            rebuild(list)?;
        }
        Ok(())
    }
    fn proof_term(
        &self,
        node: &mut Node,
        file: usize,
        locals: &HashSet<String>,
    ) -> Result<(), SourceError> {
        let kind = head(node).to_owned();
        if kind == "#pt-let" {
            // Keep malformed forms inert: a partial binder must not turn its
            // apparent name or operands into file/global references.
            let binder_name = node
                .children
                .get(1)
                .and_then(|parameter| parameter.children.get(1))
                .and_then(symbol)
                .map(str::to_owned);
            if node.children.len() != 4
                || head(&node.children[1]) != "#parameter"
                || node.children[1].children.len() != 3
                || !matches!(&node.children[1].children[1].expr, Expr::Symbol(name)
                    if !name.starts_with('#')
                        && !name.contains([':', '/', '.', '@'])
                        && name.chars().next().is_some_and(|character| character.is_alphabetic() || character == '_'))
            {
                return rebuild(node);
            }
            let mut inner = locals.clone();
            if let Some(ty) = node.children[1].children.get_mut(2) {
                self.proof_term(ty, file, locals)?;
            }
            if let Some(name) = binder_name {
                inner.insert(name);
            }
            rebuild(&mut node.children[1])?;
            self.proof_term_child(node, 2, file, locals)?;
            self.proof_term_child(node, 3, file, &inner)?;
        } else if matches!(kind.as_str(), "#pt-pi" | "#pt-lambda" | "#pt-sigma") {
            let binder_index = 1;
            let body_index = 2;
            let mut inner = locals.clone();
            if let Some(params) = node.children.get_mut(binder_index) {
                for parameter in &mut params.children {
                    if let Some(ty) = parameter.children.get_mut(1) {
                        self.proof_term(ty, file, &inner)?;
                    }
                    if let Some(name) = parameter.children.first().and_then(symbol) {
                        inner.insert(name.to_owned());
                    }
                    rebuild(parameter)?;
                }
                rebuild(params)?;
            }
            if kind == "#pt-sigma" {
                // Sigma binds its name only in the codomain.
            }
            self.proof_term_child(node, body_index, file, &inner)?;
        } else if matches!(
            kind.as_str(),
            "#pt-type" | "#pt-sort" | "#pt-level-succ" | "#pt-level-max" | "#pt-level-imax"
        ) {
            // Universe levels are metadata and never participate in file-name lookup.
        } else if kind == "#pt-use" || kind == "#pt-program" || kind == "#pt-certificate" {
            if let Some(name) = node.children.get_mut(1) {
                self.rewrite(name, file, &HashSet::new())?;
            }
        } else if kind == "#pt-construct" {
            if let Some(name) = node.children.get_mut(1) {
                self.rewrite(name, file, &HashSet::new())?;
            }
            self.proof_term_list(node, 3, file, locals)?;
            self.proof_term_list(node, 5, file, locals)?;
        } else if kind == "#pt-project" {
            // The family is a declaration role, the ordinal is metadata, and
            // only the subject is a term. Malformed forms remain inert.
            let valid_index = node.children.get(2).is_some_and(|index| match &index.expr {
                Expr::Integer(value) => *value >= 0 && usize::try_from(*value).is_ok(),
                Expr::UnsignedInteger(value) => usize::try_from(*value).is_ok(),
                _ => false,
            });
            if node.children.len() == 4 && valid_index {
                if let Some(family) = node.children.get_mut(1) {
                    self.rewrite(family, file, &HashSet::new())?;
                }
                self.proof_term_child(node, 3, file, locals)?;
            }
        } else if kind == "#pt-self-at" {
            self.proof_term_list(node, 1, file, locals)?;
        } else if kind == "#pt-recur" {
            if node.children.len() == 3
                && matches!(&node.children[1].expr, Expr::Symbol(_))
                && matches!(&node.children[2].expr, Expr::List(_))
            {
                self.rewrite(&mut node.children[1], file, &HashSet::new())?;
                self.proof_term_list(node, 2, file, locals)?;
            }
        } else if matches!(kind.as_str(), "#pt-mutual-induct" | "#pt-nested-induct") {
            let nested = kind == "#pt-nested-induct";
            let offset = usize::from(nested);
            let valid = node.children.len() == 7 + offset
                && matches!(&node.children[1].expr, Expr::Symbol(_))
                && matches!(&node.children[2].expr, Expr::List(_))
                && (!nested
                    || matches!(&node.children[4].expr,
                    Expr::Integer(value) if *value >= 0 && usize::try_from(*value).is_ok())
                    || nested
                        && matches!(&node.children[4].expr,
                        Expr::UnsignedInteger(value) if usize::try_from(*value).is_ok()))
                && head(&node.children[4 + offset]) == "#indices"
                && matches!(&node.children[3].expr, Expr::List(_))
                && matches!(&node.children[4 + offset].expr, Expr::List(_))
                && node.children[4 + offset].children.len() <= 65
                && matches!(&node.children[5 + offset].expr, Expr::List(_))
                && (2..=16).contains(&node.children[5 + offset].children.len())
                && node.children[5 + offset].children.iter().all(|bundle| {
                    if nested {
                        bundle.children.len() == 4
                            && head(bundle) == "#pt-case"
                            && matches!(&bundle.children[3].expr, Expr::List(_))
                    } else {
                        bundle.children.len() == 3
                            && matches!(&bundle.children[0].expr, Expr::Symbol(_))
                            && matches!(&bundle.children[2].expr, Expr::List(_))
                    }
                });
            if valid {
                self.rewrite(&mut node.children[1], file, &HashSet::new())?;
                self.proof_term_list(node, 3, file, locals)?;
                if let Some(indices) = node.children.get_mut(4 + offset) {
                    for term in indices.children.iter_mut().skip(1) {
                        self.proof_term(term, file, locals)?;
                    }
                    rebuild(indices)?;
                }
                if let Some(bundles) = node.children.get_mut(5 + offset) {
                    for bundle in &mut bundles.children {
                        if nested {
                            self.proof_term(&mut bundle.children[1], file, locals)?;
                            self.proof_term(&mut bundle.children[2], file, locals)?;
                            self.proof_term_list(bundle, 3, file, locals)?;
                        } else {
                            self.rewrite(&mut bundle.children[0], file, &HashSet::new())?;
                            self.proof_term(&mut bundle.children[1], file, locals)?;
                            self.proof_term_list(bundle, 2, file, locals)?;
                        }
                        rebuild(bundle)?;
                    }
                    rebuild(bundles)?;
                }
                self.proof_term_child(node, 6 + offset, file, locals)?;
            }
        } else if kind == "#pt-induct" {
            if let Some(name) = node.children.get_mut(1) {
                self.rewrite(name, file, &HashSet::new())?;
            }
            self.proof_term_list(node, 3, file, locals)?;
            if node.children.len() == 8 {
                if let Some(indices) = node.children.get_mut(4) {
                    for value in indices.children.iter_mut().skip(1) {
                        self.proof_term(value, file, locals)?;
                    }
                    rebuild(indices)?;
                }
                self.proof_term_child(node, 5, file, locals)?;
                self.proof_term_list(node, 6, file, locals)?;
                self.proof_term_child(node, 7, file, locals)?;
            } else {
                self.proof_term_child(node, 4, file, locals)?;
                self.proof_term_list(node, 5, file, locals)?;
                self.proof_term_child(node, 6, file, locals)?;
            }
        } else {
            for index in 1..node.children.len() {
                self.proof_term_child(node, index, file, locals)?;
            }
        }
        rebuild(node)
    }

    fn universe_names(node: &Node, index: usize, has_marker: bool, into: &mut HashSet<String>) {
        if let Some(universes) = node.children.get(index) {
            for universe in universes.children.iter().skip(usize::from(has_marker)) {
                if let Some(name) = symbol(universe) {
                    into.insert(name.to_owned());
                }
            }
        }
    }

    fn theorem_source(
        &self,
        node: &mut Node,
        file: usize,
        locals: &HashSet<String>,
    ) -> Result<(), SourceError> {
        if let Some(name) = node.children.get_mut(1) {
            self.rewrite(name, file, &HashSet::new())?;
        }
        if node.children.len() == 3 {
            self.rewrite(&mut node.children[2], file, locals)?;
            return rebuild(node);
        }
        let mut inner = locals.clone();
        Self::universe_names(node, 2, true, &mut inner);
        if let Some(parameters) = node.children.get_mut(3) {
            for parameter in parameters.children.iter_mut().skip(1) {
                if let Some(ty) = parameter.children.get_mut(2) {
                    self.proof_term(ty, file, &inner)?;
                }
                if let Some(name) = parameter.children.get(1).and_then(symbol) {
                    inner.insert(name.to_owned());
                }
                rebuild(parameter)?;
            }
            rebuild(parameters)?;
        }
        for index in [4, 5] {
            if let Some(clause) = node.children.get_mut(index) {
                if let Some(term) = clause.children.get_mut(1) {
                    self.proof_term(term, file, &inner)?;
                }
                rebuild(clause)?;
            }
        }
        rebuild(node)
    }

    fn math_definition_source(
        &self,
        node: &mut Node,
        file: usize,
        locals: &HashSet<String>,
    ) -> Result<(), SourceError> {
        if let Some(name) = node.children.get_mut(1) {
            self.rewrite(name, file, &HashSet::new())?;
        }
        let mut inner = locals.clone();
        Self::universe_names(node, 2, false, &mut inner);
        for index in [3, 4] {
            self.proof_term_child(node, index, file, &inner)?;
        }
        rebuild(node)
    }

    fn math_inductive_source(
        &self,
        node: &mut Node,
        file: usize,
        locals: &HashSet<String>,
    ) -> Result<(), SourceError> {
        if let Some(name) = node.children.get_mut(1) {
            self.rewrite(name, file, &HashSet::new())?;
        }
        let mut inner = locals.clone();
        Self::universe_names(node, 2, false, &mut inner);
        if let Some(parameters) = node.children.get_mut(3) {
            for parameter in &mut parameters.children {
                if let Some(ty) = parameter.children.get_mut(1) {
                    self.proof_term(ty, file, &inner)?;
                }
                if let Some(name) = parameter.children.first().and_then(symbol) {
                    inner.insert(name.to_owned());
                }
                rebuild(parameter)?;
            }
            rebuild(parameters)?;
        }
        // Mutual members are global declaration names, never term binders.
        let has_mutual = node
            .children
            .get(4)
            .is_some_and(|clause| head(clause) == "#mutual");
        if has_mutual {
            let family = &mut node.children[4];
            let members: Vec<_> = family.children.iter().skip(1).filter_map(symbol).collect();
            let valid = (2..=16).contains(&members.len())
                && members.len() + 1 == family.children.len()
                && members.iter().collect::<HashSet<_>>().len() == members.len();
            if valid {
                for member in family.children.iter_mut().skip(1) {
                    self.rewrite(member, file, &HashSet::new())?;
                }
            }
            rebuild(family)?;
        }
        let indices_at = 4 + usize::from(has_mutual);
        let indexed = node
            .children
            .get(indices_at)
            .is_some_and(|clause| head(clause) == "#indices");
        if indexed {
            if let Some(indices) = node.children.get_mut(indices_at) {
                let mut index_scope = inner.clone();
                for index in &mut indices.children {
                    if head(index) != "#parameter" || index.children.len() != 3 {
                        continue;
                    }
                    if let Some(ty) = index.children.get_mut(2) {
                        self.proof_term(ty, file, &index_scope)?;
                    }
                    if let Some(name) = index.children.get(1).and_then(symbol) {
                        index_scope.insert(name.to_owned());
                    }
                    rebuild(index)?;
                }
                rebuild(indices)?;
            }
        }
        let sort_index = indices_at + usize::from(indexed);
        let constructors_index = sort_index + 1;
        if let Some(sort) = node.children.get_mut(sort_index) {
            self.proof_term(sort, file, &inner)?;
        }
        if let Some(constructors) = node.children.get_mut(constructors_index) {
            for constructor in &mut constructors.children {
                let mut constructor_scope = inner.clone();
                if let Some(fields) = constructor.children.get_mut(1) {
                    for field in &mut fields.children {
                        if let Some(ty) = field.children.get_mut(1) {
                            self.proof_term(ty, file, &constructor_scope)?;
                        }
                        if let Some(name) = field.children.first().and_then(symbol) {
                            constructor_scope.insert(name.to_owned());
                        }
                        rebuild(field)?;
                    }
                    rebuild(fields)?;
                }
                if indexed {
                    if let Some(results) = constructor.children.get_mut(2) {
                        for result in &mut results.children {
                            self.proof_term(result, file, &constructor_scope)?;
                        }
                        rebuild(results)?;
                    }
                }
                rebuild(constructor)?;
            }
            rebuild(constructors)?;
        }
        rebuild(node)
    }

    fn file(&self, from: usize, path: &str) -> Result<usize, String> {
        if let Some(id) = self
            .files
            .iter()
            .position(|file| identity(file, "", false).strip_suffix("::") == Some(path))
        {
            return Ok(id);
        }
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
            validate_path(path)?;
            let candidate = crate::editor::path_key(&reference_path(
                self.files[from].path.parent().unwrap_or(Path::new(".")),
                path,
                &self.root,
            ));
            if let Some(id) = self
                .files
                .iter()
                .position(|file| crate::editor::path_key(&file.path) == candidate)
            {
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
            if split(name).is_some() || matches!(value.expr, Expr::Function(_)) {
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
            target.expr = Expr::Function(value);
            target.children.clear();
            node.children[1] = key;
            node.children[3] = target;
            return rebuild(node);
        }
        let kind = head(node).to_owned();
        if kind == "#theorem" {
            return self.theorem_source(node, file, locals);
        }
        if matches!(kind.as_str(), "#math-definition" | "#math-opaque") {
            return self.math_definition_source(node, file, locals);
        }
        if kind == "#math-inductive" {
            return self.math_inductive_source(node, file, locals);
        }
        if matches!(kind.as_str(), "#proof-for-all" | "#proof-with-invariants") {
            proof_children(node);
        }
        let mut inner = locals.clone();
        if kind == "#proof-for-all" {
            if let Some(parameters) = node.children.get_mut(1) {
                for parameter in &mut parameters.children {
                    if let Some(name) = parameter.children.first().and_then(symbol) {
                        inner.insert(name.to_owned());
                    }
                    for ty in parameter.children.iter_mut().skip(1) {
                        self.rewrite(ty, file, locals)?;
                    }
                    rebuild(parameter)?;
                }
                rebuild(parameters)?;
            }
            for predicate in node.children.iter_mut().skip(2) {
                self.rewrite(predicate, file, &inner)?;
            }
            return rebuild(node);
        }
        if kind == "#proof-requires-validation" {
            if let Some(entry) = node.children.get_mut(1) {
                self.rewrite(entry, file, &HashSet::new())?;
            }
            for descriptor in node.children.iter_mut().skip(2) {
                proof_children(descriptor);
                if head(descriptor) == "#parameter-of" {
                    if let Some(function) = descriptor.children.get_mut(1) {
                        self.rewrite(function, file, &HashSet::new())?;
                    }
                }
                // The final operand is a label from this function's signature,
                // not a reference in the theorem's file or lexical scope.
                rebuild(descriptor)?;
            }
            return rebuild(node);
        }
        if kind == "#proof-contract" {
            if let Some(function) = node.children.get_mut(1) {
                self.rewrite(function, file, locals)?;
                if let Some(scope) =
                    symbol(function).and_then(|name| self.proof_functions.get(name))
                {
                    inner.extend(scope.parameters.iter().cloned());
                }
            }
            for predicate in node.children.iter_mut().skip(2) {
                self.rewrite(predicate, file, &inner)?;
            }
            return rebuild(node);
        }
        if kind == "#proof-with-invariants" {
            if let Some(descriptors) = node.children.get_mut(1) {
                self.rewrite_proof_invariants(descriptors, file, locals)?;
            }
            for predicate in node.children.iter_mut().skip(2) {
                self.rewrite(predicate, file, locals)?;
            }
            return rebuild(node);
        }
        if kind == "#proof-only-unsafe" {
            if let Some(function) = node.children.get_mut(1) {
                self.rewrite(function, file, locals)?;
            }
            if let Some(allowed) = node.children.get_mut(2) {
                proof_children(allowed);
                for operation in &mut allowed.children {
                    // Builtins are literal operation names; user functions
                    // retain the same canonical identities as checked calls.
                    if !matches!(&operation.expr, Expr::Symbol(name) if name.starts_with('#')) {
                        self.rewrite(operation, file, locals)?;
                    }
                }
                rebuild(allowed)?;
            }
            return rebuild(node);
        }
        if kind == "#proof-no-overflow" {
            // Its first operand names a builtin numeric operation.
            for operand in node.children.iter_mut().skip(2) {
                self.rewrite(operand, file, locals)?;
            }
            return rebuild(node);
        }
        if matches!(
            kind.as_str(),
            "#fn" | "#unsafe-fn" | "#extern-fn" | "#gn" | "#gn-fn"
        ) {
            if matches!(kind.as_str(), "#gn" | "#gn-fn") {
                inner.insert("#file-template".into());
                // Explicit definition-site references remain resolvable even
                // inside syntax that constructs signatures or nested calls.
                for body in node.children.iter_mut().skip(3) {
                    self.marked(body, file, &inner)?;
                }
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

    fn rewrite_proof_invariants(
        &self,
        node: &mut Node,
        file: usize,
        locals: &HashSet<String>,
    ) -> Result<(), SourceError> {
        // Each descriptor is (function label invariant rank). Labels belong
        // to the function's lexical namespace, even if an alias shares one.
        if node.children.len() == 4 && node.children.first().and_then(symbol).is_some() {
            self.rewrite(&mut node.children[0], file, locals)?;
            let mut inner = locals.clone();
            if let Some(scope) =
                symbol(&node.children[0]).and_then(|name| self.proof_functions.get(name))
            {
                inner.extend(scope.locals.iter().cloned());
            }
            for predicate in node.children.iter_mut().skip(2) {
                self.rewrite(predicate, file, &inner)?;
            }
        } else {
            for descriptor in &mut node.children {
                self.rewrite_proof_invariants(descriptor, file, locals)?;
            }
        }
        rebuild(node)
    }

    fn marked(
        &self,
        node: &mut Node,
        file: usize,
        locals: &HashSet<String>,
    ) -> Result<(), SourceError> {
        // Unquoted expressions execute in the generator's definition context,
        // even when the surrounding template constructs another invocation.
        if matches!(node.expr, Expr::Unquote(_) | Expr::UnquoteSplicing(_)) {
            return self.rewrite(node, file, locals);
        }
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
        proof_functions: HashMap::new(),
        root: config
            .project_root
            .clone()
            .unwrap_or_else(|| project_root(&files[0].path)),
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
                if let Some(to) = files.iter().position(|other| {
                    crate::editor::path_key(&other.path) == crate::editor::path_key(&candidate)
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
        let mut declarations = if head(form) == "#enum-contribute" {
            Vec::new()
        } else {
            crate::generator_provenance::declared_names(&form.expr)
        };
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
                            if argument.children.first().and_then(symbol) == Some("access") {
                                if let Some(accessors) = argument.children.get(1) {
                                    for accessor in &accessors.children {
                                        if let Some(name) =
                                            accessor.children.get(1).and_then(symbol)
                                        {
                                            resolver.names[id].entry(name.into()).or_insert_with(
                                                || identity(&files[id], name, id == 0),
                                            );
                                        }
                                    }
                                }
                            }
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
            if split(name).is_some() || matches!(value.expr, Expr::Function(_)) {
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
                crate::names::require(
                    key,
                    if crate::names::variant_name(target) && crate::names::variant_name(key) {
                        "variant"
                    } else {
                        kind
                    },
                )
                .map_err(|message| SourceError::from(message).at(*span))?;
            }
        }
        for name in &resolver.exports[id] {
            let name = name.clone();
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
            if split(name).is_none() && !matches!(value.expr, Expr::Function(_)) {
                if form.span.source_id as usize != id {
                    let (path, _, unstable) = target(value)?.unwrap();
                    let to = resolver.file(id, &path).map_err(SourceError::from)?;
                    let target = resolver.reference(id, value)?.unwrap();
                    let owner = crate::library::owner(&files[to].path);
                    let author_access =
                        definitions.get(&form.span.source_id).is_some_and(|author| {
                            let author = &files[original_id(author.source_id, origins) as usize];
                            (crate::library::owner(&author.path) == owner)
                                || author
                                    .file_scope
                                    .as_ref()
                                    .is_some_and(|scope| scope.declaration_access.contains(&target))
                        });
                    let caller_access = crate::library::owner(&files[id].path) == owner;
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
            if split(name).is_none() && !matches!(value.expr, Expr::Function(_)) {
                resolver
                    .reference(id, value)
                    .map_err(|error| error.attach(files))?;
            }
        }
    }
    // Inventory function binders before rewriting any proof, so references
    // work across files and regardless of declaration order.
    for form in forms.iter() {
        let kind = head(form);
        if !matches!(kind, "#fn" | "#unsafe-fn" | "#extern-fn") {
            continue;
        }
        let Expr::List(parts) = &form.expr else {
            continue;
        };
        let id = original_id(form.span.source_id, origins) as usize;
        let name_index = if kind == "#extern-fn" { 2 } else { 1 };
        let Some(Expr::Symbol(name)) = parts.get(name_index) else {
            continue;
        };
        let name = resolver
            .lookup(id, name, &mut Vec::new())
            .map_err(SourceError::from)?
            .unwrap_or_else(|| name.clone());
        let mut scope = ProofFunctionScope::default();
        if let Some(Expr::List(parameters)) = parts.get(name_index + 1) {
            for parameter in parameters {
                if let Expr::List(pair) = parameter {
                    let offset = usize::from(
                        matches!(pair.first(), Some(Expr::Symbol(head)) if head == "#mut"),
                    );
                    if let Some(Expr::Symbol(name)) = pair.get(offset) {
                        scope.parameters.insert(name.clone());
                    }
                }
            }
        }
        scope.locals = scope.parameters.clone();
        for body in parts.iter().skip(name_index + 3) {
            proof_local_names(body, &mut scope.locals);
        }
        resolver.proof_functions.insert(name, scope);
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
        if let crate::Item::ThreadTask {
            generated_functions,
            ..
        } = item
        {
            declared.extend(
                generated_functions
                    .iter()
                    .map(|function| function.name.clone()),
            );
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
