//! Directory libraries: imports establish boundaries, never naming conventions.
use crate::{Expr, Program, SourceError, SourceFile, Span, SpannedExpr};
use std::{
    collections::HashMap,
    path::{Path, PathBuf},
};

/// The nearest lib.lim owns a source, including separately compiled white-box tests.
pub(crate) fn owner(path: &Path) -> Option<PathBuf> {
    crate::editor::path_key(path)
        .parent()?
        .ancestors()
        .find_map(|directory| {
            let root = directory.join("lib.lim");
            (root.is_file() || crate::editor::source(&root).is_some())
                .then(|| crate::editor::path_key(&root))
        })
}

pub(crate) fn check_import(from: &Path, to: &Path, external: bool) -> Result<(), String> {
    let from_owner = owner(from);
    let to_owner = owner(to);
    if external {
        if let Some(root) = to_owner {
            if crate::editor::path_key(to) != root {
                return Err(format!("cannot externally import private library implementation '{}'; import '{}' instead", to.display(), root.display()));
            }
        }
    } else if from_owner != to_owner {
        return Err(format!("internal import crosses a library boundary: '{}'; use #import-external with the library's lib.lim entry point", to.display()));
    } else if to.file_name().is_some_and(|name| name == "lib.lim") {
        return Err("lib.lim is a library entry point and requires #import-external".into());
    }
    Ok(())
}

pub(crate) fn export_names(form: &SpannedExpr) -> Result<Option<Vec<String>>, SourceError> {
    let Expr::List(items) = &form.expr else {
        return Ok(None);
    };
    if !matches!(items.first(), Some(Expr::Symbol(head)) if head == "#export") {
        return Ok(None);
    }
    let mut names = Vec::new();
    for (index, item) in items.iter().enumerate().skip(1) {
        let Expr::Symbol(name) = item else {
            return Err(
                SourceError::from("#export expects declaration identifiers").at(form
                    .children
                    .get(index)
                    .map_or(form.span, |child| child.span)),
            );
        };
        if name.contains('.') {
            return Err(SourceError::from("#export lists enum types, not individual variants; exporting an enum exposes every variant")
                .at(form.children.get(index).map_or(form.span, |child| child.span)));
        }
        if name.starts_with('#') || name.contains('@') || names.contains(name) {
            return Err(
                SourceError::from("#export expects unique, locally declared identifiers").at(form
                    .children
                    .get(index)
                    .map_or(form.span, |child| child.span)),
            );
        }
        names.push(name.clone());
    }
    Ok(Some(names))
}

pub(crate) fn validate_metadata(forms: &[SpannedExpr]) -> Result<(), SourceError> {
    fn nested(form: &SpannedExpr) -> Result<(), SourceError> {
        if matches!(form.expr, Expr::Quote(_) | Expr::QuasiQuote(_)) {
            return Ok(());
        }
        if matches!(&form.expr, Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#export"))
        {
            return Err(SourceError::from(
                "#export must be literal top-level metadata, not conditional or nested",
            )
            .at(form.span));
        }
        for child in &form.children {
            nested(child)?;
        }
        Ok(())
    }
    for form in forms {
        for child in &form.children {
            nested(child)?;
        }
    }
    Ok(())
}

pub(crate) struct Visibility {
    authorities: HashMap<u32, Span>,
    owners: Vec<Option<PathBuf>>,
    prefixes: Vec<String>,
    file_contexts: Vec<Option<PathBuf>>,
    exports: HashMap<PathBuf, Vec<String>>,
    resolved_exports: HashMap<PathBuf, std::collections::HashSet<String>>,
    unstable: Vec<std::collections::HashSet<String>>,
    declarations: HashMap<String, Span>,
    struct_owners: HashMap<String, String>,
    import_roots: HashMap<String, Option<PathBuf>>,
}

impl Visibility {
    fn new(
        files: &[SourceFile],
        origins: &HashMap<u32, Span>,
        declarations: HashMap<String, Span>,
    ) -> Result<Self, SourceError> {
        let mut owners = Vec::with_capacity(files.len());
        let mut prefixes = Vec::with_capacity(files.len());
        let mut file_contexts = Vec::with_capacity(files.len());
        let mut directories = HashMap::new();
        let mut unstable = Vec::with_capacity(files.len());
        for (id, file) in files.iter().enumerate() {
            let mut source = id as u32;
            let mut steps = 0;
            while let Some(invocation) = origins.get(&source) {
                source = invocation.source_id;
                steps += 1;
                if steps > files.len() {
                    return Err("cyclic generated source ownership".into());
                }
            }
            let path = &files.get(source as usize).unwrap_or(file).path;
            file_contexts.push(
                files
                    .get(source as usize)
                    .filter(|file| file.file_scope.is_some())
                    .map(|file| file.path.clone()),
            );
            unstable.push(
                files
                    .get(source as usize)
                    .and_then(|file| file.file_scope.as_ref())
                    .map(|scope| scope.declaration_access.clone())
                    .unwrap_or_default(),
            );
            prefixes.push(
                files
                    .get(source as usize)
                    .unwrap_or(file)
                    .import_prefix
                    .clone(),
            );
            let directory = path.parent().unwrap_or(Path::new(".")).to_path_buf();
            owners.push(
                directories
                    .entry(directory)
                    .or_insert_with(|| owner(path))
                    .clone(),
            );
        }
        let mut exports = HashMap::new();
        let mut resolved_exports: HashMap<PathBuf, std::collections::HashSet<String>> =
            HashMap::new();
        for file in files {
            if let Some(scope) = &file.file_scope {
                if file.path.file_name().is_some_and(|name| name == "lib.lim") {
                    resolved_exports
                        .entry(crate::editor::path_key(&file.path))
                        .or_default()
                        .extend(scope.exports.iter().cloned());
                }
            }
        }
        for root in owners.iter().flatten() {
            if exports.contains_key(root) {
                continue;
            }
            let text = files
                .iter()
                .find(|file| crate::editor::path_key(&file.path) == *root)
                .map(|file| file.source.clone())
                .or_else(|| crate::editor::source(root))
                .or_else(|| std::fs::read_to_string(root).ok())
                .ok_or_else(|| {
                    SourceError::from(format!(
                        "cannot read library entry point '{}'",
                        root.display()
                    ))
                })?;
            let mut names = Vec::new();
            for form in crate::parse(&text)? {
                if let Some(entries) = export_names(&form)? {
                    for entry in entries {
                        if names.contains(&entry) {
                            return Err(format!(
                                "duplicate export '{entry}' in '{}'",
                                root.display()
                            )
                            .into());
                        }
                        names.push(entry);
                    }
                }
            }
            exports.insert(root.clone(), names);
        }
        let mut import_roots = HashMap::new();
        // Import ancestry comes from loader metadata, never from whichever
        // declarations happened to survive expansion. A library may consist
        // entirely of imports and generator invocations.
        for (index, prefix) in prefixes.iter().enumerate() {
            if let Some(Some(root)) = owners.get(index).filter(|_| !prefix.is_empty()) {
                let entry = import_roots
                    .entry(prefix.clone())
                    .or_insert_with(|| Some(root.clone()));
                if entry.as_ref() != Some(root) {
                    *entry = None;
                }
            }
        }
        Ok(Self {
            authorities: HashMap::new(),
            owners,
            prefixes,
            file_contexts,
            exports,
            resolved_exports,
            unstable,
            declarations,
            struct_owners: HashMap::new(),
            import_roots,
        })
    }

    /// Internal files share an instance; distinct external prefixes never do.
    pub(crate) fn expansion_context(&self, span: Span) -> String {
        let index = span.source_id as usize;
        if let Some(Some(file)) = self.file_contexts.get(index) {
            return format!(
                "{:?}:{:?}:file={}",
                self.owners.get(index),
                self.prefixes.get(index),
                file.display()
            );
        }
        format!(
            "{:?}:{:?}",
            self.owners.get(index),
            self.prefixes.get(index)
        )
    }

    pub(crate) fn module_context(&self, span: Span) -> (String, String) {
        let index = span.source_id as usize;
        let root = self.owners.get(index).and_then(Option::as_ref);
        (
            root.map_or_else(|| "<global>".into(), |root| root.display().to_string()),
            self.prefixes.get(index).cloned().unwrap_or_default(),
        )
    }

    fn qualified_access(&self, name: &str, span: Span) -> Result<(), SourceError> {
        if self.declarations.contains_key(name) {
            return self.access(name, span, false);
        }
        if name.starts_with('#') {
            return Ok(());
        }
        if crate::file_access::split(name).is_some() {
            // A file-qualified forward name is checked again after expansion.
            return Ok(());
        }
        // A forward/generated declaration may not exist yet. Its import
        // instance and literal export list still establish the privacy boundary.
        let Some((prefix, _)) = name.rsplit_once('@') else {
            return Err(SourceError::from(format!(
                "cannot qualify undeclared global name '{name}'; @ never refers to a local binding"
            ))
            .at(span));
        };
        let Some(Some(root)) = self.import_roots.get(prefix) else {
            return Err(SourceError::from(format!(
                "cannot qualify undeclared global name '{name}'"
            ))
            .at(span));
        };
        let caller = span.source_id as usize;
        if self.exported(name, root) {
            // Preserve the intermediate-import boundary even for forward names.
            let same_instance = self.owners.get(caller).and_then(Option::as_ref) == Some(root)
                && self.prefixes.get(caller).map(String::as_str) == Some(prefix);
            if !same_instance {
                if let Some((parent, _)) = prefix.rsplit_once('@') {
                    if self.prefixes.get(caller).map(String::as_str) != Some(parent)
                        || self.import_roots.get(parent).and_then(Option::as_ref)
                            != self.owners.get(caller).and_then(Option::as_ref)
                    {
                        return Err(SourceError::from(format!(
                            "'{name}' is private behind an intermediate library import"
                        ))
                        .at(span));
                    }
                }
            }
            return Ok(());
        }
        Err(SourceError::from(format!(
            "cannot qualify private declaration '{name}' outside library '{}'",
            root.display()
        ))
        .at(span))
    }

    fn exported(&self, name: &str, root: &Path) -> bool {
        if crate::file_access::split(name).is_some() {
            let owner = name
                .rsplit_once('.')
                .filter(|(_, suffix)| !suffix.contains("::"))
                .map_or(name, |(owner, _)| owner);
            return self
                .resolved_exports
                .get(root)
                .is_some_and(|names| names.contains(owner));
        }
        let original = name.rsplit_once('@').map_or(name, |(_, name)| name);
        // Variant names are not separately exported. Their representation is
        // transparent exactly when the owning enum declaration is exported.
        let original = original
            .split_once('.')
            .map_or(original, |(owner, _)| owner);
        self.exports
            .get(root)
            .is_some_and(|names| names.iter().any(|entry| entry == original))
    }

    pub(crate) fn access(
        &self,
        name: &str,
        use_span: Span,
        representation: bool,
    ) -> Result<(), SourceError> {
        self.access_from(name, use_span, representation)
            .or_else(|error| {
                if crate::generator_authority::source_context(use_span, &self.authorities)
                    .is_some_and(|author| self.access_from(name, author, representation).is_ok())
                {
                    Ok(())
                } else {
                    Err(error)
                }
            })
    }

    fn access_from(
        &self,
        name: &str,
        use_span: Span,
        representation: bool,
    ) -> Result<(), SourceError> {
        if !representation
            && self
                .unstable
                .get(use_span.source_id as usize)
                .is_some_and(|names| {
                    names.contains(name)
                        || (crate::file_access::local_name(name).contains('.')
                            && name
                                .rsplit_once('.')
                                .is_some_and(|(owner, _)| names.contains(owner)))
                })
        {
            return Ok(());
        }
        let Some(declaration) = self.declarations.get(name) else {
            return Ok(());
        };
        let Some(Some(root)) = self.owners.get(declaration.source_id as usize) else {
            return Ok(());
        };
        if self
            .owners
            .get(use_span.source_id as usize)
            .and_then(Option::as_ref)
            == Some(root)
            && self.prefixes.get(use_span.source_id as usize)
                == self.prefixes.get(declaration.source_id as usize)
        {
            return Ok(());
        }
        if !representation && self.exported(name, root) {
            // A dependency's exports are not automatically re-exported by an
            // importing library. Every intermediate boundary must be accessible
            // from this implementation, not merely guessable in a flat name.
            if let Some((prefix, _)) = name.rsplit_once('@') {
                if let Some((parent, _)) = prefix.rsplit_once('@') {
                    let caller = self
                        .owners
                        .get(use_span.source_id as usize)
                        .and_then(Option::as_ref);
                    if self.import_roots.get(parent).and_then(Option::as_ref) != caller
                        || caller.is_none()
                        || self
                            .prefixes
                            .get(use_span.source_id as usize)
                            .map(String::as_str)
                            != Some(parent)
                    {
                        return Err(SourceError::from(format!("'{name}' is private behind an intermediate library import; dependencies are not automatically re-exported")).at(use_span));
                    }
                }
            }
            return Ok(());
        }
        Err(SourceError::from(format!(
            "cannot access private {}'{name}' outside library '{}'",
            if representation {
                "representation of "
            } else {
                "declaration "
            },
            root.display()
        ))
        .at(use_span))
    }

    fn syntax(&self, source: &SpannedExpr) -> Result<(), SourceError> {
        if crate::generator_authority::is_header(&source.expr) {
            return Err(SourceError::from("#generated-context is compiler-owned and cannot appear in source or generator input").at(source.span));
        }
        if matches!(source.expr, Expr::Quote(_) | Expr::QuasiQuote(_)) {
            return Ok(());
        }
        if let Expr::Symbol(name) = &source.expr {
            self.access(name, source.span, false)?;
        }
        if let Expr::List(items) = &source.expr {
            if let Some(Expr::Symbol(head)) = items.first() {
                if let Some(owner) = self.struct_owners.get(head) {
                    self.access(owner, source.span, true)?;
                }
            }
            if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#struct-literal") {
                if let Some(Expr::Symbol(name)) = items.get(1) {
                    let owner = self.struct_owners.get(name).map_or(name, |owner| owner);
                    self.access(
                        owner,
                        source
                            .children
                            .get(1)
                            .map_or(source.span, |child| child.span),
                        true,
                    )?;
                    if let Some(fields) = source.children.get(2) {
                        for field in &fields.children {
                            self.access(
                                owner,
                                field
                                    .children
                                    .first()
                                    .map_or(field.span, |label| label.span),
                                true,
                            )?;
                        }
                    }
                }
            }
        }
        for child in &source.children {
            self.syntax(child)?;
        }
        Ok(())
    }

    fn signature<'a>(
        &self,
        name: &str,
        types: impl IntoIterator<Item = &'a crate::Type>,
        span: Span,
        declaration_source: Option<&SpannedExpr>,
    ) -> Result<(), SourceError> {
        for ty in types {
            let source = crate::type_source(ty);
            for token in crate::lex(&source).map_err(|error| SourceError::from(error.message))? {
                let crate::TokenKind::Symbol(type_name) = token.kind else {
                    continue;
                };
                let Some(declaration) = self.declarations.get(&type_name) else {
                    continue;
                };
                let Some(Some(root)) = self.owners.get(declaration.source_id as usize) else {
                    continue;
                };
                if !self.exported(&type_name, root) {
                    fn occurrence(source: &SpannedExpr, name: &str) -> Option<Span> {
                        if matches!(&source.expr, Expr::Symbol(symbol) if symbol == name) {
                            return Some(source.span);
                        }
                        source
                            .children
                            .iter()
                            .find_map(|child| occurrence(child, name))
                    }
                    return Err(SourceError::from(format!(
                        "exported declaration '{name}' exposes private type '{type_name}'"
                    ))
                    .at(declaration_source
                        .and_then(|source| occurrence(source, &type_name))
                        .unwrap_or(span)));
                }
            }
        }
        Ok(())
    }
}

/// Check generator and helper access before interpretation erases declarations.
pub(crate) fn check_generators(
    forms: &[SpannedExpr],
    files: &[SourceFile],
) -> Result<Visibility, SourceError> {
    let mut declarations = HashMap::new();
    for form in forms {
        for name in crate::generator_provenance::declared_names(&form.expr) {
            declarations.insert(name.to_owned(), form.span);
        }
        if let Expr::List(items) = &form.expr {
            if matches!(items.first(), Some(Expr::Symbol(head)) if matches!(head.as_str(), "#gn" | "#gn-fn" | "#capability"))
            {
                if let Some(Expr::Symbol(name)) = items.get(1) {
                    declarations.insert(name.clone(), form.span);
                }
            }
        }
    }
    let visibility = Visibility::new(files, &HashMap::new(), declarations)?;
    if visibility.exports.is_empty() {
        return Ok(visibility);
    }
    for form in forms {
        visibility
            .syntax(form)
            .map_err(|error| error.attach(files))?;
    }
    Ok(visibility)
}

/// Qualify only explicitly marked source names. Literal syntax and local
/// binding roles are not interpreted by this pre-generator pass.
pub(crate) fn qualify(
    forms: &mut [SpannedExpr],
    visibility: &Visibility,
    files: &[SourceFile],
) -> Result<std::collections::HashSet<Span>, SourceError> {
    fn walk(
        tree: &mut SpannedExpr,
        visibility: &Visibility,
        qualified: &mut std::collections::HashSet<Span>,
    ) -> Result<bool, SourceError> {
        if crate::generator_authority::is_header(&tree.expr) {
            return Err(SourceError::from("#generated-context is compiler-owned and cannot appear in source or generator input").at(tree.span));
        }
        let mut changed = false;
        if let Expr::Symbol(name) = &mut tree.expr {
            if let Some(absolute) = name.strip_prefix('@') {
                if absolute.is_empty() || absolute.starts_with('@') || absolute.contains("@@") {
                    return Err(SourceError::from(
                        "@ must prefix a non-empty context-relative identifier",
                    )
                    .at(tree.span));
                }
                visibility.qualified_access(absolute, tree.span)?;
                qualified.insert(tree.span);
                *name = absolute.to_owned();
                changed = true;
            }
        }
        for child in &mut tree.children {
            changed |= walk(child, visibility, qualified)?;
        }
        if changed {
            match &mut tree.expr {
                Expr::List(items) => {
                    for (item, child) in items.iter_mut().zip(&tree.children) {
                        *item = child.expr.clone();
                    }
                }
                Expr::Quote(inner)
                | Expr::QuasiQuote(inner)
                | Expr::Unquote(inner)
                | Expr::UnquoteSplicing(inner) => {
                    if let Some(child) = tree.children.first() {
                        **inner = child.expr.clone();
                    }
                }
                _ => {}
            }
        }
        Ok(changed)
    }
    let mut qualified = std::collections::HashSet::new();
    for form in forms {
        walk(form, visibility, &mut qualified).map_err(|error| error.attach(files))?;
    }
    Ok(qualified)
}

pub(crate) fn check_contributions(
    forms: &[SpannedExpr],
    files: &[SourceFile],
    origins: &HashMap<u32, Span>,
    references: &HashMap<u32, Span>,
) -> Result<(), SourceError> {
    if !forms.iter().any(|form| matches!(&form.expr, Expr::List(items) if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#distributed-enum"))) { return Ok(()) }
    let declarations = forms
        .iter()
        .filter_map(|form| {
            let Expr::List(items) = &form.expr else {
                return None;
            };
            if !matches!(items.first(), Some(Expr::Symbol(head)) if head == "#distributed-enum") {
                return None;
            }
            let Expr::Symbol(name) = items.get(1)? else {
                return None;
            };
            Some((name.clone(), form.span))
        })
        .collect();
    let mut visibility = Visibility::new(files, origins, declarations)?;
    visibility.authorities.clone_from(references);
    for form in forms {
        let Expr::List(items) = &form.expr else {
            continue;
        };
        if !matches!(items.first(), Some(Expr::Symbol(head)) if head == "#enum-contribute") {
            continue;
        }
        if let Some(Expr::Symbol(name)) = items.get(1) {
            visibility
                .access(
                    name,
                    form.children.get(1).map_or(form.span, |node| node.span),
                    true,
                )
                .map_err(|error| error.attach(files))?;
        }
    }
    Ok(())
}

/// Splicing must check the bundle reference before replacing it with its
/// contents. Otherwise a generated reference could bypass a private bundle's
/// boundary, including authority captured by its generator-authored payload.
pub(crate) fn check_bundle_uses(
    forms: &[SpannedExpr],
    definitions: &HashMap<String, SpannedExpr>,
    files: &[SourceFile],
    origins: &HashMap<u32, Span>,
    references: &HashMap<u32, Span>,
) -> Result<(), SourceError> {
    let mut declarations = definitions
        .iter()
        .map(|(name, definition)| (name.clone(), definition.span))
        .collect::<HashMap<_, _>>();
    for form in forms {
        if let Expr::List(items) = &form.expr {
            if matches!(items.first(), Some(Expr::Symbol(head)) if head == "#syntax") {
                if let Some(Expr::Symbol(name)) = items.get(1) {
                    declarations.insert(name.clone(), form.span);
                }
            }
        }
    }
    if declarations.is_empty() {
        return Ok(());
    }
    let mut visibility = Visibility::new(files, origins, declarations)?;
    visibility.authorities.clone_from(references);
    for form in forms {
        visibility
            .syntax(form)
            .map_err(|error| error.attach(files))?;
    }
    Ok(())
}

/// Uses typed declaration identities so aliases and derived field references
/// cannot bypass representation privacy.
pub(crate) fn check(
    program: &Program,
    declarations: &crate::typed_ir::Declarations,
    global_type: impl Fn(&Expr) -> Option<crate::Type>,
) -> Result<(), SourceError> {
    use crate::{typed_body::NodeKind, typed_ir::DeclarationId};
    let mut names = program.declaration_spans.clone();
    for item in &program.items {
        if let crate::Item::Enum { name, variants, .. } = item {
            if let Some(span) = program.declaration_spans.get(name) {
                for variant in variants {
                    names.insert(variant.name.clone(), *span);
                }
            }
        }
        if let crate::Item::ThreadTask {
            name,
            generated_functions,
            ..
        } = item
        {
            if let Some(span) = program.declaration_spans.get(name) {
                names.insert(format!("{name}::spawn"), *span);
                names.insert(format!("{name}::join"), *span);
                for function in generated_functions {
                    names.insert(function.name.clone(), *span);
                }
                for suffix in ["SpawnError", "SpawnResult", "JoinResult"] {
                    let associated = format!("{name}::{suffix}");
                    if let Some(variants) = declarations.enums.get(&associated) {
                        names.insert(associated, *span);
                        for variant in variants {
                            names.insert(variant.name.clone(), *span);
                        }
                    }
                }
            }
        }
    }
    let mut visibility = Visibility::new(
        &program.source_files,
        &program.generated_source_invocations,
        names,
    )?;
    visibility
        .authorities
        .clone_from(&program.generated_definition_contexts);
    if visibility.exports.is_empty() {
        return Ok(());
    }
    for name in declarations
        .structs
        .keys()
        .chain(declarations.aliases.keys())
    {
        if let Ok(crate::Type::Named(owner)) =
            crate::typed_ir::resolve_type(&crate::Type::Named(name.clone()), &declarations.aliases)
        {
            if declarations.structs.contains_key(&owner) {
                visibility.struct_owners.insert(name.clone(), owner);
            }
        }
    }
    for form in program.declaration_expressions.values() {
        visibility.syntax(form)?;
    }
    fn initializer(
        value: &Expr,
        source: &SpannedExpr,
        visibility: &Visibility,
        declarations: &crate::typed_ir::Declarations,
        global_type: &impl Fn(&Expr) -> Option<crate::Type>,
    ) -> Result<(), SourceError> {
        let Expr::List(items) = value else {
            return Ok(());
        };
        if matches!(items.first(), Some(Expr::Symbol(head)) if head == "get") {
            if let Some(ty) = items.get(1).and_then(global_type) {
                let ty = crate::typed_ir::resolve_type(&ty, &declarations.aliases)
                    .map_err(SourceError::from)?;
                let target = match ty {
                    crate::Type::Reference { target, .. }
                    | crate::Type::PinnedReference { target, .. } => *target,
                    ty => ty,
                };
                if let crate::Type::Named(owner) = target {
                    visibility.access(
                        &owner,
                        source
                            .children
                            .get(2)
                            .map_or(source.span, |field| field.span),
                        true,
                    )?;
                }
            }
        }
        for (index, item) in items.iter().enumerate() {
            initializer(
                item,
                source.children.get(index).unwrap_or(source),
                visibility,
                declarations,
                global_type,
            )?;
        }
        Ok(())
    }
    for item in &program.items {
        if let crate::Item::Let { name, value, .. } | crate::Item::Static { name, value, .. } = item
        {
            if let Some(source) = program.declaration_expressions.get(name) {
                initializer(
                    value,
                    source.children.get(3).unwrap_or(source),
                    &visibility,
                    declarations,
                    &global_type,
                )?;
            }
        }
    }
    // Exported signatures may name opaque exported types, but cannot leak an
    // unexported type through aliases, function signatures, or enum payloads.
    for item in &program.items {
        let (name, types): (&str, Vec<&crate::Type>) = match item {
            crate::Item::Function(function) => (
                &function.name,
                function
                    .parameters
                    .iter()
                    .map(|parameter| &parameter.ty)
                    .chain(std::iter::once(&function.return_type))
                    .collect(),
            ),
            crate::Item::TypeAlias { name, target, .. } => (name, vec![target]),
            crate::Item::Let { name, ty, .. } | crate::Item::Static { name, ty, .. } => {
                (name, vec![ty])
            }
            crate::Item::Enum { name, variants, .. } => (
                name,
                variants
                    .iter()
                    .flat_map(|variant| variant.fields.iter())
                    .collect(),
            ),
            _ => continue,
        };
        let Some(span) = program.declaration_spans.get(name).copied() else {
            continue;
        };
        let Some(Some(root)) = visibility.owners.get(span.source_id as usize) else {
            continue;
        };
        if !visibility.exported(name, root) {
            continue;
        }
        visibility.signature(name, types, span, program.declaration_expressions.get(name))?;
    }
    for item in &program.items {
        let crate::Item::ThreadTask { name, .. } = item else {
            continue;
        };
        let Some(span) = program.declaration_spans.get(name).copied() else {
            continue;
        };
        let Some(Some(root)) = visibility.owners.get(span.source_id as usize) else {
            continue;
        };
        for name in [format!("{name}::spawn"), format!("{name}::join")] {
            if !visibility.exported(&name, root) {
                continue;
            }
            if let Some(id) = declarations.function_id(&name) {
                let signature = &declarations.function(id).signature;
                visibility.signature(
                    &name,
                    signature
                        .parameters
                        .iter()
                        .chain(std::iter::once(&signature.return_type)),
                    span,
                    program.declaration_expressions.get(&name),
                )?;
            }
        }
    }
    for (function, body) in &declarations.bodies {
        let fallback = program.declaration_spans.get(function).copied();
        for node in &body.nodes {
            let Some(span) = node.span.or(fallback) else {
                continue;
            };
            match &node.kind {
                NodeKind::Declaration(DeclarationId::Field(field)) => {
                    let owner =
                        declarations.declaration_name(DeclarationId::Aggregate(field.owner));
                    visibility.access(owner, span, true)?;
                }
                NodeKind::Declaration(id) => {
                    visibility.access(declarations.declaration_name(*id), span, false)?
                }
                NodeKind::Form {
                    head,
                    children,
                    callee,
                    ..
                } => {
                    if let Some(id) = callee {
                        // Normalized calls start with Expr::Function, not the
                        // surface #call keyword. Check that reference token.
                        let reference_span = children
                            .first()
                            .and_then(|id| body.nodes[id.0].span)
                            .unwrap_or(span);
                        visibility.access(
                            declarations.declaration_name(DeclarationId::Function(*id)),
                            reference_span,
                            false,
                        )?;
                    }
                    if head == "struct-literal" {
                        if let Some(id) = children.get(1) {
                            if let NodeKind::Declaration(id @ DeclarationId::Aggregate(_)) =
                                body.nodes[id.0].kind
                            {
                                visibility.access(
                                    declarations.declaration_name(id),
                                    body.nodes[children[1].0].span.unwrap_or(span),
                                    true,
                                )?;
                            }
                        }
                    }
                    if head == "clone" {
                        if let Some(crate::Type::Named(owner)) = node.ty.as_ref().and_then(|ty| {
                            crate::typed_ir::resolve_type(ty, &declarations.aliases).ok()
                        }) {
                            visibility.access(&format!("{owner}::clone"), span, false)?;
                        }
                    }
                }
                _ => {}
            }
        }
        for flow in &declarations.flows[function].nodes {
            let place = match &flow.action {
                crate::typed_flow::FlowAction::Assign { place, .. }
                | crate::typed_flow::FlowAction::Write { place, .. }
                | crate::typed_flow::FlowAction::Read { place, .. }
                | crate::typed_flow::FlowAction::Borrow { place, .. }
                | crate::typed_flow::FlowAction::Clone { place, .. }
                | crate::typed_flow::FlowAction::Release { place, .. } => place,
                _ => continue,
            };
            for segment in &place.segments {
                if let crate::typed_place::Segment::Field(field) = segment {
                    if let Some(span) = flow.span.or(fallback) {
                        visibility.access(
                            declarations.declaration_name(DeclarationId::Aggregate(field.owner)),
                            span,
                            true,
                        )?;
                    }
                }
            }
        }
    }
    Ok(())
}
