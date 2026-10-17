//! Versioned compilation settings, not executable editor commands.
use crate::{CompileConfig, TargetDescription};
use std::{
    cell::RefCell,
    collections::HashSet,
    fs,
    path::{Path, PathBuf},
};

#[derive(Clone)]
pub struct LspContext {
    pub entry: PathBuf,
    pub target: TargetDescription,
    pub config: CompileConfig,
}

impl LspContext {
    pub fn read(path: &Path) -> Result<Self, String> {
        let mut contexts = Self::read_all(path)?;
        if contexts.len() != 1 {
            return Err(format!(
                "{}: expected one compilation context, found {}",
                path.display(),
                contexts.len()
            ));
        }
        Ok(contexts.remove(0))
    }

    /// Read independent compilation contexts; never merge their symbol tables.
    pub fn read_all(path: &Path) -> Result<Vec<Self>, String> {
        if fs::metadata(path)
            .map_err(|e| format!("{}: {e}", path.display()))?
            .len()
            > 1024 * 1024
        {
            return Err(format!("{}: LSP context exceeds 1 MiB", path.display()));
        }
        let text = fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
        let base = path.parent().unwrap_or(Path::new("."));
        let mut schema = None;
        let mut builder = Builder::new();
        let mut contexts = Vec::new();
        let mut section = false;
        for (line, text) in text.lines().enumerate() {
            let text = text.trim();
            if text.is_empty() || text.starts_with('#') {
                continue;
            }
            let error = |message: &str| format!("{}:{}: {message}", path.display(), line + 1);
            if text == "[[context]]" {
                if schema != Some(2) {
                    return Err(error("[[context]] requires schema-version = 2"));
                }
                if section {
                    contexts.push(builder.finish(path)?);
                    builder = Builder::new();
                }
                if contexts.len() >= MAX_CONTEXTS {
                    return Err(error("too many compilation contexts (maximum 128)"));
                }
                section = true;
                continue;
            }
            let (key, value) = text
                .split_once('=')
                .ok_or_else(|| error("expected key = value"))?;
            let key = key.trim();
            let value = value.trim();
            if key == "schema-version" {
                if schema.is_some()
                    || section
                    || !builder.seen.is_empty()
                    || !builder.cfg_seen.is_empty()
                    || !builder.config.module_paths.is_empty()
                {
                    return Err(error("duplicate or misplaced schema-version"));
                }
                schema = Some(match value {
                    "1" => 1,
                    "2" => 2,
                    _ => return Err(error("expected schema-version = 1 or 2")),
                });
                continue;
            }
            if schema == Some(2) && !section {
                return Err(error(
                    "settings require a [[context]] block with schema-version = 2",
                ));
            }
            if !matches!(key, "cfg" | "module-path") && !builder.seen.insert(key.to_owned()) {
                return Err(error("duplicate context key"));
            }
            let decoded =
                crate::lsp::json::parse(value).map_err(|_| error("expected a quoted string"))?;
            let value = decoded
                .string()
                .ok_or_else(|| error("expected a quoted string"))?;
            match key {
                "entry" if !value.is_empty() => {
                    builder.entry = Some(crate::editor::path_key(&base.join(value)))
                }
                "target" => {
                    builder.target = Some(TargetDescription::parse(value).map_err(|e| error(&e))?)
                }
                "module-path" if !value.is_empty() => builder
                    .config
                    .add_module_path(crate::editor::path_key(&base.join(value))),
                "cfg" => {
                    let (name, value) = value
                        .split_once('=')
                        .ok_or_else(|| error("cfg requires KEY=VALUE"))?;
                    if name.is_empty() || !builder.cfg_seen.insert(name.to_owned()) {
                        return Err(error("empty or duplicate cfg key"));
                    }
                    builder.config.set(name, value);
                }
                _ => return Err(error("unknown or empty context setting")),
            }
        }
        if schema.is_none() {
            return Err(format!("{}: missing schema-version", path.display()));
        }
        if schema == Some(2) && !section {
            return Err(format!(
                "{}: schema-version = 2 requires at least one [[context]]",
                path.display()
            ));
        }
        contexts.push(builder.finish(path)?);
        let mut unique: Vec<Self> = Vec::new();
        for context in contexts {
            if unique
                .iter()
                .any(|previous| previous.same_settings(&context))
            {
                return Err(format!(
                    "{}: duplicate compilation context for '{}'",
                    path.display(),
                    context.entry.display()
                ));
            }
            unique.push(context);
        }
        Ok(unique)
    }

    fn same_settings(&self, other: &Self) -> bool {
        self.entry == other.entry
            && self.target == other.target
            && self.config.values == other.config.values
            && self.config.module_paths == other.config.module_paths
    }

    fn normalized(&self) -> Self {
        let mut context = self.clone();
        context.entry = crate::editor::path_key(&context.entry);
        context.config = context.config.with_target(context.target);
        context.config.module_paths = context
            .config
            .module_paths
            .iter()
            .map(|path| crate::editor::path_key(path))
            .collect();
        context
    }

    pub(crate) fn label(&self) -> String {
        let mut cfg = self.config.values.iter().collect::<Vec<_>>();
        cfg.sort();
        let target = match self.target {
            TargetDescription::X86_64_SYSTEM_V => "x86_64-sysv",
            TargetDescription::AARCH64_LINUX => "aarch64-linux",
            _ => "unsupported",
        };
        format!(
            "{} [target: {target}; cfg: {}; module-paths: {}]",
            self.entry.display(),
            cfg.into_iter()
                .map(|(key, value)| format!("{key}={value}"))
                .collect::<Vec<_>>()
                .join(", "),
            self.config
                .module_paths
                .iter()
                .map(|path| path.display().to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }

    /// Record another effective invocation without discarding existing entries.
    pub fn record(&self, path: &Path) -> Result<(), String> {
        if path.extension().is_none_or(|extension| extension != "lsp") {
            return Err("LSP context output must have a .lsp extension".into());
        }
        // Serialize the read/merge/publication across parallel binary/test builds.
        // The OS releases the advisory lock on process exit, even after a crash.
        let cache = path.parent().unwrap_or(Path::new(".")).join(".lim/cache");
        fs::create_dir_all(&cache).map_err(|error| error.to_string())?;
        let identity = crate::editor::path_key(path);
        let digest = crate::generator::stable_hash(identity.to_string_lossy().as_bytes());
        let lock = fs::OpenOptions::new()
            .read(true)
            .write(true)
            .create(true)
            .truncate(false)
            .open(cache.join(format!("lsp-context-{digest:032x}.lock")))
            .map_err(|error| error.to_string())?;
        lock.lock()
            .map_err(|error| format!("cannot lock LSP context '{}': {error}", path.display()))?;
        let mut contexts = if path.exists() {
            Self::read_all(path)?
        } else {
            Vec::new()
        };
        let context = self.normalized();
        if contexts
            .iter()
            .any(|previous| previous.same_settings(&context))
        {
            return Ok(());
        }
        contexts.push(context);
        Self::write_all(&contexts, path)
    }

    /// Store effective settings using absolute paths for location-independent
    /// CLI generation. Handwritten relative paths resolve beside lim.lsp.
    pub fn write(&self, path: &Path) -> Result<(), String> {
        Self::write_all(std::slice::from_ref(self), path)
    }

    /// Replace the context document explicitly; CLI recording uses `record`.
    pub fn write_all(contexts: &[Self], path: &Path) -> Result<(), String> {
        if path.extension().is_none_or(|extension| extension != "lsp") {
            return Err("LSP context output must have a .lsp extension".into());
        }
        if contexts.is_empty() || contexts.len() > MAX_CONTEXTS {
            return Err("LSP context file requires 1 to 128 compilation contexts".into());
        }
        let contexts = contexts.iter().map(Self::normalized).collect::<Vec<_>>();
        let mut text = String::from("schema-version = 2\n");
        for (index, context) in contexts.iter().enumerate() {
            if contexts[..index]
                .iter()
                .any(|previous| previous.same_settings(context))
            {
                return Err("duplicate compilation context".into());
            }
            text.push_str("\n[[context]]\n");
            text.push_str(&context.settings_text(path)?);
        }
        if text.len() > 1024 * 1024 {
            return Err("LSP context exceeds 1 MiB".into());
        }
        if fs::read_to_string(path).ok().as_deref() != Some(&text) {
            crate::write_output_atomic(path, text)
                .map_err(|e| format!("{}: {e}", path.display()))?;
        }
        Ok(())
    }

    fn settings_text(&self, path: &Path) -> Result<String, String> {
        if crate::editor::path_key(&self.entry) == crate::editor::path_key(path) {
            return Err("LSP context output must not replace an entry source".into());
        }
        if self.entry.exists() {
            crate::reject_source_output_collision(&self.entry, path).map_err(|e| e.to_string())?;
        }
        if path.exists() {
            if let Ok(source) = fs::read_to_string(&self.entry) {
                // Recording one healthy build must not require every older
                // context to compile. Import loading is enough for collision
                // protection; it does not evaluate generators or check types.
                match crate::load_imports_with_sources(
                    &source,
                    self.entry.parent().unwrap_or(Path::new(".")),
                    Some(&self.entry),
                    &self.config,
                ) {
                    Ok((_, files)) => {
                        for file in files.iter().filter(|file| file.path.is_file()) {
                            crate::reject_source_output_collision(&file.path, path)
                                .map_err(|e| e.to_string())?;
                        }
                    }
                    Err(error) => {
                        if let Some(source) = error
                            .source_name
                            .as_deref()
                            .map(Path::new)
                            .filter(|path| path.is_file())
                        {
                            crate::reject_source_output_collision(source, path)
                                .map_err(|e| e.to_string())?;
                        }
                    }
                }
            }
        }
        let quote = crate::diagnostic_json::quoted;
        let path_text = |path: &Path| -> Result<String, String> {
            crate::editor::path_key(path)
                .to_str()
                .map(str::to_owned)
                .ok_or_else(|| "LSP context paths must be UTF-8".to_owned())
        };
        let mut text = format!(
            "entry = {}\ntarget = {}\n",
            quote(&path_text(&self.entry)?),
            quote(match self.target {
                TargetDescription::X86_64_SYSTEM_V => "x86_64-sysv",
                TargetDescription::AARCH64_LINUX => "aarch64-linux",
                _ => return Err("unsupported LSP context target".into()),
            })
        );
        let config = self.config.with_target(self.target);
        let mut keys = config.values.iter().collect::<Vec<_>>();
        keys.sort();
        for (key, value) in keys {
            text.push_str(&format!("cfg = {}\n", quote(&format!("{key}={value}"))));
        }
        for module in &self.config.module_paths {
            text.push_str(&format!("module-path = {}\n", quote(&path_text(module)?)));
        }
        Ok(text)
    }
}

const MAX_CONTEXTS: usize = 128;

struct Builder {
    entry: Option<PathBuf>,
    target: Option<TargetDescription>,
    config: CompileConfig,
    seen: HashSet<String>,
    cfg_seen: HashSet<String>,
}
impl Builder {
    fn new() -> Self {
        Self {
            entry: None,
            target: None,
            config: CompileConfig {
                values: Default::default(),
                module_paths: Vec::new(),
                explicit_keys: HashSet::new(),
            },
            seen: HashSet::new(),
            cfg_seen: HashSet::new(),
        }
    }
    fn finish(self, path: &Path) -> Result<LspContext, String> {
        let target = self
            .target
            .ok_or_else(|| format!("{}: missing target", path.display()))?;
        Ok(LspContext {
            entry: self
                .entry
                .ok_or_else(|| format!("{}: missing entry", path.display()))?,
            target,
            config: self.config.with_target(target),
        })
    }
}

thread_local! { static SELECTED: RefCell<Option<LspContext>> = const { RefCell::new(None) }; }

/// Scope one independent entry during a multi-context editor query.
pub(crate) fn with_selected<R>(context: &LspContext, operation: impl FnOnce() -> R) -> R {
    struct Restore(Option<LspContext>);
    impl Drop for Restore {
        fn drop(&mut self) {
            SELECTED.with(|selected| selected.replace(self.0.take()));
        }
    }
    let _restore = Restore(SELECTED.with(|selected| selected.replace(Some(context.clone()))));
    operation()
}

pub(crate) fn selected(path: &Path) -> Result<LspContext, String> {
    SELECTED
        .with(|selected| selected.borrow().clone())
        .map_or_else(|| LspContext::read(path), Ok)
}

pub(crate) fn discover(path: &Path) -> Option<PathBuf> {
    crate::editor::path_key(path)
        .parent()?
        .ancestors()
        .map(|directory| directory.join("lim.lsp"))
        .find(|path| path.exists())
}
