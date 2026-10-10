//! Versioned compilation settings, not executable editor commands.
use crate::{CompileConfig, TargetDescription};
use std::{
    collections::HashSet,
    fs,
    path::{Path, PathBuf},
};

pub struct LspContext {
    pub entry: PathBuf,
    pub target: TargetDescription,
    pub config: CompileConfig,
}

impl LspContext {
    pub fn read(path: &Path) -> Result<Self, String> {
        if fs::metadata(path)
            .map_err(|e| format!("{}: {e}", path.display()))?
            .len()
            > 1024 * 1024
        {
            return Err(format!("{}: LSP context exceeds 1 MiB", path.display()));
        }
        let text = fs::read_to_string(path).map_err(|e| format!("{}: {e}", path.display()))?;
        let base = path.parent().unwrap_or(Path::new("."));
        let mut schema = false;
        let mut entry = None;
        let mut target = None;
        // Never derive defaults from the host running the editor.
        let mut config = CompileConfig {
            values: Default::default(),
            module_paths: Vec::new(),
            explicit_keys: HashSet::new(),
        };
        let mut seen = HashSet::new();
        let mut cfg_seen = HashSet::new();
        for (line, text) in text.lines().enumerate() {
            let text = text.trim();
            if text.is_empty() || text.starts_with('#') {
                continue;
            }
            let error = |message: &str| format!("{}:{}: {message}", path.display(), line + 1);
            let (key, value) = text
                .split_once('=')
                .ok_or_else(|| error("expected key = value"))?;
            let key = key.trim();
            let value = value.trim();
            if !matches!(key, "cfg" | "module-path") && !seen.insert(key.to_owned()) {
                return Err(error("duplicate context key"));
            }
            if key == "schema-version" {
                if value != "1" {
                    return Err(error("expected schema-version = 1"));
                }
                schema = true;
                continue;
            }
            let decoded =
                crate::lsp::json::parse(value).map_err(|_| error("expected a quoted string"))?;
            let value = decoded
                .string()
                .ok_or_else(|| error("expected a quoted string"))?;
            match key {
                "entry" if !value.is_empty() => {
                    entry = Some(crate::editor::path_key(&base.join(value)))
                }
                "target" => target = Some(TargetDescription::parse(value).map_err(|e| error(&e))?),
                "module-path" if !value.is_empty() => {
                    config.add_module_path(crate::editor::path_key(&base.join(value)))
                }
                "cfg" => {
                    let (name, value) = value
                        .split_once('=')
                        .ok_or_else(|| error("cfg requires KEY=VALUE"))?;
                    if name.is_empty() || !cfg_seen.insert(name.to_owned()) {
                        return Err(error("empty or duplicate cfg key"));
                    }
                    config.set(name, value);
                }
                _ => return Err(error("unknown or empty context setting")),
            }
        }
        if !schema {
            return Err(format!("{}: missing schema-version = 1", path.display()));
        }
        let target = target.ok_or_else(|| format!("{}: missing target", path.display()))?;
        config = config.with_target(target);
        Ok(Self {
            entry: entry.ok_or_else(|| format!("{}: missing entry", path.display()))?,
            target,
            config,
        })
    }

    /// Store effective settings using absolute paths for location-independent
    /// CLI generation. Handwritten relative paths resolve beside lim.lsp.
    pub fn write(&self, path: &Path) -> Result<(), String> {
        if path.extension().is_none_or(|extension| extension != "lsp") {
            return Err("LSP context output must have a .lsp extension".into());
        }
        crate::reject_source_output_collision(&self.entry, path).map_err(|e| e.to_string())?;
        if path.exists() {
            let source = fs::read_to_string(&self.entry).map_err(|e| e.to_string())?;
            let program =
                crate::parse_program_from_path_with_config(&source, &self.entry, &self.config)?;
            for file in program
                .source_files
                .iter()
                .filter(|file| file.path.is_file())
            {
                crate::reject_source_output_collision(&file.path, path)
                    .map_err(|e| e.to_string())?;
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
            "schema-version = 1\nentry = {}\ntarget = {}\n",
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
        if fs::read_to_string(path).ok().as_deref() != Some(&text) {
            crate::write_output_atomic(path, text)
                .map_err(|e| format!("{}: {e}", path.display()))?;
        }
        Ok(())
    }
}

pub(crate) fn discover(path: &Path) -> Option<PathBuf> {
    crate::editor::path_key(path)
        .parent()?
        .ancestors()
        .map(|directory| directory.join("lim.lsp"))
        .find(|path| path.exists())
}
