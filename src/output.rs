//! Same-filesystem staging: only successfully completed artifacts are published.
use std::{
    fs, io,
    path::{Path, PathBuf},
    sync::atomic::{AtomicUsize, Ordering},
};

static NEXT: AtomicUsize = AtomicUsize::new(0);

pub(crate) struct StagingDirectory(pub(crate) PathBuf);
impl StagingDirectory {
    pub(crate) fn beside(output: &Path) -> io::Result<Self> {
        let parent = output
            .parent()
            .filter(|p| !p.as_os_str().is_empty())
            .unwrap_or(Path::new("."));
        loop {
            let path = parent.join(format!(
                ".lim-output-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            let mut builder = fs::DirBuilder::new();
            #[cfg(unix)]
            {
                use std::os::unix::fs::DirBuilderExt;
                builder.mode(0o700);
            }
            match builder.create(&path) {
                Ok(()) => return Ok(Self(path)),
                Err(error) if error.kind() == io::ErrorKind::AlreadyExists => continue,
                Err(error) => return Err(error),
            }
        }
    }
}
impl Drop for StagingDirectory {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

pub fn write_output_atomic(output: &Path, bytes: impl AsRef<[u8]>) -> io::Result<()> {
    let directory = StagingDirectory::beside(output)?;
    let staged = directory.0.join("output");
    fs::write(&staged, bytes)?;
    fs::rename(staged, output)
}

/// Reject both canonical aliases and hard links to a source file.
pub fn reject_source_output_collision(source: &Path, output: &Path) -> io::Result<()> {
    let source_path = fs::canonicalize(source)?;
    let output_path = match fs::canonicalize(output) {
        Ok(path) => path,
        Err(error) if error.kind() == io::ErrorKind::NotFound => return Ok(()),
        Err(error) => return Err(error),
    };
    let mut same = source_path == output_path;
    #[cfg(unix)]
    {
        use std::os::unix::fs::MetadataExt;
        let source_metadata = fs::metadata(&source_path)?;
        let output_metadata = fs::metadata(&output_path)?;
        same |= source_metadata.dev() == output_metadata.dev()
            && source_metadata.ino() == output_metadata.ino();
    }
    if same {
        Err(io::Error::new(
            io::ErrorKind::InvalidInput,
            format!(
                "output '{}' would replace source '{}'",
                output.display(),
                source.display()
            ),
        ))
    } else {
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn linker_failures_preserve_binary_and_success_preserves_executable_mode() {
        let temp = StagingDirectory::beside(&std::env::temp_dir().join("unused")).unwrap();
        let output = temp.0.join("program");
        fs::write(&output, b"original").unwrap();
        let target = crate::TargetDescription::X86_64_SYSTEM_V;
        assert!(crate::link_native_binary("invalid assembly", &output, &[], &[], target).is_err());
        assert_eq!(fs::read(&output).unwrap(), b"original");
        let program = crate::parse_program("(#fn main () u64 (#return 42u64))").unwrap();
        let assembly = crate::generate_assembly_for_target(&program, target).unwrap();
        assert!(crate::link_native_binary(
            &assembly,
            &output,
            &[],
            &["lim_missing_library_test".into()],
            target
        )
        .is_err());
        assert_eq!(fs::read(&output).unwrap(), b"original");
        crate::link_native_binary(&assembly, &output, &[], &[], target).unwrap();
        assert_eq!(
            std::process::Command::new(&output).status().unwrap().code(),
            Some(42)
        );
        assert_eq!(fs::read_dir(&temp.0).unwrap().count(), 1);
    }

    #[test]
    fn source_aliases_and_import_collisions_are_rejected() {
        let temp = StagingDirectory::beside(&std::env::temp_dir().join("unused")).unwrap();
        let input = temp.0.join("input.lim");
        let imported = temp.0.join("types.lim");
        let source = "(#import \"types.lim\") (#fn main () u64 (#return 42u64))";
        fs::write(&input, source).unwrap();
        fs::write(&imported, "(#type Number u64)").unwrap();
        let alias = temp.0.join("alias");
        fs::hard_link(&input, &alias).unwrap();
        assert!(reject_source_output_collision(&input, &alias).is_err());
        #[cfg(unix)]
        {
            let symlink = temp.0.join("symlink");
            std::os::unix::fs::symlink(&input, &symlink).unwrap();
            assert!(reject_source_output_collision(&input, &symlink).is_err());
        }
        let error = crate::compile_source_to_assembly_for_output(
            source,
            &input,
            &crate::CompileConfig::default(),
            &temp.0.join("cache"),
            crate::TargetDescription::X86_64_SYSTEM_V,
            Some(&imported),
        )
        .unwrap_err();
        assert!(
            error.message.contains("would replace source"),
            "{}",
            error.message
        );
        assert_eq!(fs::read_to_string(&imported).unwrap(), "(#type Number u64)");
    }
    #[test]
    fn concurrent_publication_is_whole_and_failures_preserve_destination() {
        let temp = StagingDirectory::beside(&std::env::temp_dir().join("unused")).unwrap();
        let output = temp.0.join("result");
        fs::write(&output, b"original").unwrap();
        std::thread::scope(|scope| {
            for byte in [b'a', b'b', b'c'] {
                let output = &output;
                scope.spawn(move || write_output_atomic(output, vec![byte; 100_000]).unwrap());
            }
        });
        let contents = fs::read(&output).unwrap();
        assert_eq!(contents.len(), 100_000);
        assert!(contents.iter().all(|byte| *byte == contents[0]));
        let target_directory = temp.0.join("directory");
        fs::create_dir(&target_directory).unwrap();
        fs::write(target_directory.join("sentinel"), b"keep").unwrap();
        assert!(write_output_atomic(&target_directory, b"replace").is_err());
        assert_eq!(
            fs::read(target_directory.join("sentinel")).unwrap(),
            b"keep"
        );
        assert_eq!(fs::read_dir(&temp.0).unwrap().count(), 2);
    }
}
