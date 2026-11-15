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
            let builder = fs::DirBuilder::new();
            #[cfg(unix)]
            let builder = {
                use std::os::unix::fs::DirBuilderExt;
                let mut builder = builder;
                builder.mode(0o700);
                builder
            };
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
    use io::Write;
    write_output_atomic_with(output, |file| file.write_all(bytes.as_ref()))
}

/// Stream an artifact into same-filesystem staging. A failed writer leaves
/// the destination untouched and removes its partial temporary output.
pub fn write_output_atomic_with(
    output: &Path,
    write: impl FnOnce(&mut fs::File) -> io::Result<()>,
) -> io::Result<()> {
    let directory = StagingDirectory::beside(output)?;
    let staged = directory.0.join("output");
    let mut file = fs::File::create(&staged)?;
    write(&mut file)?;
    drop(file);
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
    let same = source_path == output_path;
    #[cfg(unix)]
    let same = {
        use std::os::unix::fs::MetadataExt;
        let source_metadata = fs::metadata(&source_path)?;
        let output_metadata = fs::metadata(&output_path)?;
        same || (source_metadata.dev() == output_metadata.dev()
            && source_metadata.ino() == output_metadata.ino())
    };
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
    fn failed_streaming_output_preserves_destination_and_removes_staging() {
        use io::Write;
        let temp = StagingDirectory::beside(&std::env::temp_dir().join("unused")).unwrap();
        let output = temp.0.join("receipt.json");
        fs::write(&output, b"previous receipt").unwrap();
        for path in [&output, &temp.0.join("new.json")] {
            let error = write_output_atomic_with(path, |file| {
                file.write_all(b"partial receipt")?;
                Err(io::Error::new(
                    io::ErrorKind::BrokenPipe,
                    "injected failure",
                ))
            })
            .unwrap_err();
            assert_eq!(error.kind(), io::ErrorKind::BrokenPipe);
            assert_eq!(fs::read(&output).unwrap(), b"previous receipt");
            assert_eq!(fs::read_dir(&temp.0).unwrap().count(), 1);
        }
        write_output_atomic_with(&output, |file| file.write_all(b"complete receipt")).unwrap();
        assert_eq!(fs::read(&output).unwrap(), b"complete receipt");
        assert_eq!(fs::read_dir(&temp.0).unwrap().count(), 1);
    }

    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    #[test]
    fn inherited_writer_blocks_exec_even_after_parent_closes_descriptor() {
        use std::{
            ffi::c_void,
            io::Write,
            os::{fd::AsRawFd, unix::fs::PermissionsExt, unix::net::UnixStream},
            process::Command,
        };

        unsafe extern "C" {
            fn fork() -> i32;
            fn read(fd: i32, buffer: *mut c_void, count: usize) -> isize;
            fn close(fd: i32) -> i32;
            fn _exit(status: i32) -> !;
            fn kill(pid: i32, signal: i32) -> i32;
            fn waitpid(pid: i32, status: *mut i32, options: i32) -> i32;
        }

        struct ChildGuard(i32);
        impl Drop for ChildGuard {
            fn drop(&mut self) {
                // SAFETY: this is our unreaped fork child, including on panic.
                // Never leave a child blocked holding a writable descriptor.
                unsafe {
                    kill(self.0, 9);
                    let mut status = 0;
                    while waitpid(self.0, &mut status, 0) == -1 {
                        if io::Error::last_os_error().kind() != io::ErrorKind::Interrupted {
                            break;
                        }
                    }
                }
            }
        }

        let directory = StagingDirectory::beside(&std::env::temp_dir().join("unused")).unwrap();
        let binary = directory.0.join("program");
        // mov eax, SYS_exit; xor edi, edi; syscall -- no compiler or libc needed.
        let image =
            crate::elf_writer::executable(&[0xb8, 60, 0, 0, 0, 0x31, 0xff, 0x0f, 0x05], 0).unwrap();
        fs::write(&binary, image).unwrap();
        fs::set_permissions(&binary, fs::Permissions::from_mode(0o700)).unwrap();
        let writer = fs::OpenOptions::new().write(true).open(&binary).unwrap();
        let writer_fd = writer.as_raw_fd();
        let (mut release, inherited) = UnixStream::pair().unwrap();
        let inherited_fd = inherited.as_raw_fd();

        // SAFETY: the child calls only async-signal-safe C functions before
        // _exit; it never allocates, locks Rust state, or runs Rust destructors.
        let pid = unsafe { fork() };
        assert!(pid >= 0, "fork failed: {}", io::Error::last_os_error());
        if pid == 0 {
            unsafe {
                let mut byte = 0u8;
                while read(inherited_fd, (&mut byte as *mut u8).cast(), 1) == -1 {}
                close(writer_fd);
                _exit(0);
            }
        }
        let _child = ChildGuard(pid);
        drop(inherited);
        drop(writer);
        assert_eq!(
            fs::read_link(format!("/proc/{pid}/fd/{writer_fd}")).unwrap(),
            binary,
            "the forked child still holds the parent's closed writer"
        );
        let error = Command::new(&binary).spawn().unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::ExecutableFileBusy);

        release.write_all(&[1]).unwrap();
        assert_eq!(
            crate::test_process::status(&mut Command::new(&binary))
                .unwrap()
                .code(),
            Some(0)
        );
    }

    #[test]
    fn linker_failures_preserve_binary_and_success_preserves_executable_mode() {
        let temp = StagingDirectory::beside(&std::env::temp_dir().join("unused")).unwrap();
        let output = temp.0.join("program");
        fs::write(&output, b"original").unwrap();
        let target = crate::TargetDescription::X86_64_SYSTEM_V;
        assert!(crate::link_native_binary("invalid assembly", &output, &[], &[], target).is_err());
        assert_eq!(fs::read(&output).unwrap(), b"original");
        let program = crate::parse_program("(#fn main () #u64 (#return 42u64))").unwrap();
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
            crate::test_process::status(&mut std::process::Command::new(&output))
                .unwrap()
                .code(),
            Some(42)
        );
        assert_eq!(fs::read_dir(&temp.0).unwrap().count(), 1);
    }

    #[test]
    fn source_aliases_and_import_collisions_are_rejected() {
        let temp = StagingDirectory::beside(&std::env::temp_dir().join("unused")).unwrap();
        let input = temp.0.join("input.lim");
        let imported = temp.0.join("types.lim");
        let source = "(#alias Number = ./types.lim::Number) (#fn main () #u64 (#return 42u64))";
        fs::write(&input, source).unwrap();
        fs::write(&imported, "(#type Number #u64)").unwrap();
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
        assert_eq!(
            fs::read_to_string(&imported).unwrap(),
            "(#type Number #u64)"
        );
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
