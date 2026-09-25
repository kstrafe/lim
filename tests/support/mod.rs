#![allow(dead_code)]

use std::os::unix::process::CommandExt;
use std::{
    fs,
    io::Read,
    path::{Path, PathBuf},
    process::{Command, ExitStatus, Stdio},
    sync::{
        atomic::{AtomicBool, AtomicU64, Ordering},
        Arc,
    },
    thread,
    time::{Duration, Instant},
};

pub struct Scratch(PathBuf);
impl Scratch {
    pub fn new(label: &str) -> Self {
        static NEXT: AtomicU64 = AtomicU64::new(0);
        loop {
            let path = std::env::temp_dir().join(format!(
                "lim-{label}-{}-{}",
                std::process::id(),
                NEXT.fetch_add(1, Ordering::Relaxed)
            ));
            match fs::create_dir(&path) {
                Ok(()) => return Self(path),
                Err(error) if error.kind() == std::io::ErrorKind::AlreadyExists => continue,
                Err(error) => panic!("create scratch directory: {error}"),
            }
        }
    }
    pub fn path(&self) -> &Path {
        &self.0
    }
}
impl Drop for Scratch {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

fn capture(
    mut input: impl Read,
    limit: usize,
    exceeded: Arc<AtomicBool>,
) -> std::io::Result<Vec<u8>> {
    let mut result = Vec::new();
    let mut buffer = [0; 4096];
    loop {
        let count = input.read(&mut buffer)?;
        if count == 0 {
            return Ok(result);
        }
        let keep = count.min(limit.saturating_sub(result.len()));
        result.extend_from_slice(&buffer[..keep]);
        if keep < count {
            exceeded.store(true, Ordering::Relaxed);
        }
    }
}

pub fn run(
    command: &mut Command,
    budget: Duration,
    output_limit: usize,
) -> Result<(ExitStatus, Vec<u8>, Vec<u8>), String> {
    // Every child gets a new group. Never send a signal to our own group.
    let mut child = command
        .process_group(0)
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| error.to_string())?;
    let pid = i32::try_from(child.id()).expect("Linux process ID fits i32");
    assert!(pid > 1);
    let exceeded = Arc::new(AtomicBool::new(false));
    let stdout = child.stdout.take().unwrap();
    let stderr = child.stderr.take().unwrap();
    let out_flag = exceeded.clone();
    let err_flag = exceeded.clone();
    let out = thread::spawn(move || capture(stdout, output_limit, out_flag));
    let err = thread::spawn(move || capture(stderr, output_limit, err_flag));
    let started = Instant::now();
    let result = loop {
        if exceeded.load(Ordering::Relaxed) {
            break Err("output limit exceeded".to_owned());
        }
        match child.try_wait() {
            Ok(Some(status)) => break Ok(status),
            Err(error) => break Err(error.to_string()),
            Ok(None) => {}
        }
        if started.elapsed() >= budget {
            break Err(format!("timeout after {budget:?}"));
        }
        thread::sleep(Duration::from_millis(5));
    };
    unsafe extern "C" {
        fn kill(pid: i32, signal: i32) -> i32;
    }
    // SAFETY: -pid identifies only the new child's process group. SIGKILL
    // also closes pipes held by descendants when the direct child has exited.
    unsafe {
        kill(-pid, 9);
    }
    let _ = child.wait();
    let stdout = out
        .join()
        .map_err(|_| "stdout reader panicked")?
        .map_err(|e| e.to_string())?;
    let stderr = err
        .join()
        .map_err(|_| "stderr reader panicked")?
        .map_err(|e| e.to_string())?;
    let result = if exceeded.load(Ordering::Relaxed) {
        Err("output limit exceeded".to_owned())
    } else {
        result
    };
    result
        .map(|status| (status, stdout.clone(), stderr.clone()))
        .map_err(|error| {
            format!(
                "{error}\nstdout (bounded): {}\nstderr (bounded): {}",
                String::from_utf8_lossy(&stdout),
                String::from_utf8_lossy(&stderr)
            )
        })
}
