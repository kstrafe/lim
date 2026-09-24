use std::{
    fs,
    path::{Path, PathBuf},
};

fn main() {
    let mut files = Vec::new();
    collect_rust_sources(Path::new("src"), &mut files);
    files.push(PathBuf::from("build.rs"));
    files.sort();

    let mut hash = 0xcbf29ce484222325u64;
    for path in files {
        println!("cargo:rerun-if-changed={}", path.display());
        let bytes = fs::read(&path).expect("read compiler source for cache fingerprint");
        for byte in path.to_string_lossy().bytes().chain([0]).chain(bytes) {
            hash ^= u64::from(byte);
            hash = hash.wrapping_mul(0x100000001b3);
        }
    }
    println!("cargo:rustc-env=LIM_BUILD_FINGERPRINT={hash:016x}");
}

fn collect_rust_sources(directory: &Path, files: &mut Vec<PathBuf>) {
    let entries = fs::read_dir(directory).expect("read compiler source directory");
    for entry in entries {
        let path = entry.expect("read compiler source entry").path();
        if path.is_dir() {
            collect_rust_sources(&path, files);
        } else if path.extension().is_some_and(|extension| extension == "rs") {
            files.push(path);
        }
    }
}
