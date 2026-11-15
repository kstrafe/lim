mod support;

use std::{fs, process::Command, time::Duration};

const HEAP: &str = include_str!("../library/system_allocator.lim");
const HELPERS: &str = r#"
#fn allocate-required {
  #params = ((size #usize));
  #returns = (#ptr-mut #u8);
  #effects = ((#effects-of system-allocate)); #body = (
    (#return (#match (#call system-allocate ((size size)))
      (#case (SystemAllocationResult.SystemAllocated pointer) pointer)
      (#case (SystemAllocationResult.SystemAllocationFailed error) (#panic))))
  );
}
#unsafe-fn resize-required {
  #params = ((pointer (#ptr-mut #u8)) (size #usize));
  #returns = (#ptr-mut #u8);
  #effects = ((#effects-of system-reallocate)); #body = (
    (#return (#match (#unsafe (#unsafe-call system-reallocate ((pointer pointer) (size size))))
      (#case (SystemAllocationResult.SystemAllocated resized) resized)
      (#case (SystemAllocationResult.SystemAllocationFailed error) (#panic))))
  );
}
#unsafe-fn fill {
  #params = ((pointer (#ptr-mut #u8)) (size #usize));
  #returns = ();
  #effects = (#global-access #io); #body = (
    (#let-mut index #usize 0usize)
    (#while (#usize::lt index size)
      (#unsafe (#ptr-write (#ptr-offset pointer index) (#as (#usize::rem-wrap index 251usize) #u8)))
      (#set index (#usize::add-wrap index 1usize)))
    (#return ())
  );
}
#unsafe-fn verify {
  #params = ((pointer (#ptr-mut #u8)) (size #usize));
  #returns = ();
  #effects = (#global-access #io); #body = (
    (#let-mut index #usize 0usize)
    (#while (#usize::lt index size)
      (#assert (#u8::eq (#unsafe (#ptr-read (#ptr-offset pointer index))) (#as (#usize::rem-wrap index 251usize) #u8)))
      (#set index (#usize::add-wrap index 1usize)))
    (#return ())
  );
}
"#;

fn replace_calls(source: &str, replacements: &[(&str, &str)]) -> String {
    fn collect(
        node: &lim::SpannedExpr,
        replacements: &[(&str, &str)],
        edits: &mut Vec<(lim::Span, String)>,
    ) {
        if matches!(node.children.first().map(|child| &child.expr), Some(lim::Expr::Symbol(head)) if matches!(head.as_str(), "#call" | "#unsafe-call"))
        {
            let callee = &node.children[1];
            if let lim::Expr::Symbol(name) = &callee.expr {
                if let Some((_, replacement)) = replacements.iter().find(|(old, _)| name == old) {
                    edits.push((callee.span, replacement.to_string()));
                }
            }
        }
        for child in &node.children {
            collect(child, replacements, edits);
        }
    }
    let mut edits = Vec::new();
    for node in lim::parse_source_unit(source).unwrap() {
        collect(&node, replacements, &mut edits);
    }
    for (_, replacement) in replacements {
        assert!(
            edits.iter().any(|(_, name)| name == replacement),
            "failure hook was not installed"
        );
    }
    edits.sort_by_key(|(span, _)| span.start);
    let mut result = source.to_string();
    for (span, name) in edits.into_iter().rev() {
        result.replace_range(span.start..span.end, &name);
    }
    result
}

fn run(heap: &str, body: &str) {
    run_with_linkage(heap, body, true);
}

fn run_with_linkage(heap: &str, body: &str, static_binary: bool) {
    let scratch = support::Scratch::new("native-system-allocator");
    let source = format!("{heap}\n{HELPERS}\n{body}");
    let target = lim::TargetDescription::X86_64_SYSTEM_V;
    let assembly = lim::compile_source_to_assembly(
        &source,
        &scratch.path().join("main.lim"),
        &lim::CompileConfig::default(),
        &scratch.path().join("cache"),
        target,
    )
    .unwrap_or_else(|error| panic!("{error:?}"));
    let binary = scratch.path().join("program");
    lim::link_native_binary(&assembly, &binary, &[], &[], target).unwrap();
    // The allocation paths must not silently reintroduce a foreign runtime.
    let elf = fs::read(&binary).unwrap();
    let offset = u64::from_le_bytes(elf[32..40].try_into().unwrap()) as usize;
    let stride = u16::from_le_bytes(elf[54..56].try_into().unwrap()) as usize;
    let count = u16::from_le_bytes(elf[56..58].try_into().unwrap()) as usize;
    let mut dynamic = false;
    for index in 0..count {
        let start = offset + index * stride;
        let kind = u32::from_le_bytes(elf[start..start + 4].try_into().unwrap());
        dynamic |= matches!(kind, 2 | 3);
    }
    assert_eq!(
        dynamic, !static_binary,
        "unexpected ELF runtime dependencies"
    );
    assert!(!assembly.contains("\n.globl malloc\n"));
    assert!(!assembly.contains("\n.globl realloc\n"));
    assert!(!assembly.contains("\n.globl free\n"));
    let (status, stdout, stderr) =
        support::run(&mut Command::new(binary), Duration::from_secs(15), 4096).unwrap();
    assert_eq!(
        status.code(),
        Some(42),
        "{status:?}\n{stdout:?}\n{stderr:?}"
    );
    assert!(stdout.is_empty());
    assert!(stderr.is_empty());
}

#[test]
fn kernel_error_pointers_and_invalid_resize_sizes_preserve_ownership() {
    run(
        HEAP,
        r#"
#fn main {
  #params = ();
  #returns = #u64;
  #effects = ((#effects-of allocate-required) (#effects-of fill) (#effects-of system-allocate) (#effects-of system-allocator-map) (#effects-of system-allocator-remap) (#effects-of system-deallocate) (#effects-of system-reallocate) (#effects-of verify)); #body = (
          (#assert (#ptr-is-null (#call system-allocator-map ((length 0usize)))))
          (#assert (#ptr-is-null (#unsafe (#unsafe-call system-allocator-remap
            ((pointer (#ptr-null (#ptr-mut #u8))) (old-length 4096usize) (length 8192usize))))))
          (#assert (#match (#call system-allocate ((size sYSTEM-ALLOCATION-MAX)))
            (#case (SystemAllocationResult.SystemAllocationFailed error) true) (#case (SystemAllocationResult.SystemAllocated unexpected) (#panic))))
          (#let pointer (#ptr-mut #u8) (#call allocate-required ((size 10000usize))))
          (#unsafe (#unsafe-call fill ((pointer pointer) (size 10000usize))))
          (#assert (#match (#unsafe (#unsafe-call system-reallocate ((pointer pointer) (size 0usize))))
            (#case (SystemAllocationResult.SystemAllocationFailed error) true) (#case (SystemAllocationResult.SystemAllocated unexpected) (#panic))))
          (#unsafe (#unsafe-call verify ((pointer pointer) (size 10000usize))))
          (#assert (#match (#unsafe (#unsafe-call system-reallocate ((pointer pointer) (size sYSTEM-ALLOCATION-MAX))))
            (#case (SystemAllocationResult.SystemAllocationFailed error) true) (#case (SystemAllocationResult.SystemAllocated unexpected) (#panic))))
          (#unsafe (#unsafe-call verify ((pointer pointer) (size 10000usize))))
          (#unsafe (#unsafe-call system-deallocate ((pointer pointer))))
          (#return 42u64)
  );
}
"#,
    );
}

#[test]
fn foreign_malloc_and_free_can_coexist_without_allocator_interposition() {
    run_with_linkage(
        HEAP,
        r#"
#extern-fn  malloc {
  #abi = #abi-c;
  #params = ((size #usize));
  #returns = (#ptr-mut #u8);
#effects = (#global-access #io); }
#extern-fn  free {
  #abi = #abi-c;
  #params = ((pointer (#ptr-mut #u8)));
  #returns = ();
#effects = (#global-access #io); }
#fn main {
  #params = ();
  #returns = #u64;
  #effects = (#global-access #io (#effects-of allocate-required) (#effects-of free) (#effects-of malloc) (#effects-of system-deallocate)); #body = (
          (#let foreign (#ptr-mut #u8) (#unsafe (#unsafe-call malloc ((size 64usize)))))
          (#assert (#bool::not (#ptr-is-null foreign)))
          (#let native (#ptr-mut #u8) (#call allocate-required ((size 64usize))))
          (#assert (#usize::ne (#ptr-address foreign) (#ptr-address native)))
          (#unsafe (#ptr-write foreign 21u8))
          (#unsafe (#ptr-write native 21u8))
          (#let answer #u64 (#u64::add-wrap (#as (#unsafe (#ptr-read foreign)) #u64)
            (#as (#unsafe (#ptr-read native)) #u64)))
          (#unsafe (#unsafe-call free ((pointer foreign))))
          (#unsafe (#unsafe-call system-deallocate ((pointer native))))
          (#return answer)
  );
}
"#,
        false,
    );
}

#[test]
fn size_classes_alignment_and_in_place_or_moving_resize_preserve_bytes() {
    let mut body = String::from("#fn main {\n  #params = ();\n  #returns = #u64;\n  #effects = ((#effects-of allocate-required) (#effects-of resize-required) (#effects-of fill) (#effects-of verify) (#effects-of system-deallocate)); #body = (\n");
    for (index, size) in [
        1, 15, 16, 17, 31, 32, 48, 49, 112, 113, 240, 241, 496, 497, 1008, 1009, 2032, 2033, 4080,
        4081, 4096, 65536,
    ]
    .into_iter()
    .enumerate()
    {
        body.push_str(&format!(r#"
          (#let pointer{index} (#ptr-mut #u8) (#call allocate-required ((size {size}usize))))
          (#assert (#usize::eq (#usize::rem-wrap (#ptr-address pointer{index}) 16usize) 0usize))
          (#unsafe (#unsafe-call fill ((pointer pointer{index}) (size {size}usize))))
          (#let grown{index} (#ptr-mut #u8) (#unsafe (#unsafe-call resize-required ((pointer pointer{index}) (size {}usize)))))
          (#unsafe (#unsafe-call verify ((pointer grown{index}) (size {size}usize))))
          (#let shrunk{index} (#ptr-mut #u8) (#unsafe (#unsafe-call resize-required ((pointer grown{index}) (size 1usize)))))
          (#assert (#usize::eq (#ptr-address shrunk{index}) (#ptr-address grown{index})))
          (#unsafe (#unsafe-call verify ((pointer shrunk{index}) (size 1usize))))
          (#unsafe (#unsafe-call system-deallocate ((pointer shrunk{index}))))
        "#, size * 3 + 1));
    }
    body.push_str(r#"
      (#let first (#ptr-mut #u8) (#call allocate-required ((size 17usize))))
      (#let second (#ptr-mut #u8) (#call allocate-required ((size 17usize))))
      (#assert (#usize::ne (#ptr-address first) (#ptr-address second)))
      (#unsafe (#unsafe-call fill ((pointer second) (size 17usize))))
      (#unsafe (#unsafe-call system-deallocate ((pointer first))))
      (#let recycled (#ptr-mut #u8) (#call allocate-required ((size 17usize))))
      (#assert (#usize::eq (#ptr-address first) (#ptr-address recycled)))
      (#unsafe (#unsafe-call verify ((pointer second) (size 17usize))))
      (#unsafe (#unsafe-call system-deallocate ((pointer second))))
      (#unsafe (#unsafe-call system-deallocate ((pointer recycled))))
      (#let in-place (#ptr-mut #u8) (#call allocate-required ((size 17usize))))
      (#unsafe (#unsafe-call fill ((pointer in-place) (size 17usize))))
      (#let extended (#ptr-mut #u8) (#unsafe (#unsafe-call resize-required ((pointer in-place) (size 47usize)))))
      (#assert (#usize::eq (#ptr-address in-place) (#ptr-address extended)))
      (#unsafe (#unsafe-call verify ((pointer extended) (size 17usize))))
      (#unsafe (#unsafe-call system-deallocate ((pointer extended))))
      (#let null-growth (#ptr-mut #u8) (#unsafe (#unsafe-call resize-required
        ((pointer (#ptr-null (#ptr-mut #u8))) (size 64usize)))))
      (#unsafe (#unsafe-call system-deallocate ((pointer null-growth))))
      (#unsafe (#unsafe-call system-deallocate ((pointer (#ptr-null (#ptr-mut #u8))))))
      (#return 42u64)
  );
}
"#);
    run(HEAP, &body);
}

const COUNT_OS_CALLS: &str = r#"
#static mapped (#atomic #u64) (#atomic-init #u64 0u64)
#static unmapped (#atomic #u64) (#atomic-init #u64 0u64)
#fn counted-map {
  #params = ((length #usize));
  #returns = (#ptr-mut #u8);
  #effects = ((#effects-of system-allocator-map) (#write-global mapped)); #body = (
    (#let previous #u64 (#unsafe (#atomic-fetch-add (#borrow mapped) 1u64 #memory-relaxed)))
    (#return (#call system-allocator-map ((length length))))
  );
}
#unsafe-fn counted-unmap {
  #params = ((pointer (#ptr-mut #u8)) (length #usize));
  #returns = ();
  #effects = ((#effects-of system-allocator-unmap) (#write-global unmapped)); #body = (
    (#let previous #u64 (#unsafe (#atomic-fetch-add (#borrow unmapped) 1u64 #memory-relaxed)))
    (#unsafe (#unsafe-call system-allocator-unmap ((pointer pointer) (length length))))
    (#return ())
  );
}
"#;

#[test]
fn full_slabs_reenter_free_lists_and_empty_cache_is_bounded() {
    let heap = format!(
        "{}\n{COUNT_OS_CALLS}",
        replace_calls(
            HEAP,
            &[
                ("system-allocator-map", "counted-map"),
                ("system-allocator-unmap", "counted-unmap"),
            ]
        )
    );
    run(
        &heap,
        r#"
#fn main {
  #params = ();
  #returns = #u64;
  #effects = ((#effects-of allocate-required) (#effects-of fill) (#effects-of system-deallocate) (#effects-of verify)); #body = (
          (#let-mut pointers (#array (#ptr-mut #u8) 96) (#array-repeat (#ptr-null (#ptr-mut #u8))))
          (#for-range (slot #usize) 0usize 96usize
            (#let pointer (#ptr-mut #u8) (#call allocate-required ((size 4080usize))))
            (#unsafe (#unsafe-call fill ((pointer pointer) (size 4080usize))))
            (#set-index pointers slot pointer))
          (#assert (#u64::eq (#unsafe (#atomic-load (#borrow mapped) #memory-relaxed)) 7u64))
          (#for-range (pass #usize) 0usize 2usize
            (#let-mut index #usize pass)
            (#while (#usize::lt index 96usize)
              (#let pointer (#ptr-mut #u8) (#index pointers index))
              (#unsafe (#unsafe-call verify ((pointer pointer) (size 4080usize))))
              (#unsafe (#unsafe-call system-deallocate ((pointer pointer))))
              (#set index (#usize::add-wrap index 2usize))))
          (#assert (#u64::eq (#unsafe (#atomic-load (#borrow unmapped) #memory-relaxed)) 6u64))
          (#for-range (iteration #usize) 0usize 100usize
            (#let pointer (#ptr-mut #u8) (#call allocate-required ((size 4080usize))))
            (#unsafe (#unsafe-call system-deallocate ((pointer pointer)))))
          (#assert (#u64::eq (#unsafe (#atomic-load (#borrow mapped) #memory-relaxed)) 7u64))
          (#let large (#ptr-mut #u8) (#call allocate-required ((size 100000usize))))
          (#unsafe (#unsafe-call system-deallocate ((pointer large))))
          (#assert (#u64::eq (#unsafe (#atomic-load (#borrow unmapped) #memory-relaxed)) 7u64))
          (#return 42u64)
  );
}
"#,
    );
}

#[test]
fn os_allocation_failures_unlock_pool_and_preserve_old_allocation() {
    let heap = format!(
        "{}\n{}",
        replace_calls(
            HEAP,
            &[
                ("system-allocator-map", "gated-map"),
                ("system-allocator-remap", "failed-remap"),
            ]
        ),
        r#"
#static failMapping (#atomic #u32) (#atomic-init #u32 1u32)
#fn gated-map {
  #params = ((length #usize));
  #returns = (#ptr-mut #u8);
  #effects = ((#effects-of system-allocator-map) (#read-global failMapping)); #body = (
          (#return (#if (#u32::eq (#unsafe (#atomic-load (#borrow failMapping) #memory-relaxed)) 1u32)
            (#ptr-null (#ptr-mut #u8)) (#call system-allocator-map ((length length)))))
  );
}
#unsafe-fn failed-remap {
  #params = ((pointer (#ptr-mut #u8)) (old-length #usize) (length #usize));
  #returns = (#ptr-mut #u8);
  #body = (
          (#return (#ptr-null (#ptr-mut #u8)))
  );
}
    "#
    );
    run(
        &heap,
        r#"
#fn main {
  #params = ();
  #returns = #u64;
  #effects = ((#effects-of allocate-required) (#effects-of fill) (#effects-of system-allocate) (#effects-of system-deallocate) (#effects-of system-reallocate) (#effects-of verify)); #body = (
          (#assert (#match (#call system-allocate ((size 17usize)))
            (#case (SystemAllocationResult.SystemAllocationFailed error) true)
            (#case (SystemAllocationResult.SystemAllocated unexpected) (#panic))))
          (#unsafe (#atomic-store (#borrow failMapping) 0u32 #memory-relaxed))
          (#let pointer (#ptr-mut #u8) (#call allocate-required ((size 17usize))))
          (#unsafe (#unsafe-call fill ((pointer pointer) (size 17usize))))
          (#unsafe (#atomic-store (#borrow failMapping) 1u32 #memory-relaxed))
          (#assert (#match (#unsafe (#unsafe-call system-reallocate ((pointer pointer) (size 10000usize))))
            (#case (SystemAllocationResult.SystemAllocationFailed error) true)
            (#case (SystemAllocationResult.SystemAllocated unexpected) (#panic))))
          (#unsafe (#unsafe-call verify ((pointer pointer) (size 17usize))))
          (#unsafe (#unsafe-call system-deallocate ((pointer pointer))))
          (#unsafe (#atomic-store (#borrow failMapping) 0u32 #memory-relaxed))
          (#let large (#ptr-mut #u8) (#call allocate-required ((size 10000usize))))
          (#unsafe (#unsafe-call fill ((pointer large) (size 10000usize))))
          (#assert (#match (#unsafe (#unsafe-call system-reallocate ((pointer large) (size 100000usize))))
            (#case (SystemAllocationResult.SystemAllocationFailed error) true)
            (#case (SystemAllocationResult.SystemAllocated unexpected) (#panic))))
          (#unsafe (#unsafe-call verify ((pointer large) (size 10000usize))))
          (#unsafe (#unsafe-call system-deallocate ((pointer large))))
          (#assert (#match (#call system-allocate ((size 0usize)))
            (#case (SystemAllocationResult.SystemAllocationFailed error) true) (#case (SystemAllocationResult.SystemAllocated unexpected) (#panic))))
          (#assert (#match (#call system-allocate ((size 18446744073709551615usize)))
            (#case (SystemAllocationResult.SystemAllocationFailed error) true) (#case (SystemAllocationResult.SystemAllocated unexpected) (#panic))))
          (#return 42u64)
  );
}
"#,
    );
}

#[test]
fn bypassing_allocator_lock_ownership_requires_unsafe() {
    let source = format!(
        "{HEAP}\n#fn main {{\n  #params = ();\n  #returns = #u64;\n  #effects = ((#effects-of system-allocator-unlock)); #body = ( (#unsafe-call system-allocator-unlock ()) (#return 42u64)\n  );\n}}\n"
    );
    let program = lim::parse_program(&source).unwrap();
    let error = lim::check_types(&program)
        .expect_err("safe callers must not release another thread's lock");
    assert!(error.contains("unsafe"), "{error}");
}

#[test]
fn embedded_standard_string_module_has_no_foreign_allocator_dependency() {
    run(
        "",
        r#"
#std
#fn main {
  #params = ();
  #returns = #u64;
  #effects = ((#effects-of String::free) (#effects-of String::from-chars)); #body = (
          (#let text (#array #char 2) "hi")
          (#let string String (#match (#call String::from-chars ((text (#borrow-slice text))))
            (#case (StringCreateResult.StringCreated owner) owner) (#case (StringCreateResult.StringCreateFailed error) (#panic))))
          (#assert (#usize::eq (#call String::len ((string (#borrow string)))) 2usize))
          (#call String::free ((string string)))
          (#return 42u64)
  );
}
"#,
    );
}

#[test]
fn standard_strings_can_allocate_and_free_inside_a_raw_worker() {
    run(
        "",
        r#"
#std
#fn worker {
  #params = ();
  #returns = #u64;
  #effects = ((#effects-of String::free) (#effects-of String::from-chars)); #body = (
          (#let characters (#array #char 2) "hi")
          (#let string String (#match (#call String::from-chars ((text (#borrow-slice characters))))
            (#case (StringCreateResult.StringCreated owner) owner) (#case (StringCreateResult.StringCreateFailed error) (#panic))))
          (#let size #usize (#call String::len ((string (#borrow string)))))
          (#call String::free ((string string)))
          (#return (#u64::add-wrap (#as size #u64) 40u64))
  );
}
#generate #thread-spawn ((task StringWorker) (worker worker))
#fn main {
  #params = ();
  #returns = #u64;
  #effects = (#global-access #io); #body = (
          (#let task StringWorker (#match (#call StringWorker::spawn ())
            (#case (StringWorker::SpawnResult.Ok handle) handle) (#case _ (#panic))))
          (#return (#match (#call StringWorker::join ((task task)))
            (#case (StringWorker::JoinResult.Ok value) value)
            (#case (StringWorker::JoinResult.Error (#tuple retry error)) (#panic))))
  );
}
"#,
    );
}

#[test]
fn raw_kernel_workers_share_heap_without_libc_tls() {
    run(
        HEAP,
        r#"
#fn worker {
  #params = ();
  #returns = #u64;
  #effects = ((#effects-of allocate-required) (#effects-of fill) (#effects-of resize-required) (#effects-of system-deallocate) (#effects-of verify)); #body = (
          (#for-range (iteration #usize) 0usize 200usize
            (#let size #usize (#usize::add-wrap (#usize::rem-wrap iteration 4080usize) 1usize))
            (#let pointer (#ptr-mut #u8) (#call allocate-required ((size size))))
            (#unsafe (#unsafe-call fill ((pointer pointer) (size size))))
            (#let resized (#ptr-mut #u8) (#unsafe (#unsafe-call resize-required ((pointer pointer) (size 5000usize)))))
            (#unsafe (#unsafe-call verify ((pointer resized) (size size))))
            (#unsafe (#unsafe-call system-deallocate ((pointer resized)))))
          (#return 21u64)
  );
}
#generate #thread-spawn ((task WorkerA) (worker worker))
#generate #thread-spawn ((task WorkerB) (worker worker))
#fn main {
  #params = ();
  #returns = #u64;
  #effects = (#global-access #io); #body = (
          (#let a WorkerA (#match (#call WorkerA::spawn ())
            (#case (WorkerA::SpawnResult.Ok handle) handle) (#case _ (#panic))))
          (#let b WorkerB (#match (#call WorkerB::spawn ())
            (#case (WorkerB::SpawnResult.Ok handle) handle) (#case _ (#panic))))
          (#let first #u64 (#match (#call WorkerA::join ((task a)))
            (#case (WorkerA::JoinResult.Ok value) value)
            (#case (WorkerA::JoinResult.Error (#tuple retry error)) (#panic))))
          (#let second #u64 (#match (#call WorkerB::join ((task b)))
            (#case (WorkerB::JoinResult.Ok value) value)
            (#case (WorkerB::JoinResult.Error (#tuple retry error)) (#panic))))
          (#return (#u64::add-wrap first second))
  );
}
"#,
    );
}
