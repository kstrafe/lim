# Linux syscall coverage and remaining work

The standard-library syscall implementation is `library/linux_x86_64.lim`.
It selects Linux x86-64 with `#cfg` and uses direct kernel calls. Other cfg
branches supply unsupported-target fallbacks; they are not implementations
of another operating system. The syscall catalog has 386 entries from its
pinned Linux source snapshot, including obsolete and privileged interfaces.

The current implementation references 278 distinct catalog numbers (about
72%). This is implementation breadth, **not a claim that every syscall path
or kernel feature has been verified**. Some wrappers share a syscall number.
No `#extern-fn` declarations appear in the library sources. This source check
is supplemented by emitted-code and ELF checks: `library/tasks.lim` exposes
`#generate #std/tasks.lim::threaded-executor`, which expands to `#generate #thread-spawn`, and its backend now
uses kernel mappings, clone, futex joining, and unmapping instead of
malloc/free/pthreads. Reachable foreign worker calls are rejected; arbitrary
user-requested FFI outside worker call graphs remains separate from the library.

The native linker now omits libc/pthread and the dynamic loader when assembled
objects have no undefined symbols and no libraries were explicitly requested.
`tests/native_linking.rs` imports the Linux library, inspects the published
ELF for absence of PT_INTERP and a dynamic section, and executes its stdout
check. Foreign calls, raw assembly references, explicit libraries, and supplied
objects retain the runtime linking path. This is separate from the source and
assembly checks below. `tests/kernel_threads.rs` verifies static binaries for
generated threads and the library's threaded executor as well.

## Reproduce the evidence

```sh
nix develop --command cargo test --test syscall_coverage -- --nocapture
nix develop --command cargo test --test unsafe_functions
nix develop --command cargo test --test io_examples
nix develop --command cargo test --test native_examples
nix develop --command cargo test --test native_linking
nix develop --command cargo test --test syscall_execution -- --ignored --nocapture
nix develop --command cargo test --test kernel_threads -- --include-ignored --nocapture
```

### Acceptance audit (2026-09-26)

| Requirement | Implementation and verified evidence |
| --- | --- |
| Lim standard library without FFI | The four `library/` modules contain no foreign declarations; emitted-code checks and static ELF tests cover the syscall library and generated threaded executor. |
| Target-selected kernel implementations | `#cfg` selects Linux x86-64; tests compare native/fallback signatures and unsafe requirements. Other targets explicitly return unsupported results; they are not presented as implemented OS backends. |
| Unsafe direct assembly | Typed `#asm` and `#linux-syscall` lower to native instructions. Unit/UI tests reject missing unsafe blocks and invalid register/argument forms; executable syscall and thread tests exercise the ABI. |
| Most Linux syscalls | 278 distinct numbers from the 386-entry native/common x86-64 catalog, about 72%, have implemented wrappers and were observed executing. Unimplemented names are printed by the structural audit. |
| Tests execute syscalls and check program output | The 54-program runtime audit checks every target's exact exit/stdout/stderr and observes all 278 numbers. The I/O suite checks kernel results; thread and byte-I/O audits additionally inject failures. |

Final verification passed the full `cargo test` suite (including 335 library
unit tests, 56 I/O tests, the 322-entry native manifest, UI tests, and all 402
unsafe-call probes). All eight kernel-thread tests were also run explicitly,
including the two ptrace tests. The fresh syscall execution audit and byte-I/O
fault-injection test passed together in 61.52 seconds. Formatting/diff checks
pass. `cargo doc --no-deps` builds with the existing rustdoc warning about
custom `run=N` code-fence metadata.

This completes the requested most-syscalls baseline on the supported target,
not every possible kernel feature or operating system. The advanced coverage
and portability work listed below remains explicit follow-up work.

The first command prints syscall-to-wrapper-to-example mappings and every
missing catalog name. Its regression checks require a runnable call site for
each Linux wrapper, reject references to unknown syscall constants, prevent
the implemented-number count falling below 278, and reject explicit FFI
declarations in library source. It parses syntax: comments, strings, and
quoted calls do not count as runtime call sites. Explicit fixture exceptions
cover paired exec programs and the stdin-driven echo program.

Additional checks compile the entire Linux library and reject external
declarations in its emitted assembly. They also type-check the native and
unsupported-target branches and compare every function's parameter names,
types, return type, and unsafe-call requirement. Fallback signatures must match native signatures;
this does not mean another operating system has a working implementation.

These are structural checks. A call site in a function or branch does not
prove that execution reaches it. The I/O tests compile and execute programs
and assert kernel results, exit statuses, and stdout/stderr.

The final command is the runtime-number audit. It requires Linux x86-64,
`strace` (included in the Linux devshell), ptrace permission, and the kernel
features exercised by the corpus. It is deliberately opt-in: ordinary
`cargo test` tests the trace parser but does **not** run this audit. An ignored
test is not evidence of runtime coverage. The audit follows fork/exec children,
excludes strace's initial launch `execve`, and rejects syscall-ABI changes.
It compiles the target programs separately, verifies their ELF files have
neither an interpreter nor a dynamic section, and requires each traced program
to meet its exit/stdout/stderr expectations within a process-group timeout.
The paired exec target and stdin-driven echo are included. Missing numbers
fail the test, and the report maps observed numbers to passing source files.

The audit observed **278/278 implemented syscall numbers in 54 passing
programs** (52 Linux examples, the paired exec driver, and echo). This proves
that each implemented number was reached by this corpus, not that every
wrapper, argument combination, or success/error path was exercised. In
particular, generated threads are outside this syscall corpus and have their
own ELF/runtime/trace tests.

The latest explicit audit rerun passed in 34.63 seconds on this host. The
full `cargo test` run also passed, including the 321-entry native manifest,
56 I/O tests, six structural coverage tests, and all 402 unsafe-call probes.
The runtime-number audit was run separately because it is ignored by default.

The same opt-in suite now injects `EINTR` and `EBADF` into the echo program's
read and write calls. It requires exact binary echo output (including NUL and
non-UTF-8 bytes) after interruption, and failure status without output after
the injected hard error. This caught a real retry bug: the wrappers had reused
the negative errno in RAX as the next syscall number. Both now preserve the
original syscall number across retries.

## Kernel-backed generated threads

`tests/kernel_threads.rs` verifies the library threaded executor and generated
workers have static ELF files with no interpreter or dynamic section. Native
tests cover scalar/float arguments, stack-passed arguments, small and large
aggregate transfers, nested workers, a 128-KiB local array, and a real guard-page
fault. A small-aggregate result ordering bug was found and fixed by these tests.
The concurrent example repeatedly exchanges an atomic readiness flag, verifies
shared PID/distinct TIDs and a zero worker FS base, joins, and prints `T\n`.
Transitive foreign worker calls receive a source-underlined compilation error.

The two opt-in thread audits verify mmap/protection/clone/exit/unmap counts and
clone flags, then inject allocation, protection, creation, and futex failures.
Protection/creation failures release the allocated mapping. EINTR/EAGAIN retry
within join; EIO returns the still-owned handle, which is then successfully
joined, with exactly one unmap. Ordinary tests also exercise failure branches
without requiring ptrace; they simulate negative kernel returns in emitted
assembly rather than substituting obsolete malloc/pthread stubs.

After adding io_uring and fixing process termination, 52 I/O tests and seven
ELF/linker tests passed. Four documentation tests and five coverage checks
also passed. The full
native-example suite subsequently passed all
319 manifest entries: 309 expected exits, five expected signals, and five
compile-only modules. Its four Rust tests passed in 218.62 seconds on this
host. The paired exec and stdin-driven echo runtime checks remain in the
I/O suite, not the generic manifest runner.

The subsequent `#unsafe-fn` change passed 333 compiler unit tests, all 52 I/O
tests, six unsafe-function tests, the UI diagnostics suite, documentation tests,
and coverage checks. The subsequent library-wide migration marked 196 wrappers
unsafe and left 81 safe. The 52 I/O tests passed after migrating their call
sites. Caller annotations enforce a boundary; they do not prove that unsafe
implementations or callers satisfy every kernel contract.

The final safety-migration verification passed 333 compiler unit tests, 52 I/O
tests, seven unsafe-function tests (including 392 rejected safe calls), six
coverage checks, four documentation tests, three UI tests, and seven ELF/linker
tests. After the example-helper cleanup, the full 319-entry native manifest
sweep passed again in 225.59 seconds on this host.

The POSIX message-queue example additionally checks actual `SIGEV_SIGNAL`
delivery: signal code, sender PID/UID, payload, one-shot removal, successful
delivery after rearming, suppression after cancellation, and restoration of
the process signal mask. Its exact stdout fixture is `B\nA\nN\n`; `N` comes
from the delivered notification payload, not a fixed success banner.

The robust-futex example verifies direct and requeued blocked-waiter wakeup
as well as the owner-death word update. A controller observes each waiter's
futex wait channel in `/proc/PID/wchan`. For the requeue path it moves one
waiter from a staging word to the robust word before releasing the owner from
a pipe read; it never uses a timed sleep to assume readiness. Each waiter
checks a zero wait return and the owner-death/waiters bits, then prints `W`.
The controller checks both child exit statuses before printing `R`. Each wait has a two-second
timeout and the I/O harness bounds each entire process group to five seconds,
repeating the executable eight times. Readable procfs wait symbols are required;
a restricted host is not silently counted as a successful run.

The memory-sealing example checks invalid flags/alignment, length rounding,
idempotence, and rejected mprotect/madvise/munmap with unchanged payload. The
secret-memory example checks invalid flags, close-on-exec, fixed sizing,
shared mapping contents, rejection of process_vm_readv, and mapping lifetime
after descriptor close. Their exact stdout fixtures are `M\n` and `T\n`.
These examples require kernel support; secret memory also needs sufficient
locked-memory allowance. They fail on unsupported hosts rather than silently
report success. Both are also included in the passing native-example sweep.

The io_uring example exercises all three syscall entry points with real
registered-file reads/writes, fourteen completions per run, queue-slot reuse,
and both shared and separate ring mappings. It validates cookies, results,
flags, unchanged dropped/overflow counters, error completions, and exact stdout.
The raw x86-64 ring accesses use load/publish fences. This is not a general
multi-producer queue, SQPOLL, or cancellation test. A first run exposed a
startup bug: thread-only exit(42) could yield process status 0 with io_uring
workers. The entry stub now uses exit_group; a separate raw-clone regression
also requires main's status while a worker remains alive. Both the focused
I/O check and full native-example sweep pass with this change.

## Caller safety contracts

Every raw-pointer Linux wrapper requires `#unsafe-call` inside `#unsafe`,
even when a particular invocation uses null, length zero, or an operation that
does not dereference the argument. The compiler does not infer safety from command numbers or
flags. `#call` accepts only safe functions, even inside `#unsafe`, while
`#unsafe-call` accepts only unsafe or external functions. Both use the same
named arguments and parameter declaration evaluation order. Safe byte/time
helpers use `#call`. The unsupported-target branch retains the same API contract.

- **Synchronous buffers and paths:** supply the kernel's layout, readable or
  writable bounds, required alignment, and initialization. Strings must have
  a readable terminating NUL. Output writes must not conflict with live shared
  references or other accesses. Nested pointers in vectors/messages have the
  same obligations. Negative errno does not guarantee that no bytes changed;
  a successful short read does not initialize the remainder of a buffer.
- **Retained memory:** io_uring, native AIO, gifted vmsplice pages, robust
  futex lists, alternate stacks, and registered signal handlers can outlive
  the registering syscall. Keep backing memory and code valid until actual
  completion, unregistering, or teardown has established no further access.
  A failed cancellation attempt does not end that obligation. Supply required
  atomic access and ordering for memory shared with the kernel or other tasks.
- **Address spaces:** mmap with fixed addresses, munmap, mremap, mprotect,
  pkey_mprotect, madvise, shared-memory operations, and similar calls must not
  invalidate live references or violate the ownership/access rules of existing
  allocations. Coordinate externally mutable backing files and other processes.
  The language cannot deduce these constraints from a pointer's type.
- **Signals and execution:** signal actions, alternate stacks, and masks must
  preserve runtime requirements; handlers/restorers must obey the target ABI
  and asynchronous execution restrictions. Installing a pointer to code is not
  checked like a normal Lim function call.

Several integer-only interfaces also require unsafe calls:

| Wrappers | Caller obligation |
| --- | --- |
| `linux-ioctl`, `linux-fcntl`, `linux-semctl` | Interpret each argument using the selected command's ABI; integer arguments may encode addresses and nested buffers. |
| `linux-prctl`, `linux-arch-prctl` | Validate command-dependent addresses and preserve TLS, memory, and execution invariants. |
| `linux-brk` | Coordinate with the allocator and never remove live heap storage; inspect the returned break before using a requested extension. |
| `linux-personality` | Preserve runtime assumptions when changing execution-domain and address-layout flags. |
| `linux-pkey-free` | Ensure no live mapping still relies on the key before releasing it. |
| `linux-io-destroy` | Own the AIO context, synchronize users, and retain submitted buffers through established completion/cancellation. |
| `linux-fork` | Account for inherited state and absent threads; a multithreaded child must restrict its work until exec. Raw fork does not run libc atfork handlers. |
| `linux-exit` | Thread-only termination must not strand live borrowers or violate runtime/thread-completion invariants. Prefer safe `linux-exit-group` for whole-process termination. |

These rules follow the command-dependent interface in
[ioctl(2)](https://man7.org/linux/man-pages/man2/ioctl.2.html), the mapping
lifetime warning in [pkeys(7)](https://man7.org/linux/man-pages/man7/pkeys.7.html),
and the child restrictions in
[fork(2)](https://man7.org/linux/man-pages/man2/fork.2.html).

The safe byte helpers (`linux-read-byte`, `linux-write-byte`,
`linux-getrandom-byte`) bound kernel access to one borrowed byte.
`linux-clock-gettime` and `linux-nanosleep` use typed, correctly laid-out
timespec references and do not retain them. Ordinary scalar descriptor and
process queries remain safe; safe does not mean side-effect-free, nonblocking,
or guaranteed to succeed. Unsafe callers that create mappings or asynchronous
registrations must coordinate them with otherwise-safe descriptor operations.

Regression tests inspect both cfg branches for raw-pointer and scalar-hidden
obligations. They attempt a safe call to every unsafe wrapper and require
E4300 at the exact callee, then compile explicitly unsafe forwarders for all
of them. These forwarders are not executed; runtime fixtures separately own
their resources and assert observable kernel results.

## Delivered signals and alternate stacks

`examples/linux_signal_handler.lim` installs a raw `SA_SIGINFO | SA_ONSTACK |
SA_RESTORER` handler and exercises actual self-directed SIGUSR1 delivery,
without FFI, dynamic code allocation, or language-level function pointers.
The handler and restorer are assembly labels in the executable's text section.
The x86-64 callback uses the supplied ucontext's stack descriptor to recover
its owned record allocation; this is target ABI code, not portable Lim code.
The layout and return-frame constraints follow the kernel's
[ucontext definition](https://raw.githubusercontent.com/torvalds/linux/v6.16/include/uapi/asm-generic/ucontext.h)
and [x86-64 signal implementation](https://raw.githubusercontent.com/torvalds/linux/v6.16/arch/x86/kernel/signal_64.c).

The first delivery is unblocked. The second is explicitly held pending until
the new `linux-rt-sigsuspend` wrapper temporarily unmasks it. The example
checks `-EINTR`, restoration of the pre-suspend mask, consumption of the
pending signal, and `-EINVAL`/`-EFAULT` for invalid suspend arguments. This
uses the raw [rt_sigsuspend interface](https://man7.org/linux/man-pages/man2/sigsuspend.2.html).

Each handler records its actual RSP, signal number, siginfo code and sender,
queries `SS_ONSTACK` and its current signal mask, and verifies that disabling
the active alternate stack is rejected. It writes `H\n` directly to stdout
using a byte derived from the delivered signal number. The resumed program
verifies both invocations and restores/checks the original action, stack, and
mask before unmapping storage and printing `S\n`. Exact output is therefore
`H\nH\nS\n`; the harness repeats the executable eight times under timeouts.

The restorer executes raw `rt_sigreturn` with the kernel-created frame in the
required stack position. It cannot be a normal Lim function with a prologue.
That syscall is exercised by this example but is not counted as an ordinary
library wrapper. Callback syscall literals are checked against the catalog
before installation. Negative tests remove alternate-stack selection, break
the restorer, or replace sigsuspend with a fake `-EINTR`. Each must fail with
only the first handler's output, so expected errno alone cannot pass the test.
At that stage, the complete I/O suite had 54 passing tests, with 197 unsafe
wrappers and 81 safe wrappers after adding `linux-rt-sigsuspend`.
The full native manifest passed all 320 entries on retry (226.42 seconds).
The first sweep timed out at the pre-existing `never.lim` trap test's two-second
deadline; an isolated run produced the expected SIGILL, and the complete
retry passed. This observation does not establish the timeout's cause.
All 394 unsafe-call probes, six coverage checks, four documentation tests,
and seven native-linker tests also passed with the new wrapper.

## Futex2 waits and wakeups

The library provides `linux-futex-waitv`, `linux-futex-wait`,
`linux-futex-wake`, and `linux-futex-requeue` using direct syscalls and matching
unsafe cfg fallbacks.
Their ABI follows the kernel's
[futex2 documentation](https://docs.kernel.org/userspace-api/futex2.html) and
[syscall declarations](https://raw.githubusercontent.com/torvalds/linux/v6.16/kernel/futex/syscalls.c).
Flags/counts use their specified 32-bit types; single-word expected values and
masks use `#usize` because those kernel parameters are native unsigned long.
Vector entries use the separate fixed-width 24-byte record layout. All four
APIs require caller-managed lifetimes and synchronization for raw storage.

`examples/linux_futex2.lim` uses shared anonymous memory and four isolated
children. Two children wait on both vector entries; waking entry zero then
entry one produces the verified return indices printed as `A\n` and `B\n`.
The third uses single-word wait with a nontrivial mask and prints `C\n` only
after a successful wake. The fourth waiter is moved from the first word to
the second with no wake requested. A live comparison mismatch must not move
it back, and a nonmatching destination mask must not wake it. The parent
retries moves after spurious wait restarts as needed. A matching destination wake releases the child,
which checks success and prints `D\n`. The parent retries harmless empty wakes/requeues until the
kernel confirms one waiter was dequeued, then verifies child exit status and
empty queues. There is no timed sleep that assumes the child is ready.
Each child has an absolute two-second deadline, and the harness repeats the
whole program eight times with five-second process-group limits.

Error checks include invalid vector counts and syscall flags, reserved fields,
per-entry flags, inaccessible/misaligned word addresses, invalid clock and
timespec values, and out-of-width values/masks. A mismatch in the second
vector entry must leave no waiter on the first. Expired absolute deadlines
are tested with both monotonic and realtime clocks. The exact stdout fixture
is `A\nB\nC\nD\n`; unsupported syscall implementations are failures, not skips.
Additional requeue checks cover an empty queue, invalid flags, null record
array, reserved destination fields, and mismatched source value. A negative
test requests a wake instead of a move: even though the syscall still returns
one and the child can print, the destination-queue assertion must trap.
The I/O suite has 56 passing tests. The library now has 201 unsafe and 81 safe
wrapper declarations across 278 distinct catalog numbers. All 402 unsafe-call
probes and six structural coverage checks pass with the new declaration.
The full 321-entry native manifest passed in 145.77 seconds; four documentation
tests and seven native-linker tests also passed.
Ordinary requeue success alone did not resolve the separate robust-owner-death
cleanup question. The gated regression described below now covers that path.

A later untraced stress run exposed a faulty test assumption: after a successful
requeue, the source wake probe occasionally woke the child and tripped the
expected-zero assertion (captured at `wake-child+0x7a4`). Linux's
[futex wait loop](https://raw.githubusercontent.com/torvalds/linux/v6.16/kernel/futex/waitwake.c)
can unqueue and retry on the original address after a spurious wake. Permanent
destination membership is therefore not a valid synchronization assumption.
The fixture no longer destructively probes the source before completing the
wait. It retries moves when needed and requires a matching destination wake
to return one, then checks the child's result/status and both empty queues.
The wake-instead-of-move mutation still fails. The corrected executable passed
1,000 consecutive untraced runs; the normal eight-run test and mutation test
also passed. This does not establish the cause of the separate robust cleanup
issue or silently count a source wake as a successful destination wake.

## Remaining work

- Expand io_uring coverage to pending-request cancellation, timeouts,
  registered buffers, and concurrent/polling modes. The current queue test is
  intentionally a single issuer that waits for each completion.
- Add futex2 private-thread coverage, multi-waiter wake/requeue counts, and
  signal interruption. Shared vector/single-word waits, masked wakes, requeue,
  timeout, mismatch, and invalid arguments are now exercised directly.
- Cover remaining memory-management interfaces, including NUMA operations
  and additional sealing/secret-memory failure paths. Distinguish unsupported/restricted environments
  from successful execution; do not count skipped operations as success.
- Extend process/thread coverage beyond the generated clone trampoline and
  clear-child-TID join tests, including clone3 and additional creation flags.
  Raw clone with a new stack cannot safely return through an ordinary function
  frame.
- Cover useful sandboxing/security interfaces with restrictions confined to
  child processes. Namespace, mount, privileged administration, and obsolete
  syscalls need an explicit coverage policy and suitable isolated test hosts;
  never change host-wide state just to increase the wrapper count.
- Expand signal coverage beyond synchronous self-delivery, including nested
  handlers, interrupted/restarted I/O, and automatic alternate-stack disarming.
  The current handler test uses one signal and a persistent alternate stack.
- Keep watching robust owner-death cleanup after `FUTEX_CMP_REQUEUE` on other
  kernels. An earlier probe on this host (kernel 7.2.6) intermittently timed
  out despite OWNER_DIED and WAITERS being set, including in an independent C
  probe; tracing masked that failure. The gated Lim regression now preserves
  direct-wait coverage and separately blocks a waiter on shared staging,
  requires CMP_REQUEUE(wake=0, move=1) to move one waiter to the registered
  robust word, then releases the pipe-gated owner. It requires wait result 0,
  OWNER_DIED/WAITERS with cleared TID, and reaps both children. The I/O test
  repeats the example eight times. The updated Lim example passed 1,000
  additional runs and a matching C probe passed 2,000 runs on this host.
  This establishes the tested path here, not the root cause of the earlier
  intermittent result or a guarantee across kernels.
- Audit new wrappers for hidden caller obligations as they are added; pointer
  type checks alone do not catch scalar arguments that encode addresses or
  operations that alter process memory/execution state.
- Keep rerunning the full native-example suite and documentation tests after
  broader additions, and review whether claimed coverage matches executed paths.
- Extend the runtime-number audit alongside new wrappers and examples. Keep
  observed-number coverage distinct from per-wrapper behavioral coverage.

The pkey example requires PKU/OSPKE support, and several examples require
specific kernel features. Successful runs on this host are not proof of
support on every Linux kernel or x86-64 CPU. Keep these requirements visible.
