# AArch64 Linux user-mode testing

The native AArch64 backend is experimental and implements the subset below.
It lowers the validated typed body IR directly, using checked binding,
function, field, and variant identities. Its instruction encoder and static
ELF writer require no external target assembler, linker, or compiler. ELF
output uses `e_machine = 183`, an RX code segment, and a non-executable stack.

The Linux Nix devshell includes `qemu-aarch64` from `qemu-user` (verified with
QEMU 11.0.2). Compile and execute the supplied examples with:

```sh
nix develop --command cargo run -- examples/aarch64_scalar.lim --target aarch64-linux -o /tmp/lim-aarch64-scalar
nix develop --command qemu-aarch64 /tmp/lim-aarch64-scalar
# Expected exit status: 42.
nix develop --command cargo run -- examples/aarch64_syscall.lim --target aarch64-linux -o /tmp/lim-aarch64-syscall
nix develop --command qemu-aarch64 /tmp/lim-aarch64-syscall
# Expected stdout: '*' (no newline), exit status: 42.
nix develop --command cargo run -- --stack-usage examples/aarch64_ownership.lim --target aarch64-linux
nix develop --command cargo test --test aarch64_encoder --test aarch64_native
nix develop --command cargo test --test native_examples
```

The executable must target AArch64 Linux and be statically linked. Static
binaries do not need a guest dynamic loader or a QEMU `-L` sysroot. QEMU user
mode translates the guest userspace instructions and forwards system calls to
the host kernel; it does not boot an AArch64 kernel.

This is a useful cross-architecture execution check, but it does not establish
equivalence with AArch64 hardware. Host kernel behavior, QEMU's CPU and system
call emulation, and the physical processor can differ. In particular, passing
under QEMU does not by itself prove hardware memory ordering, timing,
architecture-specific faults, or behavior of devices and privileged features.

`aarch64-unknown-linux-gnu` is an alias for `aarch64-linux`. Explicit target
selection supplies Linux/AArch64 cfg defaults before parsing; explicit `--cfg`
overrides remain authoritative. The syscall example selects Linux syscall
numbers by architecture so its default x86-64 native outcome is also tested.

The AArch64 tests require QEMU and fail if it is absent; they never silently
skip execution. Emulator processes run in disposable scratch directories,
including fault tests that can generate core files.

## Implemented and tested subset

The tests exercise real static executables through the compiler's native
pipeline, with expected status, output, runtime faults, and rejection cases.

| Area | Current coverage |
| --- | --- |
| Scalars | Bool, char, signed/unsigned 8/16/32/64-bit and pointer-sized integers; wrapping arithmetic, comparisons, division/remainder, bitwise operations, checked shifts, casts, and short-circuit logic |
| Control flow | Conditional expressions, while/for/loop bodies, breaks and continues, loop results, blocks, enum/scalar matches and guards, destructuring, and ordinary let-else patterns |
| Functions | Direct calls using x0–x7 and stack arguments, scalar results in x0, nested calls, and checked named-argument evaluation order |
| Aggregates | Tuples, arrays, structs, and enums; nested/large values, constructors, copies, projections, mutations, indirect arguments and results |
| References/ownership | Shared and exclusive references, referent writes, projections, moves through aggregates and calls, reference-bearing results, explicit release, and shared frontend rejection of invalid borrowing |
| Syscalls | Explicit `#linux-syscall`: x8 number, x0–x5 arguments, `svc #0`, scalar/unit results; QEMU getpid and write checks; startup exit_group=94 |
| Encoder/ELF | Known instruction words, forward/backward branch fixups, unresolved-label rejection, machine identifier and segment permissions |
| Bounds/errors | Division by zero, invalid shift/index and failed assertions fault; oversized layouts return diagnostics; unsupported codegen reports E5000 with source underlines |

These are the implemented subset and tested cases, not full language or
architecture coverage. Aggregates use an internal Lim convention: ascending
eight-byte words, indirect parameters copied into callee storage, and caller
result storage passed in x8. This is not a claim of general AAPCS64 aggregate
classification. References point to that Lim storage. Scalars and reference
handles use AAPCS64 integer registers and 16-byte stack alignment.

Every function has a fixed frame containing locals, expression temporaries,
outgoing stack arguments, and saved FP/LR. Stack reports sum the largest
direct call path and include those allocations; missing/cyclic callees fail
closed. Bounds exclude startup/kernel stack and emulator internals. Frames
are limited to 16 MiB; array lengths are bounded even for zero-sized elements.
Large offsets use register address calculation instead of exceeding encoder
immediate ranges. Out-of-range branch fixups return errors.

## Remaining unsupported features

Floating point, 128-bit integers, saturating arithmetic, raw pointers and
pointer primitives, slices, pinning/owned allocations, atomics, threads,
inline assembly, custom clone hooks, globals/statics, enum payload assignment,
range patterns, and let-else failure bindings are not implemented. Foreign
objects/libraries and foreign calls are rejected. Architecture-specific x86
library wrappers are not translated; explicit syscall numbers must match the
selected target. Unsupported operations fail with diagnostics and never fall
back to x86 lowering. Async/threaded library programs are outside this verified
subset. QEMU results do not establish hardware memory-ordering or fault parity.
