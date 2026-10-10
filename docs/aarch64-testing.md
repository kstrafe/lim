# AArch64 Linux user-mode testing

The Linux Nix devshell includes `qemu-aarch64` from `qemu-user`. This provides
a way to run statically linked AArch64 Linux executables on a Linux host:

```sh
nix develop --command qemu-aarch64 ./path/to/static-aarch64-program
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

## Future acceptance matrix

The following are future coverage targets for generated static AArch64 Linux
programs. Each should have an executable check with expected output or status;
QEMU results should be recorded separately from native hardware results.

| Area | Acceptance target |
| --- | --- |
| Scalar ABI | Integer and floating-point arguments and return values, including register and stack boundaries |
| Aggregate ABI | Small and large aggregate arguments and results, with alignment and register/stack classification covered |
| Atomic operations | Shared-memory atomic operations and concurrency checks; QEMU success is not hardware equivalence evidence |
| Ownership | Compile-time ownership and borrowing acceptance/rejection cases, plus runtime cases where relevant |
| Syscalls | Static Linux programs exercise supported syscall wrappers and verify results, errors, exit status, and output |
| Native encoder | AArch64 instruction encoding and execution tests use the project's native encoder and require no Clang dependency |

This matrix describes future acceptance coverage; adding QEMU to the devshell
does not mean these checks are already implemented or passing.
