# File and buffered reader API

Import `file.lim` directly or use `(#std)`, which includes it. The API is
implemented with direct Linux x86-64 syscalls and exposes opaque, linear
`File` and `FileReader` values. A descriptor has one owner: it cannot be
copied, abandoned, or closed while borrowed.

`File-open-read` opens an existing path for reading. `File-create` opens a
file for writing, creates it when absent, and truncates it when present. Its
`permissions` argument is the mode supplied to Linux `openat`; the process
umask still applies. For example, `384u32` is octal `0600`. Both calls take a
shared `String` path, reject embedded NUL, and return `FileOpenResult` with
either `FileOpened` or `FileOpenFailed`. `FileIoError` values are raw negative
errno results, so a missing path reports `-2` (`ENOENT`). Path cloning and NUL
termination can also report string allocation errors.

`File-write-string` borrows a file mutably and a `String` immutably. It writes
the string's exact UTF-8 byte length, including embedded NUL bytes, and loops
over short writes and interrupted syscalls. `FileWritten` reports the number
of bytes written. If a later write fails, `FileWriteFailed` reports the
completed byte count together with the I/O error. The caller remains
responsible for closing the file.

`FileReader-create` takes ownership of a `File` and allocates a caller-sized
buffer. A zero or otherwise invalid size is reported as an allocation error.
On failure, `FileReaderCreateFailed` returns the still-owned `File` together
with the error, so the caller can close it. On success, the reader owns both
the descriptor and buffer. `FileReader-next-byte` returns one binary byte at
a time as `FileByte`, returns `FileByteEof` repeatedly after end-of-file, or
returns `FileByteFailed` with the raw I/O error. An interrupted read is
returned as `-4` (`EINTR`); call `FileReader-next-byte` again if retrying is
appropriate. `FileReader-close` releases the buffer and closes its owned
descriptor.

`File-close` and `FileReader-close` consume their linear arguments even when
the close syscall reports an error. Linux releases the descriptor on close;
retrying could close a different descriptor that the process has since
opened. Close errors are returned as `FileFailed (FileIoError errno)`.

The syscall implementation is enabled only for Linux x86-64. On other
platforms and architectures, the low-level operations return `-38` (`ENOSYS`)
through the same result variants, allowing callers to handle unsupported
operation without relying on a native linker or libc wrapper.

The native regression suite is `cargo test --test files`; standard library
integration coverage is in `cargo test --test standard_library`.
