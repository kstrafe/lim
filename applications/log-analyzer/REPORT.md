# Implementation notes

The app stays within existing bundled APIs: `std-read-line`, safe `String::byte-at`, String append/clear/free, and `#println`. Each handled error path frees owned Strings. It requires no unsafe application code or compiler changes.

Actual friction encountered:

- There is no bundled decimal formatting helper in the inspected String API. The app implements iterative decimal conversion using explicit `div-wrap`/`rem-wrap`, checking every append result.
- `#return` and `#set` cannot directly occupy `#if` expression arms: compilation required explicit `#block` wrappers ending in `()`.
- Naming an output argument `label` produced `E2000: label requires a name and one value loop expression` at the enclosing main function. Renaming it to `heading` avoids the surface parser keyword collision.
- Standard input reads one byte per syscall and validates UTF-8. Reusing a String avoids retaining all lines, but memory still follows the longest line and arbitrary binary logs fail explicitly.
- The shared resource wrapper serializes workers with a nonblocking lock. Build/test attempts can be refused while another worker is running; waiting for the lock before retrying preserves its memory limits.

The test runner executes the compiled native app and compares exact stdout and exit status. It covers empty input, a mixed fixture, CRLF, 128 KiB/64 KiB lines, missing final newline, token boundaries, decimal conversion, blank lines, malformed UTF-8, a write-only stdin, and `/dev/full` output failure. Allocation failure and u64 exhaustion are handled in code but not fault-injected.

Validation completed: resource-limited compiler build, native application compilation, and all 11 black-box cases passed. `git diff --check` passed.
