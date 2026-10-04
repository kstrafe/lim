# Standard input lines

Use `(#std)` (or import `library/stdin.lim`) and pass an exclusively borrowed `String` to
`std-read-line`. The reader appends to the existing text; it never clears it.

`StdLineRead` carries the number of bytes appended for this line. LF is
consumed but is not appended, so empty lines return `StdLineRead 0`. A final
line without LF is returned normally. `StdEndOfInput` means EOF arrived before
any line bytes; EOF after text returns `StdLineRead` for that text.

Input must be valid UTF-8. Each complete scalar is validated before append, so
an invalid byte or an incomplete scalar at EOF returns
`StdReadFailed (StdTextError StringInvalidUtf8)` without appending that scalar.
Previously appended text and complete scalars from this call remain intact.
Allocation errors are returned as `StdTextError` and likewise preserve the
existing text and successful prefix. Other read errors return
`StdIoError` with negative errno; interrupted reads are retried. Embedded NUL
is valid UTF-8 and is preserved. The implementation uses Linux x86-64 stdin;
other targets return `StdIoError -38`.

`examples/string_stdin.lim` prints each accepted line and frees its String
owner. Empty input prints nothing.
