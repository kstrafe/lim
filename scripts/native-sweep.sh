#!/usr/bin/env bash
set -euo pipefail

cargo build --quiet

ok=0
trapped=0
failed=0
temporary_directory="${TMPDIR:-/tmp}/lim-native-sweep-$$"
mkdir -p "$temporary_directory"
trap 'rm -rf "$temporary_directory"' EXIT

for source in examples/*.lim; do
    base=${source##*/}
    stem=${base%.lim}
    assembly="$temporary_directory/$stem.s"
    executable="$temporary_directory/$stem"

    if ! target/debug/lim --emit-asm "$source" "$assembly"; then
        printf 'compiler failure: %s\n' "$source" >&2
        failed=$((failed + 1))
        continue
    fi
    if ! clang "$assembly" -o "$executable" 2>/dev/null; then
        printf 'linker failure: %s\n' "$source" >&2
        failed=$((failed + 1))
        continue
    fi

    if timeout 2 "$executable" >/dev/null 2>&1; then
        status=0
    else
        status=$?
    fi
    if [ "$status" -eq 124 ]; then
        printf 'timeout: %s\n' "$source" >&2
        failed=$((failed + 1))
    elif [ "$status" -ge 128 ]; then
        trapped=$((trapped + 1))
    else
        ok=$((ok + 1))
    fi
done

printf 'native sweep: ok=%s trapped=%s failed=%s\n' "$ok" "$trapped" "$failed"
test "$failed" -eq 0
