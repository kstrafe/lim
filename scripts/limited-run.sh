#!/usr/bin/env bash
# Run development commands without risking unbounded host resource use.
set -euo pipefail

if (( $# == 0 )); then
    printf 'Usage: bash scripts/limited-run.sh COMMAND [ARGUMENTS...]\n' >&2
    exit 2
fi

# Keep all invocations serial, including invocations from separate agents.
: "${XDG_RUNTIME_DIR:?A systemd user session is required}"
exec 9>"$XDG_RUNTIME_DIR/lim-agent-command.lock"
if ! flock -n 9; then
    printf 'Another limited command is already running; wait for it to finish.\n' >&2
    exit 1
fi

# Scope limits cover the entire command tree, not each process separately.
# Refuse to run if systemd cannot apply them; never fall back to no limits.
systemd-run --user --scope --quiet --slice=lim-agent.slice \
    --property=MemoryMax=2G \
    --property=MemorySwapMax=0 \
    --property=CPUQuota=200% \
    --property=TasksMax=128 \
    timeout --kill-after=5s 10m \
    env CARGO_BUILD_JOBS=1 RUST_TEST_THREADS=1 "$@"
