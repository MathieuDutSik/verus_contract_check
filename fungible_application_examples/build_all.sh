#!/usr/bin/env bash
# Run `cargo build` in every immediate subdirectory that has a Cargo.toml.
set -u

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &>/dev/null && pwd)"
pass=0
fail=0
failed=""

for dir in "$SCRIPT_DIR"/*/; do
    [ -f "$dir/Cargo.toml" ] || continue
    name="$(basename "$dir")"
    echo
    echo "=== $name ==="
    if ( cd "$dir" && cargo verus build "$@" ); then
        pass=$((pass+1))
    else
        fail=$((fail+1))
        failed="$failed $name"
    fi
done

echo
echo "passed: $pass    failed: $fail${failed:+   (}${failed# }${failed:+)}"
[ "$fail" -eq 0 ]
