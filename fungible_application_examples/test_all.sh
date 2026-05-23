#!/usr/bin/env bash
# Run `cargo test` in every immediate subdirectory that has a Cargo.toml.
# A few chains pin `build.target = "wasm32-unknown-unknown"` in their
# .cargo/config.toml (near, gear); for those we override with the host
# triple so tests can run.
# Linera's bin targets compile only for wasm32 (no_main attribute), so we
# pass `--lib` for it to skip the binaries.
# (No `set -u`: bash 3.2 on macOS treats empty arrays as unbound.)

SCRIPT_DIR="$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" &>/dev/null && pwd)"
HOST_TRIPLE="$(rustc -vV | awk '/^host:/ {print $2}')"
pass=0
fail=0
failed=""

for dir in "$SCRIPT_DIR"/*/; do
    [ -f "$dir/Cargo.toml" ] || continue
    name="$(basename "$dir")"
    echo
    echo "=== $name ==="
    extra=()
    case "$name" in
        near|gear)  extra=(--target "$HOST_TRIPLE") ;;
        linera)     extra=(--lib) ;;
    esac
    if ( cd "$dir" && cargo test "${extra[@]}" "$@" ); then
        pass=$((pass+1))
    else
        fail=$((fail+1))
        failed="$failed $name"
    fi
done

echo
echo "passed: $pass    failed: $fail${failed:+   (}${failed# }${failed:+)}"
[ "$fail" -eq 0 ]
