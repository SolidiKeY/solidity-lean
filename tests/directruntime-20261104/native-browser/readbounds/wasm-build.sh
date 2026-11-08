#!/usr/bin/env bash
set -euo pipefail
# One reviewed implementation owns writer.lock before cache/output mutations.
script_dir=$(cd -- "$(dirname -- "${BASH_SOURCE[0]}")" && pwd)
exec bash "$script_dir/scripts/wasm-build.sh" "$@"
