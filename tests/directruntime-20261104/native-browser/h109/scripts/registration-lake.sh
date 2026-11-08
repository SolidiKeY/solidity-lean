#!/usr/bin/env bash
set -euo pipefail
if [[ ${1:-} == serve ]]; then
 exec /workspace/.setup/tools/lean-4.24.0-linux/bin/lake -f .lake/native-browser-serial.toml "$@" -j1
fi
exec /workspace/.setup/tools/lean-4.24.0-linux/bin/lake -f .lake/native-browser-serial.toml "$@"
