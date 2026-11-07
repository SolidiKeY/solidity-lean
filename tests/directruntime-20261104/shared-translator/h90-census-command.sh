#!/usr/bin/env bash
# Guards H90 matched base/head census; invoked only inside bounded.sh.
set -euo pipefail
trap 'scripts/coord-tools/lean-mcp stop' EXIT
scripts/coord-tools/lean-mcp diag "${1:-tests/directruntime-20261104/shared-translator/H90Census.lean}"
