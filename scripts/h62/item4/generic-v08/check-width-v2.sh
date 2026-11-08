#!/usr/bin/env bash
# Independently check current-signature consumers; frozen v1 remains unresolved.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
export LEAN_NUM_THREADS=1
exec bash scripts/coord-tools/gate.sh per-file tests/h62/item4/generic-v08/IntrinsicWidthsV2.lean
