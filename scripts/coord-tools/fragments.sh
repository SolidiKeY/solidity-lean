#!/usr/bin/env bash
# fragments.sh [--check | --resolve [--lane NAME] [--ours-lane NAME] | --force]:
# the combined bookkeeping files (module map, docs/README.md, TERRA-TODO.md,
# the axiom-pin inventory) generated from per-lane fragments.  See the
# docstring of fragments.py and `docs/parallelism.md`, "Shared registries".
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
exec python3 scripts/coord-tools/fragments.py "$@"
