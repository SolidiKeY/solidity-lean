#!/usr/bin/env bash
# V2 uses explicit master4.24; the frozen v1 reproduce-width.py keeps its4.35 pin.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
exec python3 -B scripts/h62/item4/generic-v08/reproduce-width-v2.py "$@"
