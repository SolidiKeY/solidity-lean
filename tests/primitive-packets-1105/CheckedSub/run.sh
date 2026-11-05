#!/usr/bin/env bash
# After building CheckedSub.Controls; invoke inside the established resource guard.
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
python3 - "$work/setup.json" <<'PYSETUP'
import json,pathlib,sys
name="Solidity.Backend.PrimitivePackets.CheckedSub.Controls"
setup=json.loads(pathlib.Path(".lake/build/ir/"+name.replace(".","/")+".setup.json").read_text())
setup["name"]="CheckedSubObservations"
setup["importArts"][name]=[str(pathlib.Path(".lake/build/lib/lean/"+name.replace(".","/")+".olean").resolve(strict=True))]
pathlib.Path(sys.argv[1]).write_text(json.dumps(setup))
PYSETUP
args=()
if [ -n "${LAKE_CONFIG:-}" ]; then args=(-f "$LAKE_CONFIG"); fi
LEAN_NUM_THREADS=1 lake "${args[@]}" env lean -j1 --tstack=131072 --setup "$work/setup.json"   tests/primitive-packets-1105/CheckedSub/Observations.lean
