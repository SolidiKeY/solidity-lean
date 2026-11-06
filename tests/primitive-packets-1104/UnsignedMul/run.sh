#!/usr/bin/env bash
# Run after building WidthControls and WideControls, inside the lane's resource guard.
set -euo pipefail
root=$(git rev-parse --show-toplevel)
cd "$root"
work=$(mktemp -d)
trap 'rm -rf "$work"' EXIT
python3 - "$work/setup.json" <<'PYSETUP'
import json, pathlib, sys
prefix = "Solidity.Backend.PrimitivePackets.UnsignedMul."
setup = json.loads(pathlib.Path(".lake/build/ir/" + prefix.replace(".", "/") + "WidthControls.setup.json").read_text())
setup["name"] = "UnsignedMulObservations"
for leaf in ["WidthControls", "WideControls"]:
    name = prefix + leaf
    artifact = pathlib.Path(".lake/build/lib/lean/" + name.replace(".", "/") + ".olean").resolve(strict=True)
    setup["importArts"][name] = [str(artifact)]
pathlib.Path(sys.argv[1]).write_text(json.dumps(setup))
PYSETUP
lake_args=()
if [ -n "${LAKE_CONFIG:-}" ]; then lake_args=(-f "$LAKE_CONFIG"); fi
LEAN_NUM_THREADS=1 lake "${lake_args[@]}" env lean -j1 --tstack=131072 --setup "$work/setup.json"   tests/primitive-packets-1104/UnsignedMul/Observations.lean
