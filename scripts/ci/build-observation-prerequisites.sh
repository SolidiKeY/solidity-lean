#!/usr/bin/env bash
# One bounded prerequisite group, not a metadata/control acceptance gate.
# Run under the caller's existing resource supervisor and writer lock.
set -euo pipefail
if [[ $# != 1 ]]; then
  echo "usage: $0 SERIAL_LAKE_TOML" >&2
  exit 2
fi
python3 - "$1" <<'CHECK'
import sys, tomllib
with open(sys.argv[1], "rb") as source:
    config = tomllib.load(source)
libs = [lib for lib in config.get("lean_lib", []) if lib.get("name") == "Solidity"]
required = {"-j1", "--tstack=131072"}
if len(libs) != 1 or set(libs[0].get("weakLeanArgs", [])) != required:
    sys.exit("Solidity requires only -j1 and --tstack=131072")
def reject_overrides(value):
    if isinstance(value, dict):
        for key, entry in value.items():
            if key == "weakLeanArgs" and (len(entry) != 2 or set(entry) != required):
                sys.exit("conflicting weak Lean arguments refused")
            if key != "weakLeanArgs" and key.lower().endswith("leanargs") and entry:
                sys.exit("additional Lean arguments refused")
            reject_overrides(entry)
    elif isinstance(value, list):
        for entry in value:
            reject_overrides(entry)
reject_overrides(config)
CHECK
export LEAN_NUM_THREADS=1
# The timeout covers the entire group; it is never reset for each module.
timeout 300 bash -euc '
  for module in Solidity.Theory.Typed.Obs.Paths Solidity.Theory.Typed.Obs.Values Solidity.Theory.Typed.Obs.Ops; do
    lake --file "$1" build "$module:leanArts"
  done
' -- "$1"
