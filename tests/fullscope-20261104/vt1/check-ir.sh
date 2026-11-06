#!/usr/bin/env bash
# VT1 C06-C08 checks: fixture derivations (Python, no compiler) and the Lean
# check files. Lean files are elaborated with `lake env lean` where the
# environment permits it; on Claude cloud VMs they are checked through the Lean
# MCP server instead (evidence/claude-c08/README.md records the outputs).
set -euo pipefail
cd "$(git rev-parse --show-toplevel)"
dir=tests/fullscope-20261104/vt1
python3 -I "$dir/generate-artifacts.py" --check
python3 -I "$dir/extract-helpers.py" --check
python3 -I "$dir/gen-exp-module.py" --check
if [[ "${VT1_SKIP_LEAN:-0}" != 1 ]]; then
  for f in IrParseChecks IrEvalChecks IrHelperChecks; do
    out=$(lake env lean --tstack=131072 "$dir/$f.lean" 2>&1)
    echo "$out" | grep -E "IR_|error" || true
    if echo "$out" | grep -q "error"; then echo "FAIL $f"; exit 1; fi
  done
fi
echo VT1_IR_CHECKS_PASS
