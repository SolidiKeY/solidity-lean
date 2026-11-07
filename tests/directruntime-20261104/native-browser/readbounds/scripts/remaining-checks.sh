#!/usr/bin/env bash
set -euo pipefail
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock 9
: "${NATIVE_BROWSER_BASELINE_EVIDENCE:?explicit authenticated private baseline directory required}"
runner=tests/directruntime-20261104/native-browser/bounded-command.py
out=/workspace/scratch/browser-chain/readbounds-6513
python3 "$runner" "$out/closure-gate.json" python3 tests/directruntime-20261104/native-browser/readbounds/scripts/closure-audit.py --baseline-evidence-dir "$NATIVE_BROWSER_BASELINE_EVIDENCE"
flock -u 9
python3 "$runner" "$out/native-negatives-gate.json" python3 tests/directruntime-20261104/native-browser/readbounds/scripts/native-negatives.py
