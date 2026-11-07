#!/usr/bin/env bash
set -euo pipefail
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock 9
runner=tests/directruntime-20261104/native-browser/bounded-command.py
out=/workspace/scratch/browser-chain/readbounds-6513
python3 "$runner" "$out/closure-gate.json" python3 .lake/native-browser-readbounds-6513/closure-audit.py
python3 "$runner" "$out/native-negatives-gate.json" python3 .lake/native-browser-readbounds-6513/native-negatives.py
