#!/usr/bin/env bash
# Guard ordinary editor requests and build-provenance refusals; no timing comparison.
set -euo pipefail
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 NATIVE_BROWSER_BOUNDED_GATE=1 PYTHONDONTWRITEBYTECODE=1
export PATH=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock 9
out=/workspace/scratch/browser-chain/readbounds-6513
runner=tests/directruntime-20261104/native-browser/bounded-command.py
python3 "$runner" "$out/provenance-regressions-gate.json" bash tests/directruntime-20261104/native-browser/hardening-validation.sh
mkdir "$out/ui"
if [[ -e web/artifacts/single-file-report.json ]]; then mv web/artifacts/single-file-report.json "$out/ui/previous-report.json"; fi
python3 "$runner" "$out/ui-functional-gate.json" node web/test/website.cjs --single --proofs
cp web/artifacts/single-file-report.json "$out/ui/report.json"
