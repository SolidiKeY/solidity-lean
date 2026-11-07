#!/usr/bin/env bash
set -euo pipefail
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 NATIVE_BROWSER_BOUNDED_GATE=1
export PATH=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH
out=/workspace/scratch/browser-chain/environment
runner=tests/directruntime-20261104/native-browser/bounded-command.py
export NATIVE_BROWSER_NATIVE_OUTPUT="$PWD/.lake/native-browser-environment/native"
export NATIVE_BROWSER_DIRECT="$PWD/.lake/native-browser-environment/direct"
export NATIVE_BROWSER_ADDRESS_OUTPUT="$out"
python3 "$runner" "$out/candidate-exclusion-recovered-gate.json" python3 .lake/native-browser-environment/check-candidate-exclusion.py
export NATIVE_BROWSER_CONTROL_SUITE="$PWD/tests/directruntime-20261104/native-browser/fixed-byte/diamond-suite.json"
export NATIVE_BROWSER_CONTROL_OUTPUT="$out/fixed-byte-diamond-controls"
python3 "$runner" "$out/fixed-byte-diamond-controls-gate.json" node tests/directruntime-20261104/native-browser/published-8495-controls.mjs
export NATIVE_BROWSER_CONTROL_SUITE="$PWD/tests/directruntime-20261104/native-browser/fixed-byte/box-suite.json"
export NATIVE_BROWSER_CONTROL_OUTPUT="$out/fixed-byte-box-controls"
python3 "$runner" "$out/fixed-byte-box-controls-gate.json" node tests/directruntime-20261104/native-browser/published-8495-controls.mjs
export NATIVE_BROWSER_CONTROL_SUITE="$PWD/tests/directruntime-20261104/native-browser/primitive-return/C-suite.json"
export NATIVE_BROWSER_CONTROL_OUTPUT="$out/C-controls"
python3 "$runner" "$out/C-controls-gate.json" node tests/directruntime-20261104/native-browser/published-8495-controls.mjs
export NATIVE_BROWSER_CONTROL_SUITE="$PWD/tests/directruntime-20261104/native-browser/primitive-return/A-suite.json"
export NATIVE_BROWSER_CONTROL_OUTPUT="$out/A-controls"
python3 "$runner" "$out/A-controls-gate.json" node tests/directruntime-20261104/native-browser/published-8495-controls.mjs
unset NATIVE_BROWSER_CONTROL_SUITE
export NATIVE_BROWSER_MEMORY_PRODUCER="$PWD/.lake/native-browser-primitive-return/B-intake"
export NATIVE_BROWSER_ORIGINAL_JOURNAL=/workspace/h62-coordinator-inputs/router-20261106T200314Z
export NATIVE_BROWSER_CONTROL_OUTPUT="$out/B-controls-authenticated"
python3 "$runner" "$out/B-controls-authenticated-gate.json" node tests/directruntime-20261104/native-browser/h81-memory-controls.mjs
export NATIVE_BROWSER_FUNCTIONAL_OUTPUT="$out/functional83"
python3 "$runner" "$out/functional83-gate.json" node tests/directruntime-20261104/native-browser/primitive-return/functional83.mjs
export NATIVE_BROWSER_OUTPUT="$out/negative-controls"
mkdir "$NATIVE_BROWSER_OUTPUT"
ln -s "$out/functional83/inputs" "$NATIVE_BROWSER_OUTPUT/inputs"
python3 "$runner" "$out/browser-negatives-gate.json" node tests/directruntime-20261104/native-browser/browser-control-completion.cjs || true
python3 "$runner" "$out/native-negatives-gate.json" python3 .lake/native-browser-environment/native-negatives.py
mkdir "$out/ui"
if [[ -e web/artifacts/single-file-report.json ]]; then cp web/artifacts/single-file-report.json "$out/ui/previous-report.json"; rm web/artifacts/single-file-report.json; fi
python3 "$runner" "$out/ui-gate.json" node web/test/website.cjs --single --proofs
cp web/artifacts/single-file-report.json "$out/ui/report.json"
python3 "$runner" "$out/finite-gate.json" bash .lake/native-browser-environment/finite-gate.sh
python3 "$runner" "$out/B-kernel-gate.json" bash .lake/native-browser-environment/B-kernel-controls.sh
