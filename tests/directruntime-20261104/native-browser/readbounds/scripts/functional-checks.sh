#!/usr/bin/env bash
# Guard actual changed-source stack behavior and retained source-bound controls.
set -euo pipefail
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 NATIVE_BROWSER_BOUNDED_GATE=1
export PATH=/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH
exec 9>/tmp/solidity-lean-feature-groups-20261025/writer.lock
flock 9
out=/workspace/scratch/browser-chain/readbounds-6513
runner=tests/directruntime-20261104/native-browser/bounded-command.py
export NATIVE_BROWSER_NATIVE_OUTPUT="$PWD/.lake/native-browser-readbounds-6513/native"
export NATIVE_BROWSER_DIRECT="$PWD/.lake/native-browser-readbounds-6513/direct"
export SOLIDITY_BROWSER_DIRECT="$NATIVE_BROWSER_DIRECT"
export SOLIDITY_BROWSER_SOLJSON=/workspace/.setup/solkey/keyext.solidity.core/build/soljson/soljson-v0.8.34+commit.80d5c536.js
unset SOLIDITY_BROWSER_LEAN
python3 "$runner" "$out/package-static-gate.json" node web/tools/build-static.mjs
python3 "$runner" "$out/package-single-gate.json" node web/tools/build-single-file.mjs
export NATIVE_BROWSER_ADDRESS_OUTPUT="$out"
for item in environment:diamond environment:box address:diamond address:box fixed-byte:diamond fixed-byte:box primitive-return:C primitive-return:A; do
 area=${item%:*}; modality=${item#*:}
 export NATIVE_BROWSER_CONTROL_SUITE="$PWD/tests/directruntime-20261104/native-browser/$area/$modality-suite.json"
 export NATIVE_BROWSER_CONTROL_OUTPUT="$out/$area-$modality-controls"
 python3 "$runner" "$out/$area-$modality-gate.json" node tests/directruntime-20261104/native-browser/published-8495-controls.mjs
done
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
# No known-failure continuation: repaired runtime must complete every negative.
python3 "$runner" "$out/browser-negatives-gate.json" node tests/directruntime-20261104/native-browser/browser-control-completion.cjs
