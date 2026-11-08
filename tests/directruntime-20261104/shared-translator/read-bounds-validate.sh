#!/usr/bin/env bash
# Fixed local validation: writer lease, exact resource admission and 300s deadline.
set -euo pipefail
exec python3 -B tests/directruntime-20261104/native-browser/validation-admission.py read-bounds
# FIXED-ADMITTED-RECIPE
#!/usr/bin/env bash
# Guards H126 source, kernel equality, exact bounds and existing runtime controls.
# This separate repair gate preserves all frozen reader/audit v1 expectations.
set -euo pipefail
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 LAKE_CACHE_DIR=
export PATH="$PWD/.lake/native-browser-rowsnine-gates/bin:$PATH"
export PYTHONDONTWRITEBYTECODE=1
lean --version
lake --version
for target in Solidity.Calculus.ReadBoundsStack Solidity.Calculus.ReadBounds Solidity.Calculus.ReadBoundsStackCorrect Solidity.Tools.DirectRuntime; do
  lake build "$target"
done
export GATE_LOGS=tests/directruntime-20261104/shared-translator/artifacts/read-bounds-stack/final-gates
files=(Solidity/Calculus/ReadBoundsStack.lean Solidity/Calculus/ReadBounds.lean Solidity/Calculus/ReadBoundsStackCorrect.lean tests/directruntime-20261104/shared-translator/ReadBoundsStackControls.lean Solidity/KeySort.lean)
for name in AxiomInventory ApiSignatures IntrinsicControls ReaderControls ParityControls AdmissionControls FixtureControls ComposedControls SelectionControls ModalityControls DirectResultControls YulJsonControls RequestControls PrimitiveReturnControls NarrowLocalRuntimeControls FixedByteLocalControls AddressLocalControls EnvironmentMemberControls DynamicBytesBoundaryControls DynamicBytesModelControls; do
 files+=("tests/directruntime-20261104/shared-translator/$name.lean")
done
files+=(tests/directruntime-20261104/control-tuples/ProductionControls.lean tests/directruntime-20261104/control-tuples/ProofAudit.lean)
bash scripts/coord-tools/gate.sh per-file "${files[@]}"
python3 tests/directruntime-20261104/shared-translator/verify-read-bounds-preservation.py
python3 tests/directruntime-20261104/shared-translator/validation-inputs.py
python3 tests/directruntime-20261104/shared-translator/verify-h90-census.py
python3 tests/directruntime-20261104/shared-translator/verify-h90-reader-profile.py
bash scripts/coord-tools/register.sh --check
bash scripts/coord-tools/fragments.sh --check
git diff --check
