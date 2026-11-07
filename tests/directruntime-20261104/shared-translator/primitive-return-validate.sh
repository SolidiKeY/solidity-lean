#!/usr/bin/env bash
# Guards primitive-return entrypoint repair and retained H90/no-return controls.
# Invoke through bounded.sh; no bare Lean builds or concurrent gates.
set -euo pipefail
echo "RESOURCE memory.max=$(cat /sys/fs/cgroup/memory.max) memory.swap.max=$(cat /sys/fs/cgroup/memory.swap.max) LEAN_NUM_THREADS=$LEAN_NUM_THREADS"
/workspace/.setup/tools/lean-4.24.0-linux/bin/lean --version
/workspace/.setup/tools/lean-4.24.0-linux/bin/lake --version
for target in Solidity.Frontend.ExecutableAst.Shared.Boundary Solidity.Frontend.ExecutableAst.Shared.Translate Solidity.Frontend.ExecutableAst.ControlTuple.Adapter Solidity.Frontend.ExecutableAst.ControlTuple.AdmissionControls Solidity.Frontend.ExecutableAst.ControlTuple.IntrinsicControls Solidity.Frontend.ExecutableAst.Shared.Compose Solidity.Frontend.ExecutableAst.Shared.Scope Solidity.Frontend.ExecutableAst.Shared.Intrinsic Solidity.Tools.DirectRuntime; do
  lake build "$target"
done
export GATE_LOGS=tests/directruntime-20261104/shared-translator/artifacts/primitive-return/gates
files=(Solidity/Frontend/ExecutableAst/Shared/Intrinsic.lean tests/directruntime-20261104/shared-translator/PrimitiveReturnControls.lean Solidity/KeySort.lean Solidity/Frontend/ExecutableAst/Shared/Translate.lean Solidity/Frontend/ExecutableAst/ControlTuple/Adapter.lean Solidity/Frontend/ExecutableAst/Shared/Compose.lean)
for name in NarrowLocalControls NarrowLocalRuntimeControls AxiomInventory ApiSignatures ConstructReaderControls IntrinsicControls ReaderControls ParityControls AdmissionControls FixtureControls ComposedControls SelectionControls ModalityControls DirectResultControls YulJsonControls RequestControls; do
 files+=("tests/directruntime-20261104/shared-translator/$name.lean")
done
files+=(Solidity/Frontend/ExecutableAst/ControlTuple/AdmissionControls.lean Solidity/Frontend/ExecutableAst/ControlTuple/IntrinsicControls.lean tests/directruntime-20261104/control-tuples/ObligationControls.lean tests/directruntime-20261104/control-tuples/ProofAudit.lean tests/directruntime-20261104/control-tuples/ProductionControls.lean)
bash scripts/coord-tools/gate.sh per-file "${files[@]}"
python3 tests/directruntime-20261104/shared-translator/verify-h90-reader-profile.py
python3 tests/directruntime-20261104/shared-translator/verify-h90-census.py
python3 tests/directruntime-20261104/shared-translator/audit.py
