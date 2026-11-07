#!/usr/bin/env bash
# Guards the general environment decoder proof against runtime-definition changes.
# Run through bounded.sh, without the MCP-only root configuration overlay.
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
python3 - <<'PYBODY'
from pathlib import Path
import hashlib,json,subprocess
p=Path('Solidity/Frontend/ExecutableAst/Shared/Translate.lean')
owned=Path('tests/directruntime-20261104/shared-translator');out=owned/'artifacts/environment-proof'
base=(out/'base-head.txt').read_text().strip()
old=subprocess.check_output(['git','show',base+':'+str(p)])
current=p.read_text();begin=current.index('/-- A successful environment decoder selects an existing EnvKey map entry')
end=current.index('def expressionStep',begin);normalized=(current[:begin]+current[end:]).encode()
assert normalized==old,'executable/source definitions changed beyond added proof'
report={'base':base,'path':str(p),'baseSha256':hashlib.sha256(old).hexdigest(),'strippedCurrentSha256':hashlib.sha256(normalized).hexdigest(),'onlyAddition':'environmentMember?_guard lemma/doc','executableDefinitionsByteIdentical':True,'boundary':'Source text comparison, not compiled binary or source/world adequacy proof.'}
(out/'definition-comparison.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
PYBODY
printf 'RESOURCE memory.max=%s memory.swap.max=%s LEAN_NUM_THREADS=%s\n' "$(cat /sys/fs/cgroup/memory.max)" "$(cat /sys/fs/cgroup/memory.swap.max)" "$LEAN_NUM_THREADS"
/workspace/.setup/tools/lean-4.24.0-linux/bin/lean --version
/workspace/.setup/tools/lean-4.24.0-linux/bin/lake --version
for target in Solidity.Frontend.ExecutableAst.Shared.Boundary Solidity.Frontend.ExecutableAst.Shared.Translate Solidity.Frontend.ExecutableAst.ControlTuple.Adapter Solidity.Frontend.ExecutableAst.ControlTuple.AdmissionControls Solidity.Frontend.ExecutableAst.ControlTuple.IntrinsicControls Solidity.Frontend.ExecutableAst.Shared.Compose Solidity.Frontend.ExecutableAst.Shared.Scope Solidity.Frontend.ExecutableAst.Shared.Intrinsic Solidity.Tools.DirectRuntime; do
 lake build "$target"
done
export GATE_LOGS=tests/directruntime-20261104/shared-translator/artifacts/environment-proof/gates
bash scripts/coord-tools/gate.sh per-file Solidity/Frontend/ExecutableAst/Shared/Translate.lean tests/directruntime-20261104/shared-translator/AxiomInventory.lean tests/directruntime-20261104/shared-translator/ApiSignatures.lean tests/directruntime-20261104/shared-translator/EnvironmentMemberControls.lean tests/directruntime-20261104/shared-translator/AddressLocalControls.lean Solidity/KeySort.lean
# Runtime definitions are byte-identical; retain prior observations and refresh
# only the source-file proof hash in their authenticated census manifest.
python3 tests/directruntime-20261104/shared-translator/verify-h90-census.py --capture-manifest
python3 tests/directruntime-20261104/shared-translator/verify-h90-census.py
python3 tests/directruntime-20261104/shared-translator/verify-h90-reader-profile.py
python3 tests/directruntime-20261104/shared-translator/audit.py
git diff --check
