#!/usr/bin/env bash
# Guards metadata-decoder proof additions against changes to executable definitions.
# Run with bounded.sh; do not use the MCP-only root config overlay for this audit.
set -euo pipefail
export PYTHONDONTWRITEBYTECODE=1
python3 tests/directruntime-20261104/shared-translator/validation-inputs.py
python3 - <<'PYBODY'
from pathlib import Path
import hashlib,json,subprocess
p=Path('Solidity/Frontend/ExecutableAst/Shared/Translate.lean')
out=Path('tests/directruntime-20261104/shared-translator/artifacts/environment-decoder-proof')
out.mkdir(parents=True,exist_ok=True)
base='88a946c78971ef2fadc6d4ff72d7020092e6dfb6'
old=subprocess.check_output(['git','show',base+':'+str(p)])
current=p.read_text()
begin=current.index('/-- One shared inversion of every successful environment decode:')
end=current.index('def expressionStep',begin)
oldtext=old.decode()
oldbegin=oldtext.index('/-- A successful environment decoder selects an existing EnvKey map entry')
oldend=oldtext.index('def expressionStep',oldbegin)
guardbegin=current.index('/-- A successful environment decoder selects an existing EnvKey map entry',begin)
guardend=current.index('/-- All explicit builtin metadata guards suffice for the existing decoder.',guardbegin)
oldguard=oldtext[oldbegin:oldend]
newguard=current[guardbegin:guardend]
assert newguard[:newguard.index(':= by')] == oldguard[:oldguard.index(':= by')], 'existing guard theorem statement changed'
import re
assert re.findall(r'^theorem ([^ (]+)',current[begin:end],re.M) == ['environmentMember?_guards','environmentMember?_guard','environmentMember?_of_metadata','environmentMember?_resultType']
assert not re.search(r'^(?:private )?(?:def|axiom|opaque|abbrev|instance) ',current[begin:end],re.M)
normalized=(current[:begin]+oldguard+current[end:]).encode()
assert normalized==old,'changes beyond additive decoder theorems/docs and old guard proof'

report={'base':base,'source':str(p),'baseSha256':hashlib.sha256(old).hexdigest(),
        'strippedCurrentSha256':hashlib.sha256(normalized).hexdigest(),
        'executableDefinitionsByteIdentical':True,
        'addedTheorems':['environmentMember?_guards','environmentMember?_of_metadata','environmentMember?_resultType'],
        'existingGuardStatementByteIdentical':True,
        'existingGuardProof':'projection of the shared inversion; statement unchanged',
        'boundary':'Source text equality after removing additive proofs and restoring the old guard proof, with its statement checked byte-identical; not source/world or binary adequacy.'}
(out/'definition-comparison.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report))
PYBODY
/workspace/.setup/tools/lean-4.24.0-linux/bin/lean --version
/workspace/.setup/tools/lean-4.24.0-linux/bin/lake --version
for target in Solidity.Frontend.ExecutableAst.Shared.Boundary Solidity.Frontend.ExecutableAst.Shared.Translate Solidity.Frontend.ExecutableAst.ControlTuple.Adapter Solidity.Frontend.ExecutableAst.ControlTuple.AdmissionControls Solidity.Frontend.ExecutableAst.ControlTuple.IntrinsicControls Solidity.Frontend.ExecutableAst.Shared.Compose Solidity.Frontend.ExecutableAst.Shared.Scope Solidity.Frontend.ExecutableAst.Shared.Intrinsic Solidity.Tools.DirectRuntime; do
  lake build "$target"
done
export GATE_LOGS=tests/directruntime-20261104/shared-translator/artifacts/environment-decoder-proof/gates
bash scripts/coord-tools/gate.sh per-file Solidity/Frontend/ExecutableAst/Shared/Translate.lean tests/directruntime-20261104/shared-translator/AxiomInventory.lean tests/directruntime-20261104/shared-translator/ApiSignatures.lean tests/directruntime-20261104/shared-translator/EnvironmentMemberControls.lean tests/directruntime-20261104/shared-translator/AddressLocalControls.lean Solidity/KeySort.lean
# Replay frozen observations against committed pins; never regenerate expected
# manifests during validation. Decoder definitions remain byte-identical.
python3 tests/directruntime-20261104/shared-translator/verify-h90-census.py
python3 tests/directruntime-20261104/shared-translator/verify-h90-reader-profile.py
python3 tests/directruntime-20261104/shared-translator/audit.py
git diff --check
