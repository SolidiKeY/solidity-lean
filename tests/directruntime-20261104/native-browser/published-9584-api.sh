#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 LAKE_CACHE_DIR= PYTHONDONTWRITEBYTECODE=1
export PATH="$PWD/.lake/native-browser-prefix/bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH"
lake build Solidity.Frontend.ExecutableAst.Shared.Scope Solidity.Frontend.ExecutableAst.ControlTuple.IntrinsicControls
python3 - <<'INVENTORY'
from pathlib import Path
import json,re,hashlib,subprocess
out=Path('docs/benchmarks/directruntime-2026-11-04/published-9584');modules=['Solidity.Frontend.ExecutableAst.Shared.Scope','Solidity.Frontend.ExecutableAst.ControlTuple.IntrinsicControls'];names=[];sources=[]
for module in modules:
 p=Path(module.replace('.','/')+'.lean');s=p.read_text();ns=re.search(r'^namespace (.+)$',s,re.M)[1];decls=re.findall(r'^theorem (\w+)',s,re.M);names.extend(ns+'.'+name for name in decls);sources.append({'module':module,'sourceSha256':hashlib.sha256(p.read_bytes()).hexdigest(),'theorems':decls})
p=Path('.lake/native-browser-9584-axioms.lean');assert not p.exists();p.write_text('\n'.join('import '+m for m in modules)+'\n'+''.join('#check '+n+'\n#print axioms '+n+'\n' for n in names))
(out/'producer-inventory.json').write_text(json.dumps({'head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'publishedBase':'9584f9e7df09f638d9e0cb8930501d1660aa4b2f','producerSources':sources,'axiomTargets':names,'workerLeanChanges':[],'boundary':'Consumer audit of adopted producer model/scope theorems; no D theorem edits. Intrinsic controls do not prove compiler/source equivalence or runtime support.'},indent=2)+'\n')
INVENTORY
mkdir .lake/native-browser-9584-gate-bin
cat > .lake/native-browser-9584-gate-bin/lake <<'LAKE'
#!/usr/bin/env bash
set -euo pipefail
if [[ ${1:-} == env && ${2:-} == lean ]]; then
 shift 2
 exec /workspace/.setup/tools/lean-4.24.0-linux/bin/lake -f .lake/native-browser-serial.toml env lean -j1 "$@"
fi
exec /workspace/.setup/tools/lean-4.24.0-linux/bin/lake -f .lake/native-browser-serial.toml "$@"
LAKE
chmod +x .lake/native-browser-9584-gate-bin/lake
export PATH="$PWD/.lake/native-browser-9584-gate-bin:$PATH"
export GATE_LOGS="$PWD/.lake/native-browser-9584-axiom-gates"
bash scripts/coord-tools/gate.sh per-file .lake/native-browser-9584-axioms.lean
cp "$GATE_LOGS/1.log" docs/benchmarks/directruntime-2026-11-04/published-9584/producer-signatures-axioms.log
python3 - <<'AUDIT'
from pathlib import Path
import re,json
out=Path('docs/benchmarks/directruntime-2026-11-04/published-9584');s=(out/'producer-signatures-axioms.log').read_text();assert 'sorryAx' not in s;expected=json.loads((out/'producer-inventory.json').read_text())['axiomTargets'];entries=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",s);assert {n for n,_ in entries}==set(expected),(len(entries),len(expected));allowed={'propext','Classical.choice','Quot.sound'}
for n,axioms in entries:assert {x.strip() for x in axioms.split(',') if x.strip()}<=allowed,(n,axioms)
(out/'producer-axiom-result.json').write_text(json.dumps({'passed':True,'theorems':len(entries),'allowedExistingStandardAxioms':sorted(allowed),'newAxioms':[],'boundary':'Actual #check/#print axioms on adopted producer declarations, not runtime/source adequacy.'},indent=2)+'\n');print('PASS producer axiom inventory:',len(entries),'theorems; no new axioms or sorry')
AUDIT
