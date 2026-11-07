#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 LAKE_CACHE_DIR=
export PATH="$PWD/.lake/native-browser-prefix/bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH"
python3 - "${H35_AXIOM_RECEIPT:-docs/benchmarks/directruntime-2026-11-04/h35/axiom-inventory.json}" <<'INVENTORY'
import hashlib,json,pathlib,subprocess,sys,tomllib
root=pathlib.Path.cwd();delivery='89373e34cdfd6bb5db7054b1c204d01edffc5fa7'
changed=subprocess.check_output(['git','diff','--name-only',delivery,'HEAD','--','*.lean'],text=True).splitlines()
assert not changed,changed
working=subprocess.check_output(['git','diff','--name-only','HEAD','--','*.lean'],text=True).splitlines()
untracked=[p for p in subprocess.check_output(['git','ls-files','--others','--exclude-standard'],text=True).splitlines() if p.endswith('.lean')]
assert not working,working
assert not untracked,untracked
config=tomllib.loads((root/'.lake/native-browser-serial.toml').read_text())
target=next(lib for lib in config['lean_lib'] if lib['name']=='Solidity')
assert '-j1' in target['weakLeanArgs']
report=dict(head=subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),publishedDelivery=delivery,ownedLeanChanges=changed,uncommittedLeanChanges=working,untrackedLeanFiles=untracked,newOrChangedWorkerTheorems=[],printAxiomsCommands=[],status='not applicable: no new or changed worker Lean declarations',boundary='Published producer changes are separate from worker ownership. This does not establish their proof closure or the missing Identity acceptance.')
p=root/sys.argv[1]
with p.open('x') as f:f.write(json.dumps(report,indent=2)+'\n')
print('AXIOM INVENTORY: 0 new/changed worker theorems; no #print axioms targets')
INVENTORY
if [[ ${H35_INVENTORY_ONLY:-0} == 1 ]]; then exit 0; fi
lake build Solidity.Tools.DirectRuntime
bash tests/directruntime-20261104/native-browser/hardening-validation.sh
export NATIVE_BROWSER_CHECK_OUTPUT=docs/benchmarks/directruntime-2026-11-04/h35
export NATIVE_BROWSER_NATIVE_OUTPUT="$PWD/.lake/native-browser-cold-native"
bash tests/directruntime-20261104/native-browser/hardening-native-checks.sh
