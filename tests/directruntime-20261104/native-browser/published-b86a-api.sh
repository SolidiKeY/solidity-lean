#!/usr/bin/env bash
set -euo pipefail
[[ ${NATIVE_BROWSER_BOUNDED_GATE:-} == 1 ]]
source /workspace/.setup/activate.sh
export LEAN_NUM_THREADS=1 LAKE_CACHE_DIR= PYTHONDONTWRITEBYTECODE=1
export PATH="$PWD/.lake/native-browser-prefix/bin:/opt/codex/runtimes/codex-primary-runtime/dependencies/node/bin:$PATH"
[[ ! -e docs/benchmarks/directruntime-2026-11-04/published-b86a/composed-admission.json ]]
lake build Solidity.Frontend.ExecutableAst.Shared.Compose
python3 - <<'PREPARE'
from pathlib import Path
p=Path('.lake/native-browser-b86a-admission.lean');assert not p.exists()
p.write_text(r"""import Solidity.Frontend.ExecutableAst.Shared.Compose
open Lean Solidity
open Solidity.Frontend.ExecutableAst
#check Shared.executableExpression
#print axioms Shared.executableExpression
#check Shared.executableStatements
#print axioms Shared.executableStatements
#check Shared.executableReader
#print axioms Shared.executableReader
private def decode {α : Type} (x : Except String α) : IO α :=
  match x with
  | .ok value => pure value
  | .error reason => throw (IO.userError reason)
#eval show IO Unit from do
  let fixture ← decode (Json.parse (← IO.FS.readFile
    "docs/benchmarks/directruntime-2026-11-04/published-b86a/C-controls/controls-with-guard/Controls.ast.json"))
  let ast ← decode (fixture.getObjVal? "ast")
  let nodes ← decode (ast.getObjValAs? (Array Json) "nodes")
  let some contract := nodes.find? (fun j => (j.getObjValAs? String "name").toOption == some "ControlTuples")
    | throw (IO.userError "missing fixture contract")
  let members ← decode (contract.getObjValAs? (Array Json) "nodes")
  let functions := members.filter fun j =>
    (j.getObjValAs? String "nodeType").toOption == some "FunctionDefinition" &&
      [some "public", some "external"].contains ((j.getObjValAs? String "visibility").toOption)
  unless functions.size == 13 do throw (IO.userError "expected 13 public fixture functions")
  let rows := functions.map fun fn =>
    let name := ((fn.getObjValAs? String "name").toOption).getD ""
    match Shared.function Shared.executableReader fn contract.compress with
    | .ok (_, d) => Json.mkObj [("name", toJson name), ("accepted", toJson true),
        ("params", toJson d.params.length), ("returns", toJson d.rets.length),
        ("rawStatements", toJson d.body.length)]
    | .error reason => Json.mkObj [("name", toJson name), ("accepted", toJson false),
        ("reason", toJson reason)]
  let rootAccepted := match Shared.contract Shared.executableReader contract with
    | .ok _ => true
    | .error _ => false
  let report := Json.mkObj [("functions", Json.arr rows),
    ("rootStorageValidationAccepted", toJson rootAccepted),
    ("intrinsicProof", toJson false), ("runtimeVerdict", toJson false),
    ("boundary", toJson "Build-time published reader admission only. Separate function translation and root storage validation; no compiler/source adequacy or intrinsic/backend proof.")]
  IO.FS.writeFile "docs/benchmarks/directruntime-2026-11-04/published-b86a/composed-admission.json" report.pretty
  IO.println "13 composed-reader function admission observations saved; no intrinsic proof or runtime verdict implied"
""")
PREPARE
mkdir .lake/native-browser-b86a-gate-bin
cat > .lake/native-browser-b86a-gate-bin/lake <<'LAKE'
#!/usr/bin/env bash
set -euo pipefail
if [[ ${1:-} == env && ${2:-} == lean ]]; then
 shift 2
 exec /workspace/.setup/tools/lean-4.24.0-linux/bin/lake -f .lake/native-browser-serial.toml env lean -j1 "$@"
fi
exec /workspace/.setup/tools/lean-4.24.0-linux/bin/lake -f .lake/native-browser-serial.toml "$@"
LAKE
chmod +x .lake/native-browser-b86a-gate-bin/lake
export PATH="$PWD/.lake/native-browser-b86a-gate-bin:$PATH"
export GATE_LOGS="$PWD/.lake/native-browser-b86a-api-gates"
bash scripts/coord-tools/gate.sh per-file .lake/native-browser-b86a-admission.lean
cp "$GATE_LOGS/1.log" docs/benchmarks/directruntime-2026-11-04/published-b86a/producer-signatures-admission.log
python3 - <<'VERIFY'
from pathlib import Path
import hashlib,json,re,subprocess
out=Path('docs/benchmarks/directruntime-2026-11-04/published-b86a');s=(out/'producer-signatures-admission.log').read_text();assert 'sorryAx' not in s
entries=re.findall(r"'([^']+)' (?:depends on axioms: \[([^]]*)\]|does not depend on any axioms)",s);assert {name for name,_ in entries}=={'Solidity.Frontend.ExecutableAst.Shared.'+n for n in ['executableExpression','executableStatements','executableReader']},entries
for name,axioms in entries:assert {x.strip() for x in axioms.split(',') if x.strip()}<={'propext','Classical.choice','Quot.sound'},(name,axioms)
p=Path('Solidity/Frontend/ExecutableAst/Shared/Compose.lean');names=['executableExpression','executableStatements','executableReader'];d=json.loads((out/'composed-admission.json').read_text());source=out/'C-controls/controls-with-guard/Controls.sol';fixture=source.with_suffix('.ast.json');metadata=json.loads((out/'C-controls/control-inventory-with-guard.json').read_text());assert hashlib.sha256(source.read_bytes()).hexdigest()==metadata['sourceSha256'];assert hashlib.sha256(fixture.read_bytes()).hexdigest()==metadata['fixtureSha256'];assert len(d['functions'])==13 and len({r['name'] for r in d['functions']})==13
report={'head':subprocess.check_output(['git','rev-parse','HEAD'],text=True).strip(),'module':'Solidity.Frontend.ExecutableAst.Shared.Compose','sourceSha256':hashlib.sha256(p.read_bytes()).hexdigest(),'definitionAxiomTargets':names,'newTheorems':[],'newAxioms':[],'workerLeanChanges':[],'fixtureSourceSha256':metadata['sourceSha256'],'fixtureSha256':metadata['fixtureSha256'],'compilerHeader':metadata['compilerHeader'],'admissionTestInputSha256':hashlib.sha256(Path('.lake/native-browser-b86a-admission.lean').read_bytes()).hexdigest(),'boundary':'Definition dependency inventory and build-time admission observations, not semantic/proof/backend acceptance.'}
with (out/'producer-inventory.json').open('x') as f:f.write(json.dumps(report,indent=2)+'\n')
print('PASS published composition build, definition axiom inventory and13 fresh fixture admission observations')
VERIFY
