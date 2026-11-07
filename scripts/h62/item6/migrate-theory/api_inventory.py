#!/usr/bin/env python3
"""Generate checked-environment introspection and extract versioned API pins.
Bulk declaration/type/axiom output stays off git. This is not semantic equivalence.
"""
import argparse, hashlib, json, pathlib
from census import ROOT, OWNED, census
MODULES=sorted(p[:-5].replace('/','.') for p in OWNED)
FIXTURE=ROOT/'tests/h62/item6/migrate-theory/ApiInventory.lean'
BODY=r'''
/-! Read-only introspection of imported Theory declarations and their axiom
closures. This adds no production declarations or trust assumptions. -/
open Lean Elab Command

private def exportTheoryModule (mod : Name) : CommandElabM Unit := do
  let env : Environment ← getEnv
  let some target := env.getModuleIdx? mod | throwError "missing module {mod}"
  let entries : List (Name × ConstantInfo) := env.constants.toList.filter
    (fun entry => env.getModuleIdxFor? entry.1 == some target)
  liftIO <| IO.println ("H62_API_MODULE " ++ (Json.mkObj
    [("module", toJson mod.toString), ("count", toJson entries.length)]).compress)
  for (name, info) in entries do
    let axioms : Array Name ← Lean.collectAxioms name
    let kind : String := match info with
      | .axiomInfo _ => "axiom"
      | .defnInfo _ => "definition"
      | .thmInfo _ => "theorem"
      | .opaqueInfo _ => "opaque"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient"
    let row : Json := Json.mkObj [("module", toJson mod.toString),
      ("name", toJson name.toString), ("kind", toJson kind),
      ("level_params", toJson (info.levelParams.map (fun n => n.toString))),
      ("raw_type_expr", toJson (reprStr info.type)),
      ("axioms", toJson (axioms.map (fun n => n.toString)))]
    liftIO <| IO.println ("H62_API_JSON " ++ row.compress)
'''
def generated():
    return 'import Lean\n'+''.join('import '+m+'\n' for m in MODULES)+BODY+''.join('\nrun_cmd exportTheoryModule `'+m+'\n' for m in MODULES)
def extract(log):
    headers=[]; rows=[]
    for line in log.read_text().splitlines():
        if line.startswith('H62_API_MODULE '):headers.append(json.loads(line[len('H62_API_MODULE '):]))
        if line.startswith('H62_API_JSON '):rows.append(json.loads(line[len('H62_API_JSON '):]))
    assert sorted(x['module'] for x in headers)==MODULES, 'missing or duplicated module header'
    assert len({x['name'] for x in rows})==len(rows), 'duplicate declaration'
    for header in headers: assert sum(x['module']==header['module'] for x in rows)==header['count']
    for row in rows:
        row['axioms']=sorted(row['axioms'])
        signature={k:row[k] for k in ['module','name','kind','level_params','raw_type_expr']}
        row['interface_sha256']=hashlib.sha256(json.dumps(signature,sort_keys=True,separators=(',',':')).encode()).hexdigest()
    c=census()
    return {'base':c['base'],'modules':sorted(headers,key=lambda x:x['module']),
      'declarations':sorted(rows,key=lambda x:(x['module'],x['name'])),
      'declaration_count':len(rows),'axiom_union':sorted({a for x in rows for a in x['axioms']}),
      'source_pins':{x['path']:x['sha256'] for x in c['files']},
      'boundary':'Versioned Lean.Expr repr hashes, includes generated/private declarations; not a cross-version semantic-equivalence proof.'}
if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--write-fixture',action='store_true');p.add_argument('--check-fixture',action='store_true');p.add_argument('--extract-log',type=pathlib.Path);p.add_argument('--output',type=pathlib.Path);a=p.parse_args()
    if a.write_fixture:FIXTURE.write_text(generated())
    if a.check_fixture:assert FIXTURE.read_text()==generated();print('API_FIXTURE_REPRODUCTION_PASS')
    if a.extract_log:
        if not a.output:p.error('--extract-log requires --output')
        result=extract(a.extract_log);a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n')
        print('API_DECLARATIONS',result['declaration_count'],'AXIOMS',result['axiom_union'])
