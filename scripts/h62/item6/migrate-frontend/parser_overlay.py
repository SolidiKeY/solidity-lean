#!/usr/bin/env python3
"""Unapplied typed context eliminators; isolated branch/context controls."""
import argparse
import difflib
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import token_overlay as token

PARSER='Solidity/Frontend/Checked/Parser.lean'
CASES=[
 ('contract C { function f() public { for (;;) { continue; break; } } }',True,'accepted'),
 ('contract C { function f() public { while (true) { continue; break; } } }',True,'accepted'),
 ('contract C { function f() public { do { continue; break; } while (true); } }',True,'accepted'),
 ('contract C { function f() public { unchecked { uint x; x = 1; } } }',True,'accepted'),
 ('contract C { function f() public { unchecked { for (;;) { continue; break; } } } }',True,'accepted'),
 ('contract C { function f() public { while (true) { unchecked { continue; break; } } } }',True,'accepted'),
 ('contract C { function f() public { continue; } }',False,'continue outside a loop'),
 ('contract C { function f() public { break; } }',False,'break outside a loop'),
 ('contract C { function f() public { unchecked { unchecked {} } } }',False,'nested unchecked block')]
OBSERVE='''
open Solidity.Frontend.Checked
namespace H62.MigrateFrontend.ParserControls
def observe (text : String) : Bool × String :=
  let bytes := ascii text
  match tokens bytes with
  | .error e => (false, e.msg)
  | .ok located =>
    match parseTokens bytes.length located with
    | .error e => (false, e.msg)
    | .ok (tree, layout) =>
      if decide (tree.toks layout = some (located.map Located.tok)) && tree.prec then
        (true, "accepted")
      else (false, "checker mismatch")
'''

def frozen_names(census):
    names=['Solidity.Frontend.Checked.'+r['unqualified_candidate'] for r in census['declaration_candidates'] if r['path']==PARSER and r['kind'] in ('def','abbrev','structure')]
    names+=['Solidity.Frontend.Checked.St.'+n for n in ('mk','ts','ch','eof')]
    if len(names)!=len(set(names)):raise ValueError('Duplicate source-declared parser names')
    return names

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path.cwd());ap.add_argument('--evidence',type=Path,default=Path('/workspace/h62-migrate-frontend-evidence'))
    ap.add_argument('--token-proposal',type=Path,required=True);ap.add_argument('--out',type=Path,required=True);a=ap.parse_args()
    root=a.root.resolve();e=a.evidence.resolve();out=a.out.resolve()
    lock=Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    if out.exists():raise SystemExit('Refusing to overwrite parser proposal')
    original=subprocess.check_output(['git','show',token.BASE+':'+PARSER],cwd=root)
    if (root/PARSER).read_bytes()!=original:raise SystemExit('Original Parser differs from base')
    before=original.decode();left,right=before.split('def item :',1)
    assert left.count('match k with')==5 and right.count('match k with')==1
    after=before
    replacements=[
      ('      match k with\n      | ⟨l, uc⟩ => do return Syn.forStmt (l := l) i c u (← stmt n ⟨true, uc⟩)',
       '      SCtx.casesOn (motive := fun k => P (Syn (.stmt k))) k fun l uc => do\n        return Syn.forStmt (l := l) i c u (← stmt n ⟨true, uc⟩)'),
      ('      match k with\n      | ⟨l, uc⟩ => do return Syn.whileStmt (l := l) c (← stmt n ⟨true, uc⟩)',
       '      SCtx.casesOn (motive := fun k => P (Syn (.stmt k))) k fun l uc => do\n        return Syn.whileStmt (l := l) c (← stmt n ⟨true, uc⟩)'),
      ('      match k with\n      | ⟨l, uc⟩ => do\n        let b ← stmt n ⟨true, uc⟩',
       '      SCtx.casesOn (motive := fun k => P (Syn (.stmt k))) k fun l uc => do\n        let b ← stmt n ⟨true, uc⟩'),
      ('      match k with\n      | ⟨true, _⟩ => do advance; expectP .semi; return .continueStmt\n      | ⟨false, _⟩ => P.fail "continue outside a loop"',
       '      SCtx.casesOn (motive := fun k => P (Syn (.stmt k))) k fun l uc =>\n        Bool.casesOn (motive := fun l => P (Syn (.stmt ⟨l, uc⟩))) l\n          (P.fail "continue outside a loop")\n          (do advance; expectP .semi; return .continueStmt)'),
      ('      match k with\n      | ⟨true, _⟩ => do advance; expectP .semi; return .breakStmt\n      | ⟨false, _⟩ => P.fail "break outside a loop"',
       '      SCtx.casesOn (motive := fun k => P (Syn (.stmt k))) k fun l uc =>\n        Bool.casesOn (motive := fun l => P (Syn (.stmt ⟨l, uc⟩))) l\n          (P.fail "break outside a loop")\n          (do advance; expectP .semi; return .breakStmt)'),
      ('      match k with\n      | ⟨l, false⟩ => do advance; return .uncheckedItem (← block n ⟨l, true⟩)\n      | ⟨_, true⟩ => P.fail "nested unchecked block"',
       '      SCtx.casesOn (motive := fun k => P (Syn (.item k))) k fun l uc =>\n        Bool.casesOn (motive := fun uc => P (Syn (.item ⟨l, uc⟩))) uc\n          (do advance; return .uncheckedItem (← block n ⟨l, true⟩))\n          (P.fail "nested unchecked block")')]
    for old,new in replacements:
        assert after.count(old)==1
        after=after.replace(old,new)

    out.mkdir(parents=True);source=out/'overlay'/PARSER;source.parent.mkdir(parents=True);source.write_text(after)
    patch=out/'parser-v435.patch';patch.write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+PARSER,tofile='b/'+PARSER)))
    runner=token.load('measure');api=token.load('api_snapshot');os.sched_setaffinity(0,{0})
    oldlean='/workspace/.setup/tools/lean-4.24.0-linux/bin/lean';newlean=str(e/'toolchains/lean-4.35.0-linux/bin/lean')
    oldbase=e/'old-clean-serial/build/lib/lean';newlib=out/'new/lib/lean';oldlib=out/'old/lib/lean'
    census_path=e/'census/census.json'
    census=json.loads(census_path.read_text())
    old_measurement=e/'old-clean-serial/measurement.json'
    oldmeta=json.loads(old_measurement.read_text())
    if oldmeta['status']!='pass' or oldmeta['census_sha256']!=token.sha(census_path):raise SystemExit('Old build/census provenance mismatch')
    old_summary=json.loads((e/'old-api/summary.json').read_text())
    if old_summary['measurement_sha256']!=token.sha(old_measurement) or old_summary['census_sha256']!=token.sha(census_path):raise SystemExit('Old API provenance mismatch')
    token_dir=a.token_proposal.resolve();token_manifest=token_dir/'proposal.json'
    tp=json.loads(token_manifest.read_text())
    if tp['base']!=token.BASE or tp['original_file']!=token.TOKEN:raise SystemExit('Wrong Token proposal')
    if token.sha(Path(tp['candidate_path']))!=tp['candidate_sha256'] or token.sha(Path(tp['patch']))!=tp['patch_sha256']:raise SystemExit('Token proposal file drift')
    if token.sha(root/token.TOKEN)!=tp['original_sha256']:raise SystemExit('Original Token drift')
    token_binary=token_dir/'dependent-smoke/lib/lean'/Path(token.TOKEN).with_suffix('.olean')
    if token.sha(token_binary)!=token.sha(token_dir/'build/lib/lean'/Path(token.TOKEN).with_suffix('.olean')):raise SystemExit('Copied Token binary drift')
    bindings={'census_path':str(census_path),'census_sha256':token.sha(census_path),'old_measurement_sha256':token.sha(old_measurement),'token_proposal_path':str(token_manifest),'token_proposal_sha256':token.sha(token_manifest),'token_candidate_sha256':tp['candidate_sha256'],'token_patch_sha256':tp['patch_sha256'],'token_artifacts':[{'path':str(p),'sha256':token.sha(p)} for p in sorted(token_binary.parent.glob('Token.olean*'))]}
    shutil.copytree(token_dir/'dependent-smoke/lib/lean',newlib)
    needed=set()
    def visit(m):
        if m in needed or m not in census['closure_imports']:return
        needed.add(m)
        for d in census['closure_imports'][m]:visit(d)
    for m in ('Solidity.Frontend.Checked.Parser','Solidity.Frontend.Checked.Lexer','Solidity.Frontend.Checked.Prec'):visit(m)
    source_pins={r['path']:r['sha256'] for r in census['closure_sources']}
    bindings['dependency_source_hashes']=[]
    for m in sorted(needed):
        source_path=m.replace('.','/')+'.lean'
        if token.sha(root/source_path)!=source_pins[source_path]:raise SystemExit('Dependency source drift '+source_path)
        bindings['dependency_source_hashes'].append({'path':source_path,'sha256':source_pins[source_path]})
    (out/'input-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
    for m in needed:
        rel=Path(m.replace('.','/'));directory=oldlib/rel.parent;directory.mkdir(parents=True,exist_ok=True)
        for p in (oldbase/rel.parent).glob(rel.name+'.*'):shutil.copy2(p,directory/p.name)
    results=[];common=['--tstack=131072','-j1','-DElab.async=false']
    def execute(label,lean,lib,path,module_root,output=None,extra_env=None):
        env=dict(os.environ,LEAN_NUM_THREADS='1',LEAN_PATH=str(lib));env.update(extra_env or {})
        cmd=[lean,*common,'--root='+str(module_root),str(path)]
        if output:
            output.parent.mkdir(parents=True,exist_ok=True);cmd+=['-o',str(output)]
        row=runner.run(cmd,root,env,out/(label+'.log'));row['label']=label;results.append(row)
        (out/'commands.json').write_text(json.dumps(results,indent=2)+'\n')
        if row['exit']!=0 or row['stop'] is not None:raise SystemExit('Parser fixture failed: '+label)
    for label,lean,lib in [('old-candidate',oldlean,oldlib),('new-candidate',newlean,newlib)]:
        execute(label,lean,lib,source,out/'overlay',lib/Path(PARSER).with_suffix('.olean'))
    for m in ('Solidity.Frontend.Checked.Prec','Solidity.Frontend.Checked.Lexer'):
        rel=m.replace('.','/')+'.lean';execute('smoke-'+m,newlean,newlib,root/rel,root,newlib/Path(rel).with_suffix('.olean'))
    fixture='import Lean\nimport Solidity.Frontend.Checked.Parser\nimport Solidity.Frontend.Checked.Lexer\nimport Solidity.Frontend.Checked.Prec\n'+OBSERVE
    for i,(text,ok,msg) in enumerate(CASES):
        fixture+=f'\ntheorem case{i:02d} : observe {json.dumps(text)} = ({str(ok).lower()}, {json.dumps(msg)}) := by decide +kernel\n#print axioms case{i:02d}\n'
    fixture+='end H62.MigrateFrontend.ParserControls\n'
    proof=out/'ParserControls.lean';proof.write_text(fixture)
    for label,lean,lib in [('old-original-controls',oldlean,oldbase),('old-candidate-controls',oldlean,oldlib),('new-candidate-controls',newlean,newlib)]:
        execute(label,lean,lib,proof,out)
    api_source=out/'ParserApi.lean';api_source.write_text('import Lean\nimport Solidity.Frontend.Checked.Parser\n'+api.TEMPLATE.replace('owner.toString.startsWith "Solidity.Frontend."','owner.toString == "Solidity.Frontend.Checked.Parser"'))
    execute('new-api',newlean,newlib,api_source,out,extra_env={'H62_API_OUTPUT':str(out/'new-api.jsonl')})
    oldrows=json.loads((e/'old-api/Solidity.Frontend.Checked.Parser.json').read_text())
    with (out/'new-api.jsonl').open() as f:newrows=[json.loads(line) for line in f]
    for row in newrows:row['axioms']=sorted(row['axioms'])
    newrows.sort(key=lambda r:(r['module'],r['name']));(out/'new-api.json').write_text(json.dumps(newrows,sort_keys=True,separators=(',',':'),ensure_ascii=False)+'\n')
    oldmap={r['name']:r for r in oldrows};newmap={r['name']:r for r in newrows}
    names=frozen_names(census)
    mismatches=token.selected_type_mismatches(names,oldmap,newmap)
    changes=[{'name':n,'old':oldmap.get(n,{}).get('axioms'),'new':newmap.get(n,{}).get('axioms')} for n in names if oldmap.get(n,{}).get('axioms')!=newmap.get(n,{}).get('axioms')]
    unknown_axioms=sorted({a for r in newrows for a in r['axioms']}-set(old_summary['axioms_used']))
    new_axiom_declarations=[r['name'] for r in newrows if r['kind']=='axiom']
    manifest={'input_bindings':bindings,'new_axioms_outside_baseline_frontend_union':unknown_axioms,'new_axiom_declarations':new_axiom_declarations,'status':'unapplied_candidate_pending_full_gate_and_axiom_review','base':token.BASE,'original_file':PARSER,'original_sha256':hashlib.sha256(original).hexdigest(),'candidate_path':str(source),'candidate_sha256':token.sha(source),'patch':str(patch),'patch_sha256':token.sha(patch),'change':'Explicit SCtx/Bool eliminators for five statement contexts and one item context; branch bodies, fuel, and error strings preserved.','frozen_declarations_checked':len(names),'frozen_declarations':names,'frozen_type_mismatches':mismatches,'axiom_changes':changes,'case_count':len(CASES),'control_variants':['old-original','old-candidate','new-candidate'],'check_boundary':'Isolated parseTokens+yield+precedence cases; full production Check/SourceCtor and affected acceptance remain blocked.','original_file_modified':False,'performance_gate':False}
    (out/'proposal.json').write_text(json.dumps(manifest,indent=2)+'\n')
    if (root/PARSER).read_bytes()!=original or mismatches:raise SystemExit('Frozen parser/source mismatch')
    print(json.dumps({k:manifest[k] for k in ('status','frozen_declarations_checked','frozen_type_mismatches','case_count','patch_sha256')}))
    raise SystemExit(2)
if __name__=='__main__':main()
