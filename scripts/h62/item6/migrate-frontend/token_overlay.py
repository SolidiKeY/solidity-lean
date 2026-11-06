#!/usr/bin/env python3
"""Build an UNAPPLIED Token migration candidate and all-byte semantic controls.
Original files remain unchanged. This is an isolated reproduction/owner proposal,
not a directory build, root gate, permission grant, or timing acceptance.
"""
import argparse
import difflib
import fcntl
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

BASE='c6f550e281a7e5affa9a99bc2cdaed556dec00e4'
TOKEN='Solidity/Frontend/Checked/Token.lean'
OLD='def Bytes.str (b : Bytes) : String := ⟨b.map fun c => Char.ofNat c.toNat⟩'
NEW='def Bytes.str (b : Bytes) : String := String.ofList (b.map fun c => Char.ofNat c.toNat)'
PROOFS='''
open Solidity.Frontend.Checked
namespace H62.MigrateFrontend.TokenControls
theorem bytes_str_toList (b : List UInt8) :
    (Bytes.str b).toList = b.map (fun c => Char.ofNat c.toNat) := by
  PROOF_BODY

theorem high_bytes_are_codepoints : Bytes.str [195, 169] = "Ã©" := by decide +kernel
theorem high_bytes_are_not_utf8_decoded : Bytes.str [195, 169] ≠ "é" := by decide +kernel
#print axioms bytes_str_toList
#print axioms high_bytes_are_codepoints
#print axioms high_bytes_are_not_utf8_decoded
end H62.MigrateFrontend.TokenControls
'''

def sha(path):
    with path.open('rb') as f:return hashlib.file_digest(f,'sha256').hexdigest()

def load(name):
    spec=importlib.util.spec_from_file_location(name,Path(__file__).with_name(name+'.py'))
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m

def selected_type_mismatches(names,oldmap,newmap):
    def fields(row):return {k:v for k,v in row.items() if k!='axioms'}
    return [n for n in names if n not in oldmap or n not in newmap or fields(oldmap[n])!=fields(newmap[n])]

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--root',type=Path,default=Path.cwd())
    ap.add_argument('--evidence',type=Path,default=Path('/workspace/h62-migrate-frontend-evidence'))
    ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
    root=args.root.resolve();out=args.out.resolve();e=args.evidence.resolve()
    lock=Path('/tmp/solidity-lean-feature-groups-20261025/writer.lock').open('a');fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
    if out.exists():raise SystemExit('Refusing to overwrite proposal evidence')
    original=subprocess.check_output(['git','show',BASE+':'+TOKEN],cwd=root)
    if (root/TOKEN).read_bytes()!=original:raise SystemExit('Original Token differs from pinned base')
    before=original.decode();assert before.count(OLD)==1
    after=before.replace(OLD,NEW)
    out.mkdir(parents=True)
    source=out/'overlay'/TOKEN;source.parent.mkdir(parents=True);source.write_text(after)
    patch=out/'token-v435.patch'
    patch.write_text(''.join(difflib.unified_diff(before.splitlines(True),after.splitlines(True),fromfile='a/'+TOKEN,tofile='b/'+TOKEN)))
    oldmeta=json.loads((e/'old-clean-serial/measurement.json').read_text())
    newmeta=json.loads((e/'new-clean-serial/measurement.json').read_text())
    runner=load('measure');api=load('api_snapshot')
    results=[]
    def execute(label,cmd,env):
        row=runner.run(cmd,root,env,out/(label+'.log'));row['label']=label
        results.append(row);(out/'commands.json').write_text(json.dumps(results,indent=2)+'\n');return row
    def environment(lean,lib):
        return dict(os.environ,PATH=str(Path(lean).parent)+':'+os.environ['PATH'],LEAN_NUM_THREADS='1',LEAN_PATH=str(lib))
    newlean=str(Path(newmeta['results'][0]['command'][0]).with_name('lean'))
    oldlean=str(Path(oldmeta['results'][0]['command'][0]).with_name('lean'))
    newlib=e/'new-clean-serial/build/lib/lean';oldlib=e/'old-clean-serial/build/lib/lean'
    common=['--tstack=131072','-j1','-DElab.async=false']
    os.sched_setaffinity(0,{0})
    repro=execute('original-token-new', [newlean,*common,'--root='+str(root),str(root/TOKEN)], environment(newlean,newlib))
    if repro['exit']==0 or repro['stop'] is not None:raise SystemExit('Expected original Token compiler incompatibility was not reproduced')
    overlaylib=out/'build/lib/lean'
    # Lean resolves a package prefix from one artifact root; provide the exact
    # already-built new-toolchain dependencies beside the candidate module.
    shutil.copytree(newlib,overlaylib)
    dest=overlaylib/Path(TOKEN).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
    row=execute('candidate-token-new',[newlean,*common,'--root='+str(out/'overlay'),str(source),'-o',str(dest)],environment(newlean,newlib))
    if row['exit']!=0 or row['stop'] is not None:raise SystemExit('Candidate Token failed')
    for version,lean,lib,body in [('old',oldlean,oldlib,'rfl'),('new',newlean,str(overlaylib)+':'+str(newlib),'simp only [Bytes.str, String.toList_ofList]')]:
        fixture=out/(version+'-TokenControls.lean');fixture.write_text('import Lean\nimport Solidity.Frontend.Checked.Token\n'+PROOFS.replace('PROOF_BODY',body))
        row=execute(version+'-controls',[lean,*common,'--root='+str(out),str(fixture)],environment(lean,lib))
        if row['exit']!=0 or row['stop'] is not None:raise SystemExit('All-byte controls failed on '+version)
    api_source=out/'TokenApi.lean'
    api_source.write_text('import Lean\nimport Solidity.Frontend.Checked.Token\n'+api.TEMPLATE.replace('owner.toString.startsWith "Solidity.Frontend."','owner.toString == "Solidity.Frontend.Checked.Token"'))
    env=environment(newlean,str(overlaylib)+':'+str(newlib));env['H62_API_OUTPUT']=str(out/'new-api.jsonl')
    row=execute('new-api',[newlean,*common,'--root='+str(out),str(api_source)],env)
    if row['exit']!=0 or row['stop'] is not None:raise SystemExit('Token API extraction failed')
    oldrows=json.loads((e/'old-api/Solidity.Frontend.Checked.Token.json').read_text())
    with (out/'new-api.jsonl').open() as f:newrows=[json.loads(line) for line in f]
    for row in newrows:row['axioms']=sorted(row['axioms'])
    newrows.sort(key=lambda r:(r['module'],r['name']))
    (out/'new-api.json').write_text(json.dumps(newrows,sort_keys=True,separators=(',',':'),ensure_ascii=False)+'\n')
    oldmap={r['name']:r for r in oldrows};newmap={r['name']:r for r in newrows}
    explicit=['Solidity.Frontend.Checked.'+m[1] for m in re.finditer(r'^(?:abbrev|def|inductive|structure)\s+([\w.]+)',before,re.M)]
    constructors=[r['name'] for r in oldrows if r['kind']=='constructor' and not r['name'].startswith('_private.')]
    fields=[]
    current_struct=None
    for line in before.splitlines():
        if match:=re.match(r'^structure\s+([\w.]+)\s+where',line): current_struct=match[1]
        elif line and not line[0].isspace() and not line.startswith('--'): current_struct=None
        elif current_struct and (match:=re.match(r'\s+([\w]+)\s*:',line)):
            fields.append('Solidity.Frontend.Checked.'+current_struct+'.'+match[1])
    checked=sorted(set(explicit+constructors+fields))
    mismatches=selected_type_mismatches(checked,oldmap,newmap)
    axiom_changes=[{'name':n,'old':oldmap.get(n,{}).get('axioms'),'new':newmap.get(n,{}).get('axioms')} for n in checked if oldmap.get(n,{}).get('axioms')!=newmap.get(n,{}).get('axioms')]
    baseline_axioms=set(json.loads((e/'old-api/summary.json').read_text())['axioms_used'])
    unknown_axioms=sorted({a for r in newrows for a in r['axioms']}-baseline_axioms)
    new_axiom_declarations=[r['name'] for r in newrows if r['kind']=='axiom']
    manifest={'status':'unapplied_candidate_type_and_semantics_checked_axiom_review_pending','base':BASE,'producer_branch':subprocess.check_output(['git','branch','--show-current'],cwd=root,text=True).strip(),
              'original_file':TOKEN,'original_sha256':hashlib.sha256(original).hexdigest(),'candidate_path':str(source),'candidate_sha256':sha(source),
              'patch':str(patch),'patch_sha256':sha(patch),'change':{'before':OLD,'after':NEW},
              'source_declared_names':explicit,'constructors_checked':len(constructors),'field_projections_checked':fields,'frozen_declarations_checked':len(checked),'frozen_type_mismatches':mismatches,'axiom_changes':axiom_changes,
              'new_axioms_outside_baseline_frontend_union':unknown_axioms,'new_axiom_declarations':new_axiom_declarations,
              'old_environment_constants':len(oldrows),'new_environment_constants':len(newrows),
              'all_byte_semantics':'Universal bytes_str_toList on old and new, no ASCII premise. High byte pair preserves two Latin-1 codepoints and is provably not UTF8-decoded.',
              'runtime_gate':False,'clean_timing_comparison':False,'original_file_modified':False}
    (out/'proposal.json').write_text(json.dumps(manifest,indent=2)+'\n')
    if (root/TOKEN).read_bytes()!=original:raise SystemExit('Original unexpectedly modified')
    if mismatches:raise SystemExit('Frozen declared Token types differ; owner review required')
    print(json.dumps({k:manifest[k] for k in ('status','frozen_declarations_checked','frozen_type_mismatches','axiom_changes','patch_sha256')}))
    smoke_lib=out/'dependent-smoke/lib/lean'
    shutil.copytree(overlaylib,smoke_lib)
    census=json.loads((e/'census/census.json').read_text())
    pins={r['path']:r['sha256'] for r in census['closure_sources']}
    smoke=[]
    for module in ('Solidity.Frontend.Checked.Tables','Solidity.Keccak','Solidity.Frontend.Checked.Print','Solidity.Frontend.Checked.Parser','Solidity.Frontend.Checked.Prec','Solidity.Frontend.Checked.Lexer'):
        relative=module.replace('.','/')+'.lean'
        if sha(root/relative)!=pins[relative]:raise SystemExit('Dependent source drift '+relative)
        dest=smoke_lib/Path(relative).with_suffix('.olean');dest.parent.mkdir(parents=True,exist_ok=True)
        row=execute('smoke-'+module,[newlean,*common,'--root='+str(root),str(root/relative),'-o',str(dest)],environment(newlean,smoke_lib))
        row['module']=module;row['source_sha256']=pins[relative];smoke.append(row)
        (out/'dependent-smoke.json').write_text(json.dumps({'status':'isolated_candidate_smoke_not_acceptance','results':smoke},indent=2)+'\n')
        if row['exit']!=0 or row['stop'] is not None:raise SystemExit('Dependent candidate smoke failed: '+module)
    if axiom_changes or unknown_axioms or new_axiom_declarations: raise SystemExit(2)

if __name__=='__main__':main()
