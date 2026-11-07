#!/usr/bin/env python3
"""Guard unchanged lexical headers hiding drift in already-loaded original types.

Query only exact original identities in the admitted unheld closure. Retain all
792 rows, including unloaded/private/missing/range refusals. No witness, semantic
transport, live ownership, source-definition equivalence or STOP credit follows.
"""
import argparse
import ast
from collections import Counter
import hashlib
import importlib.util
import json
import os
import re
from pathlib import Path
import subprocess
ROOT=Path(__file__).resolve().parents[4]
PARENT_SHA='de296db73898608cd3062f15a4e8a2d9c734fb17ed7cbebe425f104e596df1e8'
CANONICAL_SHA='34726cb4b643f1b1fac8e380dfe973b74018d733e4b7581edcac5b2d4b723a65'
LEAN=Path('/workspace/.setup/tools/lean-4.24.0-linux/bin/lean')
COVERAGE=ROOT/'tests/h62/item2/audit-readonly-calls/coverage.json'
EXPORT=ROOT/'scripts/h62/item2/audit-readonly-calls/export_signatures.py'

def sha(raw):return hashlib.sha256(raw).hexdigest()
def verify(pins):
    for path,pin in pins.items():
        if sha(Path(path).read_bytes())!=pin:raise ValueError('protected input drift: '+path)
def load(name,path):
    spec=importlib.util.spec_from_file_location(name,path);m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m
def pinned(path,pin):
    raw=path.read_bytes()
    if sha(raw)!=pin:raise ValueError('unadmitted parent/canonical bytes')
    return json.loads(raw)
def unique(rows):
    result={r['source_name']:r for r in rows}
    if len(result)!=len(rows):raise ValueError('duplicate source identity')
    return result

def bind_declarations(raw,rows,mask):
    text=raw.decode();clean=mask(text);lines=clean.split('\n');result=[]
    pattern=re.compile(r'[ \t]*(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma)\s+([^\s({:]+)')
    for row in rows:
        offset=sum(len(line)+1 for line in lines[:row['line']-1]);match=pattern.match(clean,offset)
        if match is None:raise ValueError('lexical declaration name not located')
        a,b=match.span(1);token=text[a:b]
        expected=row['source_name'].rsplit('.',1)[-1]
        if token.removeprefix('_root_.').rsplit('.',1)[-1]!=expected:raise ValueError('lexical source name mismatch')
        result.append(dict(row,name_byte_range={'start':len(text[:a].encode()),'end':len(text[:b].encode())},name_token=token))
    return result

def join(frozen,selected,observations,types,sources,lexical,position):
    original=unique(frozen['declarations']);wanted=unique(selected);found=unique(observations);exported=unique(types)
    if len(original)!=792 or set(found)!=set(wanted) or set(exported)!={n for n,r in found.items() if r['status']=='present'}:raise ValueError('original/observation/type membership mismatch')
    output=[]
    for old in frozen['declarations']:
        name=old['source_name'];row={'frozen':old,'current_kernel_status':'not-loaded-by-admitted-closure','original_credit_added':False,'live_ownership_verified':False,'definition_equivalence_proved':False}
        if name in wanted:
            obs=found[name];module=old['file'][:-5].replace('/','.')
            if obs['kernel_name']!=old['kernel_name'] or obs['expected_module']!=module:raise ValueError('original kernel/module substitution')
            row['current_kernel_status']=obs['status']
            if obs['status']=='present':
                current=exported[name]
                if current['kernel_name']!=old['kernel_name'] or current['module']!=module or obs['actual_module']!=module or not current['raw_type_expr'] or not current['pretty_type']:raise ValueError('export identity/type substitution')
                current_hash=sha(current['raw_type_expr'].encode());row['current_raw_type_sha256']=current_hash
                row['raw_type_matches_frozen']=current_hash==old['elaborated']['raw_type_sha256']
                row['source_binding']='missing-direct-range'
                loc=obs['selection'];decls=lexical[old['file']];matches=[r for r in decls if r['source_name']==name]
                if loc is not None:
                    raw=sources[old['file']];a=position(raw,loc['start']);b=position(raw,loc['end']);token=raw[a:b].decode()
                    if not 0<=a<b<=len(raw) or len(matches)!=1 or token!=matches[0]['name_token'] or {'start':a,'end':b}!=matches[0]['name_byte_range']:raise ValueError('direct source identity mismatch')
                    row.update(source_binding='direct-kernel-selection-and-lexical-identity',name_byte_range={'start':a,'end':b},current_signature_sha256=matches[0]['signature_sha256'],lexical_signature_matches_frozen=matches[0]['signature_sha256']==old['signature_sha256'],current_variable_context=matches[0]['variable_context'],lexical_context_matches_frozen=matches[0]['variable_context']==old['variable_context'],current_visibility=matches[0]['visibility'],lexical_visibility_matches_frozen=matches[0]['visibility']==old['visibility'],current_type=current)
            elif obs['status'] not in ['missing-original-kernel','wrong-kind','wrong-module','missing-module-index']:raise ValueError('unknown kernel refusal')
        output.append(row)
    return {'original_obligations':792,'rows':output,'loaded_selection':len(selected),'kernel_statuses':dict(Counter(r['current_kernel_status'] for r in output)),'matched_types':sum(r.get('raw_type_matches_frozen') is True for r in output),'changed_types':sum(r.get('raw_type_matches_frozen') is False for r in output),'historical_statuses':dict(Counter(r['witness_status'] for r in frozen['declarations'])),'original_credit_added':0,'runtime_gate_pass':False,'timing_stop_released':False}

OBSERVER=r'''private def observeOne (source full expectedModule : Lean.Name) (isPrivate : Bool) : CommandElabM Unit := do
  let env ← getEnv
  let actualModule := (env.getModuleIdxFor? full).map fun i => env.header.moduleNames[i.toNat]!
  let status := match env.find? full with
    | none => "missing-original-kernel"
    | some _ => if getOriginalConstKind? env full != some .thm then "wrong-kind"
      else match actualModule with
        | none => "missing-module-index"
        | some m => if m != expectedModule then "wrong-module" else "present"
  let ranges ← findDeclarationRangesCore? full
  let selection := ranges.map fun r => Json.mkObj [("start",toJson r.selectionRange.pos),("end",toJson r.selectionRange.endPos)]
  let data := Json.mkObj [("source_name",toJson source.toString),("kernel_name",toJson full.toString),
    ("expected_module",toJson expectedModule.toString),("actual_module",toJson (actualModule.map Lean.Name.toString)),
    ("status",toJson status),("selection",toJson selection)]
  logInfo m!"H62-LOADED-ORIGINAL {data.compress}"
  if status == "present" then exportOne source expectedModule isPrivate
'''

def run(parent_path,canonical_path,output):
    head=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
    parent=pinned(parent_path,PARENT_SHA);frozen=pinned(canonical_path,CANONICAL_SHA)
    protected={str(p):sha(p.read_bytes()) for scope in ['scripts/h62','tests/h62'] for p in (ROOT/scope).rglob('*.py')}
    protected.update(parent['protected_sha256']);protected[str(parent_path)]=PARENT_SHA;protected[str(canonical_path)]=CANONICAL_SHA;protected[str(COVERAGE)]=sha(COVERAGE.read_bytes())
    protected.update({s['log']:s['sha256'] for s in parent['steps']});verify(protected)
    if parent['mode']!='current' or parent['runtime_gate_pass'] or any(s['exit']!=0 for s in parent['steps']):raise ValueError('parent proof gate incomplete')
    if len(set(parent['project_order']))!=len(parent['project_order']) or set(parent['project_order'])!=set(parent['source_pins']):raise ValueError('parent closure membership mismatch')
    objects={};sources={}
    for file,pin in parent['source_pins'].items():
        raw=(ROOT/file).read_bytes()
        if sha(raw)!=pin['source_sha256']:raise ValueError('current source diverges from admitted closure')
        sources[file]=raw;obj=parent_path.parent/'library'/(file[:-5]+'.olean');protected[str(obj)]=parent['artifacts'][file]['artifact_sha256'];objects[file]=protected[str(obj)]
    obj=parent_path.parent/'library/PrimitiveTransportWitnesses.olean';protected[str(obj)]=parent['artifacts'][parent['source']]['artifact_sha256']
    protected[str(LEAN)]=sha(LEAN.read_bytes());verify(protected)
    selected=[r for r in frozen['declarations'] if r['file'] in parent['source_pins']]
    if len(selected)!=49:raise ValueError('review loaded original surface change')
    output=output.resolve();output.mkdir(parents=True,exist_ok=False)
    buffers={str(EXPORT):EXPORT.read_bytes()}
    if sha(buffers[str(EXPORT)])!=protected[str(EXPORT)]:raise ValueError('export helper buffer drift')
    tree=ast.parse(buffers[str(EXPORT)]);helper=next(ast.literal_eval(n.value) for n in tree.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='HELPER' for t in n.targets))
    query='import Lean\nimport PrimitiveTransportWitnesses\n'+helper+OBSERVER+'\n'
    for row in selected:
        module=row['file'][:-5].replace('/','.');private='true' if row['visibility']=='private' else 'false'
        full=('(mkPrivateNameCore `'+module+' `'+row['source_name']+')') if private=='true' else '`'+row['source_name']
        query+='run_cmd observeOne `'+row['source_name']+' '+full+' `'+module+' '+private+'\n'
    query+='end Solidity.H62.ReadonlyAudit.Metadata\n'
    staged=output/'staged/LoadedOriginals.lean';staged.parent.mkdir();raw=query.encode();staged.write_bytes(raw);protected[str(staged)]=sha(raw)
    driver=load('loaded_original_position_helper',ROOT/'scripts/h62/item2/audit-readonly-calls/compiler_consumer.py')
    census=load('loaded_original_lexical_helper',ROOT/'scripts/h62/item2/audit-readonly-calls/census.py')
    env={k:v for k,v in os.environ.items() if not k.startswith(('LEAN_','ELAN_'))};env.update(LEAN_PATH=str(parent_path.parent/'library'),LEAN_SYSROOT=str(LEAN.resolve().parent.parent),LEAN_NUM_THREADS='1')
    if subprocess.check_output([str(LEAN),'--print-prefix'],env=env,text=True).strip()!=parent['sdk_root']:raise ValueError('SDK prefix mismatch')
    cmd=[str(LEAN),'-j1','--tstack=131072','--root='+str(staged.parent),str(staged)];log=output/'query.log'
    with log.open('w') as stream:done=subprocess.run(cmd,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
    data=log.read_bytes();protected[str(log)]=sha(data)
    if done.returncode:raise SystemExit('LOADED_ORIGINAL_QUERY_FAIL '+str(log))
    obs=[];types=[]
    for line in data.decode().splitlines():
        if line.startswith('H62-LOADED-ORIGINAL '):obs.append(json.loads(line[len('H62-LOADED-ORIGINAL '):]))
        if line.startswith('H62-SIGNATURE '):types.append(json.loads(line[len('H62-SIGNATURE '):]))
    lexical={file:bind_declarations(buf,census.declarations_text(file,buf.decode()),census.mask) for file,buf in sources.items() if any(r['file']==file for r in selected)}
    result=join(frozen,selected,obs,types,sources,lexical,driver.byte_position)
    for file,buf in sources.items():
        path=output/'sources'/file;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(buf);protected[str(path)]=sha(buf)
    for name,value in [('observations.json',obs),('types.json',types),('census.json',result)]:
        raw=(json.dumps(value,ensure_ascii=False,indent=2)+'\n').encode();(output/name).write_bytes(raw);protected[str(output/name)]=sha(raw)
    verify(protected)
    if subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()!=head:raise ValueError('head changed during query')
    receipt={'status':'pass','source_head':head,'parent_receipt_sha256':PARENT_SHA,'canonical_sha256':CANONICAL_SHA,'command':cmd,'exit':0,'log_sha256':sha(data),'query_sha256':sha(staged.read_bytes()),'protected_sha256':protected,'selected':49,'project_objects':len(objects),'kernel_statuses':result['kernel_statuses'],'type_matches':result['matched_types'],'type_drifts':result['changed_types'],'original_credit_added':0,'kernel_metadata_only':True,'object_boundary':'Uses actual admitted fresh-source proof objects; hashes checked before/after. Standard SDK/import-loader trust; no independent loader-byte attestation.','runtime_gate_pass':False,'timing_stop_released':False}
    (output/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:v for k,v in receipt.items() if k not in ['protected_sha256','command']}))
if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--parent',type=Path,required=True);p.add_argument('--canonical',type=Path,required=True);p.add_argument('--output',type=Path,required=True);a=p.parse_args();run(a.parent,a.canonical,a.output)
