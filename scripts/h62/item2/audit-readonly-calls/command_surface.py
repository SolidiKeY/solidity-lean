#!/usr/bin/env python3
"""Guard regex scope/header repair being promoted to kernel or owner evidence.
Use only live SDK syntax parsing, never producer imports/elaboration/execution.
Mutual and equation signatures are parser ranges; all original792 identities and
old refusals remain unchanged. No saved unbound log is accepted as execution.
Run under bounded.py, which owns the writer lock and resource bounds.
"""
import argparse
from collections import Counter
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
ROOT=Path(__file__).resolve().parents[4]
FILES=['Solidity/Backend/AbiWorld/PublicCompilerTotal.lean','Solidity/Backend/AbiWorld/PublicCompilerTotalControls.lean','Solidity/Backend/AbiWorld/P1RevertBridge.lean','Solidity/Evm/Compiler.lean']
TOTAL='Solidity.Backend.AbiWorld.PublicCompilerTotal.'
CONTROLS='Solidity.Backend.AbiWorld.PublicCompilerTotalControls.'
REQUESTED=[TOTAL+n for n in ['compile_core','compile_isSome','compile_init','compile_agrees']]+[CONTROLS+n for n in ['program_ok','program_accepted','program_kernel','program_code_nonempty','program_agrees_fresh']]
SOURCE='tests/h62/item2/audit-readonly-calls/CommandSurface.lean'
LEAN=Path('/workspace/.setup/tools/lean-4.24.0-linux/bin/lean')
PREFIX='H62_COMMAND_SURFACE '
CANONICAL_SHA='77dd8d2b6a7f771206458bbef38915f9f5269964b861a1a803d8dbd601ee862d'

def digest(raw):return hashlib.sha256(raw).hexdigest()

def require(condition,message):
    if not condition:raise ValueError(message)

def isolated_environment(parent,library):
    env={k:v for k,v in parent.items() if not k.startswith(('LEAN_','ELAN_'))}
    env.update(LEAN_PATH=str(library),LEAN_SYSROOT=str(LEAN.resolve().parent.parent),LEAN_NUM_THREADS='1')
    return env

def stage_helper(source,staged,raw,pin):
    if digest(raw)!=pin or source.read_bytes()!=raw:raise ValueError('helper source changed before staging')
    staged.write_bytes(raw)
    if digest(staged.read_bytes())!=pin:raise ValueError('staged helper substitution')

def verify_pins(pins):
    for path,pin in pins.items():
        if digest(Path(path).read_bytes())!=pin:raise ValueError('surface protected input drift')

def slice_span(raw,span):
    if not isinstance(span,dict) or set(span)!={'start','end'}:raise ValueError('bad syntax range')
    a,b=span['start'],span['end']
    if type(a)!=int or type(b)!=int or not 0<=a<=b<=len(raw):raise ValueError('invalid byte range')
    raw[:a].decode();raw[:b].decode()
    return raw[a:b].decode()

def surface(raw,result):
    if result['project_imports_loaded'] or result['commands_elaborated'] or result['kernel_binding']:raise ValueError('unexpected elaboration claim')
    if result['status']!='parsed-standard-syntax':
        return {'status':result['status'],'rows':[],'diagnostics':result['diagnostics'],'kernel_binding':False,'ownership_verified':False}
    if result['terminal']!='Lean.Parser.Command.eoi':raise ValueError('incomplete command stream')
    scopes=[];variables=[];mutual=[];rows=[]
    for row in result['records']:
        kind=row['kind'];whole=slice_span(raw,row['range'])
        if kind=='mutual-enter':mutual.append(row['range']);continue
        if kind=='mutual-exit':
            if not mutual or mutual.pop()!=row['range']:raise ValueError('unmatched mutual range')
            continue
        if kind in ['Lean.Parser.Command.namespace','Lean.Parser.Command.section']:
            names=row['identifiers']
            if len(names)>(1 if kind.endswith('.section') else 1) or (kind.endswith('.namespace') and not names):raise ValueError('scope identifier ambiguity')
            scopes.append((kind,names[0] if names else '',len(variables)));continue
        if kind=='Lean.Parser.Command.end':
            if not scopes:raise ValueError('unmatched scope end')
            previous=scopes.pop();names=row['identifiers']
            if len(names)>1 or (names and names[0]!=previous[1]):raise ValueError('mismatched scope end')
            variables=variables[:previous[2]];continue
        if kind=='Lean.Parser.Command.variable':variables.append(whole);continue
        if row.get('declaration_kind')!='Lean.Parser.Command.theorem':continue
        keyword=slice_span(raw,row['keyword_range'])
        if keyword!='theorem':raise ValueError('theorem keyword range mismatch')
        header=slice_span(raw,{'start':row['keyword_range']['start'],'end':row['signature_range']['end']})
        if row['body_kind'] not in ['Lean.Parser.Command.declValSimple','Lean.Parser.Command.declValEqns']:raise ValueError('unsupported theorem body syntax')
        name=row['name'];ns='.'.join(s[1] for s in scopes if s[0].endswith('.namespace'))
        fq=name.removeprefix('_root_.') if name.startswith('_root_.') else '.'.join(x for x in [ns,name] if x)
        rows.append({'candidate_source_name':fq,'header_span':header,'header_span_sha256':digest(header.encode()),
                     'name_span':slice_span(raw,row['name_range']),'variable_context':list(variables),
                     'body_kind':row['body_kind'],'range':row['range'],'signature_range':row['signature_range'],
                     'binding_status':'parser-surface-only-kernel-and-live-owner-unverified'})
    if mutual:raise ValueError('unclosed mutual range')
    return {'status':'parsed-surface' if not scopes else 'open-scopes-at-eof','rows':rows,'diagnostics':result['diagnostics'],
            'open_scopes':scopes,'kernel_binding':False,'ownership_verified':False}

def fixtures(marker):
    return [
      {'path':'fixture-mutual','source':'namespace N\nvariable (outer : Nat)\nmutual\ntheorem first : (n : Nat) → n = n\n | 0 => rfl\n | n+1 => rfl\ntheorem second : True := True.intro\nend\nsection Local\nvariable (inner : Nat)\ntheorem inside : inner = inner := rfl\nend Local\ntheorem after : outer = outer := rfl\nend N\n'},
      {'path':'fixture-no-execution','source':'import Lean\nrun_cmd IO.FS.writeFile '+json.dumps(str(marker))+' "executed"\ntheorem survived : True := True.intro\n'},
      {'path':'fixture-missing-import','source':'import Definitely.Missing.Project\ntheorem present : True := True.intro\n'},
      {'path':'fixture-quoted','source':'import Lean\ndef quoted := `(command| theorem forged : True := True.intro)\n/- theorem comment : False := bad -/\ndef text := "namespace FalseName"\ntheorem real : True := True.intro\n'},
      {'path':'fixture-custom','source':'macro "new_custom_command" : command => `(theorem hidden : True := True.intro)\nnew_custom_command\n'},
      {'path':'fixture-exit','source':'#exit\ntheorem skipped : True := True.intro\n'},
      {'path':'fixture-bad-end','source':'namespace A\ntheorem x : True := True.intro\nend B\n'}]

def check_fixtures(inputs,records,marker):
    by={x['path']:x for x in records};surfaces={}
    for item in inputs:
        try:surfaces[item['path']]=surface(item['source'].encode(),by[item['path']])
        except ValueError as exc:surfaces[item['path']]={'status':'scope-refused','reason':str(exc),'rows':[]}
    m=surfaces['fixture-mutual'];require(m['status']=='parsed-surface','mutual fixture failed')
    require([r['candidate_source_name'] for r in m['rows']]==['N.first','N.second','N.inside','N.after'],'mutual member loss')
    require(m['rows'][0]['body_kind'].endswith('declValEqns') and '=>' not in m['rows'][0]['header_span'],'equation body leaked into header')
    require(m['rows'][2]['variable_context']==['variable (outer : Nat)','variable (inner : Nat)'],'inner variables missing')
    require(m['rows'][3]['variable_context']==['variable (outer : Nat)'],'section variables leaked')
    require(surfaces['fixture-no-execution']['status']=='parsed-surface' and not marker.exists(),'inventoried code/import executed')
    require(surfaces['fixture-missing-import']['status']=='parsed-surface','inventoried missing import loaded')
    require([r['candidate_source_name'] for r in surfaces['fixture-quoted']['rows']]==['real'],'quoted declaration promoted')
    require(surfaces['fixture-custom']['status']=='parser-error','custom syntax silently executed')
    require(surfaces['fixture-exit']['status']=='terminal-before-eof','early exit promoted')
    require(surfaces['fixture-bad-end']['status']=='scope-refused','mismatched scope accepted')
    return surfaces

def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--head',required=True);p.add_argument('--canonical',type=Path,required=True);p.add_argument('--output',type=Path,required=True);args=p.parse_args()
    if not re.fullmatch('[0-9a-f]{40}',args.head):raise ValueError('exact Git commit required')
    out=args.output.resolve();out.mkdir(parents=True,exist_ok=False)
    canonical=args.canonical.read_bytes()
    if digest(canonical)!=CANONICAL_SHA:raise ValueError('unadmitted original ledger')
    original=json.loads(canonical);require(len(original['declarations'])==792 and len({r['source_name'] for r in original['declarations']})==792,'original792 identity drift')
    coverage=ROOT/'tests/h62/item2/audit-readonly-calls/coverage.json';coverage_pin=digest(coverage.read_bytes())
    helper_raw=(ROOT/SOURCE).read_bytes();helper_pin=digest(helper_raw)
    tools=[Path(__file__),LEAN,Path(sys.executable),ROOT/'lean-toolchain']
    pins={str(x):digest(x.read_bytes()) for x in tools};pins[str(ROOT/SOURCE)]=helper_pin;pins[str(args.canonical)]=CANONICAL_SHA
    target_files=[x for x in FILES if x.endswith('.lean')];inputs=[]
    for path in target_files:
        raw=subprocess.check_output(['git','show',args.head+':'+path],cwd=ROOT)
        saved=out/'sources'/path;saved.parent.mkdir(parents=True,exist_ok=True);saved.write_bytes(raw)
        pins[str(saved)]=digest(raw);inputs.append({'path':path,'source':raw.decode()})
    marker=out/'MUST-NOT-EXECUTE';controls=fixtures(marker);all_inputs=inputs+controls
    input_file=out/'input.jsonl';input_file.write_text(''.join(json.dumps(x,ensure_ascii=False)+'\n' for x in all_inputs));pins[str(input_file)]=digest(input_file.read_bytes())
    staged=out/'staged';staged.mkdir();library=out/'library';library.mkdir()
    tool=staged/'CommandSurface.lean';stage_helper(ROOT/SOURCE,tool,helper_raw,helper_pin);pins[str(tool)]=helper_pin
    env=isolated_environment(os.environ,library);steps=[]
    verify_pins(pins)
    sdk=subprocess.check_output([str(LEAN),'--print-prefix'],env=env,text=True).strip()
    if Path(sdk).resolve()!=LEAN.resolve().parent.parent:raise ValueError('unexpected SDK root')
    def run(tag,cmd):
        verify_pins(pins)
        log=out/(tag+'.log')
        with log.open('w') as stream:r=subprocess.run(cmd,cwd=ROOT,env=env,stdout=stream,stderr=subprocess.STDOUT)
        raw=log.read_bytes();pins[str(log)]=digest(raw);steps.append({'command':cmd,'exit':r.returncode,'log':str(log),'sha256':digest(raw)})
        if r.returncode:raise ValueError('surface subprocess failed: '+str(log))
        return raw
    common=[str(LEAN),'-j1','--tstack=131072','--root='+str(staged)]
    obj=library/'CommandSurface.olean';run('tool',common+['-o',str(obj),str(tool)]);pins[str(obj)]=digest(obj.read_bytes())
    probe=staged/'Probe.lean';probe.write_text('import CommandSurface\n#audit_command_surface '+json.dumps(str(input_file))+'\n');pins[str(probe)]=digest(probe.read_bytes())
    log=run('parser',common+[str(probe)])
    lines=[x for x in log.decode().splitlines() if x.strip()]
    if any(not x.startswith(PREFIX) for x in lines):raise ValueError('unexpected parser output')
    records=[json.loads(x[len(PREFIX):]) for x in lines]
    if [x['path'] for x in records]!=[x['path'] for x in all_inputs]:raise ValueError('parser record membership drift')
    controls_result=check_fixtures(controls,records[len(inputs):],marker)
    surfaces={item['path']:surface(item['source'].encode(),result) for item,result in zip(inputs,records[:len(inputs)],strict=True)}
    requested=[]
    for name in REQUESTED:
        rows=[dict(row,file=path) for path,result in surfaces.items() if result['status']=='parsed-surface' for row in result['rows'] if row['candidate_source_name']==name]
        if len(rows)!=1:raise ValueError('missing/duplicate requested parser candidate: '+name)
        requested.append(rows[0])
    preservation={'original_count':792,'canonical_sha256':CANONICAL_SHA,'coverage_sha256':coverage_pin,'original_statuses':dict(Counter(r['witness_status'] for r in original['declarations'])),'identities':[{'file':r['file'],'source_name':r['source_name'],'signature_sha256':r['signature_sha256'],'witness_status':r['witness_status']} for r in original['declarations']],'changed_original_rows':0}
    for name,value in [('raw-parser.json',records),('surfaces.json',surfaces),('controls.json',controls_result),('requested.json',requested),('original-preservation.json',preservation)]:
        file=out/name;file.write_text(json.dumps(value,ensure_ascii=False,indent=2)+'\n');pins[str(file)]=digest(file.read_bytes())
    verify_pins(pins)
    if subprocess.check_output([str(LEAN),'--print-prefix'],env=env,text=True).strip()!=sdk:raise ValueError('SDK root drift')
    if digest(coverage.read_bytes())!=coverage_pin or marker.exists():raise ValueError('original ledger changed or input command executed')
    receipt={'schema':1,'status':'pass','source_head':args.head,'sdk_root':sdk,'sdk_environment':'Lean/Elan overrides removed; explicit root and private library','steps':steps,'protected_sha256':pins,'files':{p:{'status':r['status'],'theorems':len(r['rows'])} for p,r in surfaces.items()},'requested_candidates':len(requested),'controls':len(controls_result),'original_obligations':792,'original_credit':0,'kernel_binding':False,'ownership_verified':False,'runtime_gate_pass':False,'boundary':'SDK syntax ranges only. Inventoried imports/commands are not loaded/elaborated/executed. Legacy refusal remains historical; no original792 or producer kernel/adequacy credit.'}
    (out/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps({k:receipt[k] for k in ['status','files','requested_candidates','controls','original_credit']}))
if __name__=='__main__':main()
