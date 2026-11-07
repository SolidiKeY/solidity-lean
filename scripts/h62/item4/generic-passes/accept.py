#!/usr/bin/env python3
"""Reproduce the complete source census; serially check additive import closure
with official v4.35.0. Reuses only this task’s isolated v4.35 output directory.
Each invocation requires a unique run identifier; old logs are never overwritten.
Stops at the first failed gate and reports it without a runtime-pass label.
"""
import hashlib, importlib.util, json, os, subprocess, sys
sys.dont_write_bytecode=True
from pathlib import Path
ROOT=Path(__file__).resolve().parents[4]; HERE=Path(__file__).parent
from runtime_paths import EVIDENCE as E, load_pin
OUT=E/'build-v4.35.0'
spec=importlib.util.spec_from_file_location('census',HERE/'census.py'); census=importlib.util.module_from_spec(spec); spec.loader.exec_module(census)

def check_lexing():
    raw='/- outer /- nested -/ theorem hidden : False := x -/\n@[irreducible] def after : Nat := 1\ntheorem equation : True\n  | => by trivial\n'
    clean=census.blank(raw); found=list(census.DECL.finditer(clean))
    assert [x[2] for x in found]==['after','equation']
    end=census.signature_end(clean,found[1].end(),len(raw))
    assert raw[found[1].start():end].strip()=='theorem equation : True'
    clean=census.blank('def x : String := "theorem fake := end" -- theorem bad\n')
    assert len(list(census.DECL.finditer(clean)))==1
    for identifier in ['somewhere','where_lemma',"where'lemma"]:
        probe='theorem test : '+identifier+' := proof'
        clean=census.blank(probe); match=census.DECL.search(clean)
        assert probe[:census.signature_end(clean,match.end(),len(probe))].strip()=='theorem test : '+identifier
    print('PASS comment/string/attribute/equation/token source-boundary regression checks')

def check_candidates():
    import re
    leaf=ROOT/'tests/h62/item4/generic-passes'
    instances=(leaf/'Instances.lean').read_text()
    correspondence=census.blank((leaf/'Correspondence.lean').read_text())
    declarations=list(census.DECL.finditer(correspondence))
    count=0
    for name in ['Addition','Subtraction','Multiplication']:
        source=(ROOT/('Solidity/Backend/Passes/Assignment'+name+'Pass.lean')).read_text()
        begin=source.index('theorem execution'); end=source.index(' := by',begin)
        expected=source[begin:end].replace('theorem execution','theorem execution_'+name.lower(),1)
        start=instances.index('theorem execution_'+name.lower())
        assert instances[start:instances.index(' := by',start)]==expected
        controls=(ROOT/('Solidity/Backend/Passes/Assignment'+name+'Controls.lean')).read_text()
        for theorem in re.findall(r'(?m)^theorem (\w+)',controls):
            original='Solidity.Backend.Passes.Assignment'+name+'Pass.Controls.'+theorem
            alias=name.lower()+'_'+theorem
            positions=[index for index,decl in enumerate(declarations) if decl[2]==alias]
            assert len(positions)==1, 'missing or duplicate alias: '+alias
            index=positions[0]
            finish=declarations[index+1].start() if index+1<len(declarations) else len(correspondence)
            body=correspondence[declarations[index].start():finish]
            body=re.split(r'(?m)^end(?:\s|$)',body,maxsplit=1)[0].strip()
            pattern=r'theorem '+re.escape(alias)+r' : type_of% '+re.escape(original)+r'\s*:=\s*'+re.escape(original)
            assert re.fullmatch(pattern,body), 'substituted type or body: '+alias
            count+=1
    assert count==36
    print('PASS 3 exact original execution source signatures and 36 original theorem aliases (lexical only)')

check_lexing()
check_candidates()
plan_only='--plan-only' in sys.argv
if plan_only: sys.argv.remove('--plan-only')
if sys.argv[1:]==['--lexical-only']: raise SystemExit(0)
if len(sys.argv)!=3 or sys.argv[1]!='--run-id' or not __import__('re').fullmatch(r'[a-zA-Z0-9-]+',sys.argv[2]):
    raise SystemExit('usage: accept.py --run-id UNIQUE-ID (or --lexical-only)')
run_id=sys.argv[2]
subprocess.run([sys.executable,str(HERE/'census.py'),'--check',str(E/'original-census.json')],cwd=ROOT,check=True)
pin=load_pin()
with (E/pin['asset']).open('rb') as source:
    assert hashlib.file_digest(source,'sha256').hexdigest()==pin['sha256']
seen=set(); order=[]
def visit(path):
    if path in seen: return
    seen.add(path)
    for name in __import__('re').findall(r'(?m)^import\s+(\S+)',census.blank((ROOT/path).read_text())):
        source=Path(name.replace('«','').replace('»','').replace('.','/')+'.lean')
        if not (ROOT/source).exists():
            official=E/'toolchain/lean-4.35.0-linux/lib/lean'/source.with_suffix('.olean')
            if official.exists() and name.split('.')[0] in {'Init','Lean','Std','Lake'}: continue
            raise SystemExit('Missing local or official import: '+name)
        visit(source)
    order.append(path)
for filename in ['Generic','Fixtures','Correspondence','Instances']:
    visit(Path('tests/h62/item4/generic-passes')/(filename+'.lean'))
(E/(run_id+'-closure.json')).write_text(json.dumps([str(x) for x in order],indent=2)+'\n')
if plan_only:
    print('PASS dependency plan: '+str(len(order))+' source files; no Lean invoked')
    raise SystemExit(0)
for index,path in enumerate(order):
    output=OUT/path.with_suffix('.olean'); output.parent.mkdir(parents=True,exist_ok=True)
    label=run_id+'-closure-'+str(index).zfill(4)+'-'+path.stem.replace('.','-')
    command=[sys.executable,str(HERE/'bounded.py'),label,'--','-j1','--tstack=131072','-o',str(output),str(path)]
    result=subprocess.run(command,cwd=ROOT)
    if result.returncode: raise SystemExit('FAIL import-closure gate '+str(path)+'; see '+str(E/(label+'.log')))
sources={str(path):hashlib.sha256((ROOT/path).read_bytes()).hexdigest() for path in order}
artifacts={str(path):hashlib.sha256(path.read_bytes()).hexdigest() for path in OUT.rglob('*') if path.is_file()}
manifest=dict(status='pass',toolchain=pin,source_sha256=sources,artifact_sha256=artifacts,
    boundary='additive import closure only; repository final gate and axiom audit separate')
(E/(run_id+'-acceptance.json')).write_text(json.dumps(manifest,indent=2)+'\n')
print('PASS full additive import closure; run repository final gate separately')
