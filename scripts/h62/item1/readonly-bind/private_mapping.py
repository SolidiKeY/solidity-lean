#!/usr/bin/env python3
"""Guard private-helper deletion silently removing frozen audit obligations.

Re-elaborate exact frozen source statements against the shared current theorem.
This is a source-statement replacement check, not restoration of the original
private identities or equality of their compiler-generated matcher constants.
"""
import argparse
import copy
import hashlib
import importlib.util
import json
import os
import re
from pathlib import Path
import subprocess

ROOT=Path(__file__).resolve().parents[4]
AUDIT=ROOT/'scripts/h62/item2/audit-readonly-calls'
spec=importlib.util.spec_from_file_location('private_mapping_export',AUDIT/'export_signatures.py')
export=importlib.util.module_from_spec(spec);spec.loader.exec_module(export)
FROZEN_SHA='e07aa0fe5f1a94c292c6d9edc22eee478f45c560b1802fab5e7ac581da9a2ffb'
SIGNATURE_SHA='f2d973844eb329c5c43aae9977b94f76106276734bf66102070ecdbd0720ad3b'
NAMES=['CapturePhases','CaptureFailures','EnvironmentCredit']
PREFIX='Solidity.Lowering.Readonly.'
NEW='Solidity.H62.ReadonlyBind.Mappings.'
MODULE='PrivateBindMappings'


def select(frozen):
    if frozen.get('base')!=export.census.BASE or len(frozen.get('declarations',[]))!=792 or frozen.get('theorem_count')!=792:raise ValueError('original792 membership drift')
    keys=[(r['file'],r['source_name']) for r in frozen['declarations']]
    if len(set(keys))!=792:raise ValueError('duplicate original obligation')
    result=[]
    for name in NAMES:
        wanted=PREFIX+name+'.run_bind';rows=[r for r in frozen['declarations'] if r['source_name']==wanted]
        if len(rows)!=1:raise ValueError('missing or duplicate private helper')
        row=rows[0]
        if row['file']!='Solidity/Lowering/Readonly/'+name+'.lean' or row['visibility']!='private':raise ValueError('private source identity drift')
        if row['signature_sha256']!=SIGNATURE_SHA or hashlib.sha256(row['signature'].encode()).hexdigest()!=SIGNATURE_SHA:raise ValueError('frozen statement drift')
        context=['variable {E : Env}'] if name=='EnvironmentCredit' else ['variable {E : Env} {Γ : RCtx} {dn : DeclName} {ps rs : List STy}']
        if row['variable_context']!=context:raise ValueError('frozen variable context drift')
        result.append(copy.deepcopy(row))
    return result


def generate(rows):
    lines=['import Solidity.Source.Hoare','import Solidity.Source.SemanticsExamples','',
           '/-! Guard deleted private bind statements being confused with restored private IDs.','Exact frozen source propositions are re-proved with the shared law.','The concrete joint tuple establishes parameter-domain satisfiability only;','it is not a capture-phase, compiler-success or Source adequacy witness. -/','']
    for row in rows:
        name=row['source_name'].split('.')[-2]
        lines+=['namespace '+NEW+name,'open Solidity.Source','open EM',*row['variable_context'],
                row['signature'].replace('private theorem run_bind','theorem statement',1)+' := by',
                '  exact Solidity.Source.Hoare.run_bind m k x','end '+NEW+name,'']
    lines+=['namespace '+NEW.removesuffix('.'),'open Solidity.Source Solidity.Source.SemanticsExamples',
            'theorem joint_parameters :',
            '    ∃ (m : EM E0 [] Nat) (k : Nat → EM E0 [] Nat) (x : EMState E0 []),',
            '      m.run x = (.ok 0, x) ∧ (k 0).run x = (.ok 1, x) :=',
            '  ⟨pure 0, (fun n => pure (n+1)), (L0 E0, s0), rfl, rfl⟩',
            'end '+NEW.removesuffix('.'),'']
    return '\n'.join(lines)


def inventory(rows):
    result=[]
    for row in rows:
        r=copy.deepcopy(row);r.update(source_name=NEW+row['source_name'].split('.')[-2]+'.statement',file=MODULE+'.lean',visibility='public');result.append(r)
    result += [{'source_name':'Solidity.Source.Hoare.run_bind','file':'Solidity/Source/Hoare.lean','visibility':'public','signature_sha256':'current-shared-statement','owner':'current shared helper'},
               {'source_name':NEW+'joint_parameters','file':MODULE+'.lean','visibility':'public','signature_sha256':'joint-parameter-domain-only','owner':'audit-readonly-calls'}]
    return {'modules':[{'file':MODULE+'.lean'},{'file':'Solidity/Source/Hoare.lean'}],'declarations':result,'theorem_count':5}


def query(rows):
    data=inventory(rows)
    imports=''.join('import '+row['file'][:-5].replace('/','.')+'\n' for row in rows)
    checks=['','open Lean Elab Command']
    for row in rows:
        module=row['file'][:-5].replace('/','.')
        checks+=['run_cmd do',f'  let moduleName := `{module}',f'  let oldName := mkPrivateNameCore moduleName `{row["source_name"]}',
                 '  let env ← getEnv','  unless env.header.moduleNames.contains moduleName do throwError "private source module not imported"',
                 f'  logInfo m!"PRIVATE_BIND_STATUS {row["source_name"]} {{env.contains oldName}}"']
    prints=''.join('#print axioms '+row['source_name']+'\n' for row in data['declarations'])
    return imports+export.generate(data)+'\n'.join(checks)+'\n'+prints



def check_axioms(log,rows):
    expected={r['source_name'] for r in inventory(rows)['declarations']};found={}
    for m in re.finditer(r"(?m)^'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)",log):
        name=m[1]
        if name not in expected or name in found:raise ValueError('unknown or duplicate axiom record')
        actual=[] if m[2] is None else [s.strip() for s in m[2].split(',') if s.strip()]
        if not set(actual)<={'propext','Classical.choice','Quot.sound'}:raise ValueError('unexpected theorem axiom')
        found[name]=actual
    if found.keys()!=expected:raise ValueError('incomplete axiom records')
    return found


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--frozen',type=Path,required=True);p.add_argument('--output',type=Path,required=True);p.add_argument('--check',action='store_true');args=p.parse_args()
    raw=args.frozen.read_bytes()
    if hashlib.sha256(raw).hexdigest()!=FROZEN_SHA:p.error('wrong original artifact bytes')
    frozen=json.loads(raw);rows=select(frozen);source=generate(rows);probe=query(rows)
    if not args.check:
        args.output.mkdir(mode=0o700,parents=True,exist_ok=False)
        (args.output/(MODULE+'.lean')).write_text(source)
        (args.output/'Probe.lean').write_text(probe)
        (args.output/'manifest.json').write_text(json.dumps({'base':export.census.BASE,'original_artifact_sha256':FROZEN_SHA,'original_count':792,'original_rows':rows,'new_inventory':inventory(rows),'source_sha256':hashlib.sha256(source.encode()).hexdigest(),'probe_sha256':hashlib.sha256(probe.encode()).hexdigest(),'boundary':__doc__},indent=2)+'\n')
        print('PRIVATE_MAPPING_PREPARED original=792 selected=3');return
    if (args.output/(MODULE+'.lean')).read_text()!=source or (args.output/'Probe.lean').read_text()!=probe:raise ValueError('generated statement/query drift')
    manifest=json.loads((args.output/'manifest.json').read_text())
    if manifest!={'base':export.census.BASE,'original_artifact_sha256':FROZEN_SHA,'original_count':792,'original_rows':rows,'new_inventory':inventory(rows),'source_sha256':hashlib.sha256(source.encode()).hexdigest(),'probe_sha256':hashlib.sha256(probe.encode()).hexdigest(),'boundary':__doc__}:raise ValueError('manifest drift')
    compiler='/workspace/.setup/tools/lean-4.24.0-linux/bin/lean';library=args.output/'library';library.mkdir(mode=0o700,exist_ok=False)
    steps=[]
    tools={'compiler_sha256':hashlib.sha256(Path(compiler).read_bytes()).hexdigest(),'compiler_version':subprocess.check_output([compiler,'--version'],text=True).strip(),'toolchain_sha256':hashlib.sha256((ROOT/'lean-toolchain').read_bytes()).hexdigest()}
    def execute(tag,command,env):
        with (args.output/(tag+'.log')).open('w') as log:done=subprocess.run(command,cwd=ROOT,env=env,stdout=log,stderr=subprocess.STDOUT)
        raw=(args.output/(tag+'.log')).read_bytes()
        steps.append({'command':command,'exit':done.returncode,'log_sha256':hashlib.sha256(raw).hexdigest(),'log':str(args.output/(tag+'.log'))})
        if done.returncode:raise SystemExit('PRIVATE_MAPPING_CHECK_FAIL '+tag)
        return raw.decode()
    execute('statements',[compiler,'-j1','--tstack=131072','--root='+str(args.output),'-o',str(library/(MODULE+'.olean')),str(args.output/(MODULE+'.lean'))],os.environ.copy())
    helper_hash=hashlib.sha256((library/(MODULE+'.olean')).read_bytes()).hexdigest()
    env=dict(os.environ,LEAN_PATH=str(library)+':'+os.environ.get('LEAN_PATH',''))
    command=[compiler,'-j1','--tstack=131072','--root='+str(args.output),str(args.output/'Probe.lean')]
    cached_log=execute('cached-probe',command,env)
    def statuses(log):
        result={}
        for row in rows:
            prefix='PRIVATE_BIND_STATUS '+row['source_name']+' '
            values=[line[len(prefix):] for line in log.splitlines() if line.startswith(prefix)]
            if len(values)!=1 or values[0] not in ('true','false'):raise ValueError('missing or ambiguous private status')
            result[row['source_name']]=values[0]=='true'
        return result
    cached=statuses(cached_log)
    # A complete package scaffold is needed: a sparse Solidity root shadows cache.
    cache=ROOT/'.lake/build/lib/lean';excluded=[r['file'][:-5] for r in rows]+['Solidity/Source/Hoare']
    for path in (cache/'Solidity').rglob('*'):
        if not path.is_file():continue
        relative=path.relative_to(cache).as_posix()
        if any(relative.startswith(name+'.') for name in excluded):continue
        dest=library/relative;dest.parent.mkdir(parents=True,exist_ok=True);dest.symlink_to(path.resolve())
    protected={};source_root=args.output/'current-sources'
    for relative in ['Solidity/Source/Hoare.lean']+[r['file'] for r in rows]:
        raw=(ROOT/relative).read_bytes();target=source_root/relative
        target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(raw);target.chmod(0o444)
        artifact=library/(relative[:-5]+'.olean');artifact.parent.mkdir(parents=True,exist_ok=True)
        execute(Path(relative).stem,[compiler,'-j1','--tstack=131072','--root='+str(source_root),'-o',str(artifact),str(target)],env)
        protected[relative]={'source_sha256':hashlib.sha256(raw).hexdigest(),'artifact_sha256':hashlib.sha256(artifact.read_bytes()).hexdigest()}
    execute('fresh-statements',[compiler,'-j1','--tstack=131072','--root='+str(args.output),'-o',str(library/(MODULE+'.olean')),str(args.output/(MODULE+'.lean'))],env)
    helper_hash=hashlib.sha256((library/(MODULE+'.olean')).read_bytes()).hexdigest()
    fresh_log=execute('fresh-probe',command,env);fresh=statuses(fresh_log)
    axioms=check_axioms(fresh_log,rows);check_axioms(cached_log,rows)
    if any(fresh.values()):raise ValueError('fresh current source retains original private helper: re-inventory')
    typed=export.collect(fresh_log,inventory(rows));export.collect(cached_log,inventory(rows))
    for relative,record in protected.items():
        if any(hashlib.sha256(path.read_bytes()).hexdigest()!=record['source_sha256'] for path in [ROOT/relative,source_root/relative]):raise ValueError('current source changed')
        if hashlib.sha256((library/(relative[:-5]+'.olean')).read_bytes()).hexdigest()!=record['artifact_sha256']:raise ValueError('current artifact changed')
    if (args.output/(MODULE+'.lean')).read_text()!=source or (args.output/'Probe.lean').read_text()!=probe or hashlib.sha256((library/(MODULE+'.olean')).read_bytes()).hexdigest()!=helper_hash:raise ValueError('statement/query/helper changed')
    for step in steps:
        if hashlib.sha256(Path(step['log']).read_bytes()).hexdigest()!=step['log_sha256']:raise ValueError('process log changed')
    if json.loads((args.output/'manifest.json').read_text())!=manifest:raise ValueError('manifest changed during check')
    if tools['compiler_sha256']!=hashlib.sha256(Path(compiler).read_bytes()).hexdigest() or tools['toolchain_sha256']!=hashlib.sha256((ROOT/'lean-toolchain').read_bytes()).hexdigest():raise ValueError('compiler or toolchain changed')
    (args.output/'types.json').write_text(json.dumps(typed,indent=2)+'\n')
    (args.output/'checked.json').write_text(json.dumps({'status':'pass','steps':steps,'source_sha256':hashlib.sha256(source.encode()).hexdigest(),'probe_sha256':hashlib.sha256(probe.encode()).hexdigest(),'helper_sha256':helper_hash,'tools':tools,'axiom_sets':axioms,'current_sources':protected,'dependency_boundary':'Only four named project files freshly compiled; remaining project/SDK dependencies cached and not independently source-bound here. Outer bounded runner supplies serial lease/resource enforcement.','cached_private_presence':cached,'fresh_private_presence':fresh,'cache_source_binding':'refused where cached and fresh presence differ','checked_statement_replacements':3,'original_private_identities':'absent in controlled current-source view; not restored','original_obligations':792,'boundary':__doc__},indent=2)+'\n')
    print('PRIVATE_STATEMENT_REPLACEMENTS_PASS count=3 original_private_ids=absent_in_fresh_view cached_view_reported_separately')


if __name__=='__main__':main()
