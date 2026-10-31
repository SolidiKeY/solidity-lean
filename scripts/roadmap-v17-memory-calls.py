#!/usr/bin/env python3
"""Published memory-call consumer. Warm checked inputs, never fresh whole closure."""
import hashlib
import importlib.util
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
PUBLICATION='91e94ab57305ca055127934fd9e68fe9ea5e6be3'
BODY=ROOT/'scripts/roadmap-v17-memory-calls-query.lean'
# Exact public requests plus private example constants discovered in the checked module.
PUBLIC_REQUESTS=[('Solidity.Evm.Compiler','Solidity.Evm.Compiler.'+name,kind) for name,kind in [
 ('Compilation.memoryCalls','constructor'),('compile','definition'),('Compilation.memoryCalls_input','theorem'),('Compilation.correct','theorem'),
 ('Compilation.requiredFrame','definition'),('Compilation.allocationCost','definition'),('Compilation.isMemoryCalls','definition'),('Compilation.usesMemory','definition')]]
PUBLIC_REQUESTS += [('Solidity.Evm.MemoryCallExamples','Solidity.Evm.Memory.CallExamples.'+name,'theorem') for name in ['mutation_input','mutation_agrees','privateFrame_refused','callerOnly_preconditions']]
PRIVATE=['mutation','compiledMutation','machine','initial']

def name_term(name):
    value='Lean.Name.anonymous'
    for part in name.split('.'): value='(Lean.Name.str '+value+' '+json.dumps(part)+')'
    return value

def query_bytes():
    source=(ROOT/'scripts/roadmap-v17-kernel-query.lean').read_text().replace('-- V17_PROJECT_IMPORTS','import Solidity.Evm.MemoryCallExamples')
    source+='\n'+BODY.read_text().split('-- V17_MEMORY_BODY\n',1)[1]
    requests=', '.join('('+name_term(n)+', '+name_term(m)+', '+json.dumps(kind)+')' for m,n,kind in PUBLIC_REQUESTS)
    source+='\nrun_cmd do\n  let result ← Lean.Elab.Command.liftTermElabM do\n    let mut requests := #['+requests+']\n'
    for suffix in PRIVATE:
        source+='    requests := requests.push (← Solidity.Roadmap.V17.MemoryCalls.privateName '+json.dumps(suffix)+', `Solidity.Evm.MemoryCallExamples, "definition")\n'
    source+='    Solidity.Roadmap.V17.KernelQuery.extract requests\n  Lean.Elab.Command.liftIO (IO.println ("V17_MEMORY_KERNEL_BEGIN\\n" ++ result.compress ++ "\\nV17_MEMORY_KERNEL_END"))\n'
    return source.encode()

def frame(raw,begin,end):
    text=raw.decode(); lines=text.splitlines()
    if lines.count(begin)!=1 or lines.count(end)!=1: raise ValueError('missing/duplicate observation frame')
    start=lines.index(begin); stop=lines.index(end)
    if stop!=start+2: raise ValueError('truncated observation frame')
    # Reuse duplicate-key rejection, never ordinary permissive json.loads.
    spec=importlib.util.spec_from_file_location('memory_evidence',ROOT/'scripts/roadmap-v17-evidence.py')
    e=importlib.util.module_from_spec(spec);spec.loader.exec_module(e)
    return e.loads(lines[start+1])

def observation(raw):
    value=frame(raw,'V17_MEMORY_CALLS_BEGIN','V17_MEMORY_CALLS_END')
    if set(value)!={'schema','isMemoryCalls','usesMemory','requiredFrame','callerFrame','allocationCost','sourceAliases','targetWords','emptyCodeWords','intrinsicCode','semanticPremisesDischarged','releaseClosed'}: raise ValueError('wrong observation fields')
    expected={'schema':1,'isMemoryCalls':True,'usesMemory':True,'requiredFrame':12,'callerFrame':4,'allocationCost':5,'sourceAliases':[2,7,88,0],'targetWords':[77,261,99,42,8,1,7,2,88,0],'semanticPremisesDischarged':False,'releaseClosed':False}
    for key,wanted in expected.items():
        if json.dumps(value[key],sort_keys=True)!=json.dumps(wanted,sort_keys=True): raise ValueError('wrong published observation: '+key)
    if not isinstance(value['intrinsicCode'],str) or not value['intrinsicCode'] or value['emptyCodeWords']==value['targetWords']:raise ValueError('missing code/nontrivial replay control')
    return value

def exact_replay(first,second):
    if json.dumps(first,sort_keys=True)!=json.dumps(second,sort_keys=True):raise ValueError('changed code/output/alias/frame/allocation observation')
    return {'exactObservationReplay':True,'semanticPremisesDischarged':False,'releaseClosed':False}


def load_kernel():
    spec=importlib.util.spec_from_file_location('memory_kernel',ROOT/'scripts/roadmap-v17-kernel.py')
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module


def publication_identity():
    import subprocess
    files={}
    for name in ('Solidity/Evm/Compiler.lean','Solidity/Evm/MemoryCalls.lean','Solidity/Evm/MemoryCallExamples.lean','tests/solc/MemoryInternalCalls.sol'):
        actual=(ROOT/name).read_bytes()
        published=subprocess.check_output(['git','show',PUBLICATION+':'+name],cwd=ROOT,timeout=30)
        if actual!=published:raise ValueError('producer differs from exact publication: '+name)
        files[name]=hashlib.sha256(actual).hexdigest()
    return {'publication':PUBLICATION,'sourceFiles':files,'syntax':'published intrinsic Prog/State/Instr',
            'externalFixture':'tests/solc/MemoryInternalCalls.sol','bytecodeOrGasAdequacy':False,
            'publishedReferenceCompiler':'0.8.34+commit.80d5c536','v17ApprovedDifferentialCompiler':'0.8.38+commit.1835d247',
            'externalReferenceRun':'not run: distinct pins, no substitution'}


def verify(record,directory,current):
    k=load_kernel();k.p.validate(record,directory,current,'warm-memory-calls-observation')
    raw=k.p.read_bound(directory,record['log'],record['logSha256']);obs=observation(raw)
    meta=frame(raw,'V17_MEMORY_KERNEL_BEGIN','V17_MEMORY_KERNEL_END')
    if set(meta)!={'schema','rows','imports','releaseClosed'} or meta['schema']!=1 or meta['releaseClosed'] is not False or len(meta['rows'])!=16:raise ValueError('missing checked metadata')
    requested={(name,module,kind) for module,name,kind in PUBLIC_REQUESTS};private_seen=set();seen=set()
    for row in meta['rows']:
        if row['name'] in seen:raise ValueError('duplicate checked declaration')
        seen.add(row['name']);identity=(row['name'],row['module'],row['kind'])
        if identity not in requested:
            suffix=next((n for n in PRIVATE if row['name'].endswith('.'+n)),None)
            if suffix is None or suffix in private_seen or row['module']!='Solidity.Evm.MemoryCallExamples' or row['kind']!='definition':raise ValueError('unrequested private declaration')
            private_seen.add(suffix)
        if row['unsafe'] is not False or row['partial'] is not False or row['semanticPremisesDischarged'] is not False:raise ValueError('unsafe or promoted metadata')
        for tree,field in [(row['type'],'typeDependencies'),(row['value'],'valueDependencies')]:
            if tree is None:raise ValueError('missing complete expression')
            k.validate_expr(tree)
            deps,_=k.ast_names(tree)
            if row[field]!=deps:raise ValueError('changed checked dependencies')
        if type(row['binderCount']) is not int or row['propositionBinders']!=sorted(set(row['propositionBinders'])) or any(type(i) is not int or i<0 or i>=row['binderCount'] for i in row['propositionBinders']):raise ValueError('invalid binders')
        if row['axioms']!=sorted(set(row['axioms'])) or not set(row['axioms'])<={'propext','Classical.choice','Quot.sound'}:raise ValueError('unapproved axiom')
    if not requested<={(r['name'],r['module'],r['kind']) for r in meta['rows']} or private_seen!=set(PRIVATE):raise ValueError('missing requested declaration')
    # Warm import paths must be exact current build artifacts, never mislabeled fresh.
    installed=k.tool_inputs(current);imports=set()
    prefix=Path(current['runtime']['lean']['path']).parent.parent
    for item in meta['imports']:
        module=item['module'];path=Path(item['olean'])
        if module in imports:raise ValueError('duplicate imported module')
        imports.add(module)
        if module.startswith('Solidity.'):
            rel='lib/lean/'+module.replace('.','/')+'.olean'
            if path.resolve()!=(ROOT/'.lake/build'/rel).resolve() or record['buildEnd']['files'].get(rel)!=hashlib.sha256(path.read_bytes()).hexdigest():raise ValueError('unbound warm import')
        else:
            if path.is_relative_to('/opt/v17-toolchain'):path=prefix/path.relative_to('/opt/v17-toolchain')
            if str(path.resolve()) not in installed:raise ValueError('unbound installed input')
    if 'Solidity.Evm.MemoryCallExamples' not in imports:raise ValueError('missing producer import')
    return {'observation':obs,'metadata':meta,'profile':publication_identity(),'sourceSnapshot':current,
            'intrinsicCodeSha256':hashlib.sha256(obs['intrinsicCode'].encode()).hexdigest(),
            'boundary':'Warm current checked producer/example inputs and replay; not fresh whole-source extraction or source-lowering/bytecode/gas proof.',
            'semanticPremisesDischarged':False,'releaseClosed':False}


if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(description=__doc__);parser.add_argument('--report',type=Path,required=True);parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args()
    try:
        k=load_kernel();r=k.e.load(args.report);current=k.e.snapshot(ROOT)
        result=verify(r,args.report.parent,current)
        args.out.write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps({'declarations':len(result['metadata']['rows']),'constructorObserved':result['observation']['isMemoryCalls'],'frame':result['observation']['requiredFrame'],'allocationCost':result['observation']['allocationCost'],'semanticPremisesDischarged':False,'releaseClosed':False}))
    except (ValueError,KeyError,TypeError,OSError) as error:
        print(json.dumps({'error':str(error),'releaseClosed':False}));raise SystemExit(2)
