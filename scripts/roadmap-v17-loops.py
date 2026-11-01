#!/usr/bin/env python3
"""Authenticated direct/scoped loop observations; no profile/release closure."""
import hashlib,importlib.util,json,subprocess
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]
PUBLICATION='5f6a75b6038371a3917dbe08b660d5f2d1207c58'
CONFIG={'direct':('Solidity.Evm.MemoryLoopSourceExamples','Solidity.Evm.Memory.LoopSourceExamples','Loops','memoryLoops','Solidity.Evm.MemoryLoopCompile'), 'scoped':('Solidity.Evm.MemoryLoopScopeSourceExamples','Solidity.Evm.Memory.LoopScopeSourceExamples','LoopScopes','memoryLoopScopes','Solidity.Evm.MemoryLoopScope')}
THEOREMS=['arrays_simulate','arraysIR_simulate','records_simulate','recordsIR_simulate']
PRIVATE=['arrays','arraysIR','records','recordsIR','compiledArrays','compiledArraysIR','compiledRecords','compiledRecordsIR']
def creation():
 s=importlib.util.spec_from_file_location('loop_creation',ROOT/'scripts/roadmap-v17-creation-try.py');c=importlib.util.module_from_spec(s);s.loader.exec_module(c);return c

def public_requests(family):
 mod,ns,rel,selector,relation_mod=CONFIG[family]
 return [(mod,ns+'.'+n,'theorem') for n in THEOREMS]+[('Solidity.Evm.Compiler','Solidity.Evm.Compiler.Compilation.'+selector+'_input','theorem'),(relation_mod,'Solidity.Evm.Memory.'+rel+'.Room','definition'),(relation_mod,'Solidity.Evm.Memory.'+rel+'.Cost','inductive'),('Solidity.Evm.Compiler','Solidity.Evm.Compiler.compile','definition')]

def query_bytes(family):
 mod,ns,rel,selector,_=CONFIG[family];m=creation().load_memory()
 s=(ROOT/'scripts/roadmap-v17-kernel-query.lean').read_text().replace('-- V17_PROJECT_IMPORTS','import '+mod)
 s+='''
namespace Solidity.Roadmap.V17.LoopObservation
open Lean Lean.Meta Lean.Elab Solidity Solidity.Evm Solidity.Evm.Memory
'''
 s+='def privateName (suffix : String) : TermElabM Lean.Name := do\n  let env ← getEnv\n  let names := env.constants.toList.filterMap fun (n, _) => do\n    let idx ← env.getModuleIdxFor? n\n    if env.header.moduleNames[idx.toNat]! == '+m.name_term(mod)+' && n.toString.endsWith ("." ++ suffix) then some n else none\n  match names with\n  | [n] => return n\n  | _ => throwError "expected one published private constant: {suffix}"\n'
 s+='''elab "v17Loop% " suffix:str : term => do
  mkConstWithFreshMVarLevels (← privateName suffix.getString)
def stackWords (out : Solidity.Evm.Out) : Option (List Nat) := match out with
  | .ok m _ => m.stack.mapM fun w => match w with | .val n => some n.val | _ => none
  | _ => none
'''
 s+='def sourceTop {K : Contract} {Δ : Ctx} (i : Idx Δ (.val .uint)) (out : TRes (Solidity.Out K [] Δ)) : Option Int := (v17Loop% "sourceTop") i out\ndef targetCells (cells : List Nat) (out : Solidity.Evm.Out) : Option (List Nat) := (v17Loop% "targetCells") cells out\n'
 for suffix in ['C','irC','machine']+PRIVATE+['checkedArrays','checkedArraysIR','checkedRecords','checkedRecordsIR']:
  s+='private abbrev '+suffix+' := v17Loop% '+json.dumps(suffix)+'\n'
 rows=[]
 for i,name in enumerate(['arrays','arraysIR','records','recordsIR']):
  ir=name.endswith('IR');arr=name.startswith('arrays');cap=name[0].upper()+name[1:];cells=[0,1,2,3,4,128,129,130,63] if arr else [0,1,2,3,128,63]
  contract='irC' if ir else 'C'
  row='do\n  let program := '+name+'\n  let result := compiled'+cap+'\n  let cert := checked'+cap+'.cert\n  let initial := State.init '+contract+'\n  let out := run result.code machine\n  let cells : List Nat := '+str(cells)+'\n  pure (Json.mkObj ['
  order=contract+'.evalOrder'
  fields=[('name',json.dumps(name)),('viaIR',order+'.binaryLeftToRight && '+order+'.modularLeftToRight && '+order+'.modifierFrames'),('evalOrder','['+order+'.binaryLeftToRight, '+order+'.modularLeftToRight, '+order+'.modifierFrames]'),('source','sourceTop .here (program.run initial)'),('cells','cells'),('target','targetCells cells out'),('stack','stackWords out'),('emptyCodeTarget','targetCells cells (run [] machine)'),('intrinsicCode','reprStr result.code'),('isDirect','result.isMemoryLoops'),('isScoped','result.isMemoryLoopScopes'),('need','cert.need'),('frameFits','decide (1 + cert.need ≤ 64)'),('zeroFrameFits','decide (1 + cert.need ≤ 0)'),('prefixBudget',rel+'.prefixBudget cert initial')]
  row+=', '.join('('+json.dumps(k)+', toJson ('+v+'))' for k,v in fields)+'])';rows.append(row)
  s+='def observation'+str(i)+' : Json := Id.run <| '+row+'\n'
 s+='#eval IO.println ("V17_LOOP_BEGIN\\n" ++ (Json.mkObj [("schema", toJson (1 : Nat)), ("family", toJson '+json.dumps(family)+'), ("base", toJson (1 : Nat)), ("frame", toJson (64 : Nat)), ("cases", toJson [observation0,observation1,observation2,observation3]), ("semanticPremisesDischarged",toJson false),("releaseClosed",toJson false)]).compress ++ "\\nV17_LOOP_END")\nend Solidity.Roadmap.V17.LoopObservation\n'
 names=', '.join('('+m.name_term(n)+','+m.name_term(mod)+','+json.dumps(kind)+')' for mod,n,kind in public_requests(family))
 s+='run_cmd do\n  let result ← Lean.Elab.Command.liftTermElabM do\n    let mut requests := #['+names+']\n'
 for suffix in PRIVATE:s+='    requests := requests.push (← Solidity.Roadmap.V17.LoopObservation.privateName '+json.dumps(suffix)+', '+m.name_term(mod)+', "definition")\n'
 s+='    Solidity.Roadmap.V17.KernelQuery.extract requests\n  Lean.Elab.Command.liftIO (IO.println ("V17_LOOP_KERNEL_BEGIN\\n" ++ result.compress ++ "\\nV17_LOOP_KERNEL_END"))\n'
 s+=''.join('#print axioms '+n+'\n' for _,n,kind in public_requests(family) if kind=='theorem')
 return s.encode()

def publication_identity(family):
 mod,_,_,_,_=CONFIG[family];paths=[mod.replace('.','/')+'.lean','Solidity/Evm/Compiler.lean','Solidity/Evm/MemoryLoopCompile.lean','Solidity/Evm/MemoryLoopScope.lean','Solidity/Evm/MemoryLoopScopeCompile.lean','Solidity/Evm/MemoryLoopScopeSound.lean']
 files={}
 for name in paths:
  actual=(ROOT/name).read_bytes();pub=subprocess.check_output(['git','show',PUBLICATION+':'+name],cwd=ROOT,timeout=30)
  if actual!=pub:raise ValueError('changed published producer: '+name)
  files[name]=hashlib.sha256(actual).hexdigest()
 return {'publication':PUBLICATION,'family':family,'sourceFiles':files,'relation':'Solidity.Evm.Memory.'+CONFIG[family][2],'finiteAllocationCostUsed':False,'externalSolcEvmRun':False}

def observation(raw,family):
 v=creation().load_memory().frame(raw,'V17_LOOP_BEGIN','V17_LOOP_END')
 if set(v)!={'schema','family','base','frame','cases','semanticPremisesDischarged','releaseClosed'} or type(v['schema']) is not int or v['schema']!=1 or v['family']!=family or type(v['base']) is not int or v['base']!=1 or type(v['frame']) is not int or v['frame']!=64 or v['semanticPremisesDischarged'] is not False or v['releaseClosed'] is not False:raise ValueError('invalid/promoted loop observation')
 if len(v['cases'])!=4:raise ValueError('missing cases')
 for row,name in zip(v['cases'],['arrays','arraysIR','records','recordsIR']):
  arr=name.startswith('arrays');ir=name.endswith('IR');cells=[0,1,2,3,4,128,129,130,63] if arr else [0,1,2,3,128,63]
  target=[131,128,128,2,4,2,3,4,99] if arr else ([130,0,5,128,3,99] if ir else [130,128,128,128,3,99])
  expected={'name':name,'viaIR':ir,'evalOrder':[ir,ir,ir],'source':4 if arr else 3,'cells':cells,'target':target,'stack':[77],'isDirect':family=='direct','isScoped':family=='scoped','frameFits':True,'zeroFrameFits':False,'prefixBudget':3 if arr else 2}
  if set(row)!=set(expected)|{'need','emptyCodeTarget','intrinsicCode'}:raise ValueError('missing/extra ordered observation')
  if any(not creation().equal(row[k],val) for k,val in expected.items()):raise ValueError('changed ordered source/target/alias/allocator/stack/frame observation')
  if type(row['need']) is not int or not 0<=row['need']<64 or not isinstance(row['intrinsicCode'],str) or not row['intrinsicCode'] or row['emptyCodeTarget']==row['target']:raise ValueError('missing need/code/negative control')
 return v

def metadata(raw,family):
 c=creation();m=c.load_memory();k=m.load_kernel();meta=m.frame(raw,'V17_LOOP_KERNEL_BEGIN','V17_LOOP_KERNEL_END');mod=CONFIG[family][0];requests=public_requests(family)
 if set(meta)!={'schema','rows','imports','releaseClosed'} or type(meta['schema']) is not int or meta['schema']!=1 or meta['releaseClosed'] is not False or len(meta['rows'])!=16:raise ValueError('missing complete metadata')
 fields={'name','nameAst','module','kind','unsafe','partial','levels','type','value','typeDisplaySupplemental','typeDependencies','valueDependencies','axioms','binderCount','propositionBinders','semanticPremisesDischarged'}
 for i,row in enumerate(meta['rows']):
  if set(row)!=fields:raise ValueError('missing/extra metadata fields')
  if i<8:
   module,name,kind=requests[i]
   if (row['name'],row['module'],row['kind'])!=(name,module,kind) or row['nameAst']!=k.name_ast(name):raise ValueError('wrong public declaration')
  else:
   suffix=PRIVATE[i-8]
   if row['module']!=mod or row['kind']!='definition' or not row['name'].startswith('_private.'+mod+'.') or not row['name'].endswith('.'+suffix):raise ValueError('wrong private declaration')
  if row['unsafe'] is not False or row['partial'] is not False or row['semanticPremisesDischarged'] is not False:raise ValueError('unsafe/promoted declaration')
  m.check_value_evidence(row,k)
  if type(row['binderCount']) is not int or row['binderCount']<0 or row['propositionBinders']!=sorted(set(row['propositionBinders'])) or any(type(n) is not int or not 0<=n<row['binderCount'] for n in row['propositionBinders']):raise ValueError('bad hypothesis accounting')
  if row['axioms']!=sorted(set(row['axioms'])) or not set(row['axioms'])<={'propext','Classical.choice','Quot.sound'}:raise ValueError('unapproved axioms')
 c.axiom_prints(raw,{r['name']:r['axioms'] for r in meta['rows'] if r['kind']=='theorem'},marker='V17_LOOP_KERNEL_END\n')
 return meta

def verify(record,directory,current,family,producer,producer_directory,previous=None):
 m=creation().load_memory();k=m.load_kernel();raw=m.verify_stage(k,record,directory,current,producer,producer_directory,previous,'warm-loop-'+family+'-producer','warm-loop-'+family)
 obs=observation(raw,family);meta=metadata(raw,family);m.verify_imports(k,meta,record,current,producer,CONFIG[family][0])
 return {'metadata':meta,'observation':obs,'sourceSnapshot':current,'profile':publication_identity(family),'installedInputs':record['installedBefore'],'metadataCompleteForRequested16':True,'semanticPremisesDischarged':False,'releaseClosed':False,'boundary':'Actual warm checked compiler/kernel component and source-order observations only; Room/Cost preserved, no finite-cost substitution or external solc/EVM/gas claim.'}

if __name__=='__main__':
 import argparse,fcntl
 from types import SimpleNamespace
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--family',choices=CONFIG,required=True)
 for flag in ['report','producer','out','replay-out']:p.add_argument('--'+flag,type=Path,required=True)
 a=p.parse_args()
 try:
  m=creation().load_memory();k=m.load_kernel()
  with open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a+') as lock:
   fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);r=k.e.load(a.report);prod=k.e.load(a.producer);first=verify(r,a.report.parent,k.e.snapshot(ROOT),a.family,prod,a.producer.parent)
   if k.p.collect(SimpleNamespace(gate='warm-loop-'+a.family,out=a.replay_out))!=0:raise ValueError('live replay failed')
   second=verify(k.e.load(a.replay_out/'provenance.json'),a.replay_out,k.e.snapshot(ROOT),a.family,prod,a.producer.parent,previous=r);m.exact_replay(first,second)
   a.out.write_text(json.dumps({'verified':first,'replay':second,'exactObservationReplay':True,'semanticPremisesDischarged':False,'releaseClosed':False},indent=2)+'\n');print(json.dumps({'family':a.family,'declarations':16,'exactObservationReplay':True,'releaseClosed':False}))
 except (ValueError,KeyError,TypeError,OSError) as e:print(json.dumps({'error':str(e),'releaseClosed':False}));raise SystemExit(2)
