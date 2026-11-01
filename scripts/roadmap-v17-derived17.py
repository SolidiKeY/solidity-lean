#!/usr/bin/env python3
"""Fixed supplemental full metadata consumer; never fresh/cold/release closure."""
import argparse,copy,fcntl,importlib.util,json,os,shlex,subprocess,uuid
from pathlib import Path
from types import SimpleNamespace
ROOT=Path(__file__).resolve().parents[1]
s=importlib.util.spec_from_file_location('derived_kernel',ROOT/'scripts/roadmap-v17-kernel.py');k=importlib.util.module_from_spec(s);s.loader.exec_module(k);p=k.p;e=k.e
PRODUCER_MANIFEST='7ababb56bd24d8febdaf7da966726ec03f1e5b616d346c87303f672079eb9b5e'
PRODUCER_ROOT=Path('/workspace/scratch/v17-warm-prerequisites')
PRODUCER_HEAD='1f3278e7ef97b68c2aa681e289e0b83b07e00396'
TAILS=['returnLeavesNestedLoops','whileCountsUp','whileBodyDeclaresLocal','whileBreakLeavesLoop','whileContinueSkipsRest','forContinueStillUpdates','forBreakKeepsCounter','doWhileRunsBodyFirst','forWritesStorageArray','invariantForCountsArrayLength']
REQUESTS=[{'name':'Solkey.TestSuite.'+tail+'.proved','module':'Solidity.TestSuite.Derived17MemoryLoop' if i==0 else 'Solidity.TestSuite.Derived17','kind':'theorem'} for i,tail in enumerate(TAILS)]
PINS=['Classical.choice','Quot.sound','propext']
ACTIVE_OUT=None
PHASE="preflight"
COLLECTOR_RETURNED=False
COLLECTOR_CODE=None
FIELDS={'name','nameAst','module','kind','unsafe','partial','levels','type','value','typeDisplaySupplemental','typeDependencies','valueDependencies','axioms','binderCount','propositionBinders','semanticPremisesDischarged'}

def fixed_request(value):
 e.require(k.canonical(value)==k.canonical({'schema':1,'declarations':REQUESTS}),'not the fixed ten checked declarations/modules/kinds');return value

def query_bytes():
 source=k.TEMPLATE.read_text().replace('-- V17_PROJECT_IMPORTS','import Solidity.TestSuite.Derived17')
 requests=', '.join('('+k.lean_name(row['name'])+', '+k.lean_name(row['module'])+', "theorem")' for row in REQUESTS)
 source+='\nrun_cmd do\n  let identities ← Lean.Elab.Command.liftTermElabM do\n    let env ← Lean.getEnv\n    let mut rows : Array Lean.Json := #[]\n    for (n, expectedModule, expectedKind) in #['+requests+'] do\n      let some ci := env.checked.get.find? n | throwError "missing checked declaration: {n}"\n      let some idx := env.getModuleIdxFor? n | throwError "not imported: {n}"\n      let module := env.header.moduleNames[idx.toNat]!\n      let kind := Solidity.Roadmap.V17.KernelQuery.kind ci\n      if ci.name != n || module != expectedModule || kind != expectedKind then throwError "wrong checked identity/module/kind: {n}"\n      rows := rows.push (Lean.Json.mkObj [("name", Lean.toJson n.toString), ("module", Lean.toJson module.toString), ("kind", Lean.toJson kind)])\n    pure (Lean.Json.arr rows)\n  Lean.Elab.Command.liftIO (IO.println ("V17_DERIVED_IDENTITIES_BEGIN\\n" ++ identities.compress ++ "\\nV17_DERIVED_IDENTITIES_END"))\n  let result ← Lean.Elab.Command.liftTermElabM (Solidity.Roadmap.V17.KernelQuery.extract #['+requests+'])\n  Lean.Elab.Command.liftIO (IO.println ("V17_KERNEL_BEGIN\\n" ++ result.compress ++ "\\nV17_KERNEL_END"))\n'
 source+='\n'+''.join('#print axioms '+row['name']+'\n' for row in REQUESTS)
 return source.encode()

def frame(raw,begin,end):
 lines=raw.decode().splitlines();e.require(lines.count(begin)==lines.count(end)==1,'missing/duplicate output frame');a=lines.index(begin);b=lines.index(end);e.require(b==a+2,'truncated output frame');return e.loads(lines[a+1])

def metadata(raw):
 e.require(frame(raw,'V17_DERIVED_IDENTITIES_BEGIN','V17_DERIVED_IDENTITIES_END')==REQUESTS,'wrong checked identity discovery')
 value=frame(raw,k.BEGIN,k.END);e.require(set(value)=={'schema','rows','imports','releaseClosed'} and type(value['schema']) is int and value['schema']==1 and value['releaseClosed'] is False,'invalid metadata frame')
 e.require(len(value['rows'])==10,'incomplete full batch')
 for row,wanted in zip(value['rows'],REQUESTS):
  e.require(set(row)==FIELDS,'missing/omitted/truncated metadata fields');e.require({key:row[key] for key in wanted}==wanted and row['nameAst']==k.name_ast(wanted['name']),'wrong name/module/kind')
  e.require(row['unsafe'] is False and row['partial'] is False and row['semanticPremisesDischarged'] is False,'unsafe/partial/promoted declaration')
  for field,deps in [('type','typeDependencies'),('value','valueDependencies')]:
   e.require(row[field] is not None,'missing full type/value');k.validate_expr(row[field]);actual,_=k.ast_names(row[field]);e.require(row[deps]==actual,'forged/missing direct dependencies')
  e.require(row['axioms']==PINS,'wrong transitive axioms')
  e.require(type(row['binderCount']) is int and row['binderCount']>=0 and row['propositionBinders']==sorted(set(row['propositionBinders'])) and all(type(i) is int and 0<=i<row['binderCount'] for i in row['propositionBinders']),'invalid binder accounting')
 text=raw.decode();suffix=text.split(k.END+'\n',1)[1];k.check_axiom_text(suffix.encode(),value['rows'])
 return value

def inputs(producer,current):
 """Positive exact bindings, not a claim of a current fresh/cold rebuild."""
 producer=producer.resolve();e.require(producer==PRODUCER_ROOT and p.resources.hash_file(producer/'SHA256SUMS')==PRODUCER_MANIFEST,'wrong sealed producer manifest')
 seals={}
 for line in (producer/'SHA256SUMS').read_text().splitlines():
  sha,name=line.split(maxsplit=1);seals[Path(name.lstrip('*'))]=sha
 for rel in ['scoped-axioms/verified.json','scoped-axioms/receipt/provenance.json','scoped-axioms/request.json','scoped-axioms/actual-lake-setup.json','scope-policy.json','fresh24/provenance.json']:
  path=producer/rel;e.require(seals.get(path)==p.resources.hash_file(path),'changed sealed supplemental input')
 verified=e.load(producer/'scoped-axioms/verified.json');old=e.load(producer/'scoped-axioms/receipt/provenance.json');request=e.load(producer/'scoped-axioms/request.json')
 e.require(verified['sourceSnapshot']['revision']==PRODUCER_HEAD and old['before']==old['after']==verified['sourceSnapshot'] and request['sourceSnapshot']==old['before'],'wrong historical producer')
 p.check_outcomes(old);e.require(old['budgets']==p.BUDGET,'changed historical budgets');e.require(old['exit']==0 and request['collectorExit']==request['inputValidationExit']==request['exit']==0,'failed producer')
 e.require(current['runtime']==old['before']['runtime'] and current['buildTools']==old['before']['buildTools'] and current['serialConfigSha256']==old['before']['serialConfigSha256'] and current['inputs']==old['before']['inputs'],'changed tool/pin/config inputs')
 installed=k.tool_inputs(current);e.require(installed==request['installedBefore']==request['installedAfter'],'changed installed inputs')
 setup_path=producer/'scoped-axioms/actual-lake-setup.json';raw=setup_path.read_bytes();e.require(e.digest(raw)==verified['actualSetupSha256'],'stale/corrupt actual setup');setup=e.loads(raw)
 e.require(setup['name']=='_unknown' and setup['isModule'] is False and setup['options']=={} and not setup.get('imports?') and setup['plugins']==[] and setup['dynlibs']==[],'changed actual external setup contract')
 closure=k.source_closure('Solidity.TestSuite.Derived17');policy=e.load(producer/'scope-policy.json');e.require(len(closure['modules'])==250 and set(setup['importArts'])==set(closure['modules']),'unexpected/missing project import closure')
 objects={}
 for module,row in closure['modules'].items():
  e.require(policy['sourceClosure'][module]['sha256']==row['sha256'],'changed proof source')
  paths=setup['importArts'][module];e.require(isinstance(paths,list) and len(paths)==1,'unsupported object parts')
  path=Path(paths[0]);e.require(path.is_absolute() and path.resolve()==path and path.is_relative_to(ROOT/'.lake/roadmap-v17-cache'/old['before']['sourceToolchainKey']),'unbound actual object path')
  relative=str(path.relative_to(ROOT/'.lake/roadmap-v17-cache'/old['before']['sourceToolchainKey']));sha=p.resources.hash_file(path)
  e.require(old['cacheEnd']['files'].get(relative)==sha,'stale actual import object');objects[module]={'path':str(path),'sha256':sha}
 fresh=e.load(producer/'fresh24/provenance.json');p.check_outcomes(fresh);e.require(fresh['budgets']==p.BUDGET,'changed ownfresh budgets');manifest=p.validate_timing_outputs(fresh,producer/'fresh24')
 e.require(fresh['before']==fresh['after']==old['before'] and all(fresh[x]==0 for x in ['exit','commandExit','executionExit','cleanupExit','validationExit']),'failed/mismatched ownfresh producer')
 e.require(verified['names']==[row['name'] for row in REQUESTS] and set(verified['freshEquivalentObjects'])==set(p.setup_modules()),'wrong supplemental catalog')
 for module in p.setup_modules():e.require(objects[module]==verified['freshEquivalentObjects'][module] and objects[module]['sha256']==manifest['fresh']['files'][module+'.olean'],'not ownfresh-equivalent inputs')
 return {'producerHead':PRODUCER_HEAD,'producerTree':old['before']['sourceTree'],'consumerSnapshot':current,'actualSetupSha256':e.digest(raw),'actualSetupPath':str(setup_path),'sourceClosure':closure,'actualProjectObjects':objects,'installedInputs':installed,'templateSha256':p.resources.hash_file(k.TEMPLATE),'fullDeclarationMetadata':False,'supplementalHistoricalInputOnly':True,'semanticPremisesDischarged':False,'releaseClosed':False}

def imports(meta,bound):
 seen=set();prefix=Path(bound['consumerSnapshot']['runtime']['lean']['path']).parent.parent
 for row in meta['imports']:
  e.require(set(row)=={'module','olean'} and row['module'] not in seen,'duplicate/malformed environment import');module=row['module'];seen.add(module);path=Path(row['olean'])
  if path.is_relative_to('/opt/v17-toolchain'):path=prefix/path.relative_to('/opt/v17-toolchain')
  path=path.resolve()
  if module.startswith('Solidity.'):
   e.require(module in bound['actualProjectObjects'] and path==(ROOT/'.lake/build/lib/lean'/(module.replace('.','/')+'.olean')).resolve(),'unexpected project search lookup')
   # findOLean is ONLY a search-path lookup. Actual inputs are the authenticated setup map.
   e.require(path.is_file(),'missing search lookup file')
  else:e.require(module.split('.')[0] in ('Init','Lean','Std') and str(path) in bound['installedInputs'] and p.resources.hash_file(path)==bound['installedInputs'][str(path)],'unbound installed lookup')
 e.require({n for n in seen if n.startswith('Solidity.')}==set(bound['actualProjectObjects']),'missing/extra actual environment source module')

def exact_replay(first,second,first_inputs,second_inputs):
 e.require(k.canonical(first)==k.canonical(second) and k.canonical(first_inputs)==k.canonical(second_inputs),'live full-metadata/input replay differs');return True

def shell_bytes(out):
 return ('set -eu\nexport LEAN_PATH='+shlex.quote(str(ROOT/'.lake/build/lib/lean'))+'\nlean -j1 --tstack=131072 --root='+shlex.quote(str(out))+' --setup '+shlex.quote(str(out/'actual-lake-setup.json'))+' '+shlex.quote(str(out/'Derived17Axioms.lean'))+'\n').encode()

def validate_files(out,request,before):
 e.require((out/'run.sh').read_bytes()==shell_bytes(out) and e.digest((out/'run.sh').read_bytes())==request['shellSha256'],'changed actual command shell')
 e.require((out/'Derived17Axioms.lean').read_bytes()==query_bytes() and e.digest((out/'Derived17Axioms.lean').read_bytes())==request['querySha256'],'changed query')
 e.require((out/'actual-lake-setup.json').read_bytes()==Path(before['actualSetupPath']).read_bytes() and e.digest((out/'actual-lake-setup.json').read_bytes())==request['setupSha256'],'changed setup')
 e.require(p.resources.hash_file(Path(__file__))==request['scriptSha256'],'changed consumer script')

def failure_outcome(phase,returned,code,record):
 return {'phase':phase,'collectorExit':code if returned else None,'validationExit':125 if phase=='validation' and returned and code==0 else None,'collectionExceptionExit':2 if phase=='collection' and not returned else None,'driverExceptionExit':2,'rawRecordOutcomes':None if record is None else {key:record[key] for key in ['exit','commandExit','executionExit','cleanupExit','validationExit']},'fullDeclarationMetadata':False,'replayVerified':False,'semanticPremisesDischarged':False,'releaseClosed':False}

def save(path,value):path.write_text(json.dumps(value,indent=2)+'\n')
def run(producer,out):
 global ACTIVE_OUT,PHASE,COLLECTOR_RETURNED,COLLECTOR_CODE
 ACTIVE_OUT=None;PHASE="preflight";COLLECTOR_RETURNED=False;COLLECTOR_CODE=None
 e.require(not out.exists() and out.is_absolute() and out.resolve()==out and not out.is_relative_to(ROOT),'new external directory required');out.mkdir(parents=True);ACTIVE_OUT=out
 current=e.snapshot(ROOT);before=inputs(producer,current);save(out/'inputs-before.json',before)
 query=out/'Derived17Axioms.lean';query.write_bytes(query_bytes());setup=out/'actual-lake-setup.json';setup.write_bytes(Path(before['actualSetupPath']).read_bytes());shell=out/'run.sh';shell.write_bytes(shell_bytes(out))
 gate='supplemental-derived17-full';p.TARGETS[gate]=([],[]);original=p.gate_command;p.gate_command=lambda name,d:['sh',str(shell)] if name==gate else original(name,d)
 request={'schema':1,'declarations':REQUESTS};fixed_request(request);save(out/'request.json',{'request':request,'querySha256':e.digest(query.read_bytes()),'shellSha256':e.digest(shell.read_bytes()),'setupSha256':e.digest(setup.read_bytes()),'scriptSha256':p.resources.hash_file(Path(__file__)),'budgets':{'nodes':100000,'depth':512,'seconds':300},'consumerSnapshot':current,'supplementalHistoricalInputOnly':True,'semanticPremisesDischarged':False,'releaseClosed':False})
 validate_files(out,e.load(out/'request.json'),before)
 PHASE='collection';code=p.collect(SimpleNamespace(gate=gate,out=out/'receipt'));COLLECTOR_RETURNED=True;COLLECTOR_CODE=code;PHASE='validation';save(out/'outcome.json',{'collectorExit':code,'validationExit':None,'replayVerified':False,'semanticPremisesDischarged':False,'releaseClosed':False})
 if code:return code
 record=e.load(out/'receipt/provenance.json');e.require(p.validate(record,out/'receipt',current,gate),'failed native extraction');raw=p.read_bound(out/'receipt',record['log'],record['logSha256']);meta=metadata(raw);imports(meta,before)
 after=inputs(producer,e.snapshot(ROOT));validate_files(out,e.load(out/'request.json'),before);e.require(before==after and query.read_bytes()==query_bytes() and setup.read_bytes()==Path(before['actualSetupPath']).read_bytes(),'source/query/setup/object/tool changed');save(out/'inputs-after.json',after)
 save(out/'metadata.json',meta);save(out/'outcome.json',{'collectorExit':0,'validationExit':0,'fullDeclarationMetadata':True,'replayVerified':False,'supplementalHistoricalInputOnly':True,'semanticPremisesDischarged':False,'releaseClosed':False});return 0

def main():
 a=argparse.ArgumentParser(description=__doc__);a.add_argument('--producer',type=Path,required=True);a.add_argument('--out',type=Path,required=True);args=a.parse_args()
 with open('/tmp/solidity-lean-feature-groups-20261025/writer.lock','a+') as lock:
  fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB);p.ensure_no_unresolved();code=run(args.producer,args.out)
  if code:return code
  replay=args.out.parent/(args.out.name+'-replay');code=run(args.producer,replay)
  if code:return code
  first=e.load(args.out/'metadata.json');second=e.load(replay/'metadata.json');exact_replay(first,second,e.load(args.out/'inputs-after.json'),e.load(replay/'inputs-before.json'))
  save(args.out/'verified.json',{'consumerSnapshot':e.snapshot(ROOT),'metadataSha256':p.resources.hash_file(args.out/'metadata.json'),'replayMetadataSha256':p.resources.hash_file(replay/'metadata.json'),'fullDeclarationMetadata':True,'replayVerified':True,'supplementalHistoricalInputOnly':True,'semanticPremisesDischarged':False,'releaseClosed':False});return 0
if __name__=='__main__':
 try:raise SystemExit(main())
 except (ValueError,OSError,KeyError,TypeError,subprocess.SubprocessError) as error:
  failure={'error':str(error),'phase':'supplemental metadata collection/validation','driverExit':2,'semanticPremisesDischarged':False,'releaseClosed':False}
  if isinstance(error,p.resources.ResourceObservationError):failure['resourceObservations']=error.observations
  if ACTIVE_OUT is not None:
   save(ACTIVE_OUT/('failure-'+uuid.uuid4().hex+'.json'),failure)
   record_path=ACTIVE_OUT/'receipt/provenance.json';record=e.load(record_path) if record_path.exists() else None
   save(ACTIVE_OUT/'outcome.json',failure_outcome(PHASE,COLLECTOR_RETURNED,COLLECTOR_CODE,record))
  print(json.dumps(failure));raise SystemExit(2)
