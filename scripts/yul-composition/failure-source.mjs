import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {resolve,join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {ROOT,sha} from './harness.mjs';
import {verifyForInputs} from './for-source.mjs';
const FROZEN={"Solidity/Yul/Composition/FailurePhysical.lean": "50b365186597e2a18c8c6125c8b84ec86fcc27b47f1704618b16c6c71fc268aa", "tests/yul-composition/FailureDriver.lean": "03841d827a570523b8fd97e2f961951e8b6e1f3eed688e5c9f2a3f5884b8a91a", "tests/yul-composition/failure-expectations.json": "cd3b29e1d5e09ad130c0175528daa091e841cbe4f8bf62278e99849a44d48f2f", "tests/yul-composition/failure-ledger.json": "9aacd09ce9790bf2079b06f967c43824a49edd1179d7707d5b7b1709e5d55acf"};
const PROVENANCE='/workspace/vy5-composition/failure-consumer-20261102/producer-provenance.json',PROVENANCE_SHA='308c204eeb585c071d9578840963458a52d8806132461e616e9e504156fdad18';
const ORACLE='tests/yul-composition/failure-expectations.json',LEDGER='tests/yul-composition/failure-ledger.json',SELF='scripts/yul-composition/failure-source.mjs';
const DEP='/workspace/vy5-dependencies-20261101';
const COMMAND=['/workspace/.setup/tools/lean-4.24.0-linux/bin/lake','-f','lakefile.vy5.toml','env','lean','-j1','--tstack=131072','--run','tests/yul-composition/FailureDriver.lean'];
const read=n=>readFileSync(join(ROOT,n));
export function validateFailureProvenance(p,readProducer=name=>readFileSync(join(DEP,name))){
 assert.equal(p.producer,'5a4678a0733702d5b74abffce9c7c6a2c3e45c28');
 assert.equal(sha(JSON.stringify(p)),PROVENANCE_SHA,'immutable complete producer closure drift');
 for(const row of p.closure)assert.equal(sha(readProducer(row.path)),row.sha256,'actual producer body drift: '+row.path);
 return p;
}
export function verifyFailureInputs(readOwn=read){
 verifyForInputs();
 for(const[name,hash]of Object.entries(FROZEN)){
  assert.equal(sha(readOwn(name)),hash,'stale owned body/oracle/ledger: '+name);
  if(name.endsWith('.lean'))assert.equal(sha(readFileSync(join(DEP,name))),hash,'stale actual private body: '+name);
 }
 assert.equal(JSON.parse(readOwn('tests/yul-composition/ledger.json')).failureEvidence,LEDGER);
 validateFailureProvenance(JSON.parse(readFileSync(PROVENANCE)));
 return {...FROZEN,[SELF]:sha(readOwn(SELF)),[PROVENANCE]:PROVENANCE_SHA};
}
const clone=x=>structuredClone(x);
export function expectedFailureModel(){
 assert.equal(sha(read(ORACLE)),FROZEN[ORACLE]);const o=JSON.parse(read(ORACLE));
 const refs=[{logicalIndex:1},{logicalIndex:0}],old=[161,178,195,212,229,246],copied=[161,17,34,212,229,246];
 const absent=[false,false,false,false];
 const account=(balance='0',nonce=0,code=null)=>({balance,nonce,code,storagePresence:clone(absent)});
 const entry=(address,oldAccount)=>({kind:'account',address,old:oldAccount});
 const prefix=[entry('32',account()),entry('48',account('11',1,0)),entry('64',account()),entry('48',account())];
 const events=[{kind:'credit',address:'64',value:'2'},{kind:'credit',address:'48',value:'5'}];
 const trace=[{kind:'event',event:clone(events[0])},{kind:'log',emitter:'48',topics:['31'],data:[112]},
  {kind:'event',event:clone(events[1])},{kind:'log',emitter:'64',topics:['41','42'],data:[128,129]}];
 const journals={residual:[[false,'1','7',o.residualOld]],owned:[[false,'1','7',0,1]],selectedResidual:'0',selectedOwnedByte:2};
 const state=(variant='base',allocated=undefined,isCopied=false)=>{
  const accounts={'1':account(),'32':account('0',37),'48':account('11',1,0),'49':account(),'64':account('23',2,0)};
  let journal=clone(prefix);
  if(variant==='poor'){accounts['48'].balance='0';journal.unshift(entry('48',account('11',1,0)));}
  if(variant==='overflow'){accounts['64'].balance=String(2n**256n-1n);journal.unshift(entry('64',account('23',2,0)));}
  if(variant==='missing'){accounts['64'].code=null;journal.unshift(entry('64',account('23',2,0)));}
  if(variant==='moved'){accounts['48'].balance='4';accounts['64'].balance='30';journal.unshift(entry('48',account('11',1,0)));journal.unshift(entry('64',account('23',2,0)));}
  return {locals:clone(refs),heapNext:allocated===undefined?2:3,heap:[{kind:'bytes',bytes:clone(o.input)},{kind:'bytes',bytes:clone(isCopied?copied:old)},allocated===undefined?null:{kind:'bytes',bytes:clone(allocated)}],fnLocals:clone(refs),events:clone(events),legacyLogs:[['48',[112]]],world:o.worldAddresses.map(address=>({address,account:accounts[address],transientPresence:clone(absent)})),journal};
 };
 const physical=(s,data)=>({state:s,journals:clone(journals),returndata:clone(data),trace:clone(trace)});
 const revert=bytes=>({tag:'revert',bytes:clone(bytes)}),timeout={tag:'timeout'};
 const layerFor=name=>name==='static'?'actual-known-staticcall':name==='entered-child-timeout'?'actual-known-call-horizon6':name.includes('transfer')?'actual-known-refusal':['missing-code','static-wrong-kind','static-nonstatic-frame'].includes(name)?'adapter-refusal':['call','consumer-timeout'].includes(name)?'actual-known-call':'decoder-boundary-control';
 const row=name=>{
  let variant='base';if(name==='insufficient-transfer')variant='poor';if(name==='overflow-transfer')variant='overflow';if(name==='missing-code')variant='missing';
  const before=state(variant);let producer=null,consumer=null;
  if(!['missing-code','static-wrong-kind','static-nonstatic-frame'].includes(name)){
   let data=clone(o.error),producerTag='revert',postVariant=variant,allocated=clone(data),status=revert(data),producerStatus=clone(status),completed=true;
   if(name==='entered-child-timeout'){postVariant='moved';allocated=undefined;status=clone(timeout);producerStatus={tag:'halt',halt:clone(timeout)};data=[9,8,7,6];completed=false;}
   else{
    if(['insufficient-transfer','overflow-transfer','empty-revert'].includes(name))data=[];
    if(name==='wrong-selector')data[0]^=1;
    if(name==='wrong-payload')data[35]=86;
    if(name==='truncated')data=data.slice(0,35);
    if(name==='short-success'){producerTag='success';data=[17,34];}
    if(name==='normal-success'){producerTag='success';data=clone(o.word);}
    producerStatus={tag:producerTag,bytes:clone(data)};
    allocated=name==='normal-success'?undefined:name==='short-success'?[]:clone(data);
    status=name==='normal-success'?{tag:'success',bytes:[]}:name==='consumer-timeout'?clone(timeout):revert(name==='short-success'?[]:data);
   }
   producer={status:producerStatus,completion:physical(state(postVariant),data),completed};
   consumer={status,state:state(postVariant,allocated),raw:clone(o.raw)};
  }
  return {name,layer:layerFor(name),before,rawBefore:clone(o.raw),producer,consumer};
 };
 const completed=physical(state(),o.error);
 const profile=pipeline=>({pipeline,cases:o.cases.map(row),
  copied:{physicalBytes:clone(copied),state:state('base',undefined,true),journals:clone(journals),returndata:clone(o.error),trace:clone(trace)},
  copiedCatch:{status:revert(o.error),state:state('base',o.error,true),journals:clone(journals),returndata:clone(o.error),trace:clone(trace)},
  invalidCopy:{completion:clone(completed),copyIsNone:true,consumerIsNone:true},decodedKnownArgument:o.decodedValue,exactEnd:[]});
 return {schema:1,engine:'actual-GeneralFailure-Source-consumer',nativeComparisons:0,fullProofGate:'pending',profiles:['legacy','viaIR'].map(profile)};
}
export function validateFailureModel(m){
 assert.deepEqual(m,expectedFailureModel(),'wrong/missing/reordered complete selected failure observation');
 return {sourcePipelines:2,orderedSourceCases:30,copyWindowProfiles:2,nativeComparisons:0,fullProofGate:'pending'};
}
export function validateFailureReport(report,directory,readEvidence=path=>readFileSync(path,'utf8')){
 const bindings=verifyFailureInputs();assert.deepEqual(report.bindings,bindings);assert.deepEqual(report.command,COMMAND);
 assert.equal(report.dependency,DEP);assert.equal(report.exit,0);
 assert.deepEqual(Object.keys(report).sort(),['command','dependency','bindings','exit','stdoutSha256','stderrSha256','model','summary'].sort());
 const receipt=JSON.parse(readEvidence(join(directory,'execution.json')));
 assert.deepEqual(receipt,{command:report.command,dependency:report.dependency,bindings,exit:report.exit,stdoutSha256:report.stdoutSha256,stderrSha256:report.stderrSha256});
 const stdout=readEvidence(join(directory,'lean.stdout')),stderr=readEvidence(join(directory,'lean.stderr'));
 assert.equal(sha(stdout),report.stdoutSha256);assert.equal(sha(stderr),report.stderrSha256);assert.equal(readEvidence(join(directory,'lean.exit')),'0\n');
 assert.deepEqual(JSON.parse(stdout),report.model);const summary=validateFailureModel(report.model);assert.deepEqual(report.summary,summary);return summary;
}
export function runFailure(out){
 const bindings=verifyFailureInputs();mkdirSync(out);
 const actual=spawnSync(COMMAND[0],COMMAND.slice(1),{cwd:DEP,env:{...process.env,LEAN_NUM_THREADS:'1'},encoding:'utf8'});
 writeFileSync(join(out,'lean.stdout'),actual.stdout??'');writeFileSync(join(out,'lean.stderr'),actual.stderr??'');writeFileSync(join(out,'lean.exit'),String(actual.status)+'\n');
 const receipt={command:COMMAND,dependency:DEP,bindings,exit:actual.status,stdoutSha256:sha(actual.stdout??''),stderrSha256:sha(actual.stderr??'')};writeFileSync(join(out,'execution.json'),JSON.stringify(receipt,null,2)+'\n');
 assert.equal(actual.status,0,'actual Source execution failed; raw outputs retained');
 const model=JSON.parse(actual.stdout);const summary=validateFailureModel(model);const report={...receipt,model,summary};writeFileSync(join(out,'report.json'),JSON.stringify(report,null,2)+'\n');validateFailureReport(report,out);return summary;
}
if(process.argv[1]===fileURLToPath(import.meta.url))console.log(JSON.stringify(runFailure(resolve(process.argv[2]))));
