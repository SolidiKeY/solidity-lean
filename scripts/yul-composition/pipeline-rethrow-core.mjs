// Versioned VY5 finite harness, derived from immutable native-rethrow-core.mjs.
// Shared compiler/EVM/capture implementations remain imported and unchanged.
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {isDeepStrictEqual as eq} from 'node:util';
import {ROOT,sha,inputFor,checkedCompiler,compileRecord,validateProvenance,policyScan} from './harness.mjs';
import {capturedMachine,validateCallCapture,compareState} from './capture.mjs';
import {predictedAliases,LOCAL_CALLER} from './oracles.mjs';
import {validateRethrowReport} from './rethrow-source.mjs';
import {INITIAL_GAS,STEP_LIMIT} from '../evm-reference/replay.mjs';
import {hexToBytes,bytesToHex} from '../evm-reference/node_modules/@ethereumjs/util/dist/esm/index.js';
import {keccak_256} from '../evm-reference/node_modules/@noble/hashes/sha3.js';
export function makePipelineRethrowHarness({SOURCE,ORACLE,LEDGER,SELF,REF,REF_SHA,FROZEN,CONTRACT,FILENAME,FIELD,FRAME_MODE,TRACE_CONTRACT}){
const read=f=>readFileSync(join(ROOT,f)),json=f=>JSON.parse(read(f));
const profiles=[['legacy',false],['legacy',true],['viaIR',false],['viaIR',true]];
function traceFor(profile){
 if(sha(read(TRACE_CONTRACT))!==FROZEN[TRACE_CONTRACT])throw Error('stale explicit trace contract');
 if(!profile||!eq(Object.keys(profile).sort(),['optimized','pipeline'])||!profiles.some(([p,o])=>p===profile.pipeline&&o===profile.optimized))throw Error('missing/invalid explicit pipeline trace identity');
 const t=json(TRACE_CONTRACT);
 same(t.profiles.map(p=>[p.pipeline,p.optimized]),profiles,'trace profile matrix drift');
 return t.profiles.find(p=>p.pipeline===profile.pipeline&&p.optimized===profile.optimized);
}
const traceIdentity=()=>({id:json(TRACE_CONTRACT).id,sha256:sha(read(TRACE_CONTRACT)),authorization:'H3 per-pipeline'});
const word=n=>'0x'+BigInt(n).toString(16).padStart(64,'0');
const selector=s=>'0x'+Buffer.from(keccak_256(new TextEncoder().encode(s))).subarray(0,4).toString('hex');
const asHex=bytes=>'0x'+Buffer.from(bytes).toString('hex');
function verifyNativeRethrowInputs(){
 for(const[file,hash]of Object.entries(FROZEN))if(sha(read(file))!==hash)throw Error('stale native rethrow source/oracle/engine/ledger: '+file);
 const l=json(LEDGER);
 if(json('tests/yul-composition/ledger.json')[FIELD]!==LEDGER||l.fullCoverage!==false||l.parentLedgerSha256!==sha(read('tests/yul-composition/rethrow-component-ledger.json')))throw Error('missing/stale selected native ledger');
 if(INITIAL_GAS!==100000000n||STEP_LIMIT!==5000000)throw Error('changed engine limits');
 const bytes=readFileSync(join(REF,'report.json'));if(sha(bytes)!==REF_SHA)throw Error('stale actual Source report');
 const source=JSON.parse(bytes);validateRethrowReport(source,REF);
 return {inputHashes:FROZEN,runnerSha256:sha(read(SELF)),sourceReportSha256:REF_SHA,source};
}
function observed(result){const e=result.result.execResult;return{failed:!!e.exceptionError,exception:e.exceptionError?.error??null,returnData:bytesToHex(e.returnValue),logs:(e.logs??[]).map(([a,t,b])=>({emitter:bytesToHex(a),topics:t.map(bytesToHex),data:bytesToHex(b)})),metrics:result.metrics};}
function bind(c,actual,ordinal,to,input){
 validateCallCapture(c,actual,{transaction:ordinal,caller:LOCAL_CALLER,to,input,value:'0'});
 const f=c.frames[0];if(f.caller!==LOCAL_CALLER||f.value!=='0'||f.input!==input||f.isStatic!==false||to!==null&&(f.address!==to||f.codeAddress!==to))throw Error('native request/root frame drift');
}
const requireState=(c,e,label)=>{const result=compareState(c,e);if(result.status!=='match')throw Error(label+': '+JSON.stringify(result));};
function same(value,wanted,label){if(!eq(value,wanted))throw Error(label);}
function validateNativeRethrowCall(row,plan,index,address,runtime,profile){
 const trace=traceFor(profile);
 same(Object.keys(row).sort(),['actual','capture','index','signature'],'unexpected native call fields');
 if(row.index!==index||row.signature!==plan.signature)throw Error('native ordered call identity drift');
 const c=row.capture,actual=row.actual,input=selector(plan.signature),failed=!['success','getter'].includes(plan.kind),logs=plan.kind==='success'?[{emitter:address,topics:[],data:'0x55'}]:[];
 bind(c,actual,index+2,address,input);
 if(actual.failed!==failed||actual.exception!==(failed?'revert':null)||actual.returnData!==plan.bytes||!eq(actual.logs,logs))throw Error('native full failure/bytes/log mismatch');
 const nested=['caught','negative-payload','success'].includes(plan.kind);
 const audited=FRAME_MODE==='audited'&&['caught','negative-payload'].includes(plan.kind);
 if(c.frames.length!==(audited?4:nested?2:1))throw Error('missing/extra native frames');
 same(c.domain.map(d=>d.address),[address,LOCAL_CALLER].sort(),'unexpected touched-account domain');
 const accounts=['pre','post'].flatMap(phase=>[
  {phase,address,fields:{exists:true,balance:'0',nonce:'1',code:runtime}},
  {phase,address:LOCAL_CALLER,fields:{exists:true,balance:json(ORACLE).callerBalance,nonce:String(index+(phase==='pre'?1:2)),code:'0x'}}]);
 const slotMaps=['pre','post'].flatMap(phase=>[{phase,address,kind:'persistent',value:{[word(0)]:word(phase==='pre'?plan.preMarker:plan.postMarker)}},{phase,address,kind:'transient',value:{[word(0)]:word(0)}},{phase,address:LOCAL_CALLER,kind:'persistent',value:{}},{phase,address:LOCAL_CALLER,kind:'transient',value:{}}]);
 const rootMemory={frame:0,at:failed?'REVERT':'RETURN',offset:0,relativeOffset:true,windowLength:(plan.bytes.length-2)/2,bytes:plan.bytes};
 const frames=[{frame:0,fields:{kind:'call',address,caller:LOCAL_CALLER,codeAddress:address,parent:null,depth:0,input,isStatic:false,value:'0',exception:failed?'revert':null,bytes:plan.bytes}}];
 if(nested)frames.push({frame:1,fields:{kind:'call',address,codeAddress:address,caller:address,parent:0,depth:1,input:plan.kind==='success'?selector('good()'):selector('child(uint256)')+word(plan.mode).slice(2),isStatic:plan.kind==='success',value:'0',exception:plan.kind==='success'?null:'revert',bytes:plan.bytes}});
 if(audited)for(const[id,parent,depth,value]of [[2,1,2,99],[3,0,1,8]])frames.push({frame:id,fields:{kind:'call',address,codeAddress:address,caller:address,parent,depth,input:selector('checkMarker(uint256)')+word(value).slice(2),isStatic:true,value:'0',exception:null,bytes:'0x'}});
 requireState(c,{accounts,slotMaps,memory:[rootMemory],logs:[{frame:0,expected:logs}],frames},'native complete touched state/result/memory');
 const writes=c.operations.filter(o=>o.kind==='putStorage').map(o=>[o.frame,o.address,o.slot,o.value]);
 const transient=c.operations.filter(o=>o.kind==='transient.put').map(o=>[o.frame,o.address,o.slot,o.value]);
 const reverted=c.operations.filter(o=>o.kind==='revert').map(o=>o.frame),tReverted=c.operations.filter(o=>o.kind==='transient.revert').map(o=>o.frame);
 if(['caught','negative-payload'].includes(plan.kind)){
  requireState(c,{logs:[{frame:1,expected:[]},...(audited?[{frame:2,expected:[]},{frame:3,expected:[]}]:[])],buffers:[{frame:0,bytes:audited?'0x':plan.bytes},{frame:1,bytes:'0x'}],memory:[
   {frame:1,at:'REVERT',offset:0,relativeOffset:true,windowLength:(plan.bytes.length-2)/2,bytes:plan.bytes},
   {frame:0,at:'LOG0',offset:0,relativeOffset:true,windowLength:1,bytes:'0x55',count:2,occurrence:0},
   {frame:0,at:'LOG0',offset:0,relativeOffset:true,windowLength:1,bytes:'0x66',count:2,occurrence:1},
   {frame:1,at:'LOG0',offset:0,relativeOffset:true,windowLength:1,bytes:'0x77'}]},'native child/catch fullbytes/windows');
  same(writes,trace.caughtPersistentWrites.map(([frame,value])=>[frame,address,word(0),word(value)]),'native ordered per-pipeline persistent write journal');
  same(transient,trace.caughtTransientWrites.map(([frame,value])=>[frame,address,word(0),word(value)]),'native ordered per-pipeline transient write journal');
  same(reverted,trace.rollbackFrames,'native child/outer rollback journal');same(tReverted,trace.rollbackFrames,'native child/outer transient rollback journal');
  if(audited)for(const[frame,marker,t]of [[2,99,51],[3,8,34]])for(const phase of ['pre','post']){
   const a=c.frames[frame][phase]?.[address];if(!a||a.persistent[word(0)]!==word(marker)||a.transient[word(0)]!==word(t))throw Error('native observable audit scope/state mismatch');
  }
  for(const[phase,marker,t]of [['pre','7','17'],['post','7','17']]){
   const a=c.frames[1][phase]?.[address];if(!a||a.persistent[word(0)]!==word(marker)||a.transient[word(0)]!==word(t))throw Error('native child frame prefix/restoration mismatch');
  }
 }else{
  same(writes,plan.kind==='success'?[[0,address,word(0),word(7)]]:[],'unexpected native persistent effects');same(transient,[],'unexpected native transient effects');
  same(reverted,failed?[0]:[],'native standalone rollback mismatch');same(tReverted,failed?[0]:[],'native standalone transient rollback mismatch');
  if(plan.kind==='success')requireState(c,{logs:[{frame:1,expected:[]}],buffers:[{frame:0,bytes:'0xbeef'}],memory:[{frame:1,at:'RETURN',offset:0,relativeOffset:true,windowLength:2,bytes:'0xbeef'},{frame:0,at:'LOG0',offset:0,relativeOffset:true,windowLength:1,bytes:'0x55'}]},'native successful try branch');
 }
 return row;
}
function sources(){return {[FILENAME]:{content:read(SOURCE).toString()}};}
function sourceLinks(row,source){
 const plan=json(ORACLE).plan;
 return plan.flatMap((p,i)=>{
  const selected=p.sourceCase??p.mustDifferFromSourceCase;if(selected===undefined)return[];
  const expected=source.model.cases[selected].result,actual=row.calls[i].actual;
  const sourceFailed=expected.tag==='revert',sourceBytes=asHex(expected.bytes),matches=actual.failed===sourceFailed&&actual.returnData===sourceBytes;
  if(matches!==(p.sourceCase!==undefined))throw Error('native/actual Source fullbytes mismatch or ineffective negative control');
  return[{call:i,sourceCase:selected,sourceFuel:source.model.cases[selected].fuel,sourceFuelRole:expected.tag==='success'?'no rethrow executed; success bypass':'positive Source rethrow horizon, not native gas',projection:'failure-and-full-bytes-only; native state independently checked',source:{failed:sourceFailed,bytes:sourceBytes},native:{failed:actual.failed,bytes:actual.returnData},expectedMatch:p.sourceCase!==undefined,status:matches?'match':'intended-mismatch'}];
 });
}
function validateNativeRethrowReport(report,directory){
 const {source,...binding}=verifyNativeRethrowInputs();
 same(Object.keys(report).sort(),['binding','fullProofGate','nativeExecution','rows','schema','traceContract','validation'],'unexpected report fields');
 same(report.traceContract,traceIdentity(),'stale trace contract identity');
 if(report.validation!=='pass'||report.schema!==1||report.nativeExecution!=='fresh-pinned-solc-evm'||report.fullProofGate!=='pending'||!eq(report.binding,binding)||!eq(report.rows?.map(r=>[r.pipeline,r.optimized]),profiles))throw Error('missing/stale native report matrix/identity/proof status');
 const address=predictedAliases().self,plan=json(ORACLE).plan;
 for(const row of report.rows){
  same(Object.keys(row).sort(),['address','calls','deployment','errors','links','optimized','pipeline','receipt','runtimeSha256'],'unexpected native profile fields');
  if(!eq(row.errors,[]))throw Error('passing report has missing/nonempty native errors');
  const stem=join(directory,row.pipeline+(row.optimized?'-optimized':'')),input=inputFor(sources(),row.pipeline,row.optimized);
  same(JSON.parse(readFileSync(stem+'.input.json')),input,'compiler input/settings/source drift');const raw=readFileSync(stem+'.output.json','utf8');validateProvenance(row.receipt,input,raw);
  const output=JSON.parse(raw);if((output.errors??[]).some(e=>e.severity==='error'))throw Error('native compiler failure retained');
  const a=output.contracts[FILENAME][CONTRACT],runtime='0x'+a.evm.deployedBytecode.object;
  same(a.storageLayout.storage.map(x=>[x.label,x.slot,x.offset]),[['marker','0',0]],'native marker slot drift');
  for(const p of plan)if(a.evm.methodIdentifiers[p.signature]!==selector(p.signature).slice(2))throw Error('native ABI selector drift');
  if(policyScan(output.sources[FILENAME].ast).refusals.length)throw Error('new fixture violates advisory approved admission policy');
  same(row.receipt,JSON.parse(readFileSync(stem+'.provenance.json')),'retained compile receipt drift');
  bind(row.deployment.capture,row.deployment.actual,1,null,'0x'+a.evm.bytecode.object);
  const creation=row.deployment.capture.frames[0];
  if(row.address!==address||creation.kind!=='create'||creation.address!==address||creation.createdAddress!==address||creation.codeAddress!==null||row.deployment.capture.frames.length!==1||row.runtimeSha256!==sha(hexToBytes(runtime))||row.deployment.actual.failed||row.deployment.actual.returnData!==runtime||row.deployment.actual.logs.length)throw Error('native deployment/runtime installation drift');
  requireState(row.deployment.capture,{installations:[{frame:0,address}],accounts:[{phase:'post',address,fields:{exists:true,balance:'0',nonce:'1',code:runtime}},{phase:'post',address:LOCAL_CALLER,fields:{exists:true,balance:json(ORACLE).callerBalance,nonce:'1',code:'0x'}}]},'native deployment world');
  if(row.calls?.length!==plan.length)throw Error('missing/extra ordered native call');
  row.calls.forEach((call,i)=>validateNativeRethrowCall(call,plan[i],i,address,runtime,{pipeline:row.pipeline,optimized:row.optimized}));
  same(row.links,sourceLinks(row,source),'actual Source/native result links drift');
  same(row,JSON.parse(readFileSync(stem+'.capture.json')),'retained native capture/report drift');
 }
 const execution=JSON.parse(readFileSync(join(directory,'native.execution.json')));
 same(execution,{kind:'fresh-pinned-solc-evm-runCall-not-runTx',compiler:jsonReceiptCompiler(report),nodeVersion:process.version,gasLimit:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,binding,profiles:profiles.map(([pipeline,optimized])=>({pipeline,optimized})),reportSha256:sha(readFileSync(join(directory,'report.json')))},'native execution receipt drift');
 return report;
}
function jsonReceiptCompiler(report){return {commit:report.rows[0].receipt.commit,version:report.rows[0].receipt.compiler,sha256:report.rows[0].receipt.compilerSha256};}
async function runNativeRethrow(compiler,out){
 mkdirSync(out,{recursive:true});const {source,...binding}=verifyNativeRethrowInputs(),compile=checkedCompiler(compiler),rows=[],plan=json(ORACLE).plan;
 for(const[pipeline,optimized]of profiles){
  const stem=join(out,pipeline+(optimized?'-optimized':'')),input=inputFor(sources(),pipeline,optimized),receipt=compileRecord(compile,input,stem);
  if(receipt.errors.length)throw Error('native compiler failure '+JSON.stringify(receipt.errors));
  const a=receipt.output.contracts[FILENAME][CONTRACT],runtime='0x'+a.evm.deployedBytecode.object,{vm,observer}=await capturedMachine();
  const deployment=await observer.run({data:hexToBytes('0x'+a.evm.bytecode.object),isStatic:false},1),addr=deployment.result.createdAddress;
  if(!addr||deployment.result.execResult.exceptionError)throw Error('native deployment failed');
  if(bytesToHex(await vm.evm.stateManager.getCode(addr))!==runtime)throw Error('native runtime installation failed');
  // Public read-only discovery, not expectation seeding: independent slot0 is fixed by source.
  await vm.evm.stateManager.getStorage(addr,hexToBytes(word(0)));vm.evm.transientStorage.get(addr,hexToBytes(word(0)));
  const row={pipeline,optimized,receipt:receipt.record,address:addr.toString(),runtimeSha256:sha(hexToBytes(runtime)),deployment:{actual:observed(deployment),capture:deployment.capture},calls:[],errors:[]};
  for(let i=0;i<plan.length;i++){
   const execution=await observer.run({to:addr,data:hexToBytes(selector(plan[i].signature)),isStatic:false},i+2);
   row.calls.push({index:i,signature:plan[i].signature,actual:observed(execution),capture:execution.capture});
   try{validateNativeRethrowCall(row.calls[i],plan[i],i,row.address,runtime,{pipeline,optimized});}catch(error){row.errors.push({call:i,message:error.message});}
   writeFileSync(stem+'.capture.json',JSON.stringify(row,null,2)+'\n');
  }
  row.links=sourceLinks(row,source);writeFileSync(stem+'.capture.json',JSON.stringify(row,null,2)+'\n');rows.push(row);
 }
 const report={schema:1,traceContract:traceIdentity(),validation:rows.some(row=>row.errors.length)?'mismatch':'pass',nativeExecution:'fresh-pinned-solc-evm',fullProofGate:'pending',binding,rows};
 writeFileSync(join(out,'report.json'),JSON.stringify(report,null,2)+'\n');
 writeFileSync(join(out,'native.execution.json'),JSON.stringify({kind:'fresh-pinned-solc-evm-runCall-not-runTx',compiler:jsonReceiptCompiler(report),nodeVersion:process.version,gasLimit:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,binding,profiles:profiles.map(([pipeline,optimized])=>({pipeline,optimized})),reportSha256:sha(readFileSync(join(out,'report.json')))},null,2)+'\n');
 validateNativeRethrowReport(report,out);return report;
}
return{verifyNativeRethrowInputs,validateNativeRethrowCall,validateNativeRethrowReport,runNativeRethrow};
}
