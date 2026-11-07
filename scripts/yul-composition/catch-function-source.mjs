#!/usr/bin/env node
/** Actual typed local/physical components plus finite pinned native projections.
 * No Source dispatch/resumption, raw-local rollback or full adequacy claim. */
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {isDeepStrictEqual as eq} from 'node:util';
import {ROOT,sha,inputFor,checkedCompiler,compileRecord,validateProvenance} from './harness.mjs';
import {verifyRawCatchInputs} from './raw-catch-source.mjs';
import {capturedMachine,validateCallCapture,compareState} from './capture.mjs';
import {predictedAliases,LOCAL_CALLER} from './oracles.mjs';
import {hexToBytes,bytesToHex} from '../evm-reference/node_modules/@ethereumjs/util/dist/esm/index.js';
import {keccak_256} from '../evm-reference/node_modules/@noble/hashes/sha3.js';
const FROZEN={"tests/yul-composition/local-producer-input.json": "3c3920686ab87fa93b04ee1aca4e6b3c5f2ce9164667f2111a9751d7bc0dbfdc", "tests/yul-composition/catch-function-expectations.json": "da02c8eb85b2b8b62c607e137ce3725653f562ae0718df2c98b701c13b2a77d5", "tests/yul-composition/CatchFunctionPhysicalControls.sol": "097e8b293d45a8ba8fd4fc26fe53553d2c267b3b3a1b0d17f23a5906d2058ebf", "tests/yul-composition/PhysicalControls.sol": "f0a8b22b0f472d157a8771ff7d853b8712db77dbe462f91125d66d83c2e1141a", "tests/yul-composition/catch-function-component-ledger.json": "80f3bdb646ec3f72af468846b48b51aa392ed18ad004d7dda040d2df2d1090e5"};
const OWN=["Solidity/Yul/Composition/CatchFunctionPhysical.lean", "tests/yul-composition/CatchFunctionDriver.lean"];
const INPUT='tests/yul-composition/local-producer-input.json',ORACLE='tests/yul-composition/catch-function-expectations.json',LEDGER='tests/yul-composition/catch-function-component-ledger.json',SELF='scripts/yul-composition/catch-function-source.mjs';
const COMMAND=['/workspace/.setup/tools/lean-4.24.0-linux/bin/lake','-f','lakefile.vy5.toml','env','lean','-j1','--tstack=131072','--run','tests/yul-composition/CatchFunctionDriver.lean'];
const SCOPE='Actual existing scoped nested-function continuation from completed RAW catch state, no initializer; finite native controls, no full Source/compiler/world adequacy or runClean resumption.';
const ownHashes=()=>Object.fromEntries(OWN.map(f=>[f,sha(readFileSync(join(ROOT,f)))]));
const read=f=>readFileSync(join(ROOT,f));
const frozen=(f,bytes=read(f))=>{if(sha(bytes)!==FROZEN[f])throw Error('stale local input: '+f);return JSON.parse(bytes);};
export const validateCatchFunctionInput=bytes=>frozen(INPUT,bytes);
export function validateCatchFunctionLedger(bytes=read(LEDGER)){
 if(JSON.parse(read('tests/yul-composition/ledger.json')).catchFunctionComponentEvidence!==LEDGER)throw Error('missing selected function ledger');
 const l=frozen(LEDGER,bytes);if(l.parentRawCatchLedgerSha256!==sha(read('tests/yul-composition/raw-catch-component-ledger.json'))||!eq(l.sourceHashes,ownHashes()))throw Error('stale raw catch proof ledger');return l;
}
const oracle=()=>frozen(ORACLE);
export function verifyCatchFunctionInputs(dependency){
 verifyRawCatchInputs(dependency);const receipt=validateCatchFunctionInput(read(INPUT));
 for(const row of receipt.modules)if(sha(readFileSync(join(dependency,row.path)))!==row.sha256)throw Error('local producer body drift');
 for(const f of OWN)if(!read(f).equals(readFileSync(join(dependency,f))))throw Error('local consumer body drift');
 for(const [f,h]of Object.entries(FROZEN))if(sha(read(f))!==h)throw Error('local source/oracle/receipt drift');
 validateCatchFunctionLedger();return {inputHashes:FROZEN,consumerHashes:ownHashes(),runnerSha256:sha(read(SELF))};
}
export function validateCatchFunctionModel(model){
 const e=oracle(),complete={tag:'complete',flow:true,cells:e.cells};
 const wanted={schema:1,cells:e.cells,inputCells:e.inputCells,wrongCells:e.wrongCells,poisonCells:e.poisonCells,resetCells:e.resetCells,arities:e.arities,flow:true,cleanBridgeAccepted:false,rawResumeRefused:true,
  nonwordId:e.nonwordId,heapBytes:e.heapBytes,sourceLogs:e.sourceLogs,
  horizons:e.horizons.map(fuel=>({fuel,outcome:fuel>=e.completedFrom?complete:{tag:'exhausted'}})),
  journalLengths:e.journalLengths,targetBytes:e.targetBytes,emptyTargetBytes:e.emptyTargetBytes,caughtBytes:[222,173],emptyCaughtBytes:[],
  worldLogs:[{emitter:'1',topics:[],data:[85]}],physical:e.physical};
 if(!eq(model,wanted))throw Error('wrong/missing/ordered raw catch model projection');return model;
}

const word=n=>'0x'+BigInt(n).toString(16).padStart(64,'0');
const selector=s=>'0x'+Buffer.from(keccak_256(new TextEncoder().encode(s))).subarray(0,4).toString('hex');
const bytes=p=>p.rawBytes??('0x'+p.words.map(n=>word(n).slice(2)).join(''));
const slots=(raw,marker)=>Object.fromEntries([42,43,44,45,46,47,48].map(n=>[word(n),word(n===43?raw:n===48?marker:0)]));
const profiles=[['legacy',false],['legacy',true],['viaIR',false],['viaIR',true]];
function observed(result){const e=result.result.execResult;return {failed:!!e.exceptionError,exception:e.exceptionError?.error??null,returnData:bytesToHex(e.returnValue),logs:(e.logs??[]).map(([a,t,b])=>({emitter:bytesToHex(a),topics:t.map(bytesToHex),data:bytesToHex(b)})),metrics:result.metrics};}
function bind(c,a,ordinal,to,input){
 validateCallCapture(c,a,{transaction:ordinal,caller:LOCAL_CALLER,to,input,value:'0'});const f=c.frames[0];
 if(f.caller!==LOCAL_CALLER||f.value!=='0'||f.input!==input||f.isStatic!==false||to!==null&&(f.address!==to||f.codeAddress!==to))throw Error('local root request/frame drift');
}
function checkCall(row,plan,index,address,runtime){
 if(row.index!==index||row.signature!==plan.signature)throw Error('raw catch call order drift');
 bind(row.capture,row.actual,index+2,address,selector(plan.signature));
 const logs=plan.logs.map(data=>({emitter:address,topics:[],data}));
 if(row.actual.failed!==(plan.exception!==null)||row.actual.exception!==plan.exception||row.actual.returnData!==bytes(plan)||!eq(row.actual.logs,logs)||row.capture.frames.length!==plan.frames)throw Error('raw catch native observable mismatch');
 const previous=index===0?'0':oracle().nativePlan[index-1].marker;
 const maps=['pre','post'].flatMap(phase=>[
  {phase,address,kind:'persistent',value:slots('0',phase==='pre'?previous:plan.marker)},
  {phase,address,kind:'transient',value:plan.transientTracked?{[word(0)]:word(0)}:{}}]);
 const memory=[{frame:0,at:plan.exception==='revert'?'REVERT':'RETURN',offset:0,relativeOffset:true,windowLength:(bytes(plan).length-2)/2,bytes:bytes(plan)}];
 const state={accounts:['pre','post'].flatMap(phase=>[
  {phase,address,fields:{exists:true,balance:'0',nonce:'1',code:runtime}},
  {phase,address:LOCAL_CALLER,fields:{exists:true,balance:'1000000000000000000000000000000',nonce:String(index+(phase==='pre'?1:2)),code:'0x'}}]),slotMaps:maps,memory,logs:[{frame:0,expected:logs}]};
 if(compareState(row.capture,state).status!=='match')throw Error('raw catch native state/memory mismatch');
 if(plan.frames>1){
  const outer=plan.catch?1:0,child=outer+1,fail=plan.empty?'0x':'0xdead';
  const expectedFrames=[{frame:0,fields:{kind:'call',address,caller:LOCAL_CALLER,codeAddress:address,parent:null,depth:0,input:selector(plan.signature),isStatic:false,value:'0',exception:plan.exception,bytes:bytes(plan)}}];
  if(plan.catch)expectedFrames.push({frame:1,fields:{kind:'call',address,caller:address,codeAddress:address,parent:0,depth:1,input:selector(plan.outer),isStatic:false,value:'0',exception:'revert',bytes:fail}});
  expectedFrames.push({frame:child,fields:{kind:'call',address,caller:address,codeAddress:address,parent:outer,depth:child,input:selector('child()'),isStatic:false,value:'0',exception:null,bytes:'0x'}});
  const checks={frames:expectedFrames,logs:[{frame:outer,expected:[]},{frame:child,expected:[{emitter:address,topics:[],data:'0x77'}]}],memory:[
   {frame:outer,at:'REVERT',offset:0,relativeOffset:true,windowLength:plan.empty?0:2,bytes:fail},
   {frame:outer,at:'LOG0',offset:0,relativeOffset:true,windowLength:1,bytes:'0x66'},
   {frame:child,at:'LOG0',offset:0,relativeOffset:true,windowLength:1,bytes:'0x77'}]};
  if(plan.catch){checks.buffers=[{frame:0,bytes:fail},{frame:outer,bytes:'0x'}];checks.memory.push({frame:0,at:'LOG0',offset:0,relativeOffset:true,windowLength:1,bytes:'0x55'});}
  if(compareState(row.capture,checks).status!=='match')throw Error('raw catch child/catch bytes, logs or frame window drift');
  const writes=row.capture.operations.filter(o=>o.kind==='putStorage'&&o.address===address&&o.slot===word(43)).map(o=>[o.frame,o.value]);
  const transient=row.capture.operations.filter(o=>o.kind==='transient.put'&&o.address===address&&o.slot===word(0)).map(o=>[o.frame,o.value]);
  if(!eq(writes,[[outer,word(0xab000002)],[child,word(0xcd000003)]])||!eq(transient,[[outer,word(0x22)],[child,word(0x33)]])||!row.capture.operations.some(o=>o.kind==='revert'&&o.frame===outer))throw Error('missing actual coupled nested writes/rollback evidence');
  if(plan.catch&&!row.capture.operations.some(o=>o.kind==='putStorage'&&o.frame===0&&o.address===address&&o.slot===word(48)&&o.value===word(7)))throw Error('missing actual caller prefix write');
 }
}
function sources(){return Object.fromEntries(['PhysicalControls.sol','CatchFunctionPhysicalControls.sol'].map(f=>[f,{content:read('tests/yul-composition/'+f).toString()}]));}
export function validateCatchFunctionReport(report,directory){
 verifyCatchFunctionInputs('/workspace/vy5-dependencies-20261101');
 for(const [file,hash]of Object.entries(FROZEN))if(sha(read(file))!==hash)throw Error('stale/missing actual local file: '+file);
 validateCatchFunctionInput(read(INPUT));validateCatchFunctionLedger();validateCatchFunctionModel(report.model);
 if(report.schema!==1||report.scope!==SCOPE||report.fullProofGate!=='pending'||!eq(report.inputHashes,FROZEN)||!eq(report.consumerHashes,ownHashes())||report.runnerSha256!==sha(read(SELF))||!eq(report.rows?.map(r=>[r.pipeline,r.optimized]),profiles))throw Error('stale/incomplete local report');
 const stdout=readFileSync(join(directory,'lean.stdout'),'utf8'),stderr=readFileSync(join(directory,'lean.stderr'),'utf8'),execution=JSON.parse(readFileSync(join(directory,'lean.execution.json')));
 if(!eq(JSON.parse(stdout),report.model)||stderr!==''||!eq(execution,{command:COMMAND,exit:0,stdoutSha256:sha(stdout),stderrSha256:sha(stderr),consumerHashes:ownHashes(),inputHashes:FROZEN}))throw Error('missing/stale actual local execution');
 const address=predictedAliases().self,plan=oracle().nativePlan;
 for(const row of report.rows){
  const stem=join(directory,row.pipeline+(row.optimized?'-optimized':'')),input=inputFor(sources(),row.pipeline,row.optimized);
  if(!eq(input,JSON.parse(readFileSync(stem+'.input.json'))))throw Error('local compiler input drift');
  const raw=readFileSync(stem+'.output.json','utf8');validateProvenance(row.receipt,input,raw);
  const a=JSON.parse(raw).contracts['CatchFunctionPhysicalControls.sol'].CatchFunctionPhysicalControls,runtime='0x'+a.evm.deployedBytecode.object;
  if(!eq(a.storageLayout.storage.map(x=>[x.label,x.slot,x.offset]),[['a','42',0],['b','42',1],['c','43',0],['items','44',0],['e','46',0],['f','47',0],['marker','48',0]]))throw Error('local physical slot layout drift');
  bind(row.deployment.capture,row.deployment.actual,1,null,'0x'+a.evm.bytecode.object);const c=row.deployment.capture.frames[0];
  if(row.address!==address||c.kind!=='create'||c.address!==address||c.createdAddress!==address||c.codeAddress!==null||row.deployment.capture.frames.length!==1||row.deployment.capture.post[address]?.code!==runtime||row.deployment.actual.failed||row.deployment.actual.exception!==null||row.deployment.actual.returnData!==runtime||row.deployment.actual.logs.length||row.runtimeSha256!==sha(hexToBytes(runtime))||row.calls?.length!==plan.length)throw Error('local deployment/plan drift');
  for(let i=0;i<plan.length;i++)checkCall(row.calls[i],plan[i],i,address,runtime);
 }
 return report;
}
export async function runCatchFunction({compiler,dependency,out}){
 mkdirSync(out,{recursive:true});const bindings=verifyCatchFunctionInputs(dependency);
 const run=spawnSync(COMMAND[0],COMMAND.slice(1),{cwd:dependency,env:{...process.env,LEAN_NUM_THREADS:'1'},encoding:'utf8'});
 writeFileSync(join(out,'lean.stdout'),run.stdout??'');writeFileSync(join(out,'lean.stderr'),run.stderr??'');
 writeFileSync(join(out,'lean.execution.json'),JSON.stringify({command:COMMAND,exit:run.status,stdoutSha256:sha(run.stdout??''),stderrSha256:sha(run.stderr??''),consumerHashes:ownHashes(),inputHashes:FROZEN},null,2)+'\n');
 if(run.status!==0)throw Error('actual local execution failed');const model=validateCatchFunctionModel(JSON.parse(run.stdout)),compile=checkedCompiler(compiler),rows=[],plan=oracle().nativePlan;
 for(const [pipeline,optimized]of profiles){
  const stem=join(out,pipeline+(optimized?'-optimized':'')),input=inputFor(sources(),pipeline,optimized),receipt=compileRecord(compile,input,stem);
  if(receipt.errors.length)throw Error('local compiler failure '+JSON.stringify(receipt.errors));
  const a=receipt.output.contracts['CatchFunctionPhysicalControls.sol'].CatchFunctionPhysicalControls,{vm,observer}=await capturedMachine();
  const deployed=await observer.run({data:hexToBytes('0x'+a.evm.bytecode.object),isStatic:false},1),addr=deployed.result.createdAddress;
  if(!addr||deployed.result.execResult.exceptionError)throw Error('local deploy failed');const runtime='0x'+a.evm.deployedBytecode.object;
  if(bytesToHex(await vm.evm.stateManager.getCode(addr))!==runtime)throw Error('local runtime installation failed');
  for(const slot of [42,43,44,45,46,47,48])await vm.evm.stateManager.getStorage(addr,hexToBytes(word(slot)));
  const row={pipeline,optimized,receipt:receipt.record,address:addr.toString(),runtimeSha256:sha(hexToBytes(runtime)),deployment:{actual:observed(deployed),capture:deployed.capture},calls:[]};
  for(let i=0;i<plan.length;i++){const result=await observer.run({to:addr,data:hexToBytes(selector(plan[i].signature)),isStatic:false},i+2);row.calls.push({index:i,signature:plan[i].signature,actual:observed(result),capture:result.capture});writeFileSync(stem+'.capture.json',JSON.stringify(row,null,2)+'\n');checkCall(row.calls[i],plan[i],i,row.address,runtime);}
  rows.push(row);
 }
 const report={schema:1,scope:SCOPE,...bindings,model,rows,fullProofGate:'pending'};validateCatchFunctionReport(report,out);writeFileSync(join(out,'report.json'),JSON.stringify(report,null,2)+'\n');return report;
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)){const[,,compiler,dependency,out]=process.argv;if(!out)throw Error('usage: catch-function-source.mjs COMPILER DEPENDENCY OUT');const r=await runCatchFunction({compiler,dependency,out});console.log(JSON.stringify({profiles:r.rows.length,calls:r.rows.reduce((n,r)=>n+r.calls.length,0),fullProofGate:r.fullProofGate}));}
