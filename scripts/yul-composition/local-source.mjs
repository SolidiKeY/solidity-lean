#!/usr/bin/env node
/** Actual typed local/physical components plus finite pinned native projections.
 * No Source dispatch/resumption, raw-local rollback or full adequacy claim. */
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {isDeepStrictEqual as eq} from 'node:util';
import {ROOT,sha,inputFor,checkedCompiler,compileRecord,validateProvenance} from './harness.mjs';
import {verifyPhysicalInputs} from './physical-source.mjs';
import {verifyInputs} from './component.mjs';
import {capturedMachine,validateCallCapture,compareState} from './capture.mjs';
import {predictedAliases,LOCAL_CALLER} from './oracles.mjs';
import {hexToBytes,bytesToHex} from '../evm-reference/node_modules/@ethereumjs/util/dist/esm/index.js';
import {keccak_256} from '../evm-reference/node_modules/@noble/hashes/sha3.js';
const FROZEN={"tests/yul-composition/local-producer-input.json": "3c3920686ab87fa93b04ee1aca4e6b3c5f2ce9164667f2111a9751d7bc0dbfdc", "tests/yul-composition/local-expectations.json": "2f45aaea937b09e169ef147b48ce9e70d1a9976ca30d98101848222a0b7def57", "tests/yul-composition/LocalPhysicalControls.sol": "a1c55df6a0eb450c8f6f9ecbad0592bfa2238da678d6731a36f49951fcb04e57", "tests/yul-composition/PhysicalControls.sol": "f0a8b22b0f472d157a8771ff7d853b8712db77dbe462f91125d66d83c2e1141a", "tests/yul-composition/local-component-ledger.json": "8782e2a1e1b98d7c3e957989c7d8e8d4b21644e8385fdb0bb1ad1f25dd395b56"};
const OWN=["Solidity/Yul/Composition/LocalPhysical.lean", "Solidity/Yul/Composition/LocalPhysicalMemory.lean", "Solidity/Yul/Composition/LocalPhysicalControls.lean", "tests/yul-composition/LocalDriver.lean"];
const INPUT='tests/yul-composition/local-producer-input.json',ORACLE='tests/yul-composition/local-expectations.json',LEDGER='tests/yul-composition/local-component-ledger.json',SELF='scripts/yul-composition/local-source.mjs';
const COMMAND=['/workspace/.setup/tools/lean-4.24.0-linux/bin/lake','-f','lakefile.vy5.toml','env','lean','-j1','--tstack=131072','--run','tests/yul-composition/LocalDriver.lean'];
const SCOPE='Actual halt-preserving physical-first/raw-local component execution and finite native projections; no ordinary dirty Source resume, raw-local rollback, allocator or whole-pipeline adequacy.';
const ownHashes=()=>Object.fromEntries(OWN.map(f=>[f,sha(readFileSync(join(ROOT,f)))]));
const read=f=>readFileSync(join(ROOT,f));
const frozen=(f,bytes=read(f))=>{if(sha(bytes)!==FROZEN[f])throw Error('stale local input: '+f);return JSON.parse(bytes);};
export const validateLocalInput=bytes=>frozen(INPUT,bytes);
export function validateLocalLedger(bytes=read(LEDGER)){
 const l=frozen(LEDGER,bytes);if(!eq(l.sourceHashes,ownHashes())||l.physicalLedgerSha256!==sha(read('tests/yul-composition/physical-component-ledger.json'))||l.olderComponentLedgerSha256!==sha(read('tests/yul-composition/component-ledger.json')))throw Error('stale local proof ledger');return l;
}
const oracle=()=>frozen(ORACLE);
export function verifyLocalInputs(dependency){
 verifyInputs(dependency);verifyPhysicalInputs(dependency);const receipt=validateLocalInput(read(INPUT));
 for(const row of receipt.modules)if(sha(readFileSync(join(dependency,row.path)))!==row.sha256)throw Error('local producer body drift');
 for(const f of OWN)if(!read(f).equals(readFileSync(join(dependency,f))))throw Error('local consumer body drift');
 for(const [f,h]of Object.entries(FROZEN))if(sha(read(f))!==h)throw Error('local source/oracle/receipt drift');
 validateLocalLedger();return {inputHashes:FROZEN,consumerHashes:ownHashes(),runnerSha256:sha(read(SELF))};
}
export function validateLocalModel(model){
 const e=oracle(),complete=flow=>({tag:'complete',flow,cells:e.cells});
 const wanted={schema:1,cells:e.cells,flow:'normal',cleanBridgeAccepted:false,rawResumeRefused:true,nonwordId:e.nonwordId,heapBytes:e.heapBytes,sourceLogs:e.sourceLogs,
  horizons:e.horizons.map(fuel=>({fuel,outcome:fuel>=e.completedFrom?complete('normal'):{tag:'exhausted'}})),
  staticHorizons:e.horizons.map(fuel=>({fuel,outcome:{tag:'halt',reason:'revert',bytes:[]}})),
  transfers:Object.fromEntries(['break','continue','leave'].map(flow=>[flow,complete(flow)])),targetBytes:e.targetBytes,physical:e.physical,wrongOwner:false,wrongSlot:false};
 if(!eq(model,wanted))throw Error('wrong/missing/ordered local model projection');return model;
}
const word=n=>'0x'+BigInt(n).toString(16).padStart(64,'0');
const selector=s=>'0x'+Buffer.from(keccak_256(new TextEncoder().encode(s))).subarray(0,4).toString('hex');
const bytes=p=>'0x'+p.words.map(n=>word(n).slice(2)).join('');
const slots=raw=>Object.fromEntries([42,43,44,45,46,47,48].map(n=>[word(n),word(n===43?raw:0)]));
const profiles=[['legacy',false],['legacy',true],['viaIR',false],['viaIR',true]];
function observed(result){const e=result.result.execResult;return {failed:!!e.exceptionError,exception:e.exceptionError?.error??null,returnData:bytesToHex(e.returnValue),logs:(e.logs??[]).map(([a,t,b])=>({emitter:bytesToHex(a),topics:t.map(bytesToHex),data:bytesToHex(b)})),metrics:result.metrics};}
function bind(c,a,ordinal,to,input){
 validateCallCapture(c,a,{transaction:ordinal,caller:LOCAL_CALLER,to,input,value:'0'});const f=c.frames[0];
 if(f.caller!==LOCAL_CALLER||f.value!=='0'||f.input!==input||f.isStatic!==false||to!==null&&(f.address!==to||f.codeAddress!==to))throw Error('local root request/frame drift');
}
function checkCall(row,plan,index,address,runtime){
 if(row.index!==index||row.signature!==plan.signature)throw Error('local call order drift');
 bind(row.capture,row.actual,index+2,address,selector(plan.signature));
 if(row.actual.failed!==(plan.exception!==null)||row.actual.exception!==plan.exception||row.actual.returnData!==bytes(plan)||!eq(row.actual.logs,[])||row.capture.frames.length!==plan.frames)throw Error('local native observable mismatch');
 const previous=index===0?'0':oracle().nativePlan[index-1].post;
 const state={accounts:['pre','post'].flatMap(phase=>[
  {phase,address,fields:{exists:true,balance:'0',nonce:'1',code:runtime}},
  {phase,address:LOCAL_CALLER,fields:{exists:true,balance:'1000000000000000000000000000000',nonce:String(index+(phase==='pre'?1:2)),code:'0x'}}]),
  slotMaps:['pre','post'].map(phase=>({phase,address,kind:'persistent',value:slots(phase==='pre'?previous:plan.post)})),
  memory:[{frame:0,at:plan.exception==='revert'?'REVERT':'RETURN',offset:0,relativeOffset:true,windowLength:plan.words.length*32,bytes:bytes(plan)}]};
 if(compareState(row.capture,state).status!=='match')throw Error('local native state/memory mismatch');
 if(plan.frames===2){const c=row.capture.frames[1];
  if(c.kind!=='call'||c.parent!==0||c.depth!==1||c.address!==address||c.codeAddress!==address||c.caller!==address||c.value!=='0'||c.isStatic||c.input!==selector('child()')||c.output.exception!==null||c.output.bytes!=='0x'||!eq(c.output.logs,[]))throw Error('local child identity drift');
  const writes=row.capture.operations.filter(o=>o.kind==='putStorage'&&o.address===address&&o.slot===word(43)).map(o=>o.value);
  if(!eq(writes,[word(0xab000002),word(0xcd000003)])||!row.capture.operations.some(o=>o.kind==='revert'))throw Error('missing actual child write/rollback evidence');
 }
}
function sources(){return Object.fromEntries(['PhysicalControls.sol','LocalPhysicalControls.sol'].map(f=>[f,{content:read('tests/yul-composition/'+f).toString()}]));}
export function validateLocalReport(report,directory){
 verifyLocalInputs('/workspace/vy5-dependencies-20261101');
 for(const [file,hash]of Object.entries(FROZEN))if(sha(read(file))!==hash)throw Error('stale/missing actual local file: '+file);
 validateLocalInput(read(INPUT));validateLocalLedger();validateLocalModel(report.model);
 if(report.schema!==1||report.scope!==SCOPE||report.fullProofGate!=='pending'||!eq(report.inputHashes,FROZEN)||!eq(report.consumerHashes,ownHashes())||report.runnerSha256!==sha(read(SELF))||!eq(report.rows?.map(r=>[r.pipeline,r.optimized]),profiles))throw Error('stale/incomplete local report');
 const stdout=readFileSync(join(directory,'lean.stdout'),'utf8'),stderr=readFileSync(join(directory,'lean.stderr'),'utf8'),execution=JSON.parse(readFileSync(join(directory,'lean.execution.json')));
 if(!eq(JSON.parse(stdout),report.model)||stderr!==''||!eq(execution,{command:COMMAND,exit:0,stdoutSha256:sha(stdout),stderrSha256:sha(stderr),consumerHashes:ownHashes(),inputHashes:FROZEN}))throw Error('missing/stale actual local execution');
 const address=predictedAliases().self,plan=oracle().nativePlan;
 for(const row of report.rows){
  const stem=join(directory,row.pipeline+(row.optimized?'-optimized':'')),input=inputFor(sources(),row.pipeline,row.optimized);
  if(!eq(input,JSON.parse(readFileSync(stem+'.input.json'))))throw Error('local compiler input drift');
  const raw=readFileSync(stem+'.output.json','utf8');validateProvenance(row.receipt,input,raw);
  const a=JSON.parse(raw).contracts['LocalPhysicalControls.sol'].LocalPhysicalControls,runtime='0x'+a.evm.deployedBytecode.object;
  if(!eq(a.storageLayout.storage.map(x=>[x.label,x.slot,x.offset]),[['a','42',0],['b','42',1],['c','43',0],['items','44',0],['e','46',0],['f','47',0],['marker','48',0]]))throw Error('local physical slot layout drift');
  bind(row.deployment.capture,row.deployment.actual,1,null,'0x'+a.evm.bytecode.object);const c=row.deployment.capture.frames[0];
  if(row.address!==address||c.kind!=='create'||c.address!==address||c.createdAddress!==address||c.codeAddress!==null||row.deployment.capture.frames.length!==1||row.deployment.capture.post[address]?.code!==runtime||row.deployment.actual.failed||row.deployment.actual.exception!==null||row.deployment.actual.returnData!==runtime||row.deployment.actual.logs.length||row.runtimeSha256!==sha(hexToBytes(runtime))||row.calls?.length!==plan.length)throw Error('local deployment/plan drift');
  for(let i=0;i<plan.length;i++)checkCall(row.calls[i],plan[i],i,address,runtime);
 }
 return report;
}
export async function runLocal({compiler,dependency,out}){
 mkdirSync(out,{recursive:true});const bindings=verifyLocalInputs(dependency);
 const run=spawnSync(COMMAND[0],COMMAND.slice(1),{cwd:dependency,env:{...process.env,LEAN_NUM_THREADS:'1'},encoding:'utf8'});
 writeFileSync(join(out,'lean.stdout'),run.stdout??'');writeFileSync(join(out,'lean.stderr'),run.stderr??'');
 writeFileSync(join(out,'lean.execution.json'),JSON.stringify({command:COMMAND,exit:run.status,stdoutSha256:sha(run.stdout??''),stderrSha256:sha(run.stderr??''),consumerHashes:ownHashes(),inputHashes:FROZEN},null,2)+'\n');
 if(run.status!==0)throw Error('actual local execution failed');const model=validateLocalModel(JSON.parse(run.stdout)),compile=checkedCompiler(compiler),rows=[],plan=oracle().nativePlan;
 for(const [pipeline,optimized]of profiles){
  const stem=join(out,pipeline+(optimized?'-optimized':'')),input=inputFor(sources(),pipeline,optimized),receipt=compileRecord(compile,input,stem);
  if(receipt.errors.length)throw Error('local compiler failure '+JSON.stringify(receipt.errors));
  const a=receipt.output.contracts['LocalPhysicalControls.sol'].LocalPhysicalControls,{vm,observer}=await capturedMachine();
  const deployed=await observer.run({data:hexToBytes('0x'+a.evm.bytecode.object),isStatic:false},1),addr=deployed.result.createdAddress;
  if(!addr||deployed.result.execResult.exceptionError)throw Error('local deploy failed');const runtime='0x'+a.evm.deployedBytecode.object;
  if(bytesToHex(await vm.evm.stateManager.getCode(addr))!==runtime)throw Error('local runtime installation failed');
  for(const slot of [42,43,44,45,46,47,48])await vm.evm.stateManager.getStorage(addr,hexToBytes(word(slot)));
  const row={pipeline,optimized,receipt:receipt.record,address:addr.toString(),runtimeSha256:sha(hexToBytes(runtime)),deployment:{actual:observed(deployed),capture:deployed.capture},calls:[]};
  for(let i=0;i<plan.length;i++){const result=await observer.run({to:addr,data:hexToBytes(selector(plan[i].signature)),isStatic:false},i+2);row.calls.push({index:i,signature:plan[i].signature,actual:observed(result),capture:result.capture});writeFileSync(stem+'.capture.json',JSON.stringify(row,null,2)+'\n');checkCall(row.calls[i],plan[i],i,row.address,runtime);}
  rows.push(row);
 }
 const report={schema:1,scope:SCOPE,...bindings,model,rows,fullProofGate:'pending'};validateLocalReport(report,out);writeFileSync(join(out,'report.json'),JSON.stringify(report,null,2)+'\n');return report;
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)){const[,,compiler,dependency,out]=process.argv;if(!out)throw Error('usage: local-source.mjs COMPILER DEPENDENCY OUT');const r=await runLocal({compiler,dependency,out});console.log(JSON.stringify({profiles:r.rows.length,calls:r.rows.reduce((n,r)=>n+r.calls.length,0),fullProofGate:r.fullProofGate}));}
