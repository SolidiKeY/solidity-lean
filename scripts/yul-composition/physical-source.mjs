#!/usr/bin/env node
/** Actual VY2 source/physical executions and finite pinned compiler controls.
 * No whole-world, source/Yul call, allocator or compiler adequacy claim. */
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {isDeepStrictEqual as eq} from 'node:util';
import {ROOT,sha,checkedCompiler,inputFor,compileRecord,validateProvenance} from './harness.mjs';
import {capturedMachine,validateCallCapture,compareState} from './capture.mjs';
import {predictedAliases,LOCAL_CALLER} from './oracles.mjs';
import {hexToBytes,bytesToHex} from '../evm-reference/node_modules/@ethereumjs/util/dist/esm/index.js';
import {keccak_256} from '../evm-reference/node_modules/@noble/hashes/sha3.js';
const INPUT_SHA='8a8fc93b5bbdacdee40422a0b98043c30bd4e2853bdf560d015e30ae7407613c',SOURCE_SHA='f0a8b22b0f472d157a8771ff7d853b8712db77dbe462f91125d66d83c2e1141a';
const OWN=['PhysicalFrames','PhysicalBytes','PhysicalControls','PhysicalMemory'].map(n=>'Solidity/Yul/Composition/'+n+'.lean').concat('tests/yul-composition/PhysicalDriver.lean');
const LEDGER_SHA='3626d4bd13537c68f00b185eb0e4c665ed3d306e8d23aee53efa65987930acbf';
const SELF='scripts/yul-composition/physical-source.mjs';
const LEAN_COMMAND=['/workspace/.setup/tools/lean-4.24.0-linux/bin/lake','-f','lakefile.vy5.toml','env','lean','-j1','--tstack=131072','--run','tests/yul-composition/PhysicalDriver.lean'];
export function validatePhysicalLedger(bytes){if(sha(bytes)!==LEDGER_SHA)throw Error('physical ledger drift');const l=JSON.parse(bytes);if(!eq(l.sourceHashes,ownHashes()))throw Error('stale physical proof hashes');return l;}
const SCOPE='Actual represented source actions/coupled journals/heap images plus finite selected native projections; full Yul, compiler, physical-world and allocation adequacy pending.';
const word=n=>'0x'+BigInt(n).toString(16).padStart(64,'0');
const selector=s=>'0x'+Buffer.from(keccak_256(new TextEncoder().encode(s))).subarray(0,4).toString('hex');
const model={schema:1,firstTruth:true,childTruth:true,firstRaw:0xab000002,childRaw:0xcd000003,innerRaw:0xab000002,outerRaw:0,staleOwnedRaw:0xab000003,stalePaddingRaw:0xcd000002,copied:[238,171,0,0,2,238],staticRaw:0xab000002,staticTag:'revert',allocations:[0,1,32,64].map(g=>({address:128+g,free:256+g,payload:[170]}))};
export const PLAN=[
 {signature:'peek()',data:word(0)+word(0).slice(2),post:0,exception:null,frames:1},
 {signature:'outer()',data:word(0xcd000003),post:0,exception:'revert',frames:2},
 {signature:'peek()',data:word(0)+word(0).slice(2),post:0,exception:null,frames:1},
 {signature:'first()',data:word(1)+word(0xab000002).slice(2),post:0xab000002,exception:null,frames:1},
 {signature:'child()',static:true,data:'0x',post:0xab000002,exception:'static state change',frames:1},
 {signature:'peek()',data:word(1)+word(0xab000002).slice(2),post:0xab000002,exception:null,frames:1},
 {signature:'child()',data:'0x',post:0xcd000003,exception:null,frames:1},
 {signature:'peek()',data:word(1)+word(0xcd000003).slice(2),post:0xcd000003,exception:null,frames:1}
];
export function validateModel(value){if(!eq(value,model))throw Error('missing/wrong actual physical model projection');return value;}
export function validateInput(bytes){if(sha(bytes)!==INPUT_SHA)throw Error('physical producer receipt drift');return JSON.parse(bytes);}
function ownHashes(){return Object.fromEntries(OWN.map(f=>[f,sha(readFileSync(join(ROOT,f)))]));}
export function verifyPhysicalInputs(dependency){
 const receipt=validateInput(readFileSync(join(ROOT,'tests/yul-composition/physical-producer-input.json')));
 for(const m of receipt.modules)if(sha(readFileSync(join(dependency,m.path)))!==m.sha256)throw Error('physical producer body drift: '+m.path);
 for(const f of OWN)if(!readFileSync(join(ROOT,f)).equals(readFileSync(join(dependency,f))))throw Error('physical consumer body drift');
 if(sha(readFileSync(join(ROOT,'tests/yul-composition/PhysicalControls.sol')))!==SOURCE_SHA)throw Error('physical source drift');
 validatePhysicalLedger(readFileSync(join(ROOT,'tests/yul-composition/physical-component-ledger.json')));
 return {producerInputSha256:INPUT_SHA,consumerHashes:ownHashes(),sourceSha256:SOURCE_SHA,physicalLedgerSha256:LEDGER_SHA,runnerSha256:sha(readFileSync(join(ROOT,SELF)))};
}
function bind(c,o,tx,to,input,isStatic){
 validateCallCapture(c,o,{transaction:tx,caller:LOCAL_CALLER,to,input,value:'0'});
 const r=c.frames[0];if(r.caller!==LOCAL_CALLER||r.value!=='0'||r.input!==input||r.isStatic!==isStatic||to!==null&&(r.address!==to||r.codeAddress!==to))throw Error('physical request/frame identity drift');
}
function observe(result){const e=result.result.execResult;return {failed:!!e.exceptionError,exception:e.exceptionError?.error??null,returnData:bytesToHex(e.returnValue),logs:(e.logs??[]).map(([a,t,b])=>({emitter:bytesToHex(a),topics:t.map(bytesToHex),data:bytesToHex(b)})),metrics:result.metrics};}
function slots(post){return Object.fromEntries([42,43,44,45,46,47,48].map(s=>[word(s),word(s===43?post:0)]));}
// Finite declared slot domain, not an untouched-world assertion. Caller nonce
// increments follow pinned EVM.runCall depth-zero behavior, not source effects.
function stateOracle(address,post,runtime,pre,index,plan){return {
 accounts:['pre','post'].flatMap(phase=>[
  {phase,address,fields:{exists:true,balance:'0',nonce:'1',code:runtime}},
  {phase,address:LOCAL_CALLER,fields:{exists:true,balance:'1000000000000000000000000000000',nonce:String(index+(phase==='pre'?1:2)),code:'0x'}}]),
 slotMaps:['pre','post'].map(phase=>({phase,address,kind:'persistent',value:slots(phase==='pre'?pre:post)})),
 memory:plan.data==='0x'?[]:[{frame:0,at:plan.exception==='revert'?'REVERT':'RETURN',offset:0,relativeOffset:true,windowLength:(plan.data.length-2)/2,bytes:plan.data}]
};}
function checkCall(row,plan,index,address,runtime){
 if(row.index!==index||row.signature!==plan.signature||row.isStatic!==!!plan.static)throw Error('physical call order drift');
 bind(row.capture,row.actual,index+2,address,selector(plan.signature),!!plan.static);
 if(row.actual.failed!==(plan.exception!==null)||row.actual.exception!==plan.exception||row.actual.returnData!==plan.data||!eq(row.actual.logs,[])||row.capture.frames.length!==plan.frames)throw Error('physical result/frame/log mismatch');
 const state=compareState(row.capture,stateOracle(address,plan.post,runtime,index===0?0:PLAN[index-1].post,index,plan));
 if(state.status!=='match')throw Error('physical state mismatch: '+JSON.stringify(state));
 if(index===1){
  const child=row.capture.frames[1];if(child.kind!=='call'||child.parent!==0||child.depth!==1||child.caller!==address||child.address!==address||child.codeAddress!==address||child.input!==selector('child()')||child.value!=='0'||child.isStatic!==false||child.output.exception!==null||child.output.bytes!=='0x'||!eq(child.output.logs,[]))throw Error('wrong physical child frame');
  const puts=row.capture.operations.filter(o=>o.kind==='putStorage'&&o.address===address&&o.slot===word(43)).map(o=>o.value);
  if(!eq(puts,[word(0xab000002),word(0xcd000003)])||!row.capture.operations.some(o=>o.kind==='revert'))throw Error('missing coupled child/outer native evidence');
 }
 if(plan.static&&row.capture.operations.some(o=>o.kind==='putStorage'))throw Error('static write observed');
}
export function validatePhysicalReport(r,directory){
 validatePhysicalLedger(readFileSync(join(ROOT,'tests/yul-composition/physical-component-ledger.json')));
 validateModel(r.model);
 const stdout=readFileSync(join(directory,'lean.stdout'),'utf8'),stderr=readFileSync(join(directory,'lean.stderr'),'utf8'),execution=JSON.parse(readFileSync(join(directory,'lean.execution.json')));
 if(!eq(JSON.parse(stdout),r.model)||stderr!==''||!eq(execution,{command:LEAN_COMMAND,exit:0,stdoutSha256:sha(stdout),stderrSha256:sha(stderr),consumerHashes:ownHashes(),producerInputSha256:INPUT_SHA}))throw Error('missing/stale physical Lean execution evidence');
 if(r.schema!==1||r.scope!==SCOPE||r.fullProofGate!=='pending'||r.producerInputSha256!==INPUT_SHA||r.sourceSha256!==SOURCE_SHA||r.physicalLedgerSha256!==LEDGER_SHA||r.runnerSha256!==sha(readFileSync(join(ROOT,SELF)))||!eq(r.consumerHashes,ownHashes())||r.callPlanSha256!==sha(JSON.stringify(PLAN)))throw Error('stale physical report identity');
 const profiles=[['legacy',false],['legacy',true],['viaIR',false],['viaIR',true]];
 if(!eq(r.rows?.map(x=>[x.pipeline,x.optimized]),profiles))throw Error('missing/reordered physical profile');
 const source=readFileSync(join(ROOT,'tests/yul-composition/PhysicalControls.sol'),'utf8'),address=predictedAliases().self;
 for(const row of r.rows){
  const input=inputFor({'PhysicalControls.sol':{content:source}},row.pipeline,row.optimized),stem=join(directory,row.pipeline+(row.optimized?'-optimized':''));
  if(!eq(JSON.parse(readFileSync(stem+'.input.json')),input))throw Error('physical raw input drift');
  const raw=readFileSync(stem+'.output.json','utf8');validateProvenance(row.receipt,input,raw);
  const artifact=JSON.parse(raw).contracts['PhysicalControls.sol'].PhysicalD,runtime='0x'+artifact.evm.deployedBytecode.object;
  const layout=artifact.storageLayout.storage.map(x=>[x.label,x.slot,x.offset]);
  if(!eq(layout,[['a','42',0],['b','42',1],['c','43',0],['items','44',0],['e','46',0],['f','47',0],['marker','48',0]]))throw Error('physical declaration layout mismatch');
  bind(row.deployment.capture,row.deployment.actual,1,null,'0x'+artifact.evm.bytecode.object,false);
  const created=row.deployment.capture.frames[0];if(created.kind!=='create'||created.createdAddress!==address||created.address!==address||created.codeAddress!==null||row.deployment.capture.post[address]?.code!==runtime||row.deployment.capture.frames.length!==1)throw Error('physical creation/install identity mismatch');
  if(row.address!==address||row.deployment.actual.failed||row.deployment.actual.exception!==null||row.deployment.actual.logs.length||row.deployment.actual.returnData!==runtime||row.runtimeSha256!==sha(hexToBytes(runtime))||row.calls?.length!==PLAN.length)throw Error('physical deployment/plan mismatch');
  for(let i=0;i<PLAN.length;i++)checkCall(row.calls[i],PLAN[i],i,address,runtime);
 }
 return r;
}
export async function runPhysical({compiler,dependency,out}){
 mkdirSync(out,{recursive:true});const bindings=verifyPhysicalInputs(dependency);
 const run=spawnSync(LEAN_COMMAND[0],LEAN_COMMAND.slice(1),{cwd:dependency,env:{...process.env,LEAN_NUM_THREADS:'1'},encoding:'utf8'});
 writeFileSync(join(out,'lean.stdout'),run.stdout??'');writeFileSync(join(out,'lean.stderr'),run.stderr??'');if(run.status!==0)throw Error('physical model execution failed');
 writeFileSync(join(out,'lean.execution.json'),JSON.stringify({command:LEAN_COMMAND,exit:run.status,stdoutSha256:sha(run.stdout),stderrSha256:sha(run.stderr),consumerHashes:ownHashes(),producerInputSha256:INPUT_SHA},null,2)+'\n');
 const actualModel=validateModel(JSON.parse(run.stdout));const compile=checkedCompiler(compiler),source=readFileSync(join(ROOT,'tests/yul-composition/PhysicalControls.sol'),'utf8'),rows=[];
 for(const pipeline of ['legacy','viaIR'])for(const optimized of [false,true]){
  const stem=join(out,pipeline+(optimized?'-optimized':'')),input=inputFor({'PhysicalControls.sol':{content:source}},pipeline,optimized),receipt=compileRecord(compile,input,stem);
  if(receipt.errors.length)throw Error('physical compiler failure: '+JSON.stringify(receipt.errors));
  const artifact=receipt.output.contracts['PhysicalControls.sol'].PhysicalD,{vm,observer}=await capturedMachine();
  const deployment=await observer.run({data:hexToBytes('0x'+artifact.evm.bytecode.object),isStatic:false},1),addr=deployment.result.createdAddress;
  if(!addr||deployment.result.execResult.exceptionError)throw Error('physical deployment failed');
  const runtime='0x'+artifact.evm.deployedBytecode.object;if(bytesToHex(await vm.evm.stateManager.getCode(addr))!==runtime)throw Error('physical installation mismatch');
  for(const slot of [42,43,44,45,46,47,48])await vm.evm.stateManager.getStorage(addr,hexToBytes(word(slot)));
  const row={pipeline,optimized,receipt:receipt.record,address:addr.toString(),runtimeSha256:sha(hexToBytes(runtime)),deployment:{actual:observe(deployment),capture:deployment.capture},calls:[]};
  for(let i=0;i<PLAN.length;i++){const plan=PLAN[i],result=await observer.run({to:addr,data:hexToBytes(selector(plan.signature)),isStatic:!!plan.static},i+2);row.calls.push({index:i,signature:plan.signature,isStatic:!!plan.static,actual:observe(result),capture:result.capture});writeFileSync(stem+'.capture.json',JSON.stringify(row,null,2)+'\n');checkCall(row.calls[i],plan,i,row.address,runtime);}
  rows.push(row);
 }
 const result={schema:1,scope:SCOPE,...bindings,model:actualModel,callPlanSha256:sha(JSON.stringify(PLAN)),rows,fullProofGate:'pending',staticBoundary:'Source primitive revert[] and native static-state-change exception are retained separately; no halt-class adequacy inferred.'};
 validatePhysicalReport(result,out);writeFileSync(join(out,'report.json'),JSON.stringify(result,null,2)+'\n');return result;
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)){const[,,compiler,dependency,out]=process.argv;if(!out)throw Error('usage: physical-source.mjs COMPILER DEPENDENCY OUT');const r=await runPhysical({compiler,dependency,out});console.log(JSON.stringify({profiles:r.rows.length,calls:r.rows.reduce((n,r)=>n+r.calls.length,0),fullProofGate:r.fullProofGate}));}
