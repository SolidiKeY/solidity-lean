import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {isDeepStrictEqual as eq} from 'node:util';
import {ROOT,sha} from './harness.mjs';
import {verifyAttemptInputs,validateAttemptReport} from './attempt-source.mjs';
const FROZEN={"Solidity/Yul/Composition/HeapCatchPhysical.lean": "d02968df51e5f4dbc4bd5b35c540692816334d234064130bfe6940b3ff40e5c7", "tests/yul-composition/HeapCatchDriver.lean": "07e6256bcbed09e7d6e7e3ce85b09f803cf0a8f9b38969ec9e4972d017ab022e", "tests/yul-composition/heap-catch-component-ledger.json": "5847d762fb35a95c8f23566b23d38c2162d6b96db1f016f56dd49caf78c0cdf7", "tests/yul-composition/heap-catch-expectations.json": "7928f5083f3dc8a80f5471d5caf946e1bd470a9de20ccb4336d900712fc9f4b6"};
const REF='/workspace/vy5-composition/attempt-20261101/native-v2',REF_SHA='cdf3608af0672a5a277a4cad6e6edd93cff9dbcee9913ec803e52e052a0f5367';
const COMMAND=['/workspace/.setup/tools/lean-4.24.0-linux/bin/lake','-f','lakefile.vy5.toml','env','lean','-j1','--tstack=131072','--run','tests/yul-composition/HeapCatchDriver.lean'];
const SELF='scripts/yul-composition/heap-catch-source.mjs',LEDGER='tests/yul-composition/heap-catch-component-ledger.json',ORACLE='tests/yul-composition/heap-catch-expectations.json';
const read=f=>readFileSync(join(ROOT,f)),json=f=>JSON.parse(read(f));
export function verifyHeapInputs(dependency){
 verifyAttemptInputs(dependency);
 for(const[file,hash]of Object.entries(FROZEN))if(sha(read(file))!==hash)throw Error('stale heap consumer/oracle/catalog: '+file);
 if(json('tests/yul-composition/ledger.json').heapCatchComponentEvidence!==LEDGER)throw Error('missing selected heap catalog');
 const l=json(LEDGER);
 if(l.fullCoverage!==false||l.parentLedgerSha256!==sha(read('tests/yul-composition/attempt-component-ledger.json')))throw Error('false/stale heap coverage');
 for(const[file,hash]of Object.entries(l.sourceHashes))if(sha(readFileSync(join(dependency,file)))!==hash)throw Error('private heap consumer drift');
 for(const[file,hash]of Object.entries(l.producerHashes))if(sha(read(file))!==hash.main||sha(readFileSync(join(dependency,file)))!==hash.private)throw Error('actual Source heap producer drift');
 return {inputHashes:FROZEN,producerHashes:l.producerHashes,runnerSha256:sha(read(SELF))};
}
const object=bytes=>({kind:'bytes',bytes,length:bytes.length});
export function validateHeapModel(m){
 const e=json(ORACLE),alias=object([170,187]),logs=[['1',[153]],['1',[85]]];
 const data=[null,[222,173],[],e.panicBytes,null,null],names=['success','revert','empty','panic','timeout','stuck'];
 const cases=names.map((name,i)=>({name,alias,logs,raw:e.inputCells,next:data[i]===null?1:2,object:data[i]===null?null:object(data[i]),result:i===0?{tag:'success',bytes:[190,239]}:i===4?{tag:'timeout'}:i===5?{tag:'stuck',reason:'sentinel'}:{tag:'allocated',ref:{kind:'memory',logicalIndex:1},bytes:data[i],length:data[i].length}}));
 const continuations=data.slice(1,4).map(bytes=>{const cells=e.cells.slice();cells[3]=String(1793+bytes.length+512);return{alias,allocated:object(bytes),cells,normal:true,next:2,clean:false};});
 const wanted={schema:1,addressDomain:'logical-heap-index',cases,continuations,badAllocation:{next:2,object:{kind:'bool',value:false},outcome:{tag:'stuck',reason:'memory reference type'}},nonbyteRead:{tag:'stuck',reason:'not a bytes object'},danglingRead:{tag:'stuck',reason:'dangling memory reference'}};
 if(!eq(m,wanted))throw Error('missing/wrong actual typed heap outcome, bytes, state or raw continuation');return m;
}
function reference(){
 const bytes=readFileSync(join(REF,'report.json'));if(sha(bytes)!==REF_SHA)throw Error('stale prior reference report');
 const r=JSON.parse(bytes);validateAttemptReport(r,REF);return r;
}
function links(model,r){
 return r.rows.map(row=>({pipeline:row.pipeline,optimized:row.optimized,comparisons:[1,2,3,4].map((index,i)=>{
  const source=model.cases[i],native=row.calls[index],bytes=source.result.bytes;
  const full='0x'+Buffer.from(bytes).toString('hex');
  if(native.capture.frames[1].output.bytes!==full||native.capture.frames[0].lastCallReturnData.bytes!==full)throw Error('Source full heap/readback versus retained native bytes mismatch');
  return{call:index,sourceCase:source.name,bytes,length:bytes.length,logicalReference:source.result.ref??null,status:'match'};
 })}));
}
export function validateHeapReport(r,directory){
 const bindings=verifyHeapInputs('/workspace/vy5-dependencies-20261101');validateHeapModel(r.model);const prior=reference();
 if(r.schema!==1||r.fullProofGate!=='pending'||r.nativeExecution!=='historical-replay-only'||r.referenceSha256!==REF_SHA||!eq(r.inputHashes,bindings.inputHashes)||!eq(r.producerHashes,bindings.producerHashes)||r.runnerSha256!==bindings.runnerSha256||!eq(r.rows,links(r.model,prior)))throw Error('missing/stale heap report or false adequacy');
 const stdout=readFileSync(join(directory,'lean.stdout'),'utf8'),stderr=readFileSync(join(directory,'lean.stderr'),'utf8'),execution=JSON.parse(readFileSync(join(directory,'lean.execution.json')));
 if(stderr!==''||!eq(JSON.parse(stdout),r.model)||!eq(execution,{command:COMMAND,exit:0,stdoutSha256:sha(stdout),stderrSha256:sha(stderr),...bindings}))throw Error('missing/stale actual heap execution');
 return r;
}
export function runHeap(dependency,out){
 mkdirSync(out,{recursive:true});const bindings=verifyHeapInputs(dependency),run=spawnSync(COMMAND[0],COMMAND.slice(1),{cwd:dependency,env:{...process.env,LEAN_NUM_THREADS:'1'},encoding:'utf8'});
 writeFileSync(join(out,'lean.stdout'),run.stdout??'');writeFileSync(join(out,'lean.stderr'),run.stderr??'');writeFileSync(join(out,'lean.execution.json'),JSON.stringify({command:COMMAND,exit:run.status,stdoutSha256:sha(run.stdout??''),stderrSha256:sha(run.stderr??''),...bindings},null,2)+'\n');
 if(run.status!==0)throw Error('actual heap allocation driver failed');const model=validateHeapModel(JSON.parse(run.stdout)),prior=reference();
 const report={schema:1,...bindings,model,rows:links(model,prior),referenceSha256:REF_SHA,nativeExecution:'historical-replay-only',fullProofGate:'pending'};
 validateHeapReport(report,out);writeFileSync(join(out,'report.json'),JSON.stringify(report,null,2)+'\n');return report;
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)){const[,,dependency,out]=process.argv;const r=runHeap(dependency,out);console.log(JSON.stringify({sourceCases:r.model.cases.length,profiles:r.rows.length,readbackComparisons:r.rows.reduce((n,r)=>n+r.comparisons.length,0),nativeExecution:r.nativeExecution,fullProofGate:r.fullProofGate}));}
