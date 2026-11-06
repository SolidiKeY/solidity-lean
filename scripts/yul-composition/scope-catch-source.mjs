import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {isDeepStrictEqual as eq} from 'node:util';
import {ROOT,sha} from './harness.mjs';
import {verifyHeapInputs,validateHeapReport} from './heap-catch-source.mjs';
const FROZEN={"Solidity/Yul/Composition/ScopeCatchPhysical.lean": "f25ff8289fce7d688c1b935171f3d801f936658b6a7082af81d4191c53e7fd14", "tests/yul-composition/ScopeCatchDriver.lean": "d90421f9db7a62672d112557f5459d90ee4a6d9a4223337bff28dde33c7d0ef3", "tests/yul-composition/scope-catch-component-ledger.json": "abde5587569754a65f01a2a761473ebf1241519f6c15b7277bbd0c007b75f294", "tests/yul-composition/scope-catch-expectations.json": "9d29db37c5790519810071ac610106eb9155ff21279bbee1aaa1c687882aaca7"};
const REF='/workspace/vy5-composition/heap-catch-20261101/readback-v1',REF_SHA='0986c09aaefc06b2c59f5b63fc1c9246d3c7e6c226fb716153b08855b19cb80f';
const COMMAND=['/workspace/.setup/tools/lean-4.24.0-linux/bin/lake','-f','lakefile.vy5.toml','env','lean','-j1','--tstack=131072','--run','tests/yul-composition/ScopeCatchDriver.lean'];
const SELF='scripts/yul-composition/scope-catch-source.mjs',LEDGER='tests/yul-composition/scope-catch-component-ledger.json',ORACLE='tests/yul-composition/scope-catch-expectations.json';
const read=f=>readFileSync(join(ROOT,f)),json=f=>JSON.parse(read(f));
export function verifyScopeInputs(dependency){
 verifyHeapInputs(dependency);
 for(const[file,hash]of Object.entries(FROZEN))if(sha(read(file))!==hash)throw Error('stale heap consumer/oracle/catalog: '+file);
 if(json('tests/yul-composition/ledger.json').scopeCatchComponentEvidence!==LEDGER)throw Error('missing selected heap catalog');
 const l=json(LEDGER);
 if(l.fullCoverage!==false||l.parentLedgerSha256!==sha(read('tests/yul-composition/heap-catch-component-ledger.json')))throw Error('false/stale heap coverage');
 for(const[file,hash]of Object.entries(l.sourceHashes))if(sha(readFileSync(join(dependency,file)))!==hash)throw Error('private heap consumer drift');
 for(const[file,hash]of Object.entries(l.producerHashes))if(sha(read(file))!==hash.main||sha(readFileSync(join(dependency,file)))!==hash.private)throw Error('actual Source heap producer drift');
 return {inputHashes:FROZEN,producerHashes:l.producerHashes,runnerSha256:sha(read(SELF))};
}
const object=bytes=>({kind:'bytes',bytes,length:bytes.length});
export function validateScopeModel(m){
 const e=json(ORACLE),ref=logicalIndex=>({kind:'memory',logicalIndex}),alias=object([170,187]),logs=[['1',[153]],['1',[85]]];
 const data=[null,[222,173],[],e.panicBytes,null,null],names=['success','revert','empty','panic','timeout','stuck'];
 const cases=names.map((name,i)=>({name,alias,logs,raw:e.inputCells,restored:ref(0),next:data[i]===null?1:2,object:data[i]===null?null:object(data[i]),result:i===0?{tag:'success',bytes:[190,239]}:i===4?{tag:'timeout'}:i===5?{tag:'stuck',reason:'sentinel'}:{tag:'scoped',ref:ref(1),bytes:data[i],length:data[i].length,inner:[ref(1),ref(0)]}}));
 const continuations=data.slice(1,4).map(bytes=>{const cells=e.cells.slice();cells[3]=String(1793+bytes.length+512);return{alias,allocated:object(bytes),cells,normal:true,clean:false,read:bytes,ref:ref(1)};});
 const halts=[{tag:'revert',bytes:[222,173]},{tag:'revert',bytes:[]},{tag:'revert',bytes:e.panicBytes},{tag:'timeout'},{tag:'stuck',reason:'scope-sentinel'}];
 const haltScopes=halts.map(outcome=>({outcome,restored:ref(0),raw:e.inputCells,logs:[['1',[119]],...logs]}));
 const wanted={schema:1,addressDomain:'logical-heap-index',outerTypes:['bytes.memory'],innerTypes:['bytes.memory','bytes.memory'],cases,continuations,haltScopes,wrongIndex:{bytes:[170,187],restored:ref(0)},wrongType:{outcome:{tag:'stuck',reason:'local type'},restored:ref(0)}};
 if(!eq(m,wanted))throw Error('missing/wrong actual scope/ref/bytes/caller restoration/halt/post-state/raw continuation');return m;
}
function reference(){
 const bytes=readFileSync(join(REF,'report.json'));if(sha(bytes)!==REF_SHA)throw Error('stale prior reference report');
 const r=JSON.parse(bytes);validateHeapReport(r,REF);return r;
}
function links(model,r){
 return r.rows.map(row=>({pipeline:row.pipeline,optimized:row.optimized,comparisons:row.comparisons.map((prior,i)=>{
  const source=model.cases[i],bytes=source.result.bytes;
  if(!eq(bytes,prior.bytes))throw Error('actual local read versus retained full heap/native bytes mismatch');
  return{...prior,typedScope:source.result.inner??null,restored:source.restored,status:'match'};
 })}));
}
export function validateScopeReport(r,directory){
 const bindings=verifyScopeInputs('/workspace/vy5-dependencies-20261101');validateScopeModel(r.model);const prior=reference();
 if(r.schema!==1||r.fullProofGate!=='pending'||r.nativeExecution!=='historical-replay-only'||r.referenceSha256!==REF_SHA||!eq(r.inputHashes,bindings.inputHashes)||!eq(r.producerHashes,bindings.producerHashes)||r.runnerSha256!==bindings.runnerSha256||!eq(r.rows,links(r.model,prior)))throw Error('missing/stale heap report or false adequacy');
 const stdout=readFileSync(join(directory,'lean.stdout'),'utf8'),stderr=readFileSync(join(directory,'lean.stderr'),'utf8'),execution=JSON.parse(readFileSync(join(directory,'lean.execution.json')));
 if(stderr!==''||!eq(JSON.parse(stdout),r.model)||!eq(execution,{command:COMMAND,exit:0,stdoutSha256:sha(stdout),stderrSha256:sha(stderr),...bindings}))throw Error('missing/stale actual heap execution');
 return r;
}
export function runScope(dependency,out){
 mkdirSync(out,{recursive:true});const bindings=verifyScopeInputs(dependency),run=spawnSync(COMMAND[0],COMMAND.slice(1),{cwd:dependency,env:{...process.env,LEAN_NUM_THREADS:'1'},encoding:'utf8'});
 writeFileSync(join(out,'lean.stdout'),run.stdout??'');writeFileSync(join(out,'lean.stderr'),run.stderr??'');writeFileSync(join(out,'lean.execution.json'),JSON.stringify({command:COMMAND,exit:run.status,stdoutSha256:sha(run.stdout??''),stderrSha256:sha(run.stderr??''),...bindings},null,2)+'\n');
 if(run.status!==0)throw Error('actual heap allocation driver failed');const model=validateScopeModel(JSON.parse(run.stdout)),prior=reference();
 const report={schema:1,...bindings,model,rows:links(model,prior),referenceSha256:REF_SHA,nativeExecution:'historical-replay-only',fullProofGate:'pending'};
 validateScopeReport(report,out);writeFileSync(join(out,'report.json'),JSON.stringify(report,null,2)+'\n');return report;
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)){const[,,dependency,out]=process.argv;const r=runScope(dependency,out);console.log(JSON.stringify({sourceCases:r.model.cases.length,profiles:r.rows.length,readbackComparisons:r.rows.reduce((n,r)=>n+r.comparisons.length,0),nativeExecution:r.nativeExecution,fullProofGate:r.fullProofGate}));}
