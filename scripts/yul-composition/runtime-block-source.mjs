import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {isDeepStrictEqual as eq} from 'node:util';
import {ROOT,sha} from './harness.mjs';
import {verifyRethrowInputs,validateRethrowReport} from './rethrow-source.mjs';
const FROZEN={"Solidity/Yul/Composition/RuntimeBlockPhysical.lean": "44dd6c22bfcb8a88d620605fe4a1ac67c595740899850e87b2f8f02e0901caf9", "tests/yul-composition/RuntimeBlockDriver.lean": "83dd328e8c021ce25f8300ea8df95d0d63b54745085ca884e1e10478d0a65270", "tests/yul-composition/runtime-block-ledger.json": "2eccc6312e612e0a626f8f62bc1d8f72f066cc4f1107ed55b60ee7d310d05886", "tests/yul-composition/runtime-block-expectations.json": "c5b85b810b668c311aa9ff604f3ebac22eaaa4c1744e495a40287113968fc7ff"};
const REF='/workspace/vy5-composition/rethrow-20261101/readback-v1',REF_SHA='3d3e0cce34d236950c7e26beb9d90030372dbf402870ee3f02e9980fa40f3dda';
const COMMAND=['/workspace/.setup/tools/lean-4.24.0-linux/bin/lake','-f','lakefile.vy5.toml','env','lean','-j1','--tstack=131072','--run','tests/yul-composition/RuntimeBlockDriver.lean'];
const SELF='scripts/yul-composition/runtime-block-source.mjs',LEDGER='tests/yul-composition/runtime-block-ledger.json',ORACLE='tests/yul-composition/runtime-block-expectations.json';
const read=f=>readFileSync(join(ROOT,f)),json=f=>JSON.parse(read(f));
export function verifyRuntimeInputs(dependency){
 verifyRethrowInputs(dependency);
 for(const[file,hash]of Object.entries(FROZEN))if(sha(read(file))!==hash)throw Error('stale heap consumer/oracle/catalog: '+file);
 if(json('tests/yul-composition/ledger.json').runtimeBlockEvidence!==LEDGER)throw Error('missing selected heap catalog');
 const l=json(LEDGER);
 if(l.fullCoverage!==false||l.parentLedgerSha256!==sha(read('tests/yul-composition/rethrow-component-ledger.json')))throw Error('false/stale heap coverage');
 for(const[file,hash]of Object.entries(l.sourceHashes))if(sha(readFileSync(join(dependency,file)))!==hash)throw Error('private heap consumer drift');
 for(const[file,hash]of Object.entries(l.producerHashes))if(sha(read(file))!==hash.main||sha(readFileSync(join(dependency,file)))!==hash.private)throw Error('actual Source heap producer drift');
 return {inputHashes:FROZEN,producerHashes:l.producerHashes,runnerSha256:sha(read(SELF))};
}
const object=bytes=>({kind:'bytes',bytes,length:bytes.length});
export function validateRuntimeModel(m){
 const e=json(ORACLE),ref=logicalIndex=>({kind:'memory',logicalIndex}),logs=[['1',[85]]];
 const state=(bytes,prefix=false)=>({raw:e.inputCells,next:bytes===null?1:2,object:bytes===null?null:object(bytes),alias:object([170,187]),logs:prefix?[['1',[153]],...logs]:logs,clean:false});
 const names=['dead-0','dead-3','dead-4','dead-32','empty','panic','success','timeout','stuck','external-revert','external-short','stuck-prefix'];
 const data=[[222,173],[222,173],[222,173],[222,173],[],e.panicBytes,null,null,null,[222,173],[],null];
 const result=names.map((n,i)=>[0,1,7].includes(i)?{tag:'timeout'}:i===6?{tag:'success',bytes:[190,239]}:i===8?{tag:'stuck',reason:'sentinel'}:i===11?{tag:'stuck',reason:'prefix'}:{tag:'revert',bytes:data[i]});
 const wanted={schema:1,addressDomain:'logical-heap-index',input:state(null),declared:{refs:[ref(1),ref(1),ref(0)],heap:object([222,173])},cases:names.map((name,i)=>({name,result:result[i],restored:ref(0),after:state(data[i],i===11)})),wrongAlias:{result:{tag:'revert',bytes:[170,187]},restored:ref(0),after:state([222,173])}};
 if(!eq(m,wanted))throw Error('missing/wrong actual Source runtime declaration/block/ABI/fullbytes/raw/heap/prefix outcome');return m;
}
const ORIGINAL='/workspace/vy5-composition/native-rethrow-20261101/original-v3/report.json',ORIGINAL_SHA='c0e8e6cd7f2f62865135b57ab395b3d256f3d0b474d20c17f88957e8d702f660';
function reference(){
 const bytes=readFileSync(join(REF,'report.json'));if(sha(bytes)!==REF_SHA)throw Error('stale prior reference report');
 const r=JSON.parse(bytes);validateRethrowReport(r,REF);const original=readFileSync(ORIGINAL);if(sha(original)!==ORIGINAL_SHA)throw Error('stale original failed journal evidence');const o=JSON.parse(original);if(o.validation!=='mismatch'||!eq(o.rows.map(r=>r.errors.length),[0,0,0,5]))throw Error('original strict journal failure relabelled');return r;
}
// Historical caught-call evidence contains no execution of this NEW rethrow path.
function links(){return [];}
const REPLAY={profiles:4,orderedCalls:24,role:'prior-caught-call-regression-only; not new rethrow execution'};

export function validateRuntimeReport(r,directory){
 const bindings=verifyRuntimeInputs('/workspace/vy5-dependencies-20261101');validateRuntimeModel(r.model);const prior=reference();
 if(r.schema!==1||r.fullProofGate!=='pending'||r.nativeExecution!=='historical-replay-only'||r.referenceSha256!==REF_SHA||!eq(r.historicalValidation,REPLAY)||!eq(r.nativeComparisons,[])||!eq(r.inputHashes,bindings.inputHashes)||!eq(r.producerHashes,bindings.producerHashes)||r.runnerSha256!==bindings.runnerSha256||!eq(r.rows,links(r.model,prior)))throw Error('missing/stale heap report or false adequacy');
 const stdout=readFileSync(join(directory,'lean.stdout'),'utf8'),stderr=readFileSync(join(directory,'lean.stderr'),'utf8'),execution=JSON.parse(readFileSync(join(directory,'lean.execution.json')));
 if(stderr!==''||!eq(JSON.parse(stdout),r.model)||!eq(execution,{command:COMMAND,exit:0,stdoutSha256:sha(stdout),stderrSha256:sha(stderr),...bindings}))throw Error('missing/stale actual heap execution');
 return r;
}
export function runRuntime(dependency,out){
 mkdirSync(out,{recursive:true});const bindings=verifyRuntimeInputs(dependency),run=spawnSync(COMMAND[0],COMMAND.slice(1),{cwd:dependency,env:{...process.env,LEAN_NUM_THREADS:'1'},encoding:'utf8'});
 writeFileSync(join(out,'lean.stdout'),run.stdout??'');writeFileSync(join(out,'lean.stderr'),run.stderr??'');writeFileSync(join(out,'lean.execution.json'),JSON.stringify({command:COMMAND,exit:run.status,stdoutSha256:sha(run.stdout??''),stderrSha256:sha(run.stderr??''),...bindings},null,2)+'\n');
 if(run.status!==0)throw Error('actual heap allocation driver failed');const model=validateRuntimeModel(JSON.parse(run.stdout)),prior=reference();
 const report={schema:1,...bindings,model,rows:links(model,prior),historicalValidation:REPLAY,nativeComparisons:[],referenceSha256:REF_SHA,nativeExecution:'historical-replay-only',fullProofGate:'pending'};
 validateRuntimeReport(report,out);writeFileSync(join(out,'report.json'),JSON.stringify(report,null,2)+'\n');return report;
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)){const[,,dependency,out]=process.argv;const r=runRuntime(dependency,out);console.log(JSON.stringify({sourceCases:r.model.cases.length,wrongAliasControl:true,historicalValidation:r.historicalValidation,nativeComparisons:r.nativeComparisons.length,nativeExecution:r.nativeExecution,fullProofGate:r.fullProofGate}));}
