import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {isDeepStrictEqual as eq} from 'node:util';
import {ROOT,sha} from './harness.mjs';
import {verifyScopeInputs,validateScopeReport} from './scope-catch-source.mjs';
const FROZEN={"Solidity/Yul/Composition/RethrowPhysical.lean": "df5cbc9513fa5c3a8aac1d12c4cab7a47466ae9522231416d766026c69f1cd6e", "tests/yul-composition/RethrowDriver.lean": "e2cb8eda9def933015985f8bec9d664b4e3bb1712ab68aa14f4c472732051c95", "tests/yul-composition/rethrow-component-ledger.json": "90dbe6e783f9a8d0c33abc05e7070999e56d384e020bd79e07a27bc0c8182930", "tests/yul-composition/rethrow-expectations.json": "59c06243dda13b503e5d0e220f9977c77f7e7f5931b4e3e4912dfd98195054ae"};
const REF='/workspace/vy5-composition/scope-catch-20261101/readback-v1',REF_SHA='1550b4eef7b0343db9396893b302e9bba876ee589d17869c608965d400fc1262';
const COMMAND=['/workspace/.setup/tools/lean-4.24.0-linux/bin/lake','-f','lakefile.vy5.toml','env','lean','-j1','--tstack=131072','--run','tests/yul-composition/RethrowDriver.lean'];
const SELF='scripts/yul-composition/rethrow-source.mjs',LEDGER='tests/yul-composition/rethrow-component-ledger.json',ORACLE='tests/yul-composition/rethrow-expectations.json';
const read=f=>readFileSync(join(ROOT,f)),json=f=>JSON.parse(read(f));
export function verifyRethrowInputs(dependency){
 verifyScopeInputs(dependency);
 for(const[file,hash]of Object.entries(FROZEN))if(sha(read(file))!==hash)throw Error('stale heap consumer/oracle/catalog: '+file);
 if(json('tests/yul-composition/ledger.json').rethrowComponentEvidence!==LEDGER)throw Error('missing selected heap catalog');
 const l=json(LEDGER);
 if(l.fullCoverage!==false||l.parentLedgerSha256!==sha(read('tests/yul-composition/scope-catch-component-ledger.json')))throw Error('false/stale heap coverage');
 for(const[file,hash]of Object.entries(l.sourceHashes))if(sha(readFileSync(join(dependency,file)))!==hash)throw Error('private heap consumer drift');
 for(const[file,hash]of Object.entries(l.producerHashes))if(sha(read(file))!==hash.main||sha(readFileSync(join(dependency,file)))!==hash.private)throw Error('actual Source heap producer drift');
 return {inputHashes:FROZEN,producerHashes:l.producerHashes,runnerSha256:sha(read(SELF))};
}
const object=bytes=>({kind:'bytes',bytes,length:bytes.length});
export function validateRethrowModel(m){
 const e=json(ORACLE),ref=logicalIndex=>({kind:'memory',logicalIndex}),logs=[['1',[153]],['1',[85]]];
 const state=bytes=>({raw:e.inputCells,next:bytes===null?1:2,object:bytes===null?null:object(bytes),alias:object([170,187]),logs});
 const caught=[['revert',[222,173]],['empty',[]],['panic',e.panicBytes]],cases=[];
 for(const[name,bytes]of caught)for(const fuel of [0,1,32])cases.push({name,fuel,capturedScope:{tag:'scoped',ref:ref(1),bytes,inner:[ref(1),ref(0)]},before:state(bytes),result:fuel===0?{tag:'timeout'}:{tag:'revert',bytes},restoredBefore:ref(0),restoredAfter:ref(0),after:state(bytes)});
 for(const[name,result,fuel]of [['success',{tag:'success',bytes:[190,239]},0],['timeout',{tag:'timeout'},32],['stuck',{tag:'stuck',reason:'sentinel'},32]])cases.push({name,fuel,capturedScope:result,before:state(null),result,restoredBefore:ref(0),restoredAfter:ref(0),after:state(null)});
 const controls=[];
 for(const fuel of [0,1,32])for(const name of ['wrong-index','dangling'])controls.push({name,fuel,inside:[ref(name==='dangling'?2:1),ref(0)],result:fuel===0?{tag:'timeout'}:name==='wrong-index'?{tag:'revert',bytes:[170,187]}:{tag:'stuck',reason:'dangling memory reference'},restored:ref(0),before:state([222,173]),after:state([222,173])});
 const wanted={schema:1,addressDomain:'logical-heap-index',global:'inhabited-legacy-source-fixture; laws quantify arbitrary Glob',cases,controls};
 if(!eq(m,wanted))throw Error('missing/wrong actual rethrow full bytes/typed scope/fuel/halt/state/raw restoration');return m;
}
function reference(){
 const bytes=readFileSync(join(REF,'report.json'));if(sha(bytes)!==REF_SHA)throw Error('stale prior reference report');
 const r=JSON.parse(bytes);validateScopeReport(r,REF);return r;
}
// Historical caught-call evidence contains no execution of this NEW rethrow path.
function links(){return [];}
const REPLAY={profiles:4,orderedCalls:24,role:'prior-caught-call-regression-only; not new rethrow execution'};

export function validateRethrowReport(r,directory){
 const bindings=verifyRethrowInputs('/workspace/vy5-dependencies-20261101');validateRethrowModel(r.model);const prior=reference();
 if(r.schema!==1||r.fullProofGate!=='pending'||r.nativeExecution!=='historical-replay-only'||r.referenceSha256!==REF_SHA||!eq(r.historicalValidation,REPLAY)||!eq(r.nativeComparisons,[])||!eq(r.inputHashes,bindings.inputHashes)||!eq(r.producerHashes,bindings.producerHashes)||r.runnerSha256!==bindings.runnerSha256||!eq(r.rows,links(r.model,prior)))throw Error('missing/stale heap report or false adequacy');
 const stdout=readFileSync(join(directory,'lean.stdout'),'utf8'),stderr=readFileSync(join(directory,'lean.stderr'),'utf8'),execution=JSON.parse(readFileSync(join(directory,'lean.execution.json')));
 if(stderr!==''||!eq(JSON.parse(stdout),r.model)||!eq(execution,{command:COMMAND,exit:0,stdoutSha256:sha(stdout),stderrSha256:sha(stderr),...bindings}))throw Error('missing/stale actual heap execution');
 return r;
}
export function runRethrow(dependency,out){
 mkdirSync(out,{recursive:true});const bindings=verifyRethrowInputs(dependency),run=spawnSync(COMMAND[0],COMMAND.slice(1),{cwd:dependency,env:{...process.env,LEAN_NUM_THREADS:'1'},encoding:'utf8'});
 writeFileSync(join(out,'lean.stdout'),run.stdout??'');writeFileSync(join(out,'lean.stderr'),run.stderr??'');writeFileSync(join(out,'lean.execution.json'),JSON.stringify({command:COMMAND,exit:run.status,stdoutSha256:sha(run.stdout??''),stderrSha256:sha(run.stderr??''),...bindings},null,2)+'\n');
 if(run.status!==0)throw Error('actual heap allocation driver failed');const model=validateRethrowModel(JSON.parse(run.stdout)),prior=reference();
 const report={schema:1,...bindings,model,rows:links(model,prior),historicalValidation:REPLAY,nativeComparisons:[],referenceSha256:REF_SHA,nativeExecution:'historical-replay-only',fullProofGate:'pending'};
 validateRethrowReport(report,out);writeFileSync(join(out,'report.json'),JSON.stringify(report,null,2)+'\n');return report;
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)){const[,,dependency,out]=process.argv;const r=runRethrow(dependency,out);console.log(JSON.stringify({sourceCases:r.model.cases.length,controls:r.model.controls.length,historicalValidation:r.historicalValidation,nativeComparisons:r.nativeComparisons.length,nativeExecution:r.nativeExecution,fullProofGate:r.fullProofGate}));}
