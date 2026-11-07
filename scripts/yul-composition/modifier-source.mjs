import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {isDeepStrictEqual as eq} from 'node:util';
import {ROOT,sha} from './harness.mjs';
import {verifyRuntimeInputs,validateRuntimeReport} from './runtime-block-source.mjs';
const FROZEN={"Solidity/Yul/Composition/ModifierPhysical.lean": "0d2ac8d35442a80f9a0787ee7bd3d9b25807c0a8475ee20489588cc3033f4206", "tests/yul-composition/ModifierDriver.lean": "381792cbcab33fd5dbc70efae1a3dc054594a89de46e2f2bb4791a32193cd3f6", "tests/yul-composition/modifier-ledger.json": "edc22d229dc0cd0465556e2af8406e9d8b827d6ff984d5a8058e81953043420e", "tests/yul-composition/modifier-expectations.json": "a6082ab5dd3342f64d0dea33cfc72badb0117662cba03a9d5bbcf9cbea10f383"};
const REF='/workspace/vy5-composition/runtime-block-20261102/readback-v1',REF_SHA='f521d5fd5b5c27d2dd92222cd7340ca217c45660cb20eb0cf1cead67409fc76f';
const COMMAND=['/workspace/.setup/tools/lean-4.24.0-linux/bin/lake','-f','lakefile.vy5.toml','env','lean','-j1','--tstack=131072','--run','tests/yul-composition/ModifierDriver.lean'];
const SELF='scripts/yul-composition/modifier-source.mjs',LEDGER='tests/yul-composition/modifier-ledger.json',ORACLE='tests/yul-composition/modifier-expectations.json';
const read=f=>readFileSync(join(ROOT,f)),json=f=>JSON.parse(read(f));
export function verifyModifierInputs(dependency){
 verifyRuntimeInputs(dependency);
 for(const[file,hash]of Object.entries(FROZEN))if(sha(read(file))!==hash)throw Error('stale heap consumer/oracle/catalog: '+file);
 if(json('tests/yul-composition/ledger.json').modifierEvidence!==LEDGER)throw Error('missing selected heap catalog');
 const l=json(LEDGER);
 if(l.fullCoverage!==false||l.parentLedgerSha256!==sha(read('tests/yul-composition/runtime-block-ledger.json')))throw Error('false/stale heap coverage');
 for(const[file,hash]of Object.entries(l.sourceHashes))if(sha(readFileSync(join(dependency,file)))!==hash)throw Error('private heap consumer drift');
 for(const[file,hash]of Object.entries(l.producerHashes))if(sha(read(file))!==hash.main||sha(readFileSync(join(dependency,file)))!==hash.private)throw Error('actual Source heap producer drift');
 return {inputHashes:FROZEN,producerHashes:l.producerHashes,runnerSha256:sha(read(SELF))};
}
const object=bytes=>({kind:'bytes',bytes,length:bytes.length});
export function validateModifierModel(m){
 const e=json(ORACLE),ref=n=>({kind:'memory',logicalIndex:n}),saved={types:['bool'],bool:true,refs:[null,null]},installed={types:['bytes.memory','bytes.memory'],bool:null,refs:[ref(1),ref(0)]},alternate={types:['bytes.memory'],bool:null,refs:[ref(0),null]};
 const state=(bytes,frame=saved)=>({raw:e.inputCells,next:2,object:object(bytes),alias:object([170,187]),frame,logs:[['1',[85]]],clean:false});
 const names=['plain','modifier','internal','empty','panic','wrong-alias',...Array.from({length:8},(_,i)=>'fuel-'+i),'missing-modifier','modifier-parameters','missing-function','invalid-call-frame','placeholder-outside','invalid-placeholder-frame','alternate-saved-frame'];
 const messages=['modifier without a body','modifier parameters','function without a body','call frame','placeholder outside a modifier','placeholder frame'];
 const cases=names.map((name,i)=>{
  const bytes=i===3?[]:i===4?e.panicBytes:[222,173],frame=i===20?alternate:saved;
  const result=i>=6&&i<14?{tag:'timeout'}:i>=14&&i<20?{tag:'stuck',reason:messages[i-14]}:{tag:'revert',bytes:i===5?[170,187]:bytes};
  return{name,before:state(bytes,frame),result,after:state(bytes,frame)};
 });
 const directPlaceholder={before:state([222,173],installed),result:{tag:'revert',bytes:[222,173]},after:state([222,173],installed)};
 const wanted={schema:1,addressDomain:'logical-heap-index',scope:'selected-resolved-runtime-not-frontend-admission',pipelines:['legacy','viaIR'].map(pipeline=>({pipeline,cases,directPlaceholder}))};
 if(!eq(m,wanted))throw Error('missing/wrong actual modifier/function fullbytes/frame/heap/raw/journal control');return m;
}
const ORIGINAL='/workspace/vy5-composition/native-rethrow-20261101/original-v3/report.json',ORIGINAL_SHA='c0e8e6cd7f2f62865135b57ab395b3d256f3d0b474d20c17f88957e8d702f660';
function reference(){
 const bytes=readFileSync(join(REF,'report.json'));if(sha(bytes)!==REF_SHA)throw Error('stale prior reference report');
 const r=JSON.parse(bytes);validateRuntimeReport(r,REF);const original=readFileSync(ORIGINAL);if(sha(original)!==ORIGINAL_SHA)throw Error('stale original failed journal evidence');const o=JSON.parse(original);if(o.validation!=='mismatch'||!eq(o.rows.map(r=>r.errors.length),[0,0,0,5]))throw Error('original strict journal failure relabelled');return r;
}
// Historical caught-call evidence contains no execution of this NEW rethrow path.
function links(){return [];}
const REPLAY={profiles:4,orderedCalls:24,role:'prior-caught-call-regression-only; not new rethrow execution'};

export function validateModifierReport(r,directory){
 const bindings=verifyModifierInputs('/workspace/vy5-dependencies-20261101');validateModifierModel(r.model);const prior=reference();
 if(r.schema!==1||r.fullProofGate!=='pending'||r.nativeExecution!=='historical-replay-only'||r.referenceSha256!==REF_SHA||!eq(r.historicalValidation,REPLAY)||!eq(r.nativeComparisons,[])||!eq(r.inputHashes,bindings.inputHashes)||!eq(r.producerHashes,bindings.producerHashes)||r.runnerSha256!==bindings.runnerSha256||!eq(r.rows,links(r.model,prior)))throw Error('missing/stale heap report or false adequacy');
 const stdout=readFileSync(join(directory,'lean.stdout'),'utf8'),stderr=readFileSync(join(directory,'lean.stderr'),'utf8'),execution=JSON.parse(readFileSync(join(directory,'lean.execution.json')));
 if(stderr!==''||!eq(JSON.parse(stdout),r.model)||!eq(execution,{command:COMMAND,exit:0,stdoutSha256:sha(stdout),stderrSha256:sha(stderr),...bindings}))throw Error('missing/stale actual heap execution');
 return r;
}
export function runModifier(dependency,out){
 mkdirSync(out,{recursive:true});const bindings=verifyModifierInputs(dependency),run=spawnSync(COMMAND[0],COMMAND.slice(1),{cwd:dependency,env:{...process.env,LEAN_NUM_THREADS:'1'},encoding:'utf8'});
 writeFileSync(join(out,'lean.stdout'),run.stdout??'');writeFileSync(join(out,'lean.stderr'),run.stderr??'');writeFileSync(join(out,'lean.execution.json'),JSON.stringify({command:COMMAND,exit:run.status,stdoutSha256:sha(run.stdout??''),stderrSha256:sha(run.stderr??''),...bindings},null,2)+'\n');
 if(run.status!==0)throw Error('actual heap allocation driver failed');const model=validateModifierModel(JSON.parse(run.stdout)),prior=reference();
 const report={schema:1,...bindings,model,rows:links(model,prior),historicalValidation:REPLAY,nativeComparisons:[],referenceSha256:REF_SHA,nativeExecution:'historical-replay-only',fullProofGate:'pending'};
 validateModifierReport(report,out);writeFileSync(join(out,'report.json'),JSON.stringify(report,null,2)+'\n');return report;
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url)){const[,,dependency,out]=process.argv;const r=runModifier(dependency,out);console.log(JSON.stringify({sourcePipelines:r.model.pipelines.length,sourceCases:r.model.pipelines.reduce((n,p)=>n+p.cases.length,0),directPlaceholderControls:2,historicalValidation:r.historicalValidation,nativeComparisons:r.nativeComparisons.length,nativeExecution:r.nativeExecution,fullProofGate:r.fullProofGate}));}
