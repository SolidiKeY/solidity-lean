import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {resolve,join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {ROOT,sha} from './harness.mjs';
import {verifyModifierInputs} from './modifier-source.mjs';
import {verifyReturning} from './returning-source.mjs';
const FROZEN={"Solidity/Yul/Composition/UncheckedLoopPhysical.lean": "0bc137c872a67a2a91901106688e05b92ee6f615934adf446c2a7d683356ac7a", "tests/yul-composition/UncheckedLoopDriver.lean": "e19283b17ed1ca74118fe4f7725480c9cd5a82c18c9980cf878cfa0f2de82b0c", "tests/yul-composition/unchecked-loop-expectations.json": "f839b11d6b69573f7eeaa132dca2fc9e7979618f367f3ca055a47ae76edf9841", "tests/yul-composition/unchecked-loop-ledger.json": "d0f7ada9543d90c421858e56b377062d9ea2b151b5b93875db2c523f41b8430c"};
const ORACLE='tests/yul-composition/unchecked-loop-expectations.json',LEDGER='tests/yul-composition/unchecked-loop-ledger.json';
const DEP='/workspace/vy5-dependencies-20261101';
const COMMAND=['/workspace/.setup/tools/lean-4.24.0-linux/bin/lake','-f','lakefile.vy5.toml','env','lean','-j1','--tstack=131072','--run','tests/yul-composition/UncheckedLoopDriver.lean'];
const read=n=>readFileSync(join(ROOT,n));
export function verifyUncheckedInputs(readOwn=read){
 verifyModifierInputs(DEP);verifyReturning();
 for(const [name,hash]of Object.entries(FROZEN)){
  assert.equal(sha(readOwn(name)),hash,'stale owned body/oracle/ledger: '+name);
  if(name.endsWith('.lean'))assert.equal(sha(readFileSync(join(DEP,name))),hash,'stale actual private body: '+name);
 }
 assert.equal(JSON.parse(readOwn('tests/yul-composition/ledger.json')).uncheckedLoopEvidence,LEDGER);
 return FROZEN;
}
export function expectedUncheckedModel(){
 assert.equal(sha(read(ORACLE)),FROZEN[ORACLE],'stale independent oracle');
 const o=JSON.parse(read(ORACLE));
 const state=payload=>({raw:structuredClone(o.raw),next:2,object:{kind:'bytes',bytes:payload,length:payload.length},alias:{kind:'bytes',bytes:[170,187],length:2},frame:structuredClone(o.frame),logs:structuredClone(o.logs),clean:false});
 return {schema:1,engine:'actual-Source-evaluator',nativeComparisons:0,fullProofGate:'pending',profiles:['legacy','viaIR'].map(pipeline=>({pipeline,cases:o.cases.map(c=>({name:c.name,before:state(c.payload),result:c.result,after:state(c.payload),physicalBefore:structuredClone(o.physical),physicalAfter:structuredClone(o.physical),outerRef:structuredClone(o.outerRef)}))}))};
}
export function validateUncheckedModel(model){
 assert.deepEqual(model,expectedUncheckedModel(),'wrong/missing/reordered full selected Source observation');
 return {sourcePipelines:2,sourceCases:44,nativeComparisons:0,fullProofGate:'pending'};
}
export function validateUncheckedReport(report,directory,readEvidence=path=>readFileSync(path,'utf8')){
 const bindings=verifyUncheckedInputs();
 assert.deepEqual(report.bindings,bindings,'stale source identity');
 assert.deepEqual(report.command,COMMAND,'wrong command/horizon identity');
 assert.equal(report.dependency,DEP);assert.equal(report.exit,0);
 assert.deepEqual(Object.keys(report).sort(),['command','dependency','bindings','exit','stdoutSha256','stderrSha256','model','summary'].sort(),'malformed report fields');
 const receipt=JSON.parse(readEvidence(join(directory,'execution.json')));
 assert.deepEqual(receipt,{command:report.command,dependency:report.dependency,bindings:report.bindings,exit:report.exit,stdoutSha256:report.stdoutSha256,stderrSha256:report.stderrSha256},'missing/wrong actual execution receipt');
 const stdout=readEvidence(join(directory,'lean.stdout')),stderr=readEvidence(join(directory,'lean.stderr'));
 assert.equal(sha(stdout),report.stdoutSha256);assert.equal(sha(stderr),report.stderrSha256);
 assert.equal(readEvidence(join(directory,'lean.exit')),'0\n');
 assert.deepEqual(JSON.parse(stdout),report.model);
 const summary=validateUncheckedModel(report.model);assert.deepEqual(report.summary,summary);
 return summary;
}
export function runUnchecked(out){
 const bindings=verifyUncheckedInputs();mkdirSync(out); // fail closed on reused evidence prefix
 const actual=spawnSync(COMMAND[0],COMMAND.slice(1),{cwd:DEP,env:{...process.env,LEAN_NUM_THREADS:'1'},encoding:'utf8'});
 writeFileSync(join(out,'lean.stdout'),actual.stdout??'');writeFileSync(join(out,'lean.stderr'),actual.stderr??'');writeFileSync(join(out,'lean.exit'),String(actual.status)+'\n');
 const receipt={command:COMMAND,dependency:DEP,bindings,exit:actual.status,stdoutSha256:sha(actual.stdout??''),stderrSha256:sha(actual.stderr??'')};writeFileSync(join(out,'execution.json'),JSON.stringify(receipt,null,2)+'\n');
 assert.equal(actual.status,0,'actual Source execution failed; raw evidence retained');
 const model=JSON.parse(actual.stdout);const summary=validateUncheckedModel(model);
 const report={...receipt,model,summary};writeFileSync(join(out,'report.json'),JSON.stringify(report,null,2)+'\n');validateUncheckedReport(report,out);return summary;
}
if(process.argv[1]===fileURLToPath(import.meta.url))console.log(JSON.stringify(runUnchecked(resolve(process.argv[2]))));
