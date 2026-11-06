import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {resolve,join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {ROOT,sha} from './harness.mjs';
import {verifyModifierPostInputs} from './modifier-post-source.mjs';
const FROZEN={"Solidity/Yul/Composition/NestedModifierPhysical.lean": "251a32dad40949f69dc0d9e79df4da875c1489bf64ca1161b5afa3bd026b2e6c", "tests/yul-composition/NestedModifierDriver.lean": "5d4f9a0ba602b5c28d31e1d7f747fd6ec2597eb77b76438dfe871d40b1a0d0b8", "tests/yul-composition/nested-modifier-expectations.json": "c8c5498711d3ec31a5ffca734a9cb2772c15fac50a77d8a2408c85dfdf736371", "tests/yul-composition/nested-modifier-ledger.json": "e0df24189782bf0f3add1bccb7246ab358da5f49dcab946641564bfff9226c35"};
const ORACLE='tests/yul-composition/nested-modifier-expectations.json',LEDGER='tests/yul-composition/nested-modifier-ledger.json',SELF='scripts/yul-composition/nested-modifier-source.mjs';
const DEP='/workspace/vy5-dependencies-20261101';
const COMMAND=['/workspace/.setup/tools/lean-4.24.0-linux/bin/lake','-f','lakefile.vy5.toml','env','lean','-j1','--tstack=131072','--run','tests/yul-composition/NestedModifierDriver.lean'];
const read=n=>readFileSync(join(ROOT,n));
export function verifyNestedModifierInputs(readOwn=read){
 verifyModifierPostInputs();
 for(const [name,hash]of Object.entries(FROZEN)){
  assert.equal(sha(readOwn(name)),hash,'stale owned body/oracle/ledger: '+name);
  if(name.endsWith('.lean'))assert.equal(sha(readFileSync(join(DEP,name))),hash,'stale actual private body: '+name);
 }
 assert.equal(JSON.parse(readOwn('tests/yul-composition/ledger.json')).nestedModifierEvidence,LEDGER);
 return {...FROZEN,[SELF]:sha(readOwn(SELF))};
}
export function expectedNestedModifierModel(){
 assert.equal(sha(read(ORACLE)),FROZEN[ORACLE],'stale independent oracle');
 const o=JSON.parse(read(ORACLE));
 const state=payload=>({raw:structuredClone(o.raw),next:2,object:{kind:'bytes',bytes:payload,length:payload.length},alias:{kind:'bytes',bytes:[170,187],length:2},frame:structuredClone(o.frame),logs:structuredClone(o.logs),events:structuredClone(o.events),clean:false});
 return {schema:1,engine:'actual-Source-nested-modifier',nativeComparisons:0,fullProofGate:'pending',profiles:['legacy','viaIR'].map(pipeline=>({pipeline,cases:o.cases.map(c=>({name:c.name,inputLocals:structuredClone(c.inputLocals),before:state(c.payload),result:structuredClone(c.result),after:state(c.payload),physicalBefore:structuredClone(o.physical),physicalAfter:structuredClone(o.physical),outerRef:structuredClone(o.outerRef)}))}))};
}
export function validateNestedModifierModel(model){
 assert.deepEqual(model,expectedNestedModifierModel(),'wrong/missing/reordered full selected Source nested modifier observation');
 return {sourcePipelines:2,sourceCases:78,nativeComparisons:0,fullProofGate:'pending'};
}
export function validateNestedModifierReport(report,directory,readEvidence=path=>readFileSync(path,'utf8')){
 const bindings=verifyNestedModifierInputs();
 assert.deepEqual(report.bindings,bindings,'stale source/runner identity');
 assert.deepEqual(report.command,COMMAND,'wrong command/horizon identity');
 assert.equal(report.dependency,DEP);assert.equal(report.exit,0);
 assert.deepEqual(Object.keys(report).sort(),['command','dependency','bindings','exit','stdoutSha256','stderrSha256','model','summary'].sort(),'malformed report fields');
 const receipt=JSON.parse(readEvidence(join(directory,'execution.json')));
 assert.deepEqual(receipt,{command:report.command,dependency:report.dependency,bindings:report.bindings,exit:report.exit,stdoutSha256:report.stdoutSha256,stderrSha256:report.stderrSha256},'missing/wrong actual execution receipt');
 const stdout=readEvidence(join(directory,'lean.stdout')),stderr=readEvidence(join(directory,'lean.stderr'));
 assert.equal(sha(stdout),report.stdoutSha256);assert.equal(sha(stderr),report.stderrSha256);
 assert.equal(readEvidence(join(directory,'lean.exit')),'0\n');
 assert.deepEqual(JSON.parse(stdout),report.model);
 const summary=validateNestedModifierModel(report.model);assert.deepEqual(report.summary,summary);
 return summary;
}
export function runNestedModifier(out){
 const bindings=verifyNestedModifierInputs();mkdirSync(out);
 const actual=spawnSync(COMMAND[0],COMMAND.slice(1),{cwd:DEP,env:{...process.env,LEAN_NUM_THREADS:'1'},encoding:'utf8'});
 writeFileSync(join(out,'lean.stdout'),actual.stdout??'');writeFileSync(join(out,'lean.stderr'),actual.stderr??'');writeFileSync(join(out,'lean.exit'),String(actual.status)+'\n');
 const receipt={command:COMMAND,dependency:DEP,bindings,exit:actual.status,stdoutSha256:sha(actual.stdout??''),stderrSha256:sha(actual.stderr??'')};writeFileSync(join(out,'execution.json'),JSON.stringify(receipt,null,2)+'\n');
 assert.equal(actual.status,0,'actual Source execution failed; raw evidence retained');
 const model=JSON.parse(actual.stdout);const summary=validateNestedModifierModel(model);
 const report={...receipt,model,summary};writeFileSync(join(out,'report.json'),JSON.stringify(report,null,2)+'\n');validateNestedModifierReport(report,out);return summary;
}
if(process.argv[1]===fileURLToPath(import.meta.url))console.log(JSON.stringify(runNestedModifier(resolve(process.argv[2]))));
