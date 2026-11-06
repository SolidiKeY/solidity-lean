import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {resolve,join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {ROOT,sha} from './harness.mjs';
import {verifyDoWhileInputs} from './do-while-source.mjs';
const FROZEN={"Solidity/Yul/Composition/ModifierPostPhysical.lean": "0f986a048e8083d7ecd9a27ead0a0f8e0bbe31ca9f142a9e5ea211aacfdffa72", "tests/yul-composition/ModifierPostDriver.lean": "49eae9400196a8d86d7581aede157c862b40899bccbec7cd1c41680ec2afb981", "tests/yul-composition/modifier-post-expectations.json": "cbade738884e68d2e22f1bcf2b85c560f011bdbb2ce7ef6921c59c1f6ba2ab97", "tests/yul-composition/modifier-post-ledger.json": "ef1874a3813a358a9903ba0a05928aa026b34adf3a86f575ad1a376195f4fa28", "Solidity/Yul/Composition/ModifierPhysical.lean": "0d2ac8d35442a80f9a0787ee7bd3d9b25807c0a8475ee20489588cc3033f4206"};
const ORACLE='tests/yul-composition/modifier-post-expectations.json',LEDGER='tests/yul-composition/modifier-post-ledger.json',SELF='scripts/yul-composition/modifier-post-source.mjs';
const DEP='/workspace/vy5-dependencies-20261101';
const COMMAND=['/workspace/.setup/tools/lean-4.24.0-linux/bin/lake','-f','lakefile.vy5.toml','env','lean','-j1','--tstack=131072','--run','tests/yul-composition/ModifierPostDriver.lean'];
const read=n=>readFileSync(join(ROOT,n));
export function verifyModifierPostInputs(readOwn=read){
 verifyDoWhileInputs();
 for(const [name,hash]of Object.entries(FROZEN)){
  assert.equal(sha(readOwn(name)),hash,'stale owned body/oracle/ledger: '+name);
  if(name.endsWith('.lean'))assert.equal(sha(readFileSync(join(DEP,name))),hash,'stale actual private body: '+name);
 }
 assert.equal(JSON.parse(readOwn('tests/yul-composition/ledger.json')).modifierPostEvidence,LEDGER);
 return {...FROZEN,[SELF]:sha(readOwn(SELF))};
}
export function expectedModifierPostModel(){
 assert.equal(sha(read(ORACLE)),FROZEN[ORACLE],'stale independent oracle');
 const o=JSON.parse(read(ORACLE));
 const state=payload=>({raw:structuredClone(o.raw),next:2,object:{kind:'bytes',bytes:payload,length:payload.length},alias:{kind:'bytes',bytes:[170,187],length:2},frame:structuredClone(o.frame),logs:structuredClone(o.logs),events:structuredClone(o.events),clean:false});
 return {schema:1,engine:'actual-Source-modifier-postlude',nativeComparisons:0,fullProofGate:'pending',profiles:['legacy','viaIR'].map(pipeline=>({pipeline,cases:o.cases.map(c=>({name:c.name,inputLocals:structuredClone(c.inputLocals),before:state(c.payload),result:structuredClone(c.result),after:state(c.payload),physicalBefore:structuredClone(o.physical),physicalAfter:structuredClone(o.physical),outerRef:structuredClone(o.outerRef)}))}))};
}
export function validateModifierPostModel(model){
 assert.deepEqual(model,expectedModifierPostModel(),'wrong/missing/reordered full selected Source modifier-postlude observation');
 return {sourcePipelines:2,sourceCases:48,nativeComparisons:0,fullProofGate:'pending'};
}
export function validateModifierPostReport(report,directory,readEvidence=path=>readFileSync(path,'utf8')){
 const bindings=verifyModifierPostInputs();
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
 const summary=validateModifierPostModel(report.model);assert.deepEqual(report.summary,summary);
 return summary;
}
export function runModifierPost(out){
 const bindings=verifyModifierPostInputs();mkdirSync(out);
 const actual=spawnSync(COMMAND[0],COMMAND.slice(1),{cwd:DEP,env:{...process.env,LEAN_NUM_THREADS:'1'},encoding:'utf8'});
 writeFileSync(join(out,'lean.stdout'),actual.stdout??'');writeFileSync(join(out,'lean.stderr'),actual.stderr??'');writeFileSync(join(out,'lean.exit'),String(actual.status)+'\n');
 const receipt={command:COMMAND,dependency:DEP,bindings,exit:actual.status,stdoutSha256:sha(actual.stdout??''),stderrSha256:sha(actual.stderr??'')};writeFileSync(join(out,'execution.json'),JSON.stringify(receipt,null,2)+'\n');
 assert.equal(actual.status,0,'actual Source execution failed; raw evidence retained');
 const model=JSON.parse(actual.stdout);const summary=validateModifierPostModel(model);
 const report={...receipt,model,summary};writeFileSync(join(out,'report.json'),JSON.stringify(report,null,2)+'\n');validateModifierPostReport(report,out);return summary;
}
if(process.argv[1]===fileURLToPath(import.meta.url))console.log(JSON.stringify(runModifierPost(resolve(process.argv[2]))));
