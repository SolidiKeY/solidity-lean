import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {resolve,join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {ROOT,sha} from './harness.mjs';
import {verifyUncheckedInputs} from './unchecked-loop-source.mjs';
const FROZEN={"Solidity/Yul/Composition/ForPhysical.lean": "f918d88aaeb916a7138ba318f8ae96d804d4bd8d317d694f6b48d9425fcaf0ed", "tests/yul-composition/ForDriver.lean": "f9043c18df53d679b23f8d46e2cbbd9f5b27ab26b22aabf14e3d96f19975d32e", "tests/yul-composition/for-expectations.json": "abf3b3f0e5ad4e3e0a34357027d01eac03951997a1c7a0d53697a2c0a17fa15c", "tests/yul-composition/for-ledger.json": "a81c6a5520ec9cfd5ed338815e0588ceba0a895d912d937df97697ed209d5bba"};
const ORACLE='tests/yul-composition/for-expectations.json',LEDGER='tests/yul-composition/for-ledger.json',SELF='scripts/yul-composition/for-source.mjs';
const DEP='/workspace/vy5-dependencies-20261101';
const COMMAND=['/workspace/.setup/tools/lean-4.24.0-linux/bin/lake','-f','lakefile.vy5.toml','env','lean','-j1','--tstack=131072','--run','tests/yul-composition/ForDriver.lean'];
const read=n=>readFileSync(join(ROOT,n));
export function verifyForInputs(readOwn=read){
 verifyUncheckedInputs();
 for(const [name,hash]of Object.entries(FROZEN)){
  assert.equal(sha(readOwn(name)),hash,'stale owned body/oracle/ledger: '+name);
  if(name.endsWith('.lean'))assert.equal(sha(readFileSync(join(DEP,name))),hash,'stale actual private body: '+name);
 }
 assert.equal(JSON.parse(readOwn('tests/yul-composition/ledger.json')).forEvidence,LEDGER);
 return {...FROZEN,[SELF]:sha(readOwn(SELF))};
}
export function expectedForModel(){
 assert.equal(sha(read(ORACLE)),FROZEN[ORACLE],'stale independent oracle');
 const o=JSON.parse(read(ORACLE));
 const state=payload=>({raw:structuredClone(o.raw),next:2,object:{kind:'bytes',bytes:payload,length:payload.length},alias:{kind:'bytes',bytes:[170,187],length:2},frame:structuredClone(o.frame),logs:structuredClone(o.logs),clean:false});
 return {schema:1,engine:'actual-Source-forLoop',nativeComparisons:0,fullProofGate:'pending',profiles:['legacy','viaIR'].map(pipeline=>({pipeline,cases:o.cases.map(c=>({name:c.name,inputLocals:structuredClone(c.inputLocals),before:state(c.payload),result:structuredClone(c.result),after:state(c.payload),physicalBefore:structuredClone(o.physical),physicalAfter:structuredClone(o.physical),outerRef:structuredClone(o.outerRef)}))}))};
}
export function validateForModel(model){
 assert.deepEqual(model,expectedForModel(),'wrong/missing/reordered full selected Source for-loop observation');
 return {sourcePipelines:2,sourceCases:56,nativeComparisons:0,fullProofGate:'pending'};
}
export function validateForReport(report,directory,readEvidence=path=>readFileSync(path,'utf8')){
 const bindings=verifyForInputs();
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
 const summary=validateForModel(report.model);assert.deepEqual(report.summary,summary);
 return summary;
}
export function runFor(out){
 const bindings=verifyForInputs();mkdirSync(out);
 const actual=spawnSync(COMMAND[0],COMMAND.slice(1),{cwd:DEP,env:{...process.env,LEAN_NUM_THREADS:'1'},encoding:'utf8'});
 writeFileSync(join(out,'lean.stdout'),actual.stdout??'');writeFileSync(join(out,'lean.stderr'),actual.stderr??'');writeFileSync(join(out,'lean.exit'),String(actual.status)+'\n');
 const receipt={command:COMMAND,dependency:DEP,bindings,exit:actual.status,stdoutSha256:sha(actual.stdout??''),stderrSha256:sha(actual.stderr??'')};writeFileSync(join(out,'execution.json'),JSON.stringify(receipt,null,2)+'\n');
 assert.equal(actual.status,0,'actual Source execution failed; raw evidence retained');
 const model=JSON.parse(actual.stdout);const summary=validateForModel(model);
 const report={...receipt,model,summary};writeFileSync(join(out,'report.json'),JSON.stringify(report,null,2)+'\n');validateForReport(report,out);return summary;
}
if(process.argv[1]===fileURLToPath(import.meta.url))console.log(JSON.stringify(runFor(resolve(process.argv[2]))));
