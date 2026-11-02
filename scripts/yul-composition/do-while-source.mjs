import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {resolve,join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {spawnSync} from 'node:child_process';
import {ROOT,sha} from './harness.mjs';
import {verifyForInputs} from './for-source.mjs';
const FROZEN={"Solidity/Yul/Composition/DoWhilePhysical.lean": "9d1bdcbac3977798d888254f80dc36925aa71585930812991afb86fc573b3081", "tests/yul-composition/DoWhileDriver.lean": "031cce7142c34c77f634b8378df3aef79f1888f26e98ec1c4be895b6b80b2e4c", "tests/yul-composition/do-while-expectations.json": "c64e341c63c071b9e9eda28396ff60fbaed07a307fc3d912790ce03a19a46a2f", "tests/yul-composition/do-while-ledger.json": "389fbe32210c9afb2b62dd4acd42f4357d4bc164db97be8f59057e8821cac1ae"};
const ORACLE='tests/yul-composition/do-while-expectations.json',LEDGER='tests/yul-composition/do-while-ledger.json',SELF='scripts/yul-composition/do-while-source.mjs';
const DEP='/workspace/vy5-dependencies-20261101';
const COMMAND=['/workspace/.setup/tools/lean-4.24.0-linux/bin/lake','-f','lakefile.vy5.toml','env','lean','-j1','--tstack=131072','--run','tests/yul-composition/DoWhileDriver.lean'];
const read=n=>readFileSync(join(ROOT,n));
export function verifyDoWhileInputs(readOwn=read){
 verifyForInputs();
 for(const [name,hash]of Object.entries(FROZEN)){
  assert.equal(sha(readOwn(name)),hash,'stale owned body/oracle/ledger: '+name);
  if(name.endsWith('.lean'))assert.equal(sha(readFileSync(join(DEP,name))),hash,'stale actual private body: '+name);
 }
 assert.equal(JSON.parse(readOwn('tests/yul-composition/ledger.json')).doWhileEvidence,LEDGER);
 return {...FROZEN,[SELF]:sha(readOwn(SELF))};
}
export function expectedDoWhileModel(){
 assert.equal(sha(read(ORACLE)),FROZEN[ORACLE],'stale independent oracle');
 const o=JSON.parse(read(ORACLE));
 const state=payload=>({raw:structuredClone(o.raw),next:2,object:{kind:'bytes',bytes:payload,length:payload.length},alias:{kind:'bytes',bytes:[170,187],length:2},frame:structuredClone(o.frame),logs:structuredClone(o.logs),clean:false});
 return {schema:1,engine:'actual-Source-doWhile',nativeComparisons:0,fullProofGate:'pending',profiles:['legacy','viaIR'].map(pipeline=>({pipeline,cases:o.cases.map(c=>({name:c.name,inputLocals:structuredClone(c.inputLocals),before:state(c.payload),result:structuredClone(c.result),after:state(c.payload),physicalBefore:structuredClone(o.physical),physicalAfter:structuredClone(o.physical),outerRef:structuredClone(o.outerRef)}))}))};
}
export function validateDoWhileModel(model){
 assert.deepEqual(model,expectedDoWhileModel(),'wrong/missing/reordered full selected Source doWhile observation');
 return {sourcePipelines:2,sourceCases:50,nativeComparisons:0,fullProofGate:'pending'};
}
export function validateDoWhileReport(report,directory,readEvidence=path=>readFileSync(path,'utf8')){
 const bindings=verifyDoWhileInputs();
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
 const summary=validateDoWhileModel(report.model);assert.deepEqual(report.summary,summary);
 return summary;
}
export function runDoWhile(out){
 const bindings=verifyDoWhileInputs();mkdirSync(out);
 const actual=spawnSync(COMMAND[0],COMMAND.slice(1),{cwd:DEP,env:{...process.env,LEAN_NUM_THREADS:'1'},encoding:'utf8'});
 writeFileSync(join(out,'lean.stdout'),actual.stdout??'');writeFileSync(join(out,'lean.stderr'),actual.stderr??'');writeFileSync(join(out,'lean.exit'),String(actual.status)+'\n');
 const receipt={command:COMMAND,dependency:DEP,bindings,exit:actual.status,stdoutSha256:sha(actual.stdout??''),stderrSha256:sha(actual.stderr??'')};writeFileSync(join(out,'execution.json'),JSON.stringify(receipt,null,2)+'\n');
 assert.equal(actual.status,0,'actual Source execution failed; raw evidence retained');
 const model=JSON.parse(actual.stdout);const summary=validateDoWhileModel(model);
 const report={...receipt,model,summary};writeFileSync(join(out,'report.json'),JSON.stringify(report,null,2)+'\n');validateDoWhileReport(report,out);return summary;
}
if(process.argv[1]===fileURLToPath(import.meta.url))console.log(JSON.stringify(runDoWhile(resolve(process.argv[2]))));
