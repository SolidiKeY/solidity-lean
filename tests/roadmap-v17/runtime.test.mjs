import {execFileSync} from 'node:child_process';
import {test} from 'node:test';
import {strict as assert} from 'node:assert';
import {readFileSync,mkdtempSync,writeFileSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {createHash} from 'node:crypto';
import {checkCompiler,sameInputs,reportBinding,verifyOutputs,checkoutStatus,VERSION} from '../../scripts/roadmap-v17-runtime.mjs';
const sha='6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390';
const good={sha256:sha,version:VERSION,bytes:10798266};
test('approved identity and changed/missing compiler controls',()=>{
 checkCompiler(good);
 for(const bad of [{...good,sha256:'0'.repeat(64)},{...good,version:'0.8.34'},{...good,bytes:0},{}])assert.throws(()=>checkCompiler(bad));
});
test('whole runtime/source/revision equality controls',()=>{
 const input={revision:'a',files:{source:'x',runtime:'y'},compiler:good};sameInputs(input,structuredClone(input));
 for(const bad of [{...input,revision:'b'},{...input,files:{source:'changed',runtime:'y'}},{...input,compiler:null}])assert.throws(()=>sameInputs(input,bad));
});
test('historical actual640 report shape baseline is never current evidence',()=>{
 const report=JSON.parse(readFileSync('/workspace/scratch/v17-recovery/generated-seed-0-compatible.json'));
 const m=report.metadata,files={};
 for(const [key,path] of Object.entries({runnerSha256:'scripts/evm-reference/generated.mjs',replaySha256:'scripts/evm-reference/replay.mjs',lockSha256:'scripts/evm-reference/package-lock.json',generatorBinarySha256:'.lake/build/bin/solcases',driverSha256:'SolCases.lean',generatorSha256:'Solidity/Tools/SolCases.lean'}))files[path]=m[key];
 const inputs={revision:m.checkoutCommit,compiler:good,leanVersion:m.leanVersion,lakeVersion:m.lakeVersion,files};
 reportBinding(report,inputs); // Schema baseline only, no actual snapshot supplied.
 assert.throws(()=>reportBinding(report,{...inputs,revision:'current'}));
 for(const mutate of [r=>r.records.pop(),r=>r.metadata.compilerSha256='bad',r=>r.metadata.lockSha256='bad',r=>r.summary.agree=639,r=>r.records[0].variants.pop(),r=>r.records[0].variants.reverse(),r=>r.records[0].variants[1]=r.records[0].variants[0],r=>r.records[0].record.index=true,r=>r.records[0].variants[0].status='blocked',r=>r.records[0].variants[0].runtimeCode='00',r=>r.records[0].variants[0].runtimeCode+='zz',r=>r.records[0].variants[0].runtimeCode+='0']){
  const bad=structuredClone(report);mutate(bad);assert.throws(()=>reportBinding(bad,inputs));
 }
});

test('actual retained observation corruption is refused by existing consumer',()=>{
 const report=JSON.parse(readFileSync('/workspace/scratch/v17-recovery/generated-seed-0-compatible.json'));
 report.records[0].variants[0].run.returnData='0x01';
 assert.throws(()=>execFileSync(process.execPath,['scripts/roadmap-v17-compare.mjs'],{input:JSON.stringify(report),timeout:60000,maxBuffer:16*1024*1024,stdio:['pipe','pipe','pipe']}));
});

test('native manifest parser rejects missing duplicate corrupt omitted outputs and failed phases',()=>{
 const out=mkdtempSync(tmpdir()+'/v17-output-control-');
 const hash=b=>createHash('sha256').update(b).digest('hex');
 try{
  const files={'inputs-after.json':'{}','inputs-before.json':'{}','report.json':'{}'};
  files['runtime-outcome.json']=JSON.stringify({commandExit:0,validationExit:0,postInputExit:0,phaseErrors:[],reportSha256:hash('{}')});
  const manifest={schema:1,files:{}};
  for(const [name,bytes] of Object.entries(files)){writeFileSync(out+'/'+name,bytes);manifest.files[name]=hash(bytes);}
  const log='V17_RUNTIME_OUTPUTS '+JSON.stringify(manifest)+'\n';verifyOutputs(log,out);
  assert.throws(()=>verifyOutputs('V17_RUNTIME_OUTPUTS {',out));writeFileSync(out+'/extra','x');assert.throws(()=>verifyOutputs(log,out));rmSync(out+'/extra');assert.throws(()=>verifyOutputs('',out));assert.throws(()=>verifyOutputs(log+log,out));
  writeFileSync(out+'/report.json','corrupted');assert.throws(()=>verifyOutputs(log,out));writeFileSync(out+'/report.json','{}');
  const missing=structuredClone(manifest);delete missing.files['inputs-after.json'];assert.throws(()=>verifyOutputs('V17_RUNTIME_OUTPUTS '+JSON.stringify(missing),out));
  const failed=JSON.parse(files['runtime-outcome.json']);failed.commandExit=124;const raw=JSON.stringify(failed);writeFileSync(out+'/runtime-outcome.json',raw);manifest.files['runtime-outcome.json']=hash(raw);assert.throws(()=>verifyOutputs('V17_RUNTIME_OUTPUTS '+JSON.stringify(manifest),out));
 }finally{rmSync(out,{recursive:true});}
});

test('only the exact original serial configuration is an admitted temporary input',()=>{
 checkoutStatus('',null,'expected');checkoutStatus('?? roadmap-v17-runtime.lakefile.toml','expected','expected');
 for(const status of ['?? other','M lakefile.toml','?? roadmap-v17-runtime.lakefile.toml\n?? other'])assert.throws(()=>checkoutStatus(status,'expected','expected'));
 assert.throws(()=>checkoutStatus('?? roadmap-v17-runtime.lakefile.toml','changed','expected'));
});
