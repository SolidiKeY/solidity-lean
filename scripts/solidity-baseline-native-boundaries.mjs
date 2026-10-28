#!/usr/bin/env node
// Additional refusal controls via the unchanged existing production adapters.
import {readFileSync,writeFileSync,mkdirSync,existsSync} from 'node:fs';
import {resolve,join} from 'node:path';
import {createHash} from 'node:crypto';
import {runTool} from './test-solidity.mjs';
const base=resolve(process.env.BASELINE_NATIVE_OUT??'tests/upstream/baseline-20261028/native-cache');
const prior=resolve('tests/upstream/baseline-20261028/probes/rechecked');
const sha=x=>createHash('sha256').update(x).digest('hex');
const fnv=b=>{let h=0xcbf29ce484222325n;for(const v of b)h=BigInt.asUintN(64,(h^BigInt(v))*0x100000001b3n);return '0x'+h.toString(16);};
const records=[];
for(const pipeline of ['legacy','viaIR']){
 for(const mutation of ['compiler-digest','pragma-record']){
  const job=join(base,'boundaries',mutation,pipeline);if(existsSync(job))throw Error('no overwrite');mkdirSync(job,{recursive:true});
  const parent=join(base,'runs','ScalarMatrixValid',pipeline,'source.ast.json'),fixture=join(job,mutation+'.ast.json'),file=join(job,'Provenance.lean');
  const changed=JSON.parse(readFileSync(parent));
  if(mutation==='compiler-digest')changed.header.compilerSha256='0'.repeat(64);else changed.header.acceptedPragmas=[['solidity','>=','0.9','.0']];
  writeFileSync(fixture,JSON.stringify(changed,null,2)+'\n');
  writeFileSync(file,`import Solidity.Frontend.Import\nsolc_import ${JSON.stringify(fixture)} hash ${fnv(readFileSync(fixture))} as Invalid.«ScalarMatrixValid» testing entrypoints\n`);
  let output='',tool={exitCode:0,timedOut:false},start=performance.now();const args=['--quiet','--no-build','lean',file,'--','--tstack=131072','-j1'];
  try{output=runTool('lake',args,120000);}catch(e){output=e.message;tool=e.tool??{exitCode:null};}
  writeFileSync(join(job,'native.log'),output);records.push({control:mutation,pipeline,fixture,fixtureSha256:sha(readFileSync(fixture)),command:['lake',...args],...tool,elapsedMs:performance.now()-start,log:join(job,'native.log'),logSha256:sha(Buffer.from(output))});
  const wanted=mutation==='compiler-digest'?'compiler binary provenance does not match its exact pin':'recorded pragmas disagree with the source AST';
  if(tool.exitCode!==1||tool.timedOut||!output.includes(wanted))throw Error('not the intended production provenance refusal');
 }
 const job=join(base,'boundaries','internal-entry',pipeline);if(existsSync(job))throw Error('no overwrite');mkdirSync(job,{recursive:true});
 const fixture=join(base,'runs','NativePositive',pipeline,'source.ast.json'),input=join(job,'jobs.json'),out=join(job,'runtime.json'),file=join(job,'Entry.lean');
 const jobs=[{path:'native-diagnostic/internal-entry-refusal',pipeline,requiredPipelines:['legacy','viaIR'],fixture,contract:'NativePositive',vectors:[{signature:'checkedHelper(uint8)',args:['1'],expected:['2'],failure:false,revertBytes:[]}]}];
 writeFileSync(input,JSON.stringify(jobs,null,2)+'\n');writeFileSync(file,`import Solidity.Tools.Upstream\n#upstream_batch ${JSON.stringify(input)} to ${JSON.stringify(out)}\n`);
 const args=['--quiet','--no-build','lean',file,'--','--tstack=131072','-j1'];const start=performance.now();const output=runTool('lake',args,120000);writeFileSync(join(job,'native.log'),output);const result=JSON.parse(readFileSync(out));
 records.push({control:'internal-entry',pipeline,fixture,fixtureSha256:sha(readFileSync(fixture)),command:['lake',...args],exitCode:0,timedOut:false,elapsedMs:performance.now()-start,result,log:join(job,'native.log'),logSha256:sha(Buffer.from(output))});
 if(result[0].status!=='broken'||!result[0].reason.includes('no imported ABI entry'))throw Error('missing exact ABI-entry refusal');
}
writeFileSync(join(base,'boundary-records.json'),JSON.stringify(records,null,2)+'\n');console.log(JSON.stringify({productionProvenanceRefusals:4,internalEntryRefusals:2,pipelines:['legacy','viaIR']}));
