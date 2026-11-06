// Actual current receipt mutations; these remain host-only parser controls.
import {test} from 'node:test';
import {strict as assert} from 'node:assert';
import {readFileSync} from 'node:fs';
import {execFileSync} from 'node:child_process';
import {fileURLToPath} from 'node:url';
import {reportBinding,verifyOutputs} from '../../scripts/roadmap-v17-runtime.mjs';
const root=process.env.V17_DIFFERENTIAL_RESULT;
test('actual full matrix, output manifest and mutation controls',{skip:!root},()=>{
 const log=readFileSync(root+'/../build.log','utf8');
 verifyOutputs(log,root);
 const report=JSON.parse(readFileSync(root+'/report.json'));
 const inputs=JSON.parse(readFileSync(root+'/inputs-before.json'));
 reportBinding(report,inputs);
 const mutations=[r=>r.metadata.checkoutCommit='0'.repeat(40),r=>r.metadata.compilerSha256='0'.repeat(64),
  r=>r.metadata.generatorBinarySha256='0'.repeat(64),r=>r.records.reverse(),r=>r.records.pop(),
  r=>r.records[0].variants.reverse(),r=>r.records[0].variants[0].runtimeCode='00',
  r=>r.records[0].variants[0].deployment.runtimeCodeSha256='0'.repeat(64),
  r=>r.records[0].variants[0].sourceSha256='0'.repeat(64),r=>r.summary.blocked=1];
 for(const mutate of mutations){const bad=structuredClone(report);mutate(bad);assert.throws(()=>reportBinding(bad,inputs));}
 assert.throws(()=>JSON.parse(readFileSync(root+'/report.json','utf8').slice(0,-2)));
 assert.throws(()=>verifyOutputs(log.replace('V17_RUNTIME_OUTPUTS ','MISSING '),root));
 assert.throws(()=>verifyOutputs(log+log,root));
 const comparator=fileURLToPath(new URL('../../scripts/roadmap-v17-compare.mjs',import.meta.url));
 const options={timeout:60000,maxBuffer:16*1024*1024,stdio:['pipe','pipe','pipe']};
 assert.equal(execFileSync(process.execPath,[comparator],{...options,input:JSON.stringify(report)}).toString(),'V17_COMPARE_PASS\n');
 const bad=structuredClone(report);bad.records[0].variants[0].run.returnData='0x01';
 assert.throws(()=>execFileSync(process.execPath,[comparator],{...options,input:JSON.stringify(bad)}),error=>error.status===1&&/contradictory/.test(error.stderr.toString()));
});
