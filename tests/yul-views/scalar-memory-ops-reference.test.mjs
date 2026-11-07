import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertScalarMemoryOpsReport,assertScalarMemoryOpsVariant} from './scalar-memory-ops-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8')).scalarMemoryOps;
const clone=x=>JSON.parse(JSON.stringify(x));
assertScalarMemoryOpsReport(report);let negatives=0;
const mutations=[
 x=>x.observed.pop(),x=>x.observed.reverse(),x=>[x.observed[1],x.observed[2]]=[x.observed[2],x.observed[1]],
 ...Array.from({length:38},(_,i)=>x=>x.observed[0].values[i]='999'),
 ...Array.from({length:8},(_,i)=>x=>x.observed[i].returnData='0x01'),
 x=>x.observed[1].values[2]='255',x=>x.observed[1].values[3]='4660',x=>x.observed[1].values[4]='16711850',x=>x.observed[1].values[5]='255',
 x=>x.observed[1].values[10]='1',x=>x.observed[2].values[5]='128',x=>x.observed[3].values[9]='2',x=>x.observed[3].values[12]='2',
 x=>x.observed[3].values[10]='0',x=>x.observed[4].values[9]='0',x=>x.observed[5].values[9]='2',x=>x.observed[5].values[35]='0',
 x=>x.observed[6].failed=false,x=>x.observed[6].exception=null,x=>x.observed[6].exception='out of gas',
 x=>x.observed[7].values[2]='0',x=>x.observed[0].signature='wrong()',
 x=>delete x.deployment,x=>x.deployment.failed=true,x=>x.deployment.exception='revert',
 x=>x.deployment.returnData='0x01',x=>x.deployment.runtimeCodeSha256='wrong',x=>x.deployment.runtimeCodeBytes++,
 x=>delete x.sourceSha256,
 x=>{delete x.runtimeSha256;delete x.deployment.runtimeCodeSha256;},x=>x.vectors.pop(),x=>x.vectors.reverse(),
];
assert.equal(mutations.length,76);
for(const v of report.variants)for(const mutate of mutations){
 const bad=clone(v);mutate(bad);assert.throws(()=>assertScalarMemoryOpsVariant(bad));negatives++;
}
for(const mutate of [x=>x.variants.pop(),x=>x.variants.reverse(),x=>x.variants=[]]){
 const bad=clone(report);mutate(bad);assert.throws(()=>assertScalarMemoryOpsReport(bad));negatives++;
}
assert.equal(negatives,155);
console.log(JSON.stringify({pipelines:2,negativeControls:negatives,status:'pass'}));
