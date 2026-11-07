import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertRetainedHeapReport,assertRetainedHeapVariant} from './retained-heap-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8')).retainedHeap;
const clone=x=>JSON.parse(JSON.stringify(x));
assertRetainedHeapReport(report);let negatives=0;
const mutations=[
 x=>x.observed.pop(),x=>x.observed.reverse(),x=>[x.observed[1],x.observed[2]]=[x.observed[2],x.observed[1]],
 ...Array.from({length:22},(_,i)=>x=>x.observed[0].values[i]='999'),
 ...Array.from({length:9},(_,i)=>x=>x.observed[i].returnData='0x01'),
 x=>x.observed[1].values[14]='0',x=>x.observed[2].values[2]='3',x=>x.observed[3].values[6]='0',
 x=>x.observed[3].values[5]='0',x=>x.observed[4].values[2]='0',x=>x.observed[5].values[4]='0',
 x=>x.observed[6].values[0]='3',x=>x.observed[6].values[5]='0',
 x=>x.observed[8].values[2]='4',x=>x.observed[7].failed=false,x=>x.observed[7].exception=null,
 x=>x.observed[7].exception='out of gas',x=>x.observed[0].signature='wrong()',
 x=>delete x.deployment,x=>x.deployment.failed=true,x=>x.deployment.exception='revert',
 x=>x.deployment.returnData='0x01',x=>x.deployment.runtimeCodeSha256='wrong',x=>x.deployment.runtimeCodeBytes++,
 x=>delete x.sourceSha256,x=>delete x.parentSourceSha256,x=>delete x.resizeSourceSha256,
 x=>{delete x.runtimeSha256;delete x.deployment.runtimeCodeSha256;},x=>x.vectors.pop(),x=>x.vectors.reverse(),
];
assert.equal(mutations.length,59);
for(const v of report.variants)for(const mutate of mutations){
 const bad=clone(v);mutate(bad);assert.throws(()=>assertRetainedHeapVariant(bad));negatives++;
}
for(const mutate of [x=>x.variants.pop(),x=>x.variants.reverse(),x=>x.variants=[]]){
 const bad=clone(report);mutate(bad);assert.throws(()=>assertRetainedHeapReport(bad));negatives++;
}
assert.equal(negatives,121);
console.log(JSON.stringify({pipelines:2,negativeControls:negatives,status:'pass'}));
