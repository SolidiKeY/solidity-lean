import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertMixedHeapReport,assertMixedHeapVariant} from './mixed-heap-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8')).mixedHeap;
const clone=x=>JSON.parse(JSON.stringify(x));
assertMixedHeapReport(report);let negatives=0;
const mutations=[
 x=>x.observed.pop(),x=>x.observed.reverse(),x=>[x.observed[1],x.observed[2]]=[x.observed[2],x.observed[1]],
 ...Array.from({length:42},(_,i)=>x=>x.observed[0].values[i]='999'),
 ...Array.from({length:8},(_,i)=>x=>x.observed[i].returnData='0x01'),
 x=>x.observed[1].values[32]='17',x=>x.observed[1].values[33]='17',
 x=>x.observed[2].values[7]='9',x=>x.observed[2].values[35]='9',
 x=>x.observed[5].values[11]='128',x=>x.observed[5].values[29]='3',x=>x.observed[5].values[31]='17',
 x=>x.observed[3].values[14]='129',x=>x.observed[4].values[15]='129',x=>x.observed[7].values[3]='0',
 x=>x.observed[6].failed=false,x=>x.observed[6].exception=null,x=>x.observed[6].exception='out of gas',
 x=>x.observed[0].signature='wrong()',x=>delete x.deployment,x=>x.deployment.failed=true,
 x=>x.deployment.exception='revert',x=>x.deployment.returnData='0x01',x=>x.deployment.runtimeCodeSha256='wrong',
 x=>x.deployment.runtimeCodeBytes++,x=>delete x.sourceSha256,
 x=>{delete x.runtimeSha256;delete x.deployment.runtimeCodeSha256;},x=>x.vectors.pop(),x=>x.vectors.reverse(),
];
assert.equal(mutations.length,77);
for(const v of report.variants)for(const mutate of mutations){
 const bad=clone(v);mutate(bad);assert.throws(()=>assertMixedHeapVariant(bad));negatives++;
}
for(const mutate of [x=>x.variants.pop(),x=>x.variants.reverse(),x=>x.variants=[]]){
 const bad=clone(report);mutate(bad);assert.throws(()=>assertMixedHeapReport(bad));negatives++;
}
assert.equal(negatives,157);
console.log(JSON.stringify({pipelines:2,negativeControls:negatives,status:'pass'}));
