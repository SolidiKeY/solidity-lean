import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertHeapBytesReport,assertHeapBytesVariant} from './heap-bytes-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8')).heapBytes;
const clone=x=>JSON.parse(JSON.stringify(x));
assertHeapBytesReport(report);let negatives=0;
const mutations=[
 x=>x.observed.pop(),x=>x.observed.reverse(),x=>[x.observed[0],x.observed[1]]=[x.observed[1],x.observed[0]],
 ...Array.from({length:18},(_,i)=>x=>x.observed[0].values[i]='999'),
 x=>x.observed[0].returnData='0x',x=>x.observed[6].values[2]='3',x=>x.observed[9].values[2]='4',
 x=>x.observed[7].values[2]='1',x=>x.observed[7].values[13]='512',x=>x.observed[7].values[10]='96',
 x=>x.observed[8].exception='out of gas',x=>x.observed[8].exception='stack overflow',
 x=>x.observed[8].exception=null,x=>x.observed[8].failed=false,x=>x.observed[8].returnData='0x01',
 x=>delete x.deployment,x=>x.deployment.failed=true,x=>x.deployment.exception='revert',
 x=>x.deployment.returnData='0x01',x=>x.deployment.runtimeCodeSha256='wrong',
 x=>x.observed[0].signature='wrong()',x=>x.vectors.pop(),x=>x.vectors.reverse(),
 x=>{delete x.runtimeSha256;delete x.deployment.runtimeCodeSha256;},x=>delete x.sourceSha256,
 x=>x.deployment.runtimeCodeBytes++,
];
assert.equal(mutations.length,43);
for(const v of report.variants)for(const mutate of mutations){
 const bad=clone(v);mutate(bad);assert.throws(()=>assertHeapBytesVariant(bad));negatives++;
}
for(const mutate of [x=>x.variants.pop(),x=>x.variants.reverse(),x=>x.variants=[]]){
 const bad=clone(report);mutate(bad);assert.throws(()=>assertHeapBytesReport(bad));negatives++;
}
assert.equal(negatives,89);
console.log(JSON.stringify({pipelines:report.variants.length,negativeControls:negatives,status:'pass'}));
