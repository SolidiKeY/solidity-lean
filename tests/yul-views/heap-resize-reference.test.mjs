import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertHeapResizeReport,assertHeapResizeVariant} from './heap-resize-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8')).heapResize;
const clone=x=>JSON.parse(JSON.stringify(x));
assertHeapResizeReport(report);let negatives=0;
const mutations=[
 x=>x.observed.pop(),x=>x.observed.reverse(),x=>[x.observed[0],x.observed[1]]=[x.observed[1],x.observed[0]],
 ...Array.from({length:22},(_,i)=>x=>x.observed[0].values[i]='999'),
 x=>x.observed[0].returnData='0x',x=>x.observed[3].values[14]='3',x=>x.observed[2].values[21]='0',
 x=>x.observed[6].values[5]=(BigInt(x.observed[6].values[5])&~255n).toString(),
 x=>x.observed[5].values[6]='0',x=>x.observed[8].values[14]='33',x=>x.observed[9].failed=true,
 x=>x.observed[11].values[2]='4',
 x=>x.observed[10].exception='out of gas',x=>x.observed[10].exception='stack overflow',
 x=>x.observed[10].exception=null,x=>x.observed[10].failed=false,x=>x.observed[10].returnData='0x01',
 x=>delete x.deployment,x=>x.deployment.failed=true,x=>x.deployment.exception='revert',
 x=>x.deployment.returnData='0x01',x=>x.deployment.runtimeCodeSha256='wrong',x=>x.deployment.runtimeCodeBytes++,
 x=>delete x.sourceSha256,x=>{delete x.runtimeSha256;delete x.deployment.runtimeCodeSha256;},x=>delete x.parentSourceSha256,
 x=>x.vectors.pop(),x=>x.vectors.reverse(),x=>x.observed[0].signature='wrong()',
];
assert.equal(mutations.length,50);
for(const v of report.variants)for(const mutate of mutations){
 const bad=clone(v);mutate(bad);assert.throws(()=>assertHeapResizeVariant(bad));negatives++;
}
for(const mutate of [x=>x.variants.pop(),x=>x.variants.reverse(),x=>x.variants=[]]){
 const bad=clone(report);mutate(bad);assert.throws(()=>assertHeapResizeReport(bad));negatives++;
}
assert.equal(negatives,103);
console.log(JSON.stringify({pipelines:report.variants.length,negativeControls:negatives,status:'pass'}));
