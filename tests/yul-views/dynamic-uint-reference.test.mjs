import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertDynamicUintReport,assertDynamicUintVariant} from './dynamic-uint-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8')).dynamicUint;
const clone=x=>JSON.parse(JSON.stringify(x));
assertDynamicUintReport(report);let negatives=0;
const mutations=[
 x=>x.observed.pop(),x=>x.observed.reverse(),x=>[x.observed[5],x.observed[6]]=[x.observed[6],x.observed[5]],
 ...Array.from({length:34},(_,i)=>x=>x.observed[0].values[i]='999'),
 ...Array.from({length:9},(_,i)=>x=>x.observed[i].returnData='0x01'),
 x=>x.observed[1].values[3]='7',x=>x.observed[1].values[4]='9',x=>x.observed[1].values[5]='1',
 x=>x.observed[2].values[2]='3',x=>x.observed[2].values[16]='3',x=>x.observed[2].values[17]='3',
 x=>x.observed[2].values[3]='0',x=>x.observed[2].values[4]='0',x=>x.observed[2].values[5]='0',
 x=>x.observed[3].values[2]='0',x=>x.observed[3].values[17]='0',x=>x.observed[4].values[2]='1',
 x=>x.observed[5].values[7]='11',x=>x.observed[6].values[4]='9',
 x=>x.observed[7].failed=false,x=>x.observed[7].exception=null,x=>x.observed[7].exception='out of gas',
 x=>x.observed[8].values[3]='42',x=>x.observed[0].signature='wrong()',
 x=>delete x.deployment,x=>x.deployment.failed=true,x=>x.deployment.exception='revert',
 x=>x.deployment.returnData='0x01',x=>x.deployment.runtimeCodeSha256='wrong',x=>x.deployment.runtimeCodeBytes++,
 x=>delete x.sourceSha256,x=>{delete x.runtimeSha256;delete x.deployment.runtimeCodeSha256;},
 x=>x.vectors.pop(),x=>x.vectors.reverse(),
];
assert.equal(mutations.length,75);
for(const v of report.variants)for(const mutate of mutations){
 const bad=clone(v);mutate(bad);assert.throws(()=>assertDynamicUintVariant(bad));negatives++;
}
for(const mutate of [x=>x.variants.pop(),x=>x.variants.reverse(),x=>x.variants=[]]){
 const bad=clone(report);mutate(bad);assert.throws(()=>assertDynamicUintReport(bad));negatives++;
}
assert.equal(negatives,153);
console.log(JSON.stringify({pipelines:2,negativeControls:negatives,status:'pass'}));
