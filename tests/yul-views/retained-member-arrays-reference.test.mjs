import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertRetainedMemberArraysReport,assertRetainedMemberArraysVariant} from './retained-member-arrays-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8')).retainedMemberArrays;
const clone=x=>JSON.parse(JSON.stringify(x));
assertRetainedMemberArraysReport(report);let negatives=0;
const mutations=[
 x=>x.observed.pop(),x=>x.observed.reverse(),x=>[x.observed[1],x.observed[2]]=[x.observed[2],x.observed[1]],
 ...Array.from({length:58},(_,i)=>x=>x.observed[0].values[i]='999'),
 ...Array.from({length:8},(_,i)=>x=>x.observed[i].returnData='0x01'),
 x=>x.observed[1].values[7]='3',x=>x.observed[1].values[11]='2',x=>x.observed[1].values[9]='0',x=>x.observed[1].values[12]='0',
 x=>x.observed[1].values[32]='3',x=>x.observed[2].values[7]='0',x=>x.observed[3].values[7]='3',x=>x.observed[3].values[26]='1',
 x=>x.observed[3].values[33]='3',x=>x.observed[4].values[7]='0',x=>x.observed[5].values[12]='1152',x=>x.observed[5].values[17]='0',
 x=>x.observed[6].failed=false,x=>x.observed[6].exception=null,x=>x.observed[6].exception='out of gas',
 x=>x.observed[7].values[5]='1408',x=>x.observed[0].signature='wrong()',
 x=>delete x.deployment,x=>x.deployment.failed=true,x=>x.deployment.exception='revert',
 x=>x.deployment.returnData='0x01',x=>x.deployment.runtimeCodeSha256='wrong',x=>x.deployment.runtimeCodeBytes++,
 x=>delete x.sourceSha256,
 x=>{delete x.runtimeSha256;delete x.deployment.runtimeCodeSha256;},x=>x.vectors.pop(),x=>x.vectors.reverse(),
];
assert.equal(mutations.length,96);
for(const v of report.variants)for(const mutate of mutations){
 const bad=clone(v);mutate(bad);assert.throws(()=>assertRetainedMemberArraysVariant(bad));negatives++;
}
for(const mutate of [x=>x.variants.pop(),x=>x.variants.reverse(),x=>x.variants=[]]){
 const bad=clone(report);mutate(bad);assert.throws(()=>assertRetainedMemberArraysReport(bad));negatives++;
}
assert.equal(negatives,195);
console.log(JSON.stringify({pipelines:2,negativeControls:negatives,status:'pass'}));
