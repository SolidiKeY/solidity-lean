import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertFiniteReport,assertFiniteVariant} from './finite-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8')).finite;
const clone=x=>JSON.parse(JSON.stringify(x));
assertFiniteReport(report);let negatives=0;
const mutations=[
 x=>x.observed.pop(),x=>x.observed.reverse(),x=>[x.observed[0],x.observed[1]]=[x.observed[1],x.observed[0]],
 ...Array.from({length:8},(_,i)=>x=>x.observed[1].values[i]='999'),
 x=>x.observed[1].returnData='0x',x=>x.observed[6].exception='out of gas',
 x=>x.observed[6].exception='stack overflow',x=>x.observed[6].failed=false,
 x=>x.observed[8].values[7]='0',x=>x.observed[9].values[7]='1',
 x=>delete x.deployment,x=>x.deployment.exception='revert',x=>x.deployment.returnData='0x01',
 x=>x.deployment.runtimeCodeSha256='wrong',x=>x.vectors.pop(),x=>x.observed[0].signature='wrong()',
 x=>x.storageLayout.storage[1].offset=2,
 x=>x.storageLayout.types[x.storageLayout.storage[1].type].numberOfBytes='3',
 x=>x.transientStorageLayout.storage.pop(),
];
assert.equal(mutations.length,26);
for(const v of report.variants)for(const mutate of mutations){
 const bad=clone(v);mutate(bad);assert.throws(()=>assertFiniteVariant(bad));negatives++;
}
for(const mutate of [x=>x.variants.pop(),x=>x.variants.reverse(),x=>x.variants=[]]){
 const bad=clone(report);mutate(bad);assert.throws(()=>assertFiniteReport(bad));negatives++;
}
assert.equal(negatives,55);
console.log(JSON.stringify({pipelines:report.variants.length,negativeControls:negatives,status:'pass'}));
