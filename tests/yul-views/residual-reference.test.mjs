import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertResidualReport,assertResidualVariant} from './residual-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8')).residual;
const clone=x=>JSON.parse(JSON.stringify(x));
assertResidualReport(report);let negatives=0;
for(const v of report.variants)for(const mutate of [
 x=>x.observed.pop(),x=>x.observed.reverse(),x=>x.observed[0].values[1]='43',
 x=>x.observed[0].returnData='0x',x=>x.observed[1].exception='out of gas',
 x=>x.observed[1].exception='stack overflow',x=>x.observed[1].failed=false,
 x=>x.observed[2].values[3]='165',x=>x.observed[3].values[4]='0',
 x=>x.observed[0].signature='wrong()',x=>x.vectors.pop(),x=>delete x.deployment,
 x=>x.deployment.exception='revert',x=>x.deployment.returnData='0x01',
 x=>x.deployment.runtimeCodeSha256='wrong',
]){const bad=clone(v);mutate(bad);assert.throws(()=>assertResidualVariant(bad));negatives++;}
for(const mutate of [x=>x.variants.pop(),x=>x.variants.reverse(),x=>x.variants=[]]){
 const bad=clone(report);mutate(bad);assert.throws(()=>assertResidualReport(bad));negatives++;
}
assert.equal(negatives,33);
console.log(JSON.stringify({pipelines:report.variants.length,negativeControls:negatives,status:'pass'}));
