import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {checkWritebackReplay} from './writeback-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8')).writeback;
assert.equal(report.variants.length,2);
assert.deepEqual(report.variants.map(v=>v.viaIR),[false,true]);
let negatives=0;
for(const variant of report.variants){
 assert.equal(checkWritebackReplay(variant).status,'working');
 for(const mutate of [
  x=>x.observed[5].exception='out of gas',x=>x.observed[5].exception='stack overflow',
  x=>x.observed[5].exception=null,x=>x.observed[5].signature='wrong()',
  x=>x.observed.pop(),x=>x.observed[5].failed=false,x=>x.observed[5].returnData='0x01',
 ]){
  const wrong=JSON.parse(JSON.stringify(variant));mutate(wrong);
  assert.equal(checkWritebackReplay(wrong).status,'broken');negatives++;
 }
}
assert.equal(negatives,14);
console.log(JSON.stringify({positivePipelines:report.variants.length,explicitFailureNegativeControls:negatives,status:'pass'}));
