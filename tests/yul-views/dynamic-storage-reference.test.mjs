import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertDynamicStorageReport,assertDynamicStorageVariant} from './dynamic-storage-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8'));assertDynamicStorageReport(report);
const clone=x=>JSON.parse(JSON.stringify(x));let negativeControls=0,completeWordMutations=0;
for(const v of report.variants){
 const mutations=[x=>x.observed.pop(),x=>x.observed.reverse(),x=>x.vectors.pop(),x=>x.vectors.reverse(),x=>x.encodedCalls.reverse(),
 x=>x.lineage.reverse(),x=>x.lineage.pop(),x=>x.sourceOwners.reverse(),x=>x.sourceOwners[0][0]='DynamicStorage',
 x=>x.hashInputs.reverse(),x=>x.hashInputs[0]='00'.repeat(32),x=>x.dataRoots.reverse(),x=>x.dataRoots[0]='43',
 x=>x.initialGas='100000001',x=>x.stepLimit=5000001,x=>x.deployment.failed=true,x=>x.deployment.returnData='0x01',x=>x.deployment.exception='revert',
 x=>x.deployment.runtimeCodeBytes++,x=>delete x.runtimeSha256,x=>delete x.runtimeCodeBytes,x=>x.sourceSha256='0'.repeat(64),x=>delete x.inputSha256,x=>delete x.creationSha256,
 x=>x.methodIdentifiers['shrink()']='00000000',x=>x.storageLayout.storage.reverse(),x=>x.storageLayout.storage[2].slot='44',x=>x.storageLayout.storage[4].slot='43',
 x=>x.storageLayout.storage[1].offset=0,x=>x.transientStorageLayout.storage[0].slot='42',x=>x.transientStorageLayout.storage.pop()];
 for(let i=0;i<v.observed.length;i++){
  mutations.push(x=>x.observed[i].calldata='0x00000000',x=>x.observed[i].returnData='0x01',x=>x.observed[i].failed=!x.observed[i].failed,x=>x.observed[i].exception='out of gas',x=>x.observed[i].steps=5000001,x=>x.observed[i].gasUsed='100000001');
  if(!v.observed[i].failed)for(let j=0;j<v.observed[i].values.length;j++){
   mutations.push(x=>{const a=x.observed[i];a.values[j]=String(BigInt(a.values[j])+1n);a.returnData='0x'+a.values.map(y=>BigInt(y).toString(16).padStart(64,'0')).join('');});completeWordMutations++;
  }
 }
 for(const mutate of mutations){const bad=clone(v);mutate(bad);assert.throws(()=>assertDynamicStorageVariant(bad));negativeControls++;}
}
for(const mutate of [x=>x.variants.pop(),x=>x.variants.reverse(),x=>x.status='blocked']){const bad=clone(report);mutate(bad);assert.throws(()=>assertDynamicStorageReport(bad));negativeControls++;}
assert.equal(completeWordMutations,398);assert.equal(negativeControls,607);
console.log(JSON.stringify({pipelines:2,orderedCalls:24,completeWordMutations,negativeControls,status:'pass'}));
