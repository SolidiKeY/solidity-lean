import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertOriginSequenceVariant,assertOriginSequenceReport} from './origin-sequence-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8'));assertOriginSequenceReport(report);
const clone=x=>JSON.parse(JSON.stringify(x));let negativeControls=0,completeWordMutations=0;
for(const v of report.variants){
 const l=v.storageLayout,inner=l.types[l.types[l.storage[3].type].base],innerKey=l.types[l.storage[3].type].base,bKey=l.storage[1].type,tKey=v.transientStorageLayout.storage[0].type;
 const mutations=[x=>x.layoutBase.baseSlotExpression.value='0',x=>x.layoutBase.baseSlotExpression.kind='string',x=>x.layoutBase.baseSlotExpression.nodeType='BinaryOperation',x=>x.baseLayouts.DiamondA[0][1]='42',x=>x.baseLayouts.DiamondB.reverse(),x=>delete x.baseLayouts.DiamondC,x=>x.transientOwners.pop(),x=>x.transientOwners[0][0]='DiamondA',x=>x.lineage.reverse(),x=>x.lineage.pop(),x=>x.lineage[3]='Missing',x=>x.sourceOwners.reverse(),x=>x.sourceOwners[0][0]='OriginSequence',x=>x.sourceOwners.pop(),x=>x.observed.pop(),x=>x.observed.reverse(),x=>x.vectors.pop(),x=>x.vectors.reverse(),x=>x.encodedCalls.reverse(),
  x=>x.methodIdentifiers['readAll()']='00000000',x=>{x.methodIdentifiers['readAll()']='00000000';x.encodedCalls=x.encodedCalls.map(()=> '0x00000000');x.observed.forEach(a=>a.calldata='0x00000000');},
  x=>x.initialGas='100000001',x=>x.stepLimit=5000001,x=>x.deployment.failed=true,x=>x.deployment.returnData='0x01',x=>x.deployment.exception='revert',
  x=>x.deployment.runtimeCodeBytes++,x=>{delete x.runtimeSha256;delete x.deployment.runtimeCodeSha256;},x=>{delete x.runtimeCodeBytes;delete x.deployment.runtimeCodeBytes;},
  x=>x.sourceSha256='0'.repeat(64),x=>delete x.inputSha256,x=>delete x.creationSha256,
  x=>x.storageLayout.storage[0].offset=1,x=>x.storageLayout.storage[1].slot='1',x=>x.storageLayout.storage[2].offset=1,
  x=>x.storageLayout.storage[3].slot='1',x=>x.storageLayout.storage[4].slot='3',x=>x.storageLayout.storage[5].slot='4',x=>x.storageLayout.storage[6].slot='5',
  x=>x.storageLayout.types[bKey].numberOfBytes='32',x=>x.storageLayout.storage.reverse(),
  x=>x.storageLayout.types[innerKey].members[1].offset=2,x=>x.storageLayout.types[innerKey].members.reverse(),
  x=>x.transientStorageLayout.storage[0].slot='1',x=>x.transientStorageLayout.types[tKey].numberOfBytes='1',x=>x.transientStorageLayout.storage.pop(),
  x=>x.observed[5].returnData='0x',x=>{x.observed[5].exception=null;x.observed[5].failed=false;}];
 assert.equal(inner.members.length,2);assert.equal(mutations.length,48);
 for(let i=0;i<v.observed.length;i++){
  mutations.push(x=>x.observed[i].calldata='0x00000000',x=>x.observed[i].returnData='0x01',x=>x.observed[i].failed=!x.observed[i].failed,x=>x.observed[i].steps=5000001,x=>x.observed[i].gasUsed='100000001');
  if(!v.observed[i].failed)for(let j=0;j<20;j++){
   mutations.push(x=>{const a=x.observed[i];a.values[j]=String(BigInt(a.values[j])+1n);a.returnData='0x'+a.values.map(y=>BigInt(y).toString(16).padStart(64,'0')).join('');});completeWordMutations++;
  }
 }
 for(const mutate of mutations){const bad=clone(v);mutate(bad);assert.throws(()=>assertOriginSequenceVariant(bad));negativeControls++;}
}
for(const mutate of [x=>x.variants.pop(),x=>x.variants.reverse(),x=>x.status='blocked']){const bad=clone(report);mutate(bad);assert.throws(()=>assertOriginSequenceReport(bad));negativeControls++;}
assert.equal(completeWordMutations,240);assert.equal(negativeControls,409);
console.log(JSON.stringify({pipelines:2,orderedCalls:14,completeWordMutations,negativeControls,status:'pass'}));
