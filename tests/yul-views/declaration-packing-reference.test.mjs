import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertDeclarationVariant,assertDeclarationReport} from './declaration-packing-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8'));assertDeclarationReport(report);
const clone=x=>JSON.parse(JSON.stringify(x));let negativeControls=0,completeWordMutations=0;
for(const v of report.variants){
 const mutations=[x=>x.observed.pop(),x=>x.observed.reverse(),x=>x.vectors.pop(),x=>x.vectors.reverse(),x=>x.encodedCalls.reverse(),
  x=>x.methodIdentifiers['readAll()']='00000000',x=>{x.methodIdentifiers['readAll()']='00000000';x.encodedCalls=x.encodedCalls.map(()=> '0x00000000');x.observed.forEach(a=>a.calldata='0x00000000');},
  x=>x.initialGas='100000001',x=>x.stepLimit=5000001,x=>x.deployment.failed=true,x=>x.deployment.returnData='0x01',x=>x.deployment.exception='revert',
  x=>x.deployment.runtimeCodeBytes++,x=>{delete x.runtimeSha256;delete x.deployment.runtimeCodeSha256;},x=>{delete x.runtimeCodeBytes;delete x.deployment.runtimeCodeBytes;},
  x=>x.sourceSha256='0'.repeat(64),x=>delete x.inputSha256,x=>delete x.creationSha256,
  x=>x.storageLayout.storage[1].slot='5',x=>x.storageLayout.storage[2].slot='6'];
 const packed=v.storageLayout.storage[0].type,composite=v.storageLayout.storage[1].type;
 mutations.push(x=>x.storageLayout.types[packed].members[3].offset=7,x=>x.storageLayout.types[packed].members[4].slot='0',x=>x.storageLayout.types[packed].members[6].offset=0,
  x=>x.storageLayout.types[composite].members[1].slot='1',x=>x.storageLayout.types[packed].members.reverse());
 for(let i=0;i<v.observed.length;i++){
  mutations.push(x=>x.observed[i].calldata='0x00000000',x=>x.observed[i].returnData='0x01',x=>x.observed[i].failed=!x.observed[i].failed,x=>x.observed[i].steps=5000001,x=>x.observed[i].gasUsed='100000001');
  if(!v.observed[i].failed)for(let j=0;j<8;j++){mutations.push(x=>{const a=x.observed[i];a.values[j]=String(BigInt(a.values[j])+1n);a.returnData='0x'+a.values.map(y=>BigInt(y).toString(16).padStart(64,'0')).join('');});completeWordMutations++;}
 }
 assert.equal(mutations.length,108);
 for(const mutate of mutations){const bad=clone(v);mutate(bad);assert.throws(()=>assertDeclarationVariant(bad));negativeControls++;}
}
for(const mutate of [x=>x.variants.pop(),x=>x.variants.reverse(),x=>x.status='blocked']){const bad=clone(report);mutate(bad);assert.throws(()=>assertDeclarationReport(bad));negativeControls++;}
assert.equal(completeWordMutations,96);assert.equal(negativeControls,219);
console.log(JSON.stringify({pipelines:2,orderedCalls:14,completeWordMutations,negativeControls,status:'pass'}));
