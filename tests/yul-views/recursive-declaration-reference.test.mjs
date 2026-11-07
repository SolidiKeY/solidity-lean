import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertRecursiveDeclarationVariant,assertRecursiveDeclarationReport} from './recursive-declaration-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8'));assertRecursiveDeclarationReport(report);
const clone=x=>JSON.parse(JSON.stringify(x));let negativeControls=0,completeWordMutations=0;
for(const v of report.variants){
 const root=v.storageLayout.storage[1].type;
 const outer=v.storageLayout.types[root].members[0].type;
 const row=v.storageLayout.types[outer].base,inner=v.storageLayout.types[row].base;
 const mutations=[x=>x.observed.pop(),x=>x.observed.reverse(),x=>x.vectors.pop(),x=>x.vectors.reverse(),x=>x.encodedCalls.reverse(),
  x=>x.methodIdentifiers['readAll()']='00000000',x=>{x.methodIdentifiers['readAll()']='00000000';x.encodedCalls=x.encodedCalls.map(()=> '0x00000000');x.observed.forEach(a=>a.calldata='0x00000000');},
  x=>x.initialGas='100000001',x=>x.stepLimit=5000001,x=>x.deployment.failed=true,x=>x.deployment.returnData='0x01',x=>x.deployment.exception='revert',
  x=>x.deployment.runtimeCodeBytes++,x=>{delete x.runtimeSha256;delete x.deployment.runtimeCodeSha256;},x=>{delete x.runtimeCodeBytes;delete x.deployment.runtimeCodeBytes;},
  x=>x.sourceSha256='0'.repeat(64),x=>delete x.inputSha256,x=>delete x.creationSha256,
  x=>x.storageLayout.storage[1].slot='9',x=>x.storageLayout.storage[2].slot='13',
  x=>x.storageLayout.types[root].members[1].slot='3',x=>x.storageLayout.types[root].members.reverse(),
  x=>x.storageLayout.types[outer].numberOfBytes='64',x=>x.storageLayout.types[row].numberOfBytes='32',
  x=>x.storageLayout.types[inner].members[1].offset=2,x=>x.storageLayout.types[inner].members.reverse(),
  x=>x.observed[5].returnData='0x',x=>{x.observed[5].exception=null;x.observed[5].failed=false;}];
 for(let i=0;i<v.observed.length;i++){
  mutations.push(x=>x.observed[i].calldata='0x00000000',x=>x.observed[i].returnData='0x01',x=>x.observed[i].failed=!x.observed[i].failed,x=>x.observed[i].steps=5000001,x=>x.observed[i].gasUsed='100000001');
  if(!v.observed[i].failed)for(let j=0;j<20;j++){
   mutations.push(x=>{const a=x.observed[i];a.values[j]=String(BigInt(a.values[j])+1n);a.returnData='0x'+a.values.map(y=>BigInt(y).toString(16).padStart(64,'0')).join('');});completeWordMutations++;
  }
 }
 for(const mutate of mutations){const bad=clone(v);mutate(bad);assert.throws(()=>assertRecursiveDeclarationVariant(bad));negativeControls++;}
}
for(const mutate of [x=>x.variants.pop(),x=>x.variants.reverse(),x=>x.status='blocked']){const bad=clone(report);mutate(bad);assert.throws(()=>assertRecursiveDeclarationReport(bad));negativeControls++;}
assert.equal(completeWordMutations,240);assert.equal(negativeControls,369);
console.log(JSON.stringify({pipelines:2,orderedCalls:14,completeWordMutations,negativeControls,status:'pass'}));
