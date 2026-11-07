import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertNestedDynamicReport,assertNestedDynamicVariant} from './nested-dynamic-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8'));assertNestedDynamicReport(report);
const clone=x=>JSON.parse(JSON.stringify(x));let negativeControls=0,completeWordMutations=0;
for(const v of report.variants){
 const mutations=[x=>x.observed.pop(),x=>x.observed.reverse(),x=>x.vectors.pop(),x=>x.vectors.reverse(),
  x=>x.encodedCalls.reverse(),x=>x.hashInputs.reverse(),x=>x.hashInputs[0]='ff'.repeat(32),x=>x.dataRoots.reverse(),x=>x.dataRoots[0]='0',
  x=>x.initialGas='100000001',x=>x.stepLimit=5000001,x=>x.deployment.failed=true,x=>x.deployment.returnData='0x01',
  x=>x.deployment.exception='revert',x=>x.deployment.runtimeCodeBytes++,x=>delete x.inputSha256,x=>delete x.sourceSha256,
  x=>delete x.creationSha256,x=>delete x.runtimeSha256,x=>x.sourceSha256='0'.repeat(64),x=>delete x.runtimeCodeBytes,
  x=>x.methodIdentifiers['regrow()']='00000000',x=>x.storageLayout.storage.reverse(),x=>x.storageLayout.storage[0].slot='1',
  x=>x.storageLayout.types[x.storageLayout.storage[0].type].members.reverse(),
  x=>x.storageLayout.types[x.storageLayout.storage[0].type].members[1].slot='0',
  x=>x.storageLayout.types[x.storageLayout.storage[0].type].members[4].offset=0,
  x=>x.transientStorageLayout.storage.push({label:'box',slot:'0',offset:0}),
  x=>x.observed[12].returnData=x.observed[12].returnData.slice(0,-2),x=>x.observed[14].returnData=x.observed[14].returnData.slice(0,-2)];
 const change=(x,i,edit)=>{edit(x.observed[i].values);x.observed[i].returnData='0x'+x.observed[i].values.map(y=>BigInt(y).toString(16).padStart(64,'0')).join('');};
 mutations.push(x=>change(x,5,w=>[w[2],w[4]]=[w[4],w[2]]),x=>change(x,5,w=>w[25]='0'),
  x=>change(x,7,w=>w[7]='77'),x=>change(x,5,w=>w[23]=String(BigInt(w[23])&((1n<<184n)-1n))),
  x=>change(x,9,w=>w[28]=String(BigInt(w[28])-(2n<<24n))),x=>change(x,15,w=>w[0]='1'),
  x=>x.observed[6]=clone(x.observed[4]));
 for(let i=0;i<v.observed.length;i++){
  mutations.push(x=>x.observed[i].calldata='0x00000000',x=>x.observed[i].returnData='0x01',
   x=>x.observed[i].failed=!x.observed[i].failed,x=>x.observed[i].exception='out of gas',
   x=>x.observed[i].steps=5000001,x=>x.observed[i].gasUsed='100000001');
  if(!v.observed[i].failed)for(let j=0;j<v.observed[i].values.length;j++){
   mutations.push(x=>{const a=x.observed[i];a.values[j]=String((BigInt(a.values[j])+1n)&((1n<<256n)-1n));a.returnData='0x'+a.values.map(y=>BigInt(y).toString(16).padStart(64,'0')).join('');});completeWordMutations++;
  }
 }
 for(const mutate of mutations){const bad=clone(v);mutate(bad);assert.throws(()=>assertNestedDynamicVariant(bad));negativeControls++;}
}
for(const mutate of [x=>x.variants.pop(),x=>x.variants.reverse(),x=>x.status='blocked']){const bad=clone(report);mutate(bad);assert.throws(()=>assertNestedDynamicReport(bad));negativeControls++;}
assert.equal(completeWordMutations,926);assert.equal(negativeControls,1207);
console.log(JSON.stringify({status:'pass',pipelines:2,orderedCalls:34,completeWordMutations,negativeControls}));
