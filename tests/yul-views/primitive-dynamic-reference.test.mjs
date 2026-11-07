import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertPrimitiveDynamicReport,assertPrimitiveDynamicVariant} from './primitive-dynamic-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8'));assertPrimitiveDynamicReport(report);
const clone=x=>JSON.parse(JSON.stringify(x));let negativeControls=0,completeWordMutations=0;
for(const v of report.variants){
 const mutations=[
 x=>x.observed.pop(),x=>x.observed.reverse(),x=>x.vectors.pop(),
 x=>x.vectors.reverse(),x=>x.encodedCalls.reverse(),x=>x.hashInputs.reverse(),
 x=>x.hashInputs[0]='ff'.repeat(32),x=>x.dataRoots.reverse(),x=>x.dataRoots[0]='0',
 x=>x.initialGas='100000001',x=>x.stepLimit=5000001,x=>x.deployment.failed=true,
 x=>x.deployment.returnData='0x01',x=>x.deployment.exception='revert',x=>x.deployment.runtimeCodeBytes++,
 x=>delete x.inputSha256,x=>delete x.creationSha256,x=>delete x.sourceSha256,
 x=>delete x.runtimeSha256,x=>x.sourceSha256='0'.repeat(64),x=>delete x.runtimeCodeBytes,
 x=>x.methodIdentifiers['regrow()']='00000000',x=>x.storageLayout.storage.reverse(),x=>x.storageLayout.storage[0].slot='1',
 x=>x.storageLayout.types[x.storageLayout.types[x.storageLayout.storage[0].type].base].numberOfBytes='1',
 x=>x.storageLayout.types[x.storageLayout.types[x.storageLayout.storage[2].type].base].label='uint24',
 x=>x.transientStorageLayout.storage.push({label:'xs',slot:'0',offset:0})];
 assert.equal(mutations.length,27);
 const changeWords=(x,i,edit)=>{edit(x.observed[i].values);x.observed[i].returnData='0x'+x.observed[i].values.map(y=>BigInt(y).toString(16).padStart(64,'0')).join('');};
 mutations.push(
  x=>changeWords(x,9,w=>[w[33],w[39]]=[w[39],w[33]]),
  x=>changeWords(x,9,w=>w[34]=String(BigInt(w[34])&0xffffffffn)),
  x=>changeWords(x,5,w=>w[33]='0'),x=>changeWords(x,3,w=>w[35]='0'),
  x=>x.observed[18].returnData=x.observed[18].returnData.slice(0,-2),
  x=>x.observed[20].returnData=x.observed[20].returnData.slice(0,-2),
  x=>changeWords(x,21,w=>w[0]='1'),x=>x.observed[7]=clone(x.observed[5]),
  x=>changeWords(x,23,w=>w[0]=String(BigInt(w[0])>>232n)),
  x=>changeWords(x,9,w=>w[41]=String(BigInt(w[41])&((1n<<160n)-1n))),
  x=>changeWords(x,15,w=>w[39]=String(BigInt(w[39])-(1n<<24n))));
 assert.equal(mutations.length,38);
 for(let i=0;i<v.observed.length;i++){
  mutations.push(x=>x.observed[i].calldata='0x00000000',x=>x.observed[i].returnData='0x01',
   x=>x.observed[i].failed=!x.observed[i].failed,x=>x.observed[i].exception='out of gas',
   x=>x.observed[i].steps=5000001,x=>x.observed[i].gasUsed='100000001');
  if(!v.observed[i].failed)for(let j=0;j<v.observed[i].values.length;j++){
   mutations.push(x=>{const a=x.observed[i];a.values[j]=String((BigInt(a.values[j])+1n)&((1n<<256n)-1n));a.returnData='0x'+a.values.map(y=>BigInt(y).toString(16).padStart(64,'0')).join('');});completeWordMutations++;
  }
 }
 for(const mutate of mutations){const bad=clone(v);mutate(bad);assert.throws(()=>assertPrimitiveDynamicVariant(bad));negativeControls++;}
}
for(const mutate of [x=>x.variants.pop(),x=>x.variants.reverse(),x=>x.status='blocked']){
 const bad=clone(report);mutate(bad);assert.throws(()=>assertPrimitiveDynamicReport(bad));negativeControls++;
}
assert.equal(completeWordMutations,2170);assert.equal(negativeControls,2537);
console.log(JSON.stringify({status:'pass',pipelines:2,orderedCalls:48,completeWordMutations,negativeControls}));
