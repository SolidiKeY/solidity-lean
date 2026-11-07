import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertPackedResidualReport,assertPackedResidualVariant} from './packed-residual-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8')).packedResidual;
const clone=x=>JSON.parse(JSON.stringify(x));
const abi=xs=>'0x'+xs.map(x=>BigInt(x).toString(16).padStart(64,'0')).join('');
assertPackedResidualReport(report);let negativeControls=0,wordMutations=0;
for(const original of report.variants){
 const mutations=[
  ...['inputSha256','sourceSha256','creationSha256','runtimeSha256'].map(key=>x=>delete x[key]),
  ...['inputSha256','sourceSha256','creationSha256','runtimeSha256'].map(key=>x=>x[key]='wrong'),
  x=>{delete x.runtimeSha256;delete x.deployment.runtimeCodeSha256;},
  x=>{delete x.runtimeCodeBytes;delete x.deployment.runtimeCodeBytes;},
  ...[0,-1,0.5,Number.MAX_SAFE_INTEGER+1].map(size=>x=>{x.runtimeCodeBytes=size;x.deployment.runtimeCodeBytes=size;}),
  x=>delete x.observed[0].calldata,x=>x.observed[16].calldata='0x08fc43c4'+'0'.repeat(63)+'1',
  x=>x.observed.pop(),x=>x.observed.reverse(),x=>[x.observed[3],x.observed[4]]=[x.observed[4],x.observed[3]],
  x=>x.vectors.pop(),x=>x.vectors.reverse(),x=>x.vectors[16].args=['1'],
  x=>x.encodedCalls.pop(),x=>x.encodedCalls[16]='0x08fc43c4'+'0'.repeat(63)+'1',
  x=>x.encodedCalls[0]='0x00000000',x=>x.methodIdentifiers['readStored()']='00000000',
  x=>x.observed[7].failed=false,x=>x.observed[7].exception='out of gas',x=>x.observed[7].returnData='0x01',
  x=>x.observed[16].returnData='0x01',x=>x.observed[16].exception='stack overflow',
  x=>x.observed[15].failed=true,x=>x.observed[15].exception='revert',
  x=>delete x.deployment,x=>x.deployment.failed=true,x=>x.deployment.exception='revert',
  x=>x.deployment.returnData='0x01',x=>x.deployment.runtimeCodeSha256='wrong',x=>x.deployment.runtimeCodeBytes++,
  x=>x.deployment.steps=5000001,x=>x.deployment.gasUsed='100000001',
  x=>x.observed[1].gasUsed='100000001',x=>x.observed[1].steps=5000001,
  x=>x.initialGas='100000001',x=>x.stepLimit=5000001,x=>x.status='blocked',
  x=>x.storageLayout.storage[1].offset=2,x=>x.storageLayout.storage[2].offset=4,
  x=>x.storageLayout.storage[3].slot='8',x=>x.storageLayout.types[x.storageLayout.storage[2].type].numberOfBytes='4',
  x=>x.transientStorageLayout.storage.pop(),x=>x.transientStorageLayout.storage[10].slot='8',
  x=>x.transientStorageLayout.storage[7].offset=1,
 ];
 for(let row=0;row<original.observed.length;row++){
  if(original.observed[row].failed)continue;
  for(let col=0;col<original.observed[row].values.length;col++){
   mutations.push(x=>{x.observed[row].values[col]=((BigInt(x.observed[row].values[col])+1n)% (1n<<256n)).toString();x.observed[row].returnData=abi(x.observed[row].values);});wordMutations++;
  }
 }
 for(const mutate of mutations){const bad=clone(original);mutate(bad);assert.throws(()=>assertPackedResidualVariant(bad));negativeControls++;}
}
for(const mutate of [x=>x.variants.pop(),x=>x.variants.reverse(),x=>x.variants=[]]){const bad=clone(report);mutate(bad);assert.throws(()=>assertPackedResidualReport(bad));negativeControls++;}
assert.equal(wordMutations,394);assert.equal(negativeControls,503);
console.log(JSON.stringify({pipelines:2,orderedCalls:36,completeWordMutations:wordMutations,negativeControls,status:'pass'}));
