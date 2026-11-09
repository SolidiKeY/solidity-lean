import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertMappingTransientReport,assertMappingTransientVariant,vectors,abi} from './mapping-transient-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8')),clone=x=>JSON.parse(JSON.stringify(x)),W=1n<<256n;
const coherent=(v,i,j,n)=>{v.observed[i].values[j]=BigInt(n).toString();v.observed[i].returnData=abi(v.observed[i].values);};
assertMappingTransientReport(report);assert.equal(vectors.length,23);
const base=[v=>v.status='blocked',v=>v.initialGas='100000001',v=>v.stepLimit=5000001,
 v=>v.inputSha256='0'.repeat(64),v=>v.sourceSha256='0'.repeat(64),v=>delete v.creationSha256,
 v=>delete v.runtimeSha256,v=>v.runtimeCodeBytes++,v=>delete v.deployment,
 v=>v.deployment.failed=true,v=>v.deployment.exception='revert',v=>v.deployment.returnData='0x01',
 v=>v.deployment.runtimeCodeSha256='wrong',v=>v.deployment.runtimeCodeBytes++,
 v=>v.methodIdentifiers['setMap(uint256,uint256,bool)']='00000000',v=>v.encodedCalls.reverse(),v=>v.vectors.pop(),
 v=>v.vectors.reverse(),v=>v.observed.pop(),v=>v.observed.reverse(),
 v=>[v.observed[1],v.observed[3]]=[v.observed[3],v.observed[1]],
 v=>v.storageLayout.storage[0].slot='1',v=>v.transientStorageLayout.storage=[{label:'fake',slot:'0',offset:0}],
 v=>v.deployment.steps=5000001,v=>v.deployment.gasUsed='100000001'];
assert.equal(base.length,25);
const extra=[
 v=>{[v.observed[3],v.observed[5]]=[v.observed[5],v.observed[3]];for(const i of [3,5]){v.observed[i].signature=vectors[i].signature;v.observed[i].calldata=v.encodedCalls[i];}},
 v=>coherent(v,1,2,BigInt(v.observed[1].values[2])^1n),
 v=>coherent(v,11,2,0xb6b6abcd),v=>coherent(v,10,1,0xa5a51234),v=>v.observed[14].storage=['0','5','77','999'],
 v=>coherent(v,15,0,1)
];
assert.equal(extra.length,6);assert.equal(vectors.reduce((n,x)=>n+x.expected.length,0),93);
let negativeControls=0,wordControls=0;
for(const v of report.variants){
 for(const mutate of [...base,...extra]){const b=clone(v);mutate(b);assert.throws(()=>assertMappingTransientVariant(b));negativeControls++;}
 for(let i=0;i<vectors.length;i++){
  const mutations=[b=>b.observed[i].signature='wrong()',b=>b.observed[i].calldata='0x00000000',
   b=>b.observed[i].storage=['4243'],b=>b.observed[i].transientAfter=['1','0'],b=>b.observed[i].logs=[['00',[],'00']],
   b=>{if(vectors[i].failure)b.observed[i].returnData='0x01';else{b.observed[i].failed=true;b.observed[i].exception='revert';}},
   b=>b.observed[i].steps=5000001,b=>b.observed[i].maxStack=1025];
  for(const mutate of mutations){const b=clone(v);mutate(b);assert.throws(()=>assertMappingTransientVariant(b));negativeControls++;}
  for(let j=0;j<vectors[i].expected.length;j++){const b=clone(v);coherent(b,i,j,(BigInt(b.observed[i].values[j])+1n)%W);assert.throws(()=>assertMappingTransientVariant(b));negativeControls++;wordControls++;}
 }
}
assert.equal(negativeControls,616);assert.equal(wordControls,186);
console.log(JSON.stringify({status:'pass',pipelines:2,orderedCalls:46,negativeControls,coherentWordControls:wordControls,boundary:'Fail-closed finite external controls; no source/compiler or memory-safe adequacy inference.'}));
