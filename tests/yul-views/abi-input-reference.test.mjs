import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertAbiInputReport,assertAbiInputVariant,vectors} from './abi-input-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8')),clone=x=>JSON.parse(JSON.stringify(x));
const W=1n<<256n,abi=xs=>'0x'+xs.map(x=>{const w=BigInt(x);assert.ok(w>=0n&&w<W);return w.toString(16).padStart(64,'0');}).join('');
const coherent=(v,call,at,value)=>{v.observed[call].values[at]=BigInt(value).toString();v.observed[call].returnData=abi(v.observed[call].values);};
assertAbiInputReport(report);assert.equal(vectors.length,17);assert.equal(report.variants.length,2);
const base=[
 v=>v.status='blocked',v=>v.initialGas='100000001',v=>v.stepLimit=5000001,
 v=>delete v.inputSha256,v=>v.sourceSha256='0'.repeat(64),
 v=>delete v.creationSha256,v=>delete v.runtimeSha256,v=>v.runtimeCodeBytes++,
 v=>delete v.deployment,v=>v.deployment.failed=true,v=>v.deployment.exception='revert',
 v=>v.deployment.returnData='0x01',v=>v.deployment.runtimeCodeSha256='wrong',v=>v.deployment.runtimeCodeBytes++,
 v=>v.methodIdentifiers['inspect(bytes)']='00000000',v=>v.encodedCalls.reverse(),v=>v.vectors.pop(),v=>v.vectors.reverse(),
 v=>v.observed.pop(),v=>v.observed.reverse(),v=>[v.observed[1],v.observed[2]]=[v.observed[2],v.observed[1]],
 v=>v.storageLayout.storage[0].slot='1',v=>v.transientStorageLayout.storage=[{label:'fake',slot:'0',offset:0}],
 v=>v.deployment.steps=5000001,v=>v.deployment.gasUsed='100000001',
];assert.equal(base.length,25);
const extra=[
 v=>{[v.observed[1],v.observed[2]]=[v.observed[2],v.observed[1]];for(const i of [1,2]){v.observed[i].signature=vectors[i].signature;v.observed[i].calldata=v.encodedCalls[i];}},
 v=>coherent(v,2,2,7),
 v=>coherent(v,1,3,0),
 v=>coherent(v,1,5,2),
 v=>{v.observed[8].returnData='0x';},
 v=>{v.observed[11].storage=['8888'];},
 v=>coherent(v,14,0,1),
];assert.equal(extra.length,7);
const wordCount=vectors.reduce((n,x)=>n+x.expected.length,0);assert.equal(wordCount,70);
let negativeControls=0;
for(const v of report.variants){
 for(const mutate of [...base,...extra]){const b=clone(v);mutate(b);assert.throws(()=>assertAbiInputVariant(b));negativeControls++;}
 for(let i=0;i<vectors.length;i++){
  const cases=[b=>b.observed[i].signature='wrong()',b=>b.observed[i].calldata='0x00000000',b=>b.observed[i].storage=['4243'],b=>b.observed[i].logs=[['00',[],'00']],b=>{if(vectors[i].failure)b.observed[i].returnData='0x01';else{b.observed[i].failed=true;b.observed[i].exception='revert';}},b=>b.observed[i].steps=5000001,b=>b.observed[i].maxStack=1025];assert.equal(cases.length,7);
  for(const mutate of cases){const b=clone(v);mutate(b);assert.throws(()=>assertAbiInputVariant(b));negativeControls++;}
  for(let j=0;j<vectors[i].expected.length;j++){const b=clone(v);coherent(b,i,j,(BigInt(vectors[i].expected[j])+1n)%W);assert.throws(()=>assertAbiInputVariant(b));negativeControls++;}
 }
}
for(const mutate of [x=>x.variants.pop(),x=>x.variants.reverse(),x=>x.variants=[]]){const b=clone(report);mutate(b);assert.throws(()=>assertAbiInputReport(b));negativeControls++;}
assert.equal(negativeControls,445);assert.equal(report.variants.reduce((n,v)=>n+v.observed.length,0),34);
console.log(JSON.stringify({status:'pass',pipelines:2,orderedCalls:34,negativeControls,coherentWordMutations:wordCount*2}));
