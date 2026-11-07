import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertObjectAllocationReport,assertObjectAllocationVariant,vectors} from './object-allocation-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8')),clone=x=>JSON.parse(JSON.stringify(x));
const W=1n<<256n,abi=xs=>'0x'+xs.map(x=>{const w=BigInt(x);assert.ok(w>=0n&&w<W);return w.toString(16).padStart(64,'0');}).join('');
const coherent=(v,call,at,value)=>{v.observed[call].values[at]=BigInt(value).toString();v.observed[call].returnData=abi(v.observed[call].values);};
assertObjectAllocationReport(report);assert.equal(vectors.length,13);assert.equal(report.variants.length,2);
const base=[
 v=>v.status='blocked',v=>v.initialGas='100000001',v=>v.stepLimit=5000001,
 v=>delete v.inputSha256,v=>v.sourceSha256='0'.repeat(64),v=>v.parentSourceSha256='0'.repeat(64),
 v=>delete v.creationSha256,v=>delete v.runtimeSha256,v=>v.runtimeCodeBytes++,
 v=>delete v.deployment,v=>v.deployment.failed=true,v=>v.deployment.exception='revert',
 v=>v.deployment.returnData='0x01',v=>v.deployment.runtimeCodeSha256='wrong',v=>v.deployment.runtimeCodeBytes++,
 v=>v.methodIdentifiers['forward()']='00000000',v=>v.encodedCalls.reverse(),v=>v.vectors.pop(),v=>v.vectors.reverse(),
 v=>v.observed.pop(),v=>v.observed.reverse(),v=>[v.observed[1],v.observed[2]]=[v.observed[2],v.observed[1]],
 v=>v.storageLayout.storage[0].slot='1',v=>v.transientStorageLayout.storage=[{label:'fake',slot:'0',offset:0}],
 v=>v.deployment.steps=5000001,v=>v.deployment.gasUsed='100000001',
];assert.equal(base.length,26);
const extra=[
 v=>{[v.observed[2],v.observed[3]]=[v.observed[3],v.observed[2]];for(const i of [2,3]){v.observed[i].signature=vectors[i].signature;v.observed[i].calldata=v.encodedCalls[i];}},
 v=>coherent(v,2,6,4096),
 v=>coherent(v,2,6,1),
 v=>coherent(v,2,17,BigInt('0x998833'+'00'.repeat(29))),
 v=>{coherent(v,4,9,0);coherent(v,4,31,0);},
 v=>{coherent(v,2,11,4352);coherent(v,2,29,3);},
 v=>{coherent(v,2,13,1);coherent(v,2,32,1);},
];assert.equal(extra.length,7);
const wordCount=vectors.reduce((n,x)=>n+x.expected.length,0);assert.equal(wordCount,237);
let negativeControls=0;
for(const v of report.variants){
 for(const mutate of [...base,...extra]){const b=clone(v);mutate(b);assert.throws(()=>assertObjectAllocationVariant(b));negativeControls++;}
 for(let i=0;i<vectors.length;i++){
  const cases=[b=>b.observed[i].signature='wrong()',b=>b.observed[i].calldata='0x00000000',b=>b.observed[i].storage=['778'],b=>b.observed[i].logs=[['00',[],'00']],b=>{if(vectors[i].failure)b.observed[i].returnData='0x01';else{b.observed[i].failed=true;b.observed[i].exception='revert';}},b=>b.observed[i].steps=5000001,b=>b.observed[i].maxStack=1025];assert.equal(cases.length,7);
  for(const mutate of cases){const b=clone(v);mutate(b);assert.throws(()=>assertObjectAllocationVariant(b));negativeControls++;}
  for(let j=0;j<vectors[i].expected.length;j++){const b=clone(v);coherent(b,i,j,(BigInt(vectors[i].expected[j])+1n)%W);assert.throws(()=>assertObjectAllocationVariant(b));negativeControls++;}
 }
}
for(const mutate of [x=>x.variants.pop(),x=>x.variants.reverse(),x=>x.variants=[]]){const b=clone(report);mutate(b);assert.throws(()=>assertObjectAllocationReport(b));negativeControls++;}
assert.equal(negativeControls,725);assert.equal(report.variants.reduce((n,v)=>n+v.observed.length,0),26);
console.log(JSON.stringify({status:'pass',pipelines:2,orderedCalls:26,negativeControls,coherentWordMutations:wordCount*2}));
