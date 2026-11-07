import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertOwnedInventoryReport,assertOwnedInventoryVariant} from './owned-inventory-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8')).ownedInventory;
assertOwnedInventoryReport(report);
const clone=x=>JSON.parse(JSON.stringify(x));
const badWord=(call,word)=>v=>{const a=v.observed[call];a.values[word]=String(BigInt(a.values[word])+1n);a.returnData='0x'+a.values.map(x=>BigInt(x).toString(16).padStart(64,'0')).join('');};
const mutations=[v=>v.observed.pop(),v=>v.observed.reverse(),
 ...report.variants[0].observed.flatMap((a,i)=>a.failed?[]:a.values.map((_,j)=>badWord(i,j))),
 ...Array.from({length:10},(_,i)=>v=>v.observed[i].returnData='0x01'),
 ...Array.from({length:10},(_,i)=>v=>v.observed[i].calldata='0x00000000'),
 ...Array.from({length:10},(_,i)=>v=>v.observed[i].signature='wrong()'),
 ...Array.from({length:7},(_,a)=>Array.from({length:6-a},(_,b)=>[a,a+b+1])).flat().map(([a,b])=>v=>[v.observed[a],v.observed[b]]=[v.observed[b],v.observed[a]]),
 v=>v.observed[7].returnData='0x',v=>v.observed[7].returnData=v.observed[7].returnData.slice(0,-2)+'33',v=>v.observed[7].failed=false,v=>v.observed[7].exception='out of gas',
 v=>v.observed[8].returnData=v.observed[7].returnData,v=>v.observed[8].failed=false,v=>v.observed[8].exception=null,
 ...Array.from({length:10},(_,i)=>v=>v.observed[i].storageWritesBefore=1),
 ...Array.from({length:10},(_,i)=>v=>v.observed[i].storageWritesAfter=1),
 v=>v.storageWrites.push({value:'01'}),v=>v.deployment.storageWriteCount=1,v=>v.initialGas='100000001',v=>v.stepLimit=5000001,
 v=>delete v.deployment,v=>v.deployment.failed=true,v=>v.deployment.exception='revert',v=>v.deployment.returnData='0x01',
 v=>v.deployment.runtimeCodeSha256='wrong',v=>v.deployment.runtimeCodeBytes++,v=>delete v.sourceSha256,
 v=>{delete v.runtimeSha256;delete v.deployment.runtimeCodeSha256;},v=>v.vectors.pop(),v=>v.vectors.reverse(),
 v=>v.vectors[1].args=['3','0','0'],v=>v.vectors[4].args=['3','0','1'],
];
let negatives=0;
for(const v of report.variants)for(const mutate of mutations){const bad=clone(v);mutate(bad);assert.throws(()=>assertOwnedInventoryVariant(bad));negatives++;}
for(const mutate of [v=>v.variants.pop(),v=>v.variants.reverse(),v=>v.variants=[]]){const bad=clone(report);mutate(bad);assert.throws(()=>assertOwnedInventoryReport(bad));negatives++;}
assert.equal(mutations.length,337);assert.equal(negatives,677);
console.log(JSON.stringify({pipelines:2,negativeControls:negatives,completeWordMutations:241,status:'pass'}));
