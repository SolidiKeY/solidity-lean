import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertJointMemoryReport,assertJointMemoryVariant} from './joint-memory-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8')).jointMemory;
const clone=x=>JSON.parse(JSON.stringify(x));
assertJointMemoryReport(report);let negatives=0;
const mutations=[
 x=>x.observed.pop(),x=>x.observed.reverse(),
 ...Array.from({length:7},(_,i)=>x=>x.observed[i].calldata='0x00000000'+'0'.repeat(128)),
 ...[[0,1],[0,2],[0,3],[1,2],[1,3],[2,3]].map(([a,b])=>x=>[x.observed[a],x.observed[b]]=[x.observed[b],x.observed[a]]),
 ...Array.from({length:34},(_,i)=>x=>x.observed[0].values[i]='999'),
 ...Array.from({length:7},(_,i)=>x=>x.observed[i].returnData='0x01'),
 x=>x.observed[0].values[1]='0',x=>x.observed[0].values[6]='11',x=>x.observed[1].values[7]='9',
 x=>x.observed[2].values[26]='0',x=>x.observed[3].values[31]='7',x=>x.observed[0].values[2]='16711850',
 x=>x.observed[4].returnData='0x',x=>x.observed[4].returnData=x.observed[4].returnData.slice(0,-2)+'33',x=>x.observed[4].failed=false,x=>x.observed[4].exception='out of gas',
 x=>x.observed[5].returnData=x.observed[4].returnData,x=>x.observed[5].failed=false,x=>x.observed[5].exception=null,
 x=>x.observed[6].values[31]='7',x=>x.observed[0].signature='wrong()',x=>x.storageWrites.push({value:'01'}),x=>x.deployment.storageWriteCount=1,
 ...Array.from({length:7},(_,i)=>x=>x.observed[i].storageWritesBefore=1),
 ...Array.from({length:7},(_,i)=>x=>x.observed[i].storageWritesAfter=1),
 x=>x.initialGas='100000001',x=>x.stepLimit=5000001,
 x=>delete x.deployment,x=>x.deployment.failed=true,x=>x.deployment.exception='revert',x=>x.deployment.returnData='0x01',
 x=>x.deployment.runtimeCodeSha256='wrong',x=>x.deployment.runtimeCodeBytes++,
 x=>delete x.sourceSha256,x=>{delete x.runtimeSha256;delete x.deployment.runtimeCodeSha256;},
 x=>x.observed[1].values[1]='0',x=>x.observed[2].values[24]='2',x=>x.observed[3].values[29]='9',x=>x.vectors[2].args=['0','0'],
 x=>x.vectors.pop(),x=>x.vectors.reverse(),x=>x.vectors[1].args=['0','0'],x=>x.vectors[0].args=['1','0'],
];
for(const v of report.variants)for(const mutate of mutations){const bad=clone(v);mutate(bad);assert.throws(()=>assertJointMemoryVariant(bad));negatives++;}
for(const mutate of [x=>x.variants.pop(),x=>x.variants.reverse(),x=>x.variants=[]]){const bad=clone(report);mutate(bad);assert.throws(()=>assertJointMemoryReport(bad));negatives++;}
assert.equal(negatives,213);console.log(JSON.stringify({pipelines:2,negativeControls:negatives,status:'pass'}));
