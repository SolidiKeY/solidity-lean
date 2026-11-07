// Narrow history controls over the unchanged complete pinned physical report.
// These are finite EVM observations, not source/compiler/journal adequacy.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertDynamicStorageReport} from './dynamic-storage-reference.mjs';
const report=JSON.parse(readFileSync(process.argv[2],'utf8'));
assertDynamicStorageReport(report);
const max=((1n<<256n)-1n).toString();
const abi=xs=>'0x'+xs.map(x=>BigInt(x).toString(16).padStart(64,'0')).join('');
function history(v){
 const a=v.observed;
 assert.deepEqual(a.map(x=>x.signature),['readAll()','fill()','readAll()','shrink()','readAll()','regrow()','readAll()','failAfterWrite()','readAll()','outOfBounds()','staticProbe()','readAll()']);
 for(const i of [1,2,3,4,5,6,8,11]){
  const w=a[i].values;assert.equal(a[i].failed,false);assert.equal(a[i].exception,null);assert.equal(a[i].returnData,abi(w));
  assert.equal(w[0],w[1]);assert.equal(w[0],w[10]);assert.equal(w[2],w[12]);
  assert.deepEqual(w.slice(17,21),['12',max,'77','33']);
  assert.equal(w[6],'55');assert.equal(w[13],'55');assert.equal(w[14],'999');
  assert.deepEqual(w.slice(15,17),v.dataRoots);
 }
 for(const i of [1,2])assert.deepEqual(a[i].values.slice(0,6),['2','2','1','12',max,'33']);
 for(const i of [3,4])assert.deepEqual(a[i].values.slice(0,6),['0','0','0','0','0','0']);
 for(const i of [5,6,8,11])assert.deepEqual(a[i].values.slice(0,6),['3','3','1','12',max,'33']);
 assert.equal(a[7].failed,true);assert.equal(a[7].exception,'revert');assert.equal((a[7].returnData.length-2)/2,100);
 assert.equal(a[9].failed,true);assert.equal(a[9].returnData,'0x4e487b71'+(0x32n).toString(16).padStart(64,'0'));
 assert.deepEqual(a[10].values,['0']);assert.equal(a[10].failed,false);assert.equal(a[10].returnData,abi(['0']));
 for(const i of [6,8,11])assert.deepEqual(a[i].values,a[5].values);
}
let negatives=0;const clone=x=>JSON.parse(JSON.stringify(x));
for(const v of report.variants){
 history(v);
 const mutations=[];
 // Coherent ABI mutations discriminate lost dead words/stale ownership masks,
 // aliases, wrong headers, changed failed/static calls and wrong physical roots.
 for(const i of [1,2,3,4,5,6,8,11])for(const j of [0,1,2,10,12,15,16,17,18,19,20]){
  mutations.push(x=>{const w=x.observed[i].values;w[j]=String(BigInt(w[j])+1n);x.observed[i].returnData=abi(w);});
 }
 mutations.push(x=>[x.observed[3],x.observed[5]]=[x.observed[5],x.observed[3]],x=>x.observed.splice(4,1),
  x=>x.observed[7].failed=false,x=>x.observed[7].returnData='0x',x=>x.observed[9].returnData='0x',
  x=>{x.observed[10].values=['1'];x.observed[10].returnData=abi(['1']);},x=>x.dataRoots.reverse());
 for(const mutate of mutations){const bad=clone(v);mutate(bad);assert.throws(()=>history(bad));negatives++;}
}
assert.equal(negatives,190);
console.log(JSON.stringify({status:'pass',pipelines:2,orderedCalls:24,newCalls:0,negativeControls:negatives,boundary:'Unchanged finite external observations; actual source/residual rollback is proved separately in Lean.'}));
