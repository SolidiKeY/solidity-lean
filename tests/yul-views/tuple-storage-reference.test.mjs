import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertTupleStorageReport} from './tuple-storage-reference.mjs';
const r=JSON.parse(readFileSync(process.argv[2],'utf8'));assertTupleStorageReport(r);
const W=1n<<256n;let n=0;
function reject(f){const x=structuredClone(r);f(x);assert.throws(()=>assertTupleStorageReport(x));n++;}
reject(x=>x.variants.reverse());reject(x=>x.variants.pop());
for(let v=0;v<2;v++){
 for(const k of ['runtimeCodeBytes','sourceSha256','dataRoots','storageLayout','transientStorageLayout','methodIdentifiers','deployment','initialGas','stepLimit'])reject(x=>delete x.variants[v][k]);
 reject(x=>{delete x.variants[v].runtimeCodeBytes;delete x.variants[v].deployment.runtimeCodeBytes;});
 for(const size of [0,-1,1.5,null,'12'])reject(x=>{x.variants[v].runtimeCodeBytes=size;x.variants[v].deployment.runtimeCodeBytes=size;});
 for(let i=0;i<r.variants[v].observed.length;i++){
  reject(x=>x.variants[v].observed.splice(i,1));reject(x=>x.variants[v].vectors.splice(i,1));reject(x=>x.variants[v].encodedCalls.splice(i,1));
  reject(x=>x.variants[v].observed[i].failed=!x.variants[v].observed[i].failed);
  reject(x=>x.variants[v].observed[i].returnData+='00');reject(x=>x.variants[v].observed[i].calldata='0x');
  reject(x=>delete x.variants[v].observed[i].storage);reject(x=>delete x.variants[v].observed[i].logs);
  reject(x=>x.variants[v].observed[i].logs.push(['00',[],'']));
  const a=r.variants[v].observed[i];
  for(let j=0;j<a.values.length;j++)reject(x=>{const o=x.variants[v].observed[i];o.values[j]=((BigInt(o.values[j])+1n)%W).toString();o.returnData='0x'+o.values.map(y=>BigInt(y).toString(16).padStart(64,'0')).join('');});
  for(let j=0;j<a.storage.length;j++)reject(x=>{const o=x.variants[v].observed[i];o.storage[j]=((BigInt(o.storage[j])+1n)%W).toString();});
  if(i)reject(x=>{const a=x.variants[v].observed;[a[i],a[i-1]]=[a[i-1],a[i]];});
 }
 reject(x=>x.variants[v].dataRoots[0]=x.variants[v].dataRoots[1]);
 reject(x=>{const t=x.variants[v].storageLayout;t.types[t.types[t.storage[0].type].base].numberOfBytes='32';});
 reject(x=>{const t=x.variants[v].storageLayout;t.types[t.types[t.storage[0].type].base].members[1].slot='0';});
 // Caller-held aliases must observe3, not a stale2 after empty-local child work.
 reject(x=>{const o=x.variants[v].observed[1];o.values[1]='2';o.returnData='0x'+o.values.map(y=>BigInt(y).toString(16).padStart(64,'0')).join('');});
 // Erasing residual padding, missing child rollback, and reversing regrowth.
 reject(x=>x.variants[v].observed[2].storage[2]=(BigInt(x.variants[v].observed[2].storage[2])% (1n<<240n)).toString());
 reject(x=>x.variants[v].observed[2].storage[5]='222');
 reject(x=>x.variants[v].observed[5].storage[5]='333');
 reject(x=>x.variants[v].observed[3].storage[0]='0');
 reject(x=>x.variants[v].observed.find(a=>a.signature==='successThenOuterRevert()').returnData='0x');
}
for(let v=0;v<2;v++){
 reject(x=>delete x.variants[v].tupleProducer);
 reject(x=>x.variants[v].tupleProducer.returns.pop());
 reject(x=>x.variants[v].tupleProducer.returns[1][1]='memory');
 reject(x=>x.variants[v].tupleProducer.callerNames.reverse());
 reject(x=>x.variants[v].tupleProducer.callee='other');
}
assert.equal(n,662);assert.equal(r.variants.length,2);assert.equal(r.variants.reduce((s,v)=>s+v.observed.length,0),24);
console.log(JSON.stringify({status:'pass',negativeControls:n,pipelines:2,orderedCalls:24}));
