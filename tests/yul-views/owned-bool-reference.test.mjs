import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertOwnedBoolReport} from './owned-bool-reference.mjs';
const r=JSON.parse(readFileSync(process.argv[2],'utf8'));assertOwnedBoolReport(r);
const W=1n<<256n;let n=0;
function reject(f){const x=structuredClone(r);f(x);assert.throws(()=>assertOwnedBoolReport(x));n++;}
reject(x=>x.variants.reverse());reject(x=>x.variants.pop());
for(let v=0;v<2;v++){
 for(const k of ['runtimeCodeBytes','sourceSha256','storageLayout','transientStorageLayout','methodIdentifiers','deployment','initialGas','stepLimit'])reject(x=>delete x.variants[v][k]);
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
 }
assert.equal(n,608);assert.equal(r.variants.length,2);assert.equal(r.variants.reduce((n,v)=>n+v.observed.length,0),34);
console.log(JSON.stringify({negativeControls:n,orderedCalls:34,pipelines:2,status:'pass'}));
