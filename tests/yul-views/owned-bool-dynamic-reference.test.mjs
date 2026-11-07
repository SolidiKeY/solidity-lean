import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertOwnedBoolDynamicReport} from './owned-bool-dynamic-reference.mjs';
const r=JSON.parse(readFileSync(process.argv[2],'utf8'));assertOwnedBoolDynamicReport(r);
const W=1n<<256n;let n=0;
function reject(f){const x=structuredClone(r);f(x);assert.throws(()=>assertOwnedBoolDynamicReport(x));n++;}
reject(x=>x.variants.reverse());reject(x=>x.variants.pop());
for(let v=0;v<2;v++){
 for(const k of ['runtimeCodeBytes','dataRoot','sourceSha256','storageLayout','transientStorageLayout','methodIdentifiers','deployment','initialGas','stepLimit'])reject(x=>delete x.variants[v][k]);
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
assert.equal(r.variants.length,2);assert.equal(r.variants.reduce((n,v)=>n+v.observed.length,0),38);
for(let v=0;v<2;v++){
 reject(x=>x.variants[v].dataRoot='0');
 reject(x=>{const a=x.variants[v].storageLayout; a.types[a.types[a.storage[0].type].base].label='uint8';});
 reject(x=>{const o=x.variants[v].observed[1];o.values[8]=(BigInt(o.values[8])-(1n<<24n)).toString();o.storage[1]=o.values[8];o.returnData='0x'+o.values.map(y=>BigInt(y).toString(16).padStart(64,'0')).join('');});
 reject(x=>{const o=x.variants[v].observed[1];o.values[9]=(BigInt(o.values[9])-(2n<<8n)).toString();o.storage[2]=o.values[9];o.values[5]='32';o.values[7]='0';o.returnData='0x'+o.values.map(y=>BigInt(y).toString(16).padStart(64,'0')).join('');});
}
assert.equal(n,1032);
console.log(JSON.stringify({negativeControls:n,orderedCalls:38,pipelines:2,status:'pass'}));
