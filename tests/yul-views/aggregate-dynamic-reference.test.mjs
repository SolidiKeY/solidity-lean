import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {assertAggregateReport} from './aggregate-dynamic-reference.mjs';
const r=JSON.parse(readFileSync(process.argv[2],'utf8'));assertAggregateReport(r);
let n=0;const reject=f=>{const x=structuredClone(r);f(x);assert.throws(()=>assertAggregateReport(x));n++;};
reject(x=>x.variants.reverse());reject(x=>x.variants.pop());
for(let v=0;v<2;v++){
 for(const k of ['runtimeCodeBytes','sourceSha256','dataRoots','storageLayout','transientStorageLayout','methodIdentifiers','deployment','initialGas','stepLimit'])reject(x=>delete x.variants[v][k]);
 reject(x=>{delete x.variants[v].runtimeCodeBytes;delete x.variants[v].deployment.runtimeCodeBytes;});
 for(const size of [0,-1,1.5,null,'12'])reject(x=>{x.variants[v].runtimeCodeBytes=size;x.variants[v].deployment.runtimeCodeBytes=size;});
 for(let i=0;i<r.variants[v].observed.length;i++){
  reject(x=>x.variants[v].observed.splice(i,1));reject(x=>x.variants[v].vectors.splice(i,1));reject(x=>x.variants[v].encodedCalls.splice(i,1));
  reject(x=>x.variants[v].observed[i].failed=!x.variants[v].observed[i].failed);
  reject(x=>x.variants[v].observed[i].returnData+='00');reject(x=>x.variants[v].observed[i].calldata='0x');
  const a=r.variants[v].observed[i];
  for(let j=0;j<a.values.length;j++)reject(x=>{const o=x.variants[v].observed[i];o.values[j]=((BigInt(o.values[j])+1n)%(1n<<256n)).toString();o.returnData='0x'+o.values.map(y=>BigInt(y).toString(16).padStart(64,'0')).join('');});
  if(i)reject(x=>{const a=x.variants[v].observed;[a[i],a[i-1]]=[a[i-1],a[i]];});
 }
 reject(x=>x.variants[v].dataRoots[0]=x.variants[v].dataRoots[1]);
 reject(x=>{const t=x.variants[v].storageLayout;t.types[t.types[t.storage[0].type].base].numberOfBytes='96';});
 reject(x=>{const t=x.variants[v].storageLayout; t.types[t.types[t.storage[0].type].base].members[1].slot='2';});
 reject(x=>x.variants[v].observed.find(a=>a.signature==='failAfterWrite()').returnData='0x');
 // Coherent corruption of the late post-revert sentinel must still fail.
 reject(x=>{const o=x.variants[v].observed.at(-1);o.values[14]='222';o.returnData='0x'+o.values.map(y=>BigInt(y).toString(16).padStart(64,'0')).join('');});
}
assert.equal(n,494);assert.equal(r.variants.length,2);assert.equal(r.variants.reduce((s,v)=>s+v.observed.length,0),26);
console.log(JSON.stringify({status:'pass',negativeControls:n,pipelines:2,orderedCalls:r.variants.reduce((s,v)=>s+v.observed.length,0)}));
