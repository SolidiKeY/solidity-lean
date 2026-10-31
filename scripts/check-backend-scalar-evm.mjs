#!/usr/bin/env node
// Execute actual Backend.encode output at pinned EthereumJS Osaka. This is
// external agreement evidence, distinct from the Lean kernel slice proofs.
// Usage: node scripts/check-backend-scalar-evm.mjs EXPORT_LOG NODE_MODULES
import {readFileSync} from 'node:fs';
import {createRequire} from 'node:module';
import {resolve} from 'node:path';
import assert from 'node:assert/strict';
const [fixturePath,modulesPath]=process.argv.slice(2);
if(!fixturePath||!modulesPath) throw new Error('expected EXPORT_LOG NODE_MODULES');
const req=createRequire(resolve(modulesPath,'reference.cjs'));
const version=m=>JSON.parse(readFileSync(resolve(modulesPath,m,'package.json'),'utf8')).version;
for(const m of ['@ethereumjs/common','@ethereumjs/evm']) assert.equal(version(m),'10.1.3');
const {Common,Mainnet,Hardfork}=req('@ethereumjs/common');
const {createEVM,paramsEVM}=req('@ethereumjs/evm');
const common=new Common({chain:Mainnet,hardfork:Hardfork.Osaka,params:paramsEVM});
const evm=await createEVM({common});
const fixtures=readFileSync(fixturePath,'utf8').split('\n').filter(l=>l.startsWith('{"name":')).map(JSON.parse);
assert.ok(fixtures.length>=40,'missing exported vectors');
assert.equal(new Set(fixtures.map(v=>v.name)).size,fixtures.length,'duplicate names');
const results=[];
for(const v of fixtures){
  assert.ok(Array.isArray(v.code)&&Array.isArray(v.body)&&Array.isArray(v.expected));
  assert.equal(typeof v.accepts,'boolean');
  for(const b of v.code) assert.ok(Number.isInteger(b)&&b>=0&&b<256);
  const prefix=v.code.slice(0,v.input.length*33);
  assert.deepEqual(v.code.slice(prefix.length),v.body,'body must be exact encoded suffix');
  for(const [i,word] of [...v.input].reverse().entries()){
    assert.equal(prefix[33*i],0x7f,'input must use real PUSH32');
    const hex=prefix.slice(33*i+1,33*i+33).map(b=>b.toString(16).padStart(2,'0')).join('');
    assert.equal(BigInt('0x'+hex),BigInt(word),'encoded input immediate');
  }
  const r=await evm.runCode({code:Uint8Array.from(v.code),gasLimit:1000000n});
  assert.equal(r.exceptionError,undefined,`${v.name}: ${r.exceptionError?.error}`);
  const actual=r.runState.stack.getStack().map(String).reverse();
  const agrees=actual.length===v.expected.length&&actual.every((w,i)=>w===v.expected[i]);
  assert.equal(agrees,v.accepts,`${v.name}: unexpected stack ${JSON.stringify(actual)}`);
  results.push({name:v.name,kind:v.accepts?'positive':'negative',gas:String(r.executionGasUsed),bodyBytes:v.body.length,pass:true});
}
assert.ok(results.some(r=>r.kind==='negative'),'missing negative control');
console.log(JSON.stringify({reference:'EthereumJS',evm:version('@ethereumjs/evm'),common:version('@ethereumjs/common'),hardfork:common.hardfork(),boundary:'actual encoded numeric/test slices; no generic branch/revert payload or source compiler proof',vectors:results.length,positive:results.filter(r=>r.kind==='positive').length,negative:results.filter(r=>r.kind==='negative').length,results},null,2));
