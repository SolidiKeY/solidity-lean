#!/usr/bin/env node
// Finite independent message observations, not a kernel source/world simulation.
import {readFileSync} from 'node:fs';
import {createRequire} from 'node:module';
import {resolve} from 'node:path';
import {createHash} from 'node:crypto';
import assert from 'node:assert/strict';
const [fixturePath,modulesPath]=process.argv.slice(2);
assert.ok(fixturePath&&modulesPath,'expected EXPORT_LOG NODE_MODULES');
const req=createRequire(resolve(modulesPath,'reference.cjs'));
const version=m=>JSON.parse(readFileSync(resolve(modulesPath,m,'package.json'),'utf8')).version;
for(const m of ['@ethereumjs/common','@ethereumjs/evm','@ethereumjs/util']) assert.equal(version(m),'10.1.3');
const {Common,Mainnet,Hardfork}=req('@ethereumjs/common');
const {createEVM,paramsEVM}=req('@ethereumjs/evm');
const {Account,createAddressFromBigInt}=req('@ethereumjs/util');
const fixtures=readFileSync(fixturePath,'utf8').split('\n').filter(l=>l.startsWith('{"name":')).map(JSON.parse);
const spec={
 'false-to-true':{old:'0',amount:'1',flag:'1',balance:2n,credit:1n,entry:'2300'},
 'true-stays-true':{old:'1',amount:'1',flag:'1',balance:2n,credit:1n,entry:'2300'},
 'true-to-false':{old:'1',amount:'1',flag:'0',balance:3n,credit:0n,entry:'2300',reverted:true},
 'false-stays-false':{old:'0',amount:'1',flag:'0',balance:3n,credit:0n,entry:'2300',reverted:true},
 'funding-before-revert':{old:'1',amount:'4',flag:'0',balance:3n,credit:0n,entry:'NONE',reverted:true},
 'zero-value':{old:'0',amount:'0',flag:'1',balance:3n,credit:0n,entry:'2300'},
 'wrong-POP':{old:'0',amount:'1',flag:'1',balance:2n,credit:1n,entry:'2300',variant:'pop'},
 'wrong-SWAP2':{old:'0',amount:'1',flag:'1',balance:2n,credit:1n,entry:'2300',variant:'swap2'}
};
assert.equal(fixtures.length,8);assert.equal(new Set(fixtures.map(v=>v.name)).size,8);
assert.deepEqual(fixtures.map(v=>v.name).sort(),Object.keys(spec).sort());
const byName=Object.fromEntries(fixtures.map(v=>[v.name,v]));
const pushWord=n=>[0x7f,...Array.from(Buffer.from(n.toString(16).padStart(64,'0'),'hex'))];
const results=[];
for(const v of fixtures){
 const e=spec[v.name],input=[e.old,'99','17','29'];
 assert.deepEqual(v.input,input,'actual typed bool/uint locals and distinct spill');
 assert.equal(v.initialBalance,'3');assert.equal(v.amount,e.amount);assert.equal(v.variant,e.variant??'store');
 for(const key of ['code','body','preamble','callee']){
  assert.ok(Array.isArray(v[key])&&v[key].length>0);
  for(const b of v[key]) assert.ok(Number.isInteger(b)&&b>=0&&b<256);
 }
 const seed=[0x60,0x55,0x7f,...Array(32).fill(0),0x53];
 for(const word of [...input].reverse()) seed.push(...pushWord(BigInt(word)));
 assert.deepEqual(v.preamble,seed);assert.equal(seed.length,168);
 const gas=e.amount==='0'?2300n:0n;
 const call=[0x60,0,0x80,0x80,0x80,...pushWord(BigInt(e.amount)),...pushWord(4097n),...pushWord(gas),0xf1];
 const suffix=e.variant==='pop'?[0x50]:e.variant==='swap2'?[0x91,0x50]:[0x90,0x50];
 assert.deepEqual(v.body,[...call,...suffix],'entire independent literal CALL/store bytes');
 assert.equal(v.body.length,e.variant==='pop'?106:107);
 assert.deepEqual(v.code,[...seed,...v.body]);
 if(e.reverted) assert.deepEqual(v.callee,byName['true-to-false'].callee,'same rejecting receiver including unfunded case');
 else assert.deepEqual(v.callee,[0]);
 if(e.amount==='1'&&!e.variant) assert.deepEqual(v.body,byName['false-to-true'].body,'same code across old true/false and receiver success/revert');
 const common=new Common({chain:Mainnet,hardfork:Hardfork.Osaka,params:paramsEVM});
 assert.equal(common.hardfork(),'osaka');const evm=await createEVM({common});
 const self=createAddressFromBigInt(0xa000n),sender=createAddressFromBigInt(0xb000n),target=createAddressFromBigInt(4097n);
 for(const [address,balance] of [[self,3n],[sender,0n],[target,0n]]) await evm.stateManager.putAccount(address,new Account(0n,balance));
 await evm.stateManager.putCode(self,Uint8Array.from(v.code));
 await evm.stateManager.putCode(target,Uint8Array.from(v.callee));
 let entry='NONE',peak=0,callBoundary=null,storeBoundary=null,eventError;
 evm.events.on('step',async(s,done)=>{
  try{
   if(s.depth===1&&entry==='NONE') entry=s.gasLeft.toString();
   if(s.depth===0){
    peak=Math.max(peak,s.stack.length);
    if(s.pc===272){
     assert.equal(s.opcode.name,'CALL');assert.equal(callBoundary,null);
     callBoundary=s.stack.map(String).reverse();
    }
    if(s.pc===273){
     assert.equal(storeBoundary,null);
     storeBoundary={stack:s.stack.map(String).reverse(),self:(await evm.stateManager.getAccount(self)).balance.toString(),
      target:(await evm.stateManager.getAccount(target)).balance.toString()};
    }
   }
  }catch(error){eventError=error;}finally{done();}
 });
 const message=await evm.runCall({to:self,caller:sender,value:0n,gasLimit:1000000n});
 if(eventError) throw eventError;
 const r=message.execResult;assert.equal(r.exceptionError,undefined,'send returns normally after failed CALL');
 assert.equal(Buffer.from(r.returnValue).toString('hex'),'');
 const nestedData=Buffer.from(r.runState.returnBytes).toString('hex');
 assert.equal(nestedData,e.reverted&&e.entry!=='NONE'?'dead':'');assert.equal(entry,e.entry);
 assert.deepEqual(callBoundary,[gas.toString(),'4097',e.amount,'0','0','0','0',...input],'exact top-first CALL operand order');
 assert.deepEqual(storeBoundary,{stack:[e.flag,...input],self:e.balance.toString(),target:e.credit.toString()},'actual canonical CALL flag and world before physical store');
 const expected=e.variant==='pop'?[e.old,'99','17','29']:e.variant==='swap2'?[e.old,e.flag,'17','29']:[e.flag,'99','17','29'];
 const actual=r.runState.stack.getStack().map(String).reverse();assert.deepEqual(actual,expected);
 assert.equal(JSON.stringify(actual)===JSON.stringify([e.flag,'99','17','29']),!e.variant,'wrong store rejects intended complete typed frame');
 assert.equal(peak,11,'actual seven operand words above four protected words');
 assert.deepEqual(Array.from(r.runState.memory.read(0,32)),[0x55,...Array(31).fill(0)]);assert.equal(r.runState.memoryWordCount,1n);
 assert.equal((await evm.stateManager.getAccount(self)).balance,e.balance);assert.equal((await evm.stateManager.getAccount(target)).balance,e.credit);
 assert.equal((await evm.stateManager.getAccount(sender)).balance,0n);
 results.push({name:v.name,kind:e.variant?'negative':'positive',codeSha256:createHash('sha256').update(Uint8Array.from(v.code)).digest('hex'),
  bodyBytes:v.body.length,callBoundary,storeBoundary,stack:actual,entryGas:entry,nestedData,peak,memory0:85,pass:true});
}
console.log(JSON.stringify({reference:'EthereumJS',evm:version('@ethereumjs/evm'),hardfork:'osaka',gasLimit:'1000000',vectors:results.length,
 boundary:'finite independent fetched message plus typed local value encoding; no general Tx/world/frame/CALL/source/gas/profile simulation',results},null,2));
