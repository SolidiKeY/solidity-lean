#!/usr/bin/env node
// Finite creation/session validation; raw code reads are internal test oracles,
// not newly admitted source observations or a kernel source/world simulation.
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
assert.equal(version('ethers'),'6.17.0');
const {Common,Mainnet,Hardfork}=req('@ethereumjs/common');
const {createEVM,paramsEVM}=req('@ethereumjs/evm');
const {Account,createAddressFromBigInt}=req('@ethereumjs/util');
const {getCreateAddress,keccak256}=req('ethers');
const fixtures=readFileSync(fixturePath,'utf8').split('\n').filter(l=>l.startsWith('{"name":')).map(JSON.parse);
const spec={
 'deploy-transfer':{},
 'deploy-then-receiver-revert':{reject:true},
 'constructor-revert':{ctorRevert:true},
 'wrong-runtime-base':{wrongBase:true,negative:true},
 'arguments-leak':{leak:true,negative:true},
 'empty-runtime':{empty:true},
 'two-instances':{two:true},
 'occupied-address':{occupied:true}
};
assert.equal(fixtures.length,8);assert.equal(new Set(fixtures.map(v=>v.name)).size,8);
assert.deepEqual(fixtures.map(v=>v.name).sort(),Object.keys(spec).sort());
const pushWord=n=>[0x7f,...Array.from(Buffer.from(n.toString(16).padStart(64,'0'),'hex'))];
const frame=[((1n<<256n)-7n).toString(),'99','17','29'];
const prelude=[0x60,0x55,...pushWord(0n),0x53];
for(const w of [...frame].reverse()) prelude.push(...pushWord(BigInt(w)));
assert.equal(prelude.length,168);
const call=[0x60,0,0x80,0x80,0x80,0x85,...pushWord(4097n),0x81,0x15,...pushWord(2300n),0x02,0xf1];
assert.equal(call.length,76);
const failure=[...pushWord(0n),...pushWord(0n),0xfd];
const goodRuntime=[...prelude,...call,0x15,0x60,252,0x57,0x61,1,64,0x56,0x5b,...failure,0x5b];
const badRuntime=[...prelude,...call,0x15,0x61,1,15,0x57,0x61,1,83,0x56,0x5b,...failure,0x5b];
assert.equal(goodRuntime.length,321);assert.equal(badRuntime.length,322);
const copyPrefix=[0x60,1,0x5f,0x60,32,0x39],args=[0xaa,0xbb];
const byName=Object.fromEntries(fixtures.map(v=>[v.name,v]));
const hash=bytes=>createHash('sha256').update(Uint8Array.from(bytes)).digest('hex');
const results=[];
for(const v of fixtures){
 const e=spec[v.name];
 for(const key of ['runtime','initcode','callee','paymentRuntime','args']){
  assert.ok(Array.isArray(v[key]));for(const b of v[key]) assert.ok(Number.isInteger(b)&&b>=0&&b<256);
 }
 assert.deepEqual(v.paymentRuntime,goodRuntime,'entire independent canonical assembled runtime');
 assert.deepEqual(v.args,args);
 const expectedRuntime=e.empty?[]:e.wrongBase?badRuntime:e.leak?[...goodRuntime,...args]:goodRuntime;
 assert.deepEqual(v.runtime,expectedRuntime);
 const n=expectedRuntime.length;
 const terminal=e.ctorRevert?0xfd:0xf3;
 const wrapper=e.empty?[0x5f,0x60,14,0x5f,0x39,0x5f,0x5f,terminal]:
  [0x61,Math.floor(n/256),n%256,0x60,18,0x5f,0x39,0x61,Math.floor(n/256),n%256,0x5f,terminal];
 assert.deepEqual(v.initcode,[...copyPrefix,...wrapper,...expectedRuntime,...(e.leak?[]:args)],'whole constructor byte program and argument interval');
 assert.equal(copyPrefix.length+wrapper.length,e.empty?14:18);
 if(e.reject) assert.deepEqual(v.callee,byName['deploy-then-receiver-revert'].callee);
 else assert.deepEqual(v.callee,[0]);
 const common=new Common({chain:Mainnet,hardfork:Hardfork.Osaka,params:paramsEVM});assert.equal(common.hardfork(),'osaka');
 const evm=await createEVM({common});
 const deployer=createAddressFromBigInt(0xa000n),target=createAddressFromBigInt(4097n);
 for(const [address,balance] of [[deployer,2000n],[target,0n]]) await evm.stateManager.putAccount(address,new Account(0n,balance));
 await evm.stateManager.putCode(target,Uint8Array.from(v.callee));
 const predicted=[];
 for(let nonce=0;nonce<2;nonce++){
  const native=v['create'+nonce];assert.match(native,/^(0|[1-9][0-9]*)$/);
  assert.ok(BigInt(native)<(1n<<160n));
  const expected=getCreateAddress({from:deployer.toString(),nonce}).toLowerCase();
  assert.equal('0x'+BigInt(native).toString(16).padStart(40,'0'),expected,'actual published withKeccak CREATE predictor vs pinned reference');
  predicted.push(createAddressFromBigInt(BigInt(native)));
 }
 assert.notEqual(predicted[0].toString(),predicted[1].toString(),'finite fresh-instance identity');
 for(const p of predicted){assert.notEqual(p.toString(),deployer.toString());assert.notEqual(p.toString(),target.toString());assert.ok(BigInt(p.toString())>256n);}
 if(e.occupied) await evm.stateManager.putAccount(predicted[0],new Account(1n,7n));
 let phase='constructor',constructorSteps=0,constructorCalls=0,constructorPeak=0,runtimePeak=0,entry='NONE';
 evm.events.on('step',(s)=>{
  if(phase==='constructor'){
   constructorSteps++;constructorPeak=Math.max(constructorPeak,s.stack.length);
   if(s.opcode.name==='CALL') constructorCalls++;
  }else{
   if(s.depth===0) runtimePeak=Math.max(runtimePeak,s.stack.length);
   if(s.depth===1&&s.address.toString()===target.toString()&&entry==='NONE') entry=s.gasLeft.toString();
  }
 });
 const value=e.two?100n:1000n;
 const first=await evm.runCall({caller:deployer,value,gasLimit:1000000n,data:Uint8Array.from(v.initcode)});
 assert.equal(first.createdAddress?.toString(),predicted[0].toString(),'actual returned candidate address, not necessarily an installed handle');
 const c=first.execResult;
 const ctorHalt=c.exceptionError?.error??'none';
 assert.equal(ctorHalt,e.occupied?'create collision':e.ctorRevert?'revert':'none');
 assert.equal(constructorSteps,e.occupied?0:11,'runtime data is not executed during constructor');
 assert.equal(constructorCalls,0);assert.equal(constructorPeak,e.occupied?0:3);
 const constructorData=Buffer.from(c.returnValue).toString('hex');
 assert.equal(constructorData,e.occupied?'':Buffer.from(v.runtime).toString('hex'),'exact constructor return/revert bytes exclude arguments');
 if(!e.occupied){
  assert.deepEqual(c.runState.stack.getStack(),[],'actual constructor protocol starts/ends empty');
  assert.equal(c.runState.memoryWordCount,e.empty?2n:11n,'actual rounded constructor memory');
 }
 let account=await evm.stateManager.getAccount(predicted[0]);
 if(e.ctorRevert||e.occupied){
  assert.deepEqual(Array.from(await evm.stateManager.getCode(predicted[0])),[],'failed creation does not install runtime');
  if(e.occupied){assert.ok(account);assert.equal(account.nonce,1n);assert.equal(account.balance,7n);}
  else assert.equal(account,undefined,'fresh failed constructor account rolled back');
  const owner=await evm.stateManager.getAccount(deployer);assert.equal(owner.balance,2000n);assert.equal(owner.nonce,1n,'top-level creator nonce increment is retained');
  assert.equal((await evm.stateManager.getAccount(target)).balance,0n);
  results.push({name:v.name,kind:'positive',candidate:predicted[0].toString(),ctorHalt,constructorData,
   installed:false,existingOccupiedAccount:!!e.occupied,constructorPeak,constructorSteps,pass:true});
  continue;
 }
 assert.ok(account);assert.equal(account.nonce,1n);assert.equal(account.balance,value);
 assert.deepEqual(Array.from(await evm.stateManager.getCode(predicted[0])),v.runtime,'exact installed runtime');
 let owner=await evm.stateManager.getAccount(deployer);assert.equal(owner.balance,2000n-value);assert.equal(owner.nonce,1n);
 if(e.two){
  const second=await evm.runCall({caller:deployer,value:100n,gasLimit:1000000n,data:Uint8Array.from(v.initcode)});
  assert.equal(second.execResult.exceptionError,undefined);assert.equal(second.createdAddress?.toString(),predicted[1].toString());
  assert.deepEqual(Array.from(await evm.stateManager.getCode(predicted[1])),v.runtime);
  const other=await evm.stateManager.getAccount(predicted[1]);assert.equal(other.nonce,1n);assert.equal(other.balance,100n);
  assert.equal(constructorSteps,22);assert.equal(constructorPeak,3);assert.equal(constructorCalls,0);
 }
 phase='runtime';
 const called=await evm.runCall({to:predicted[0],caller:deployer,value:0n,gasLimit:1000000n});
 const r=called.execResult,halt=r.exceptionError?.error??'none';
 const expectedHalt=e.wrongBase?`invalid JUMP at ${keccak256(Uint8Array.from(v.runtime))}/${predicted[0].toString()}:252`:
  e.leak?'invalid opcode':e.reject?'revert':'none';
 assert.equal(halt,expectedHalt,'exact fetched-runtime halt including full bad-jump context');
 assert.equal(Buffer.from(r.returnValue).toString('hex'),'');
 const failed=!!(e.wrongBase||e.leak||e.reject);
 if(e.empty){assert.equal(r.runState,undefined);assert.equal(runtimePeak,0);assert.equal(entry,'NONE');}
 else{
  assert.deepEqual(r.runState.stack.getStack().map(String).reverse(),frame,'full protected runtime frame');
  assert.deepEqual(Array.from(r.runState.memory.read(0,32)),[0x55,...Array(31).fill(0)]);assert.equal(r.runState.memoryWordCount,1n);
  assert.equal(Buffer.from(r.runState.returnBytes).toString('hex'),e.reject?'dead':'');
  assert.equal(runtimePeak,12);assert.equal(entry,'2300');
 }
 const credit=e.empty||failed?0n:99n;
 account=await evm.stateManager.getAccount(predicted[0]);assert.equal(account.nonce,1n);assert.equal(account.balance,value-credit);
 assert.deepEqual(Array.from(await evm.stateManager.getCode(predicted[0])),v.runtime,'deployment is retained after later message failure');
 assert.equal((await evm.stateManager.getAccount(target)).balance,credit);
 owner=await evm.stateManager.getAccount(deployer);assert.equal(owner.balance,e.two?1800n:1000n);assert.equal(owner.nonce,e.two?3n:2n);
 if(e.two){const other=await evm.stateManager.getAccount(predicted[1]);assert.equal(other.balance,100n);assert.equal(other.nonce,1n);assert.notEqual(other.balance,account.balance,'wrong-instance alias control');}
 assert.equal(JSON.stringify(v.runtime)===JSON.stringify(e.empty?[]:goodRuntime),!e.negative,'wrong relocation/argument leak reject intended runtime identity');
 results.push({name:v.name,kind:e.negative?'negative':'positive',candidate:predicted[0].toString(),secondCandidate:e.two?predicted[1].toString():null,
  ctorHalt,constructorData,runtimeBytes:v.runtime.length,initcodeBytes:v.initcode.length,installedRuntimeSha256:hash(v.runtime),
  halt,constructorPeak,constructorSteps,runtimePeak,entryGas:entry,callerBalance:account.balance.toString(),recipientBalance:credit.toString(),pass:true});
}
assert.equal(results.filter(v=>v.kind==='positive').length,6);assert.equal(results.filter(v=>v.kind==='negative').length,2);
console.log(JSON.stringify({reference:'EthereumJS',evm:version('@ethereumjs/evm'),hardfork:'osaka',gasLimit:'1000000',vectors:results.length,
 boundary:'finite CREATE/installed-runtime session observations and internal artifact validation; not kernel Source/world/nonce/gas/fetched semantics or a new raw-code source observation',results},null,2));
