#!/usr/bin/env node
// Finite fetched-message execution. No kernel CALL/jump/world/gas simulation.
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
assert.equal(version('ethers'),'6.17.0');
const {keccak256}=req('ethers');
const fixtures=readFileSync(fixturePath,'utf8').split('\n').filter(l=>l.startsWith('{"name":')).map(JSON.parse);
const frame=(n,signed=-7n)=>[((1n<<256n)+signed).toString(),String(n),'17','29'];
const spec={
 'transfer-zero':{input:frame(0),halt:'none',balance:1000n,credit:0n,prior:0n,entry:'2300'},
 'transfer99':{input:frame(99),halt:'none',balance:901n,credit:99n,prior:0n,entry:'2300'},
 'transfer13':{input:frame(13,-9n),halt:'none',balance:987n,credit:13n,prior:0n,entry:'2300'},
 'transfer99-revert':{input:frame(99),halt:'revert',balance:1000n,credit:0n,prior:0n,entry:'2300',reverted:true},
 'transfer-unfunded':{input:frame(1001),halt:'revert',balance:1000n,credit:0n,prior:0n,entry:'NONE',reverted:true},
 'paid-prefix-success':{input:frame(99),halt:'none',balance:900n,credit:99n,prior:1n,entry:'2300',paid:true},
 'paid-prefix-failure':{input:frame(99),halt:'revert',balance:1000n,credit:0n,prior:0n,entry:'2300',paid:true,reverted:true},
 'wrong-relative':{input:frame(99),halt:'invalid JUMP',balance:1000n,credit:0n,prior:0n,entry:'2300',wrong:true}
};
assert.equal(fixtures.length,8,'all eight required scenarios');
assert.equal(new Set(fixtures.map(v=>v.name)).size,8,'no duplicate scenarios');
assert.deepEqual(fixtures.map(v=>v.name).sort(),Object.keys(spec).sort());
const byName=Object.fromEntries(fixtures.map(v=>[v.name,v]));
const emptyRevert=[0x7f,...Array(32).fill(0),0x7f,...Array(32).fill(0),0xfd];
const results=[];
for(const v of fixtures){
 const e=spec[v.name];
 assert.deepEqual(v.input,e.input,`${v.name}: complete typed caller input`);
 assert.equal(v.paidPrefix,!!e.paid);assert.equal(v.wrongRelative,!!e.wrong);
 for(const key of ['code','preamble','callBytes','firstPayment','assembledPrefix','callee']){
  assert.ok(Array.isArray(v[key]));
  for(const b of v[key]) assert.ok(Number.isInteger(b)&&b>=0&&b<256);
 }
 const seed=[0x60,0x55,0x7f,...Array(32).fill(0),0x53];
 for(const word of [...v.input].reverse()){
  const hex=BigInt(word).toString(16).padStart(64,'0');assert.equal(hex.length,64);
  seed.push(0x7f,...Array.from({length:32},(_,i)=>parseInt(hex.slice(2*i,2*i+2),16)));
 }
 assert.deepEqual(v.preamble,seed,'exact independent memory/frame seed');
 assert.equal(v.preamble.length,168);assert.equal(v.callBytes.length,76);
 assert.equal(v.callBytes.at(-1),0xf1);
 assert.deepEqual(v.callBytes,byName.transfer99.callBytes,'all dynamic CALL bytes identical');
 assert.equal(v.firstPayment.length,e.paid?106:0);
 if(e.paid){
  const pushWord=n=>[0x7f,...Array.from(Buffer.from(n.toString(16).padStart(64,'0'),'hex'))];
  assert.deepEqual(v.firstPayment,[0x60,0,0x80,0x80,0x80,...pushWord(1n),...pushWord(4098n),...pushWord(0n),0xf1,0x50],'entire first payment and discarded flag');
 }
 const prefix=e.wrong?v.callBytes:[...seed,...v.firstPayment,...v.callBytes];
 assert.deepEqual(v.assembledPrefix,prefix,'actual assembler coordinate prefix');
 const suffix=e.wrong?[0x15,0x60,83,0x57,0x60,151,0x56,0x5b,...emptyRevert,0x5b]:
  e.paid?[0x15,0x61,1,103,0x57,0x61,1,171,0x56,0x5b,...emptyRevert,0x5b]:
  [0x15,0x60,252,0x57,0x61,1,64,0x56,0x5b,...emptyRevert,0x5b];
 assert.deepEqual(v.code,[...(e.wrong?seed:[]),...prefix,...suffix],'entire independently expected assembled branch bytes');
 assert.equal(v.code.length,e.wrong?320:e.paid?428:321);
 if(e.reverted) assert.deepEqual(v.callee,byName['transfer99-revert'].callee,'same real reverting receiver');
 else assert.deepEqual(v.callee,[0],'actual STOP receiver');
 const common=new Common({chain:Mainnet,hardfork:Hardfork.Osaka,params:paramsEVM});
 assert.equal(common.hardfork(),'osaka');
 const evm=await createEVM({common});
 const self=createAddressFromBigInt(0xa000n),sender=createAddressFromBigInt(0xb000n);
 const target=createAddressFromBigInt(4097n),other=createAddressFromBigInt(4098n);
 for(const [addr,balance] of [[self,1000n],[sender,0n],[target,0n],[other,0n]])
  await evm.stateManager.putAccount(addr,new Account(0n,balance));
 await evm.stateManager.putCode(self,Uint8Array.from(v.code));
 await evm.stateManager.putCode(target,Uint8Array.from(v.callee));
 await evm.stateManager.putCode(other,Uint8Array.of(0));
 let entry='NONE',firstEntry='NONE',prefixObserved=null,eventError;
 evm.events.on('step',async(s,done)=>{
  try{
   if(s.depth===1&&s.address.toString()===target.toString()&&entry==='NONE') entry=s.gasLeft.toString();
   if(s.depth===1&&s.address.toString()===other.toString()&&firstEntry==='NONE') firstEntry=s.gasLeft.toString();
   if(e.paid&&s.depth===0&&s.pc===273){
    assert.equal(s.opcode.name,'POP');assert.equal(s.stack.at(-1),1n);
    assert.equal(prefixObserved,null,'exactly one first-prefix boundary');
    prefixObserved={self:(await evm.stateManager.getAccount(self)).balance.toString(),
     other:(await evm.stateManager.getAccount(other)).balance.toString(),
     target:(await evm.stateManager.getAccount(target)).balance.toString()};
   }
  }catch(error){eventError=error;}finally{done();}
 });
 // runCall fetches installed code and owns the real outer message journal;
 // runCode alone would not establish rollback of an earlier successful CALL.
 const message=await evm.runCall({to:self,caller:sender,value:0n,gasLimit:1000000n});
 if(eventError) throw eventError;
 const r=message.execResult,halt=r.exceptionError?.error??'none';
 const expectedHalt=e.wrong?`invalid JUMP at ${keccak256(Uint8Array.from(v.code))}/${self.toString()}:250`:e.halt;
 assert.equal(halt,expectedHalt,`${v.name}: exact outer halt including failing code/address/PC`);
 assert.equal(Buffer.from(r.returnValue).toString('hex'),'','outer transfer failure bytes are empty');
 const nestedData=Buffer.from(r.runState.returnBytes).toString('hex');
 assert.equal(nestedData,e.reverted&&e.entry!=='NONE'?'dead':'','exact nested result distinct from empty outer transfer halt');
 assert.deepEqual(r.runState.stack.getStack().map(String).reverse(),v.input,'branch consumes flag and preserves full caller stack');
 assert.deepEqual(Array.from(r.runState.memory.read(0,32)),[0x55,...Array(31).fill(0)]);
 assert.equal(r.runState.memoryWordCount,1n);
 assert.equal((await evm.stateManager.getAccount(self)).balance,e.balance);
 assert.equal((await evm.stateManager.getAccount(target)).balance,e.credit);
 assert.equal((await evm.stateManager.getAccount(other)).balance,e.prior);
 assert.equal((await evm.stateManager.getAccount(sender)).balance,0n);
 assert.equal(entry,e.entry,`${v.name}: real receiver entry/funds-before-entry`);
 assert.equal(firstEntry,e.paid?'2300':'NONE');
 assert.deepEqual(prefixObserved,e.paid?{self:'999',other:'1',target:'0'}:null,'actual successful first payment before resumed tail');
 const desiredHalt=e.wrong?'none':e.halt;
 assert.equal(halt===desiredHalt,!e.wrong,'wrong relocation rejects intended successful transfer');
 results.push({name:v.name,kind:e.wrong?'negative':'positive',codeBytes:v.code.length,
  codeSha256:createHash('sha256').update(Uint8Array.from(v.code)).digest('hex'),halt,
  returnData:'',nestedData,entryGas:entry,firstEntry,prefixObserved,callerBalance:e.balance.toString(),
  recipientBalance:e.credit.toString(),priorRecipientBalance:e.prior.toString(),pass:true});
}
console.log(JSON.stringify({reference:'EthereumJS',evm:version('@ethereumjs/evm'),hardfork:'osaka',gasLimit:'1000000',
 vectors:results.length,boundary:'finite fetched runCall with outer journal; no universal kernel CALL/jump/world/gas/profile simulation',results},null,2));
