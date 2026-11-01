#!/usr/bin/env node
// Bounded actual encoded CALL observations; no general Source/world/gas proof.
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
assert.equal(fixtures.length,6,'missing/extra exported cases');
assert.equal(new Set(fixtures.map(v=>v.name)).size,6,'duplicate names');
const local99=[((1n<<256n)-7n).toString(),'99','17','29'];
const local13=[((1n<<256n)-9n).toString(),'13','17','29'];
const frame=n=>[((1n<<256n)-7n).toString(),String(n),'17','29'];
const spec={
  'ordinary-zero':{transferred:'0',entryGas:'2300',recipient:'4097',desiredTransfer:'0',accepts:true,returnData:'',bodyBytes:76,input:frame(0),flag:'1'},
  'ordinary99':{transferred:'99',entryGas:'2300',recipient:'4097',desiredTransfer:'99',accepts:true,returnData:'',bodyBytes:76,input:local99,flag:'1'},
  'ordinary13-same-code':{transferred:'13',entryGas:'2300',recipient:'4097',desiredTransfer:'13',accepts:true,returnData:'',bodyBytes:76,input:local13,flag:'1'},
  'ordinary99-revert':{transferred:'0',entryGas:'2300',recipient:'4097',desiredTransfer:'0',accepts:true,returnData:'dead',bodyBytes:76,input:local99,flag:'0'},
  'ordinary-unfunded':{transferred:'0',entryGas:'NONE',recipient:'4097',desiredTransfer:'0',accepts:true,returnData:'',bodyBytes:76,input:frame(1001),flag:'0'},
  'wrong-fixed2300':{transferred:'99',entryGas:'4600',recipient:'4097',desiredTransfer:'99',accepts:false,returnData:'',bodyBytes:73,input:local99,flag:'1'}
};
assert.deepEqual(fixtures.map(v=>v.name).sort(),Object.keys(spec).sort(),'exact required scenario set');
assert.equal(fixtures.filter(v=>v.accepts===true).length,5,'five required positive cases');
assert.equal(fixtures.filter(v=>v.accepts===false).length,1,'one required negative case');
for(const v of fixtures){
  const expected=spec[v.name];
  for(const key of ['transferred','recipient','desiredTransfer','desiredGas']){
    assert.equal(typeof v[key],'string',`${v.name}: required ${key}`);
    assert.match(v[key],/^(0|[1-9][0-9]*)$/,`${v.name}: canonical decimal ${key}`);
    assert.equal(v[key],key==='desiredGas'?'2300':expected[key],`${v.name}: exact ${key}`);
  }
  for(const key of ['accepts','returnData','entryGas']) assert.equal(v[key],key==='desiredGas'?'2300':expected[key],`${v.name}: exact ${key}`);
  assert.deepEqual(v.input,expected.input,`${v.name}: actual typed frame`);
  assert.deepEqual(v.expected,[expected.flag,...expected.input],`${v.name}: expected full stack`);
  assert.equal(v.body.length,expected.bodyBytes,`${v.name}: required emitter kind`);
  const seed=[0x60,0x55,0x7f,...Array(32).fill(0),0x53];
  for(const word of [...v.input].reverse()){
    const hex=BigInt(word).toString(16).padStart(64,'0');
    assert.equal(hex.length,64,'input word width');
    seed.push(0x7f,...Array.from({length:32},(_,i)=>parseInt(hex.slice(2*i,2*i+2),16)));
  }
  assert.deepEqual(v.preamble,seed,`${v.name}: exact memory/frame preamble`);
}
const byName=Object.fromEntries(fixtures.map(v=>[v.name,v]));
assert.deepEqual(byName['ordinary99'].body,byName['ordinary13-same-code'].body,'uniform runtime-local code');
assert.notEqual(byName['ordinary99'].input[1],byName['ordinary13-same-code'].input[1]);
for(const name of ['ordinary-zero','ordinary13-same-code','ordinary99-revert','ordinary-unfunded'])
  assert.deepEqual(byName[name].body,byName['ordinary99'].body,`${name}: uniform zero/nonzero runtime emitter`);
assert.deepEqual(byName['ordinary-unfunded'].callee,byName['ordinary99-revert'].callee,'same reverting receiver before/after funds check');
for(const name of ['ordinary-zero','ordinary99','ordinary13-same-code','wrong-fixed2300'])
  assert.deepEqual(byName[name].callee,[0],'actual STOP receiver');
const results=[];
for(const v of fixtures){
  for(const key of ['code','body','preamble','callee']){
    assert.ok(Array.isArray(v[key])&&v[key].length>0,`${v.name}: missing ${key}`);
    for(const b of v[key]) assert.ok(Number.isInteger(b)&&b>=0&&b<256,'not a byte');
  }
  assert.deepEqual(v.code,[...v.preamble,...v.body],'exact encoded concatenation');
  assert.equal(v.body.at(-1),0xf1,'actual terminal CALL opcode');
  assert.ok([73,76].includes(v.body.length),'actual emitted body width');
  assert.equal(v.expected.length,v.input.length+1,'protected frame plus CALL result');
  assert.equal(typeof v.accepts,'boolean');
  const common=new Common({chain:Mainnet,hardfork:Hardfork.Osaka,params:paramsEVM});
  assert.equal(common.hardfork(),'osaka');
  const evm=await createEVM({common});
  const self=createAddressFromBigInt(0xa000n),target=createAddressFromBigInt(BigInt(v.recipient));
  assert.notEqual(self.toString(),target.toString());
  await evm.stateManager.putAccount(self,new Account(0n,1000n));
  await evm.stateManager.putAccount(target,new Account(0n,0n));
  await evm.stateManager.putCode(self,Uint8Array.from(v.code));
  await evm.stateManager.putCode(target,Uint8Array.from(v.callee));
  let entryGas;
  evm.events.on('step',s=>{if(s.depth===1&&entryGas===undefined) entryGas=s.gasLeft.toString();});
  const r=await evm.runCode({code:Uint8Array.from(v.code),gasLimit:1000000n,to:self,caller:self});
  assert.equal(r.exceptionError,undefined,`${v.name}: ${r.exceptionError?.error}`);
  const actual=r.runState.stack.getStack().map(String).reverse();
  assert.deepEqual(actual,v.expected,`${v.name}: full stack`);
  assert.deepEqual(actual.slice(1),v.input,`${v.name}: protected caller frame`);
  const debit=1000n-(await evm.stateManager.getAccount(self)).balance;
  const credit=(await evm.stateManager.getAccount(target)).balance;
  assert.equal(debit,BigInt(v.transferred),`${v.name}: caller debit/rollback`);
  assert.equal(credit,BigInt(v.transferred),`${v.name}: recipient credit/rollback`);
  assert.equal(entryGas??'NONE',v.entryGas,`${v.name}: bounded callee entry gas observation`);
  const returned=Buffer.from(r.runState.returnBytes).toString('hex');
  assert.equal(returned,v.returnData,`${v.name}: exact nested return data`);
  assert.deepEqual(Array.from(r.runState.memory.read(0,32)),[0x55,...Array(31).fill(0)],`${v.name}: entire protected caller word`);
  assert.equal(r.runState.memoryWordCount,1n,`${v.name}: caller memory expansion unchanged`);
  assert.equal(credit===BigInt(v.desiredTransfer)&&(entryGas===undefined||entryGas===v.desiredGas),v.accepts,`${v.name}: desired-transfer positive/negative control`);
  results.push({name:v.name,kind:v.accepts?'positive':'negative',bodyBytes:v.body.length,
    codeSha256:createHash('sha256').update(Uint8Array.from(v.code)).digest('hex'),
    stack:actual,callerBalance:(1000n-debit).toString(),recipientBalance:credit.toString(),
    entryGas:entryGas??'NONE',returnData:returned,memory0:85,gasUsed:r.executionGasUsed.toString(),pass:true});
}
assert.ok(results.some(v=>v.kind==='negative'),'no negative control');
console.log(JSON.stringify({reference:'EthereumJS',evm:version('@ethereumjs/evm'),common:version('@ethereumjs/common'),
  hardfork:'osaka',gasLimit:'1000000',vectors:results.length,
  boundary:'bounded ordinary requested-gas selection with installed STOP/REVERT callees and funding-before-entry; not a kernel Source/world/fitted/enforced/fetched-decoder simulation',results},null,2));
