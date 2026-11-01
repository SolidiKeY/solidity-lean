/** Bounded modern API controls; all EVM roots use explicit attempt budgets. */
import test from 'node:test';
import assert from 'node:assert/strict';
import {createRequire} from 'node:module';
import {readFileSync,mkdtempSync,rmSync,existsSync} from 'node:fs';
import {resolve,join} from 'node:path';
import {tmpdir} from 'node:os';
import {spawnSync} from 'node:child_process';
import {createHash} from 'node:crypto';
import {AttemptBudget,AttemptLimit,runWithAttemptBudget,verifyBudgetArtifact} from './attempt-budget.mjs';
const modules=process.argv[2];assert.ok(modules,'explicit derived node_modules required');
verifyBudgetArtifact(modules);
const req=createRequire(resolve(modules,'reference.cjs'));
const {createVM}=req('@ethereumjs/vm');
const {Common,Mainnet,Hardfork}=req('@ethereumjs/common');
const {createAddressFromString,hexToBytes}=req('@ethereumjs/util');
const {Interface}=req('ethers');
const to=createAddressFromString('0x0000000000000000000000000000000000001000');
const child=createAddressFromString('0x0000000000000000000000000000000000003000');
const caller=createAddressFromString('0x0000000000000000000000000000000000002000');
const fresh=()=>createVM({common:new Common({chain:Mainnet,hardfork:Hardfork.Cancun})});
const code=h=>hexToBytes('0x'+h);
async function raw(vm,hex,limit,records=[],gasLimit=30000000n){
 return runWithAttemptBudget(vm,'runCode',{to,caller,code:code(hex),gasLimit},
  {limit,label:'raw:'+hex,onRecord:r=>records.push(r)});
}
test('attempt budget invalid caps and exact N/N+1, successful-root reset, poisoned VM rejection',async()=>{
 for(const n of [0,-1,5000001,1.5])assert.throws(()=>new AttemptBudget(n),RangeError);
 const vm=await fresh(),records=[];
 assert.equal((await raw(vm,'600160020100',4,records)).exceptionError,undefined);
 assert.equal((await raw(vm,'600160020100',4,records)).exceptionError,undefined);
 assert.deepEqual(records.map(r=>r.used),[4,4]);
 await assert.rejects(raw(vm,'600160020100',3,records),AttemptLimit);
 assert.equal(records.at(-1).used,3);assert.equal(records.at(-1).status,'blocked');
 await assert.rejects(raw(vm,'',4),AttemptLimit); // no reuse even for zero code
 await assert.rejects(vm.evm.runCall({to:child,caller,gasLimit:30000000n}),AttemptLimit);
});
test('stop precedes dynamic-gas warming and storage effects',async()=>{
 const vm=await fresh(),slot=new Uint8Array(32),records=[];
 await vm.stateManager.putCode(to,code('00'));
 assert.equal(vm.evm.journal.isWarmedStorage(to.bytes,slot),false);
 await assert.rejects(raw(vm,'60015f5500',2,records),AttemptLimit);
 assert.equal(vm.evm.journal.isWarmedStorage(to.bytes,slot),false);
 assert.deepEqual(await vm.stateManager.getStorage(to,slot),new Uint8Array());
 assert.equal(records[0].used,2);
});
test('invalid STOP REVERT and static/dynamic OOG attempts counted exactly once',async()=>{
 for(const [hex,gas,used,error] of [
  ['fe',30000000n,1,'invalid opcode'],['00',30000000n,1,null],
  ['5f5ffd',30000000n,3,'revert'],['60ff',0n,1,'out of gas'],
  ['60015f5500',100n,3,'out of gas']]){
  const vm=await fresh(),records=[];await vm.stateManager.putCode(to,code('00'));
  const result=await raw(vm,hex,20,records,gas);
  assert.equal(result.exceptionError?.error??null,error,hex);
  assert.equal(records[0].used,used,hex);assert.equal(records[0].status,'completed');
 }
});
for(const [opcode,zeros,cap] of [['f1',5,9],['fa',4,8],['f4',4,8]])
 test('nested '+opcode+' shares the root budget and propagates synchronous host abort',async()=>{
  const hex='5f'.repeat(zeros)+'73'+child.toString().slice(2)+'61ffff'+opcode+'5000';
  const vm=await fresh();await vm.stateManager.putCode(to,code('00'));await vm.stateManager.putCode(child,code('600160020100'));
  const records=[];await assert.rejects(raw(vm,hex,cap,records),AttemptLimit);
  assert.equal(records[0].used,cap);assert.equal(records[0].maxDepth,1);
  const good=await fresh();await good.stateManager.putCode(to,code('00'));await good.stateManager.putCode(child,code('600160020100'));
  const allowed=[];assert.equal((await raw(good,hex,50,allowed)).exceptionError,undefined);
  assert.equal(allowed[0].used,zeros+9);assert.equal(allowed[0].maxDepth,1);
 });
test('CREATE init interpreter shares budget and cannot reset it',async()=>{
 const vm=await fresh(),records=[];
 await vm.stateManager.putCode(to,code('00'));
 await assert.rejects(raw(vm,'6004600d5f3960045f5ff0500060015000',9,records),AttemptLimit);
 assert.equal(records[0].used,9);assert.equal(records[0].maxDepth,1);
});
test('empty code and native precompile are honest zero interpreted attempts',async()=>{
 const vm=await fresh(),records=[];
 await raw(vm,'',1,records);
 const sha256=createAddressFromString('0x0000000000000000000000000000000000000002');
 const r=await runWithAttemptBudget(vm,'runCall',{to:sha256,caller,data:new Uint8Array(),gasLimit:30000000n},
  {limit:1,onRecord:r=>records.push(r)});
 assert.equal(Buffer.from(r.execResult.returnValue).toString('hex'),createHash('sha256').update(new Uint8Array()).digest('hex'));
 assert.deepEqual(records.map(r=>r.used),[0,0]);
});
test('host abort cannot become an expected EVM failure or allow next vector',async()=>{
 const vm=await fresh(),records=[];let reachedAssertion=false,next=false;
 await assert.rejects((async()=>{
  const result=await raw(vm,'5b600056',2,records);
  reachedAssertion=true;assert.ok(result.exceptionError);next=true;
 })(),AttemptLimit);
 assert.equal(reachedAssertion,false);assert.equal(next,false);assert.equal(records[0].status,'blocked');
});
test('existing process/descendant supervisor enforces host timeout independently',()=>{
 const dir=mkdtempSync(join(tmpdir(),'budget-process-'));
 try{
  const checkpoint=join(dir,'status.json'),pidFile=join(dir,'grandchild.pid');
  const script="const c=require('node:child_process').spawn(process.execPath,['-e','while(true){}'],{stdio:'ignore'});require('node:fs').writeFileSync("+JSON.stringify(pidFile)+",String(c.pid));require('node:fs').writeSync(1,'HOST_PREFIX');while(true){}";
  const result=spawnSync(process.execPath,['scripts/tool-job.mjs',checkpoint,'200',process.execPath,'-e',script],{encoding:'utf8',timeout:10000});
  assert.equal(result.status,1);assert.match(result.stdout,/HOST_PREFIX/);
  const status=JSON.parse(readFileSync(checkpoint));assert.equal(status.timedOut,true);assert.equal(status.signal,'SIGKILL');
  const pid=Number(readFileSync(pidFile,'utf8')),stat='/proc/'+pid+'/stat';
  if(existsSync(stat))assert.equal(readFileSync(stat,'utf8').split(') ')[1][0],'Z','owned descendant must be gone or terminated zombie');
 }finally{rmSync(dir,{recursive:true,force:true});}
});
const pinned=resolve(process.argv[3]);
assert.equal(createHash('sha256').update(readFileSync(pinned)).digest('hex'),'6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390');
const solc=req(pinned),compile=solc.cwrap('solidity_compile','string',['string','number','number']);
const source='contract C {uint x; function bump() external returns(uint){return ++x;} function fail() external {x=99;revert("kept");} function read() external view returns(uint){return x;} function child(bool b) external pure returns(uint){require(b,"kept");return 13;} function self(bool b) external returns(uint){try this.child(b) returns(uint n){return n;}catch Error(string memory m){return bytes(m).length;}}}';
for(const viaIR of [false,true])test('budgeted ordered state/rollback/actual self catch legacy-viaIR '+viaIR,async()=>{
 const out=JSON.parse(compile(JSON.stringify({language:'Solidity',sources:{'control.sol':{content:source}},settings:{viaIR,evmVersion:'cancun',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'*':['abi','evm.deployedBytecode.object']}}}}),0,0));
 assert.deepEqual((out.errors??[]).filter(e=>e.severity==='error'),[]);
 const c=out.contracts['control.sol'].C,iface=new Interface(c.abi),vm=await fresh(),records=[];
 await vm.stateManager.putCode(to,code(c.evm.deployedBytecode.object));
 for(const [name,args,value,failure]of [['bump',[],1,false],['fail',[],0,true],['read',[],1,false],['bump',[],2,false],['self',[true],13,false],['self',[false],4,false],['read',[],2,false]]){
  const result=await runWithAttemptBudget(vm,'runCall',{to,caller,data:hexToBytes(iface.encodeFunctionData(name,args)),gasLimit:30000000n},{label:viaIR+':'+name,onRecord:r=>records.push(r)});
  const exec=result.execResult;assert.equal(!!exec.exceptionError,failure);
  const expected=failure?new Interface(['error Error(string)']).encodeErrorResult('Error',['kept']):iface.encodeFunctionResult(name,[value]);
  assert.equal('0x'+Buffer.from(exec.returnValue).toString('hex'),expected);
 }
 assert.equal(records.length,7);assert.ok(records.every(r=>r.used<=5000000&&r.status==='completed'));
 console.log('ORDERED_BUDGET_CONTROL '+JSON.stringify({viaIR,records}));
});
