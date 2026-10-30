import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,mkdtempSync,rmSync,writeFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {join} from 'node:path';
import {tmpdir} from 'node:os';
import {COMPILER_SHA,parseFixture} from '../solidity-upstream.mjs';
import {hostGas,paymentVectors,replayPayments,runPaymentFixture} from './payment-replay.mjs';
import {referenceCompiler} from '../test-compiler.mjs';
const compiler=referenceCompiler();
assert.equal(createHash('sha256').update(readFileSync(compiler)).digest('hex'),COMPILER_SHA);
const solc=createRequire(import.meta.url)(compiler);
const c=solc.cwrap('solidity_compile','string',['string','number','number']);
const compile=input=>JSON.parse(c(JSON.stringify(input),0,0));
test('ordered payment parser retains funding, empty calldata and every gas row',()=>{
 const p=paymentVectors(parseFixture('contract C{}\n// ----\n// constructor(), 20 wei ->\n// gas legacy: 42\n// gas legacy code: 200\n// (), 10 wei ->\n'),[{type:'constructor',inputs:[],stateMutability:'payable'}]);
 assert.deepEqual(p.ordered.map(x=>x.kind),['call','gas','gas','call']);
 assert.deepEqual(p.vectors.map(x=>[x.signature,x.value]),[['constructor','20'],['()','10']]);
 assert.deepEqual(p.gas.map(x=>[x.vector,x.code,x.expected]),[[0,false,'42'],[0,true,'200']]);
 assert.throws(()=>paymentVectors({expectations:['gas legacy: 1']},[]),/without preceding/);
 assert.throws(()=>paymentVectors({expectations:['unadapted']},[]),/unadapted/);
});
test('pinned host accounts intrinsic, deposit and bounded refund independently',()=>{
 assert.deepEqual(hostGas([0,1],true,1000n,999999n,200n),{
 intrinsic:'53020',gross:'54020',refundApplied:'10804',used:'43216',codeDeposit:'200',nonCode:'43016'});
 assert.throws(()=>hostGas([],false,0n,-1n,0n),/invalid/);
});
for(const viaIR of [false,true])test(`real stipend receive and rollback preserve payload (viaIR=${viaIR})`,async()=>{
 const content='pragma solidity >=0.0; contract R { receive() external payable {revert("no_receive");} } contract C {R r=new R(); receive() external payable{} function g() external view returns(uint){return address(this).balance;} function f() external {payable(address(r)).transfer(1);} function h() external {payable(address(r)).transfer(100 ether);} }';
 const out=compile({language:'Solidity',sources:{'x.sol':{content}},settings:{viaIR,evmVersion:'osaka',debug:{revertStrings:'debug'},metadata:{appendCBOR:false},outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.methodIdentifiers']}}}});
 assert.deepEqual((out.errors??[]).filter(e=>e.severity==='error'),[]);
 const code=out.contracts['x.sol'].C;
 const payload=[8,195,121,160,...new Array(31).fill(0),32,...new Array(31).fill(0),10,...Buffer.from('no_receive'),...new Array(22).fill(0)];
 const v=(signature,expected=[],failure=false,extra={})=>({signature,args:[],expected,failure,...extra});
 const vectors=[v('()',[],false,{calldata:[],value:'10',expectedBytes:[]}),v('g()',['10']),v('f()',[],true,{revertBytes:payload}),v('h()',[],true,{revertBytes:[]}),v('g()',['10'])];
 const r=await replayPayments(code,vectors);assert.equal(r.status,'working',JSON.stringify(r));
 assert.equal(r.observed[2].returnData,'0x'+Buffer.from(payload).toString('hex'));
 assert.ok(r.observed[2].frames.some(f=>f.depth===1&&f.gasLimit==='2300'&&f.steps>0&&f.exception==='revert'));
 assert.equal(r.observed[3].frames.length,1,'insufficient funds does not invoke recipient');
 const wrong=await replayPayments(code,[...vectors.slice(0,2),v('f()',[],true,{revertBytes:[]})]);
 assert.equal(wrong.status,'broken','expected bytes never synthesize actual recipient output');
});
test('wrong gas observation stays broken',async()=>{
 const dir=mkdtempSync(join(tmpdir(),'payment-gas-control-'));
 try {writeFileSync(join(dir,'x.sol'),'contract C {constructor() payable{}}\n// ----\n// constructor(), 20 wei ->\n// gas legacy: 0\n');
 const r=await runPaymentFixture('x.sol',dir,compile);assert.equal(r.status,'broken');
 assert.equal(r.variants[0].gasObserved[0].matches,false);
 }finally{rmSync(dir,{recursive:true,force:true});}
});

test('early exact mismatch dominates later unexecuted gas observation',async()=>{
 const dir=mkdtempSync(join(tmpdir(),'payment-mismatch-control-'));
 try {writeFileSync(join(dir,'x.sol'),'contract C {function f() external pure returns(uint){return 1;}}\n// ----\n// f() -> 99\n// f() -> 1\n// gas legacy: 0\n');
 const r=await runPaymentFixture('x.sol',dir,compile);assert.equal(r.status,'broken');
 assert.equal(r.variants[0].reason,'exact payment observation mismatch');
 }finally{rmSync(dir,{recursive:true,force:true});}
});
test('failed creation payload host-gas mismatch is explicitly blocked',async()=>{
 const out=compile({language:'Solidity',sources:{'x.sol':{content:'pragma solidity >=0.0; contract C {constructor(){revert("keep");}}'}},settings:{outputSelection:{'*':{'*':['evm.bytecode.object','evm.methodIdentifiers']}}}});
 const r=await replayPayments(out.contracts['x.sol'].C,[{signature:'constructor',args:[],expected:[],failure:true}]);
 assert.equal(r.status,'blocked');assert.match(r.reason,/failed creation with return data/);
});
