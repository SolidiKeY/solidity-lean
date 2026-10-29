import {libraryTryContext,libraryTryVectorsFixture} from '../library-try-adapter.mjs';
import {SELF_TRY_ADDRESS} from '../self-try-adapter.mjs';
import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync, writeFileSync, mkdtempSync, rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {createRequire} from 'node:module';
import {createHash} from 'node:crypto';
import {resolve} from 'node:path';
import {hexToBytes} from '@ethereumjs/util';
import {COMPILER_SHA, revertBytes, parseFixture, semanticVectors} from '../solidity-upstream.mjs';
import {machine, observation, replayBytecode, HostLimit, INITIAL_GAS, runFixture} from './replay.mjs';

// Reference compiler controls use the same integrity gate as the CLI.
const compiler = resolve(process.env.SOLC_REFERENCE ?? '/workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js');
assert.equal(createHash('sha256').update(readFileSync(compiler)).digest('hex'), COMPILER_SHA);
const solc = createRequire(import.meta.url)(compiler);
const compile = solc.cwrap('solidity_compile','string',['string','number','number']);
const source = 'pragma solidity >=0.0; contract C { uint x=5; function bump() external returns(uint) {return ++x;} function fail() external {x=99; revert();} function spin() external pure {while(true){}} }';
function artifact(viaIR, content = source) {
  const out = JSON.parse(compile(JSON.stringify({language:'Solidity',sources:{'control.sol':{content}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false},metadata:{appendCBOR:false},outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.methodIdentifiers']}}}}),0,0));
  assert.deepEqual((out.errors ?? []).filter(e=>e.severity === 'error'), []);
  return out.contracts['control.sol'].C;
}
const vector = (signature, expected=[], failure=false) => ({signature,args:[],expected,failure});
for (const viaIR of [false,true]) {
  test(`stateful ordering, rollback and wrong-output control (viaIR=${viaIR})`, async () => {
    const code = artifact(viaIR);
    const result = await replayBytecode(code,[vector('bump()',['6']),vector('fail()',[],true),vector('bump()',['7'])]);
    assert.equal(result.status,'working',JSON.stringify(result));
    assert.equal(result.observed.length,3);
    assert.equal(result.observed[1].exception,'revert');
    assert.equal(result.observed[0].gasUsed,result.observed[2].gasUsed,
      'each successful SSTORE uses a fresh transaction original/warmth cache');
    const wrong = await replayBytecode(code,[vector('bump()',['999'])]);
    assert.equal(wrong.status,'broken');
    assert.deepEqual(wrong.observed[0].values,['6']);
  });
  test(`host instruction exhaustion never matches FAILURE and retains prefix (viaIR=${viaIR})`, async () => {
    const result = await replayBytecode(artifact(viaIR),[vector('bump()',['6']),vector('spin()',[],true)],2000);
    assert.equal(result.status,'blocked');
    assert.match(result.reason,/instruction budget exhausted/);
    assert.deepEqual(result.observed.map(x=>x.values),[['6']]);
    assert.equal(result.blockedVector.signature,'spin()');
  });
}
test('bounded EVM stack overflow is an actual machine exception, not host fuel',async () => {
  const vm = await machine();
  const {result,metrics} = await vm.call({data:hexToBytes('0x5b6001600056')});
  const actual = observation(result.execResult,'stack()',metrics);
  assert.equal(actual.exception,'stack overflow');
  assert.equal(actual.maxStack,1024);
  assert.equal(actual.failed,true);
  assert.equal(actual.returnData,'0x');
  assert.ok(actual.steps < 10_000);
  assert.equal(actual.gasUsed,INITIAL_GAS.toString());
});
test('unexpected engine exceptions stay unadapted',()=>{
  assert.throws(()=>observation({exceptionError:{error:'configuration failure'}},'bad()',{}),HostLimit);
});

for (const viaIR of [false,true]) {
  test(`constructor failure data and default deployment logs retained (viaIR=${viaIR})`,async()=>{
    const reverting = artifact(viaIR,'pragma solidity >=0.0; contract C { constructor(){revert("keep");} function bump() external pure {} }');
    const explicit = await replayBytecode(reverting,[vector('constructor',[],true)]);
    assert.equal(explicit.status,'broken'); // FAILURE expects empty bytes.
    assert.notEqual(explicit.observed[0].returnData,'0x');
    const implicit = await replayBytecode(reverting,[vector('bump()')]);
    assert.equal(implicit.status,'blocked');
    assert.equal(implicit.deployment.returnData,explicit.observed[0].returnData);
    const logs = artifact(viaIR,'pragma solidity >=0.0; contract C { event E(); constructor(){emit E();} function bump() external pure {} }');
    const unsupported = await replayBytecode(logs,[vector('bump()')]);
    assert.equal(unsupported.status,'blocked');
    assert.match(unsupported.reason,/log observation/);
  });
}
test('later compiler/configuration failure retains completed pipeline',async()=>{
  const directory = mkdtempSync(resolve(tmpdir(),'solidity-evm-control-'));
  try {
    writeFileSync(resolve(directory,'control.sol'),source+'\n// ----\n// bump() -> 6\n');
    const result = await runFixture('control.sol',directory,input=>{
      if (input.settings.viaIR) throw new HostLimit('injected unavailable configuration');
      return JSON.parse(compile(JSON.stringify(input),0,0));
    });
    assert.equal(result.status,'blocked');
    assert.equal(result.variants[0].status,'working');
    assert.equal(result.variants[0].observed.length,1);
    assert.equal(result.variants[1].status,'blocked');
  } finally {rmSync(directory,{recursive:true,force:true});}
});

for (const body of ['return address(0).balance;', 'return address(0).code.length;',
    'return uint(address(0).codehash);', 'return gasleft();',
    'assembly { mstore(0, selfbalance()) return(0,32) }']) {
  test(`unconfigured host behavior stays blocked: ${body}`,async()=>{
    const directory = mkdtempSync(resolve(tmpdir(),'solidity-evm-host-'));
    try {
      writeFileSync(resolve(directory,'host.sol'),'pragma solidity >=0.0; contract C { function f() external view returns(uint) { '+body+' } }\n// ----\n// f() -> 0\n');
      const result = await runFixture('host.sol',directory,input=>JSON.parse(compile(JSON.stringify(input),0,0)));
      assert.equal(result.status,'blocked');
      assert.equal(result.variants.length,2);
      for (const v of result.variants) assert.equal(v.reason,'host-dependent behavior not adapted');
    } finally {rmSync(directory,{recursive:true,force:true});}
  });
}

for (const viaIR of [false,true]) test(`direct self try executes actual callee and checks deployment context (viaIR=${viaIR})`, async()=>{
  const c=artifact(viaIR,'pragma solidity >=0.0; contract C { function g(bool b) public pure returns(uint){require(b);return 13;} function f(bool b) public view returns(uint){try this.g(b) returns(uint x){return x;}catch{return 9;}} }');
  const vectors=[{signature:'f(bool)',args:['true'],expected:['13'],failure:false},
    {signature:'f(bool)',args:['false'],expected:['9'],failure:false}];
  const r=await replayBytecode(c,vectors,undefined,{kind:'direct-self-try',selfAddress:SELF_TRY_ADDRESS});
  assert.equal(r.status,'working',JSON.stringify(r));
  assert.deepEqual(r.observed.map(o=>o.values),[['13'],['9']]);
  assert.equal(BigInt(r.deployment.address).toString(),SELF_TRY_ADDRESS);
  const bad=await replayBytecode(c,vectors,undefined,{kind:'direct-self-try',selfAddress:'1'});
  assert.equal(bad.status,'blocked');assert.match(bad.reason,/actual reference deployment/);
});

for(const viaIR of [false,true]) test(`raw ABI outputs and uncaught revert bytes remain exact (viaIR=${viaIR})`,async()=>{
  const c=artifact(viaIR,'pragma solidity >=0.0; contract C { function text() external pure returns(string memory){return "kept";} function reason() external pure {revert("kept");} }');
  const vectors=[{signature:'text()',calldata:[],failure:false,expectedBytes:revertBytes('0x20, 4, "kept"')},
    {signature:'reason()',calldata:[],failure:true,expectedBytes:revertBytes('hex"08c379a0", 0x20, 4, "kept"')}];
  const good=await replayBytecode(c,vectors);assert.equal(good.status,'working',JSON.stringify(good));
  assert.deepEqual(good.observed.map(o=>o.failed),[false,true]);
  const wrong=await replayBytecode(c,[{...vectors[1],expectedBytes:[]}]);assert.equal(wrong.status,'broken');
  const malformed=await replayBytecode(c,[{...vectors[0],calldata:[256]}]);assert.equal(malformed.status,'blocked');
});

const creationSource = `contract Reverts { constructor(uint) { revert("test message."); } }
contract Succeeds { constructor(uint) {} }
contract C {
 function f() public returns(bool created,string memory txt) {
  uint i=3; try new Reverts(i) returns(Reverts r) { created=(address(r)!=address(0));txt="success"; }
  catch Error(string memory s) {txt=s;}
 }
 function g() public returns(bool created,string memory txt) {
  uint i=8; try new Succeeds(i) returns(Succeeds r) { created=(address(r)!=address(0));txt="success"; }
  catch Error(string memory s) {txt=s;}
 }
}`;
const creationExpected=(b,text)=>{
 const word=n=>Buffer.from(BigInt(n).toString(16).padStart(64,'0'),'hex');
 const bytes=Buffer.from(text);return [...Buffer.concat([word(b),word(64),word(bytes.length),bytes,Buffer.alloc(32-bytes.length)])];
};
for(const viaIR of [false,true])test(`creation source receipts preserve failure bytes, address order and wrong-output refusal (viaIR=${viaIR})`,async()=>{
 const code=artifact(viaIR,creationSource);
 const context={kind:'creation-try-source',selfAddress:SELF_TRY_ADDRESS};
 const vectors=[{signature:'f()',calldata:[],expectedBytes:creationExpected(0,'test message.'),failure:false},
  {signature:'g()',calldata:[],expectedBytes:creationExpected(1,'success'),failure:false}];
 const actual=await replayBytecode(code,vectors,undefined,context);
 assert.equal(actual.status,'working',JSON.stringify(actual));
 assert.equal(actual.observed.length,2);
 const [failed]=actual.observed[0].creations,[created]=actual.observed[1].creations;
 assert.equal(failed.address,'0x4b02e501f6a0a60f173a94ce8f79d7dd9a75acb1');
 assert.equal(failed.failed,true);assert.equal(failed.halt,'revert');
 assert.equal(failed.returnData,'0x08c379a0'+'20'.padStart(64,'0')+'0d'.padStart(64,'0')+Buffer.from('test message.').toString('hex').padEnd(64,'0'));
 assert.equal(created.address,'0x86269761d7fb90e36b87a269aa03cf98b7ab92c4');
 assert.equal(created.failed,false);assert.ok(created.runtimeCodeBytes>0);
 const wrong=structuredClone(vectors[0]);wrong.expectedBytes[31]=1;
 assert.equal((await replayBytecode(code,[wrong],undefined,context)).status,'broken');
});

const linkedSource=readFileSync(new URL('../../tests/solc/LibraryTry.sol',import.meta.url),'utf8');
for(const viaIR of [false,true])test(`original linked try receipts, context, error bytes and refusal controls (viaIR=${viaIR})`,async()=>{
 const file='linked.sol',settings={viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},metadata:{appendCBOR:false},outputSelection:{'*':{'':['ast'],'*':['abi','evm.bytecode.object','evm.bytecode.linkReferences','evm.deployedBytecode.object','evm.deployedBytecode.linkReferences','evm.methodIdentifiers']}}};
 const out=JSON.parse(compile(JSON.stringify({language:'Solidity',sources:{[file]:{content:linkedSource}},settings}),0,0));
 assert.deepEqual((out.errors??[]).filter(e=>e.severity==='error'),[]);
 const ast=out.sources[file].ast,C=ast.nodes.find(n=>n.name==='C'),context=libraryTryContext(ast,C);
 assert.ok(context);const code=out.contracts[file].C,linked={file,name:'L',artifact:out.contracts[file].L};
 const vectors=semanticVectors(libraryTryVectorsFixture(parseFixture(linkedSource),context),code.abi);
 const actual=await replayBytecode(code,vectors,undefined,context,linked);
 assert.equal(actual.status,'working',JSON.stringify(actual));assert.equal(actual.observed.length,4);
 assert.equal(actual.libraryDeployment.address,'0x501f373d5541129778e4195692f7fff4dd01ebc9');
 assert.equal(actual.deployment.address,'0x8f047056608fdb1be4725341c345326702096cb2');
 assert.equal(actual.linkManifest.address,actual.libraryDeployment.address);
 assert.ok(actual.libraryDeployment.runtimeCodeBytes>0);assert.equal(actual.libraryDeployment.failed,false);
 const error='0x08c379a0'+'20'.padStart(64,'0')+'07'.padStart(64,'0')+Buffer.from('failure').toString('hex').padEnd(64,'0');
 for(const [i,obs]of actual.observed.entries()){
  const calls=obs.calls.filter(c=>c.delegatecall);assert.equal(calls.length,1);
  const c=calls[0];assert.equal(c.to,actual.deployment.address);assert.equal(c.codeAddress,actual.libraryDeployment.address);
  assert.equal(c.caller,'0x'+'12'.repeat(20));assert.equal(c.value,'0');
  assert.equal(c.failed,i%2===1);if(c.failed)assert.equal(c.returnData,error);
  else assert.equal(c.returnData,'0x'+BigInt(i===0?8:9).toString(16).padStart(64,'0'));
 }
 const wrongContext=await replayBytecode(code,vectors,undefined,{...context,libraryAddress:'1'},linked);
 assert.equal(wrongContext.status,'blocked');assert.equal(wrongContext.libraryDeployment.address,actual.libraryDeployment.address);assert.equal(wrongContext.linkManifest,null);
 const bad=structuredClone(vectors[0]);bad.expectedBytes[31]^=1;
 const wrong=await replayBytecode(code,[bad],undefined,context,linked);
 assert.equal(wrong.status,'broken');assert.equal(wrong.libraryDeployment.address,actual.libraryDeployment.address);assert.deepEqual(wrong.linkManifest,actual.linkManifest);
 const malformed=await replayBytecode(code,[{...vectors[0],calldata:[256]}],undefined,context,linked);
 assert.equal(malformed.status,'blocked');assert.equal(malformed.libraryDeployment.address,actual.libraryDeployment.address);assert.deepEqual(malformed.linkManifest,actual.linkManifest);
});
