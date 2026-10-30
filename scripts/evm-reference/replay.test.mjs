import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync, writeFileSync, mkdtempSync, rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {createRequire} from 'node:module';
import {createHash} from 'node:crypto';
import {resolve} from 'node:path';
import {hexToBytes} from '@ethereumjs/util';
import {COMPILER_SHA} from '../solidity-upstream.mjs';
import {machine, observation, replayBytecode, HostLimit, INITIAL_GAS, runFixture} from './replay.mjs';

// Reference compiler controls use the same integrity gate as the CLI.
import {referenceCompiler} from '../test-compiler.mjs';
const compiler = referenceCompiler();
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
