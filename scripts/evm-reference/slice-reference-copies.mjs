#!/usr/bin/env node
// Optional compiler/EVM observations, separate from the kernel certificates.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {resolve} from 'node:path';
import {hexToBytes} from '@ethereumjs/util';
import {machine, observation, creationObservation} from './replay.mjs';
import {COMPILER_SHA} from '../solidity-upstream.mjs';
const sha = b => createHash('sha256').update(b).digest('hex');
const path = resolve(process.argv[2]);
assert.equal(sha(readFileSync(path)), COMPILER_SHA);
const c = createRequire(import.meta.url)(path);
const version = c.cwrap('solidity_version','string',[])();
assert.equal(version, '0.8.38+commit.1835d247.Emscripten.clang');
const compile = c.cwrap('solidity_compile','string',['string','number','number']);
const source = readFileSync(new URL('../../tests/solc/SliceReferenceCopies.sol',import.meta.url),'utf8');
const errors = o => (o.errors ?? []).filter(e => e.severity === 'error');
const word = n => BigInt.asUintN(256,BigInt(n)).toString(16).padStart(64,'0');
const panic = n => '0x4e487b71'+word(n);
const input = (...arrays) => {
  let offset = arrays.length * 32;
  const heads=[], bodies=[];
  for (const rows of arrays) {
    heads.push(offset); const body=[rows.length,...rows.flat()];
    bodies.push(...body); offset += body.length * 32;
  }
  return [...heads,...bodies];
};
const xs=[[3,4],[5,6],[9,10]];
const vectors = [
  ...['copies','endpoints','passing','returned','storageCopy','empty','inlineCopy'].map(n =>
    [n+'(uint8[2][])',input(xs),null,[]]),
  ['independent(uint8[2][])',input([[5,6],[5,6]]),null,[]],
  ['rebound(uint8[2][],uint8[2][])',input(xs,[[3,4]]),null,[]],
  ['signed(int8[2][])',input([[-128,127]]),null,[]],
  ['kinds(bool[2][],bytes2[2][],address[2][])',input([[1,0]],[[0x1234n<<240n,0xabcdn<<240n]],[[17,18]]),null,[]],
  ['invalidRange(uint8[2][])',input(xs),'0x',[]],
  ['getMarker()',[],null,['0']],
  ['rowBounds(uint8[2][])',input(xs),panic(0x32),[]],
  ['falsePost(uint8[2][])',input(xs),panic(0x01),[]],
  ['narrowFailure(uint8[2][])',input([[255,0]]),panic(0x11),[]],
];
const results=[];
for (const viaIR of [false,true]) {
  const settings={viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},
    outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.methodIdentifiers']}}};
  const compilerInput={language:'Solidity',sources:{'SliceReferenceCopies.sol':{content:source}},settings};
  const out=JSON.parse(compile(JSON.stringify(compilerInput),0,0));
  assert.deepEqual(errors(out),[]);
  const a=out.contracts['SliceReferenceCopies.sol'].SliceReferenceCopies;
  const vm=await machine();
  const deploy=await vm.call({data:hexToBytes('0x'+a.evm.bytecode.object)});
  const deployment=creationObservation(deploy.result.execResult,'constructor',deploy.metrics);
  assert.equal(deployment.failed,false);
  const to=deploy.result.createdAddress; assert(to);
  const observed=[];
  for (const [signature,args,revertData,expected] of vectors) {
    const selector=a.evm.methodIdentifiers[signature]; assert(selector,signature);
    const exec=await vm.call({to,data:hexToBytes('0x'+selector+args.map(word).join(''))});
    const actual=observation(exec.result.execResult,signature,exec.metrics);
    assert.equal(actual.failed,revertData!==null,signature);
    assert.deepEqual(actual.values,expected,signature);
    if(revertData!==null) {
      assert.equal(actual.exception,'revert',signature);
      assert.equal(actual.returnData,revertData,signature);
    }
    observed.push({inputWords:args.map(String),expectedFailureData:revertData,expectedValues:expected,...actual});
  }
  // Source admission, not native model slicing, decides whether a shape is legal.
  const invalid='pragma solidity ^0.8.38; contract C { function f(uint[][] calldata xs) external pure { uint[][] memory m=xs[:]; } }';
  const bad=JSON.parse(compile(JSON.stringify({...compilerInput,sources:{'C.sol':{content:invalid}}}),0,0));
  assert(errors(bad).some(e=>e.message.includes('dynamically encoded base types')));
  const wrongKind='pragma solidity ^0.8.38; contract C { function f(address[2][] calldata xs) external pure { uint[2][] memory m=xs[:]; } }';
  const wrong=JSON.parse(compile(JSON.stringify({...compilerInput,sources:{'C.sol':{content:wrongKind}}}),0,0));
  assert(errors(wrong).length>0,'source address/integer row conversion must be rejected');
  results.push({pipeline:viaIR?'viaIR':'legacy',settings,inputSha256:sha(JSON.stringify(compilerInput)),
    creationSha256:sha(Buffer.from(a.evm.bytecode.object,'hex')),deployment,observed,invalidDynamicElementSource:'rejected',invalidAddressIntegerConversion:'rejected'});
}
console.log(JSON.stringify({compiler:version,compilerSha256:COMPILER_SHA,sourceSha256:sha(source),results},null,2));
