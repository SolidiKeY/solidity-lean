#!/usr/bin/env node
/** Reference-solc controls only; this does not establish Lean source coverage. */
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {readFileSync} from 'node:fs';
import {createRequire} from 'node:module';
import {resolve} from 'node:path';
import {COMPILER_SHA} from './solidity-upstream.mjs';
const path=resolve(process.argv[2] ?? '');
assert.equal(createHash('sha256').update(readFileSync(path)).digest('hex'),COMPILER_SHA);
const solc=createRequire(import.meta.url)(path);
assert.equal(solc.cwrap('solidity_version','string',[])(),'0.8.38+commit.1835d247.Emscripten.clang');
const compile=solc.cwrap('solidity_compile','string',['string','number','number']);
const cases=[
 ['signed count','function f(int a,int n) public pure returns(int){return a >> n;}', '2271',
  'Built-in binary operator >> cannot be applied to types int256 and int256.'],
 ['signed exponent','function f(int a,int n) public pure returns(int){return a ** n;}', '2271',
  'Built-in binary operator ** cannot be applied to types int256 and int256. Exponentiation power is not allowed to be a signed integer type.'],
 ['negative unsigned literal','function f() public pure returns(uint){return -1;}', '6359',
  'Return argument type int_const -1 is not implicitly convertible to expected type (type of first return variable) uint256. Cannot implicitly convert signed literal to unsigned type.'],
 ['narrow literal power','function f(uint n) public pure returns(int8){return (-2)**n;}', '6359',
  'Return argument type int256 is not implicitly convertible to expected type (type of first return variable) int8.'],
];
for (const viaIR of [false,true]) {
 const input=content=>({language:'Solidity',sources:{'control.sol':{content}},settings:{viaIR,outputSelection:{'*':{'':['ast']}}}});
 const errors=content=>JSON.parse(compile(JSON.stringify(input(content)),0,0)).errors?.filter(e=>e.severity==='error')??[];
 assert.deepEqual(errors(readFileSync(new URL('../tests/solc/SignedNumeric.sol',import.meta.url),'utf8')),[]);
 for(const [label,body,code,message] of cases){
  const source='// SPDX-License-Identifier: GPL-3.0\npragma solidity ^0.8.38; contract C{'+body+'}';
  assert.deepEqual(errors(source).map(e=>({type:e.type,code:e.errorCode,message:e.message})),
   [{type:'TypeError',code,message}],label);
 }
}
console.log('2 positive source compilations and 8 exact reference-solc rejection controls passed');
