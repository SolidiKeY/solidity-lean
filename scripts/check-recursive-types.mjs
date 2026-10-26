#!/usr/bin/env node
// Reference tooling is external to the dependency-free Lean package.
// node scripts/check-recursive-types.mjs SOLJSON_FILE NODE_MODULES_DIRECTORY
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
const [compiler, modules] = process.argv.slice(2);
assert.ok(compiler && modules, 'expected pinned compiler and external EVM modules directory');
assert.equal(createHash('sha256').update(readFileSync(compiler)).digest('hex'),
  '6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390');
const solc = createRequire(import.meta.url)(resolve(compiler));
assert.match(solc.cwrap('solidity_version','string',[])(), /^0\.8\.38\+commit\.1835d247/);
const compile = solc.cwrap('solidity_compile','string',['string','number','number']);
const source = readFileSync(fileURLToPath(new URL('../tests/recursive-0.8.38/RecursiveTypes.sol',import.meta.url)),'utf8');
function build(content, viaIR=false) {
  return JSON.parse(compile(JSON.stringify({language:'Solidity',sources:{'RecursiveTypes.sol':{content}},
    settings:{viaIR,optimizer:{enabled:true},evmVersion:'cancun',
      outputSelection:{'*':{'*':['abi','evm.deployedBytecode.object'],'':['ast']}}}}),0,0));
}
const bad = [
  ['direct','struct N { N child; } N root;','2046'],
  ['fixed','struct N { N[1] child; } N root;','2046'],
  ['mutual inline','struct A { B b; } struct B { A a; } A root;','2046'],
  ['recursive public ABI','struct N { N[] children; } function f(N memory n) external pure returns(uint) { return n.children.length; }','4103'],
  ['mapping memory','struct N { mapping(uint=>N) next; } function f(N memory) internal {}','4061']
];
for (const [label, body, code] of bad) {
  const out=build('pragma solidity 0.8.38; contract Bad { '+body+' }');
  const errors=(out.errors??[]).filter(e=>e.severity==='error');
  assert.deepEqual(errors.map(e=>[e.type,e.errorCode]),[['TypeError',code]],
    label+' must fail for the pinned source-type reason');
}
const require = createRequire(resolve(modules,'recursive-reference.cjs'));
const {createVM}=require('@ethereumjs/vm');
const {Common,Mainnet,Hardfork}=require('@ethereumjs/common');
const {hexToBytes,bytesToHex,Account,createAddressFromString}=require('@ethereumjs/util');
const {Interface}=require('ethers');
let count=0;
for (const viaIR of [false,true]) {
  const out=build(source,viaIR);
  assert.deepEqual((out.errors??[]).filter(e=>e.severity==='error'),[]);
  const c=out.contracts['RecursiveTypes.sol'].RecursiveTypesConformance;
  const iface=new Interface(c.abi);
  const vm=await createVM({common:new Common({chain:Mainnet,hardfork:Hardfork.Cancun})});
  const address=createAddressFromString('0x'+'1'.repeat(40));
  await vm.stateManager.putAccount(address,new Account());
  const code=hexToBytes('0x'+c.evm.deployedBytecode.object);
  for (const [name,expected] of [
    ['mappingDefault',[0n]],['mappingDelete',[0n,7n,9n]],
    ['arrayDelete',[0n,0n,0n]],['retainedWrite',[7n]],
    ['mutualDepth',[0n]],['memoryCycle',[9n]]
  ]) {
    const r=await vm.evm.runCode({code,to:address,data:hexToBytes(iface.encodeFunctionData(name,[])),gasLimit:30000000n});
    assert.equal(r.exceptionError,undefined,`${name}, viaIR=${viaIR}: ${r.exceptionError}`);
    assert.deepEqual(Array.from(iface.decodeFunctionResult(name,bytesToHex(r.returnValue))),expected,
      `${name}, viaIR=${viaIR}`);
    count++;
  }
}
console.log(`${count} pinned solc 0.8.38/EVM recursive-type vectors and ${bad.length} compiler rejection cases passed`);
