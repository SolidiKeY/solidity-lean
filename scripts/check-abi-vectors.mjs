#!/usr/bin/env node
/** Independent pinned-solc/EVM vectors; test dependencies live outside this package.
 * Usage: node scripts/check-abi-vectors.mjs SOLJSON_FILE NODE_MODULES_DIRECTORY
 * Reference versions: @ethereumjs/{vm,common,util} 10.1.3, ethers 6.17.0.
 */
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { createRequire } from 'node:module';
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
const [compiler, modules] = process.argv.slice(2);
if (!compiler || !modules) throw new Error('expected compiler file and external node_modules directory');
const sha = createHash('sha256').update(readFileSync(compiler)).digest('hex');
assert.equal(sha, '6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390');
const require = createRequire(resolve(modules, 'reference.cjs'));
const { createVM } = require('@ethereumjs/vm');
const { Common, Mainnet, Hardfork } = require('@ethereumjs/common');
const { hexToBytes, bytesToHex } = require('@ethereumjs/util');
const { Interface, SigningKey, computeAddress } = require('ethers');
const solc = createRequire(import.meta.url)(resolve(compiler));
const compile = solc.cwrap('solidity_compile', 'string', ['string', 'number', 'number']);
assert.match(solc.cwrap('solidity_version', 'string', [])(), /^0\.8\.38\+commit\.1835d247/);
const typeCases = [
  ['bytes narrowing', 'function g(bytes2) external {} function bad(bytes3 x) external view { abi.encodeCall(this.g,(x)); }'],
  ['integer narrowing', 'function g(uint8) external {} function bad(uint x) external view { abi.encodeCall(this.g,(x)); }'],
  ['boolean mismatch', 'function g(bool) external {} function bad(uint x) external view { abi.encodeCall(this.g,(x)); }'],
  ['function mismatch', 'function g(function(uint) external returns(uint)) external {} function bad(function(bool) external returns(bool) x) external view { abi.encodeCall(this.g,(x)); }'],
  ['nested string concat', 'function bad() external pure { bytes.concat(string.concat("a")); }']
];
for (const [label, body] of typeCases) {
  const result = JSON.parse(compile(JSON.stringify({language:'Solidity', sources:{'Bad.sol':{
    content:'pragma solidity 0.8.38; contract Bad { '+body+' }'}}, settings:{outputSelection:{'*':{'':['ast']}}}}), 0, 0));
  assert.ok((result.errors ?? []).some(e => e.severity === 'error'), label+' must be rejected');
}
const source = fileURLToPath(new URL('../tests/abi-0.8.38/Features.sol', import.meta.url));
const out = JSON.parse(compile(JSON.stringify({ language: 'Solidity',
  sources: { 'Features.sol': { content: readFileSync(source, 'utf8') } },
  settings: { evmVersion: 'osaka', optimizer: { enabled: true },
    outputSelection: { '*': { '*': ['abi', 'evm.deployedBytecode.object'] } } } }), 0, 0));
assert.deepEqual((out.errors ?? []).filter(e => e.severity === 'error'), []);
const c = out.contracts['Features.sol'].ABIConformance;
const iface = new Interface(c.abi);
const vm = await createVM({ common: new Common({ chain: Mainnet, hardfork: Hardfork.Osaka }) });
const code = hexToBytes('0x' + c.evm.deployedBytecode.object);
let count = 0;
async function call(name, args, expected, fail = false) {
  const r = await vm.evm.runCode({ code, data: hexToBytes(iface.encodeFunctionData(name, args)),
    gasLimit: 30000000n });
  if (fail) assert.ok(r.exceptionError, `${name} must revert`);
  else {
    assert.equal(r.exceptionError, undefined, `${name}: ${r.exceptionError}`);
    const actual = Array.from(iface.decodeFunctionResult(name, bytesToHex(r.returnValue)),
      x => typeof x === 'bigint' ? x.toString() : typeof x === 'string' ? x.toLowerCase() : x);
    assert.deepEqual(actual, expected.map(x => typeof x === 'number' ? String(x) : x), name);
  }
  count++;
}
await call('constantRoot', [], ['37439836327923360225337895871394760624280537466773280374265222508165906222592']);
for (const [id, root] of [
  ['', '30348469548119976384149824193117947667795829812057172845188107037932402691072'],
  ['abc', '89080316084849266924113458916420441381095493738250323500559816430735688691456'],
  ['a b', '57861545570621347113984716387450989072831671086294251435296248171547464265216'],
  ['é', '58817168841818429821822861410436174112975048784383205212621391405482053771264']
]) await call('runtimeRoot', [id], [root]);
await call('fixedLiteral', [], [36,97,98,0]);
await call('externalValue', [], [true]);
await call('unicodeSelector', [], [78,69,207,137,true]);
await call('nestedPrefix', [], [196,64,7]);
await call('hugeNestedHead', [], [], true);
await call('unaligned', [], [0]);
await call('overlapping', [], [0]);
await call('trueProperty', [], []);
await call('falseProperty', [], [], true);
const word = n => '0x' + BigInt(n).toString(16).padStart(64, '0');
const rOne = 0x79be667ef9dcbbac55a06295ce870b07029bfcdb2dce28d959f2815b16f81798n;
const order = 0xfffffffffffffffffffffffffffffffebaaedce6af48a03bbfd25e8cd0364141n;
const addressOne = '0x7e5f4552091a69125d5dfcb7b8c2659029395bdf';
for (const [h,v,r,s,address] of [
  [0n,27,rOne,rOne,addressOne], [1n,27,rOne,rOne+1n,addressOne],
  [1n,28,rOne,order-rOne-1n,addressOne],
  [0n,27,5n,1n,'0x'+'0'.repeat(40)],
  [1n,27,rOne,1n,'0x'+'0'.repeat(40)],
  [order,27,rOne,rOne,addressOne],
  [0n,29,rOne,rOne,'0x'+'0'.repeat(40)],
  [0n,27,0n,rOne,'0x'+'0'.repeat(40)],
  [0n,27,rOne,0n,'0x'+'0'.repeat(40)],
  [0n,27,order,rOne,'0x'+'0'.repeat(40)],
  [0n,27,rOne,order,'0x'+'0'.repeat(40)]
]) await call('recovery', [word(h),v,word(r),word(s)], [address]);
for (const key of [2n,7n,12345n]) {
  const signer = new SigningKey(word(key));
  const digest = word(42n);
  const sig = signer.sign(digest);
  const expected = computeAddress(signer.publicKey).toLowerCase();
  await call('recovery', [digest,sig.v,sig.r,sig.s], [expected]);
  await call('recovery', [digest,55-sig.v,sig.r,word(order-BigInt(sig.s))], [expected]);
  console.log(JSON.stringify({h:'42',v:sig.v,r:BigInt(sig.r).toString(),s:BigInt(sig.s).toString(),address:BigInt(expected).toString()}));
}
console.log(`${count} pinned Solidity 0.8.38 / EVM ABI vectors and ${typeCases.length} compiler rejection cases passed`);
