#!/usr/bin/env node
/** Source-level ABI hex boundary regression. Optional reference dependencies:
 * @ethereumjs/{vm,common,util} 10.1.3 and ethers 6.17.0, outside this package.
 * Usage: node scripts/check-abi-hex-call.mjs EXTERNAL_NODE_MODULES SOLJSON_FILE [SOLJSON_FILE...]
 * Both pinned compilers are exercised with legacy and via-IR Cancun codegen.
 * This is a concrete conformance test, not a frontend-equivalence proof.
 */
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { createRequire } from 'node:module';
import { resolve } from 'node:path';
const [modules, ...compilers] = process.argv.slice(2);
if (!modules || compilers.length === 0)
  throw new Error('expected external node_modules directory and pinned compiler file(s)');
const pins = new Map([
  ['6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390', '0.8.38+commit.1835d247'],
  ['c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8', '0.8.34+commit.80d5c536']
]);
const require = createRequire(resolve(modules, 'reference.cjs'));
const { createVM } = require('@ethereumjs/vm');
const { Common, Mainnet, Hardfork } = require('@ethereumjs/common');
const { hexToBytes, bytesToHex } = require('@ethereumjs/util');
const { Interface } = require('ethers');
const source = readFileSync(new URL('../tests/abi-0.8.38/HexCall.sol', import.meta.url), 'utf8');
const positive = ['exactHex', 'leadingZero', 'mixedHex', 'groupedMixed', 'pointerHex',
  'selectorArgument', 'fullWord', 'numericHex'];
const rejects = [
  ['decimal', 'function f(bytes2) external {} function bad() external view { abi.encodeCall(this.f,(43981)); }'],
  ['short hex', 'function f(bytes2) external {} function bad() external view { abi.encodeCall(this.f,(0xab)); }'],
  ['long hex', 'function f(bytes2) external {} function bad() external view { abi.encodeCall(this.f,(0x00abcd)); }'],
  ['numeric local', 'function f(bytes2) external {} function bad(uint16 x) external view { abi.encodeCall(this.f,(x)); }'],
  ['arithmetic constant', 'function f(bytes2) external {} function bad() external view { abi.encodeCall(this.f,(0xabcd + 0)); }'],
  ['address-typed literal', 'function f(bytes20) external {} function bad() external view { abi.encodeCall(this.f,(0x0000000000000000000000000000000000000000)); }'],
  ['whole-tuple parentheses', 'function f(bytes2,uint) external {} function bad() external view { abi.encodeCall(this.f,((0xabcd,7))); }'],
  ['omitted component', 'function f(bytes2,uint) external {} function bad() external view { abi.encodeCall(this.f,(0xabcd,)); }'],
  ['double separator', 'function f(bytes2) external {} function bad() external view { abi.encodeCall(this.f,(0xab__cd)); }'],
  ['trailing separator', 'function f(bytes2) external {} function bad() external view { abi.encodeCall(this.f,(0xabcd_)); }']
];
let runs = 0, rejections = 0;
for (const compiler of compilers) {
  const sha = createHash('sha256').update(readFileSync(compiler)).digest('hex');
  const version = pins.get(sha);
  assert.ok(version, 'compiler SHA256 must match an explicit pin');
  const solc = createRequire(import.meta.url)(resolve(compiler));
  assert.ok(solc.cwrap('solidity_version', 'string', [])().startsWith(version));
  const compile = solc.cwrap('solidity_compile', 'string', ['string', 'number', 'number']);
  const build = (content, viaIR) => JSON.parse(compile(JSON.stringify({ language: 'Solidity',
    sources: { 'HexCall.sol': { content } }, settings: { viaIR, evmVersion: 'cancun',
      optimizer: { enabled: true }, outputSelection: { '*': { '*': ['abi', 'evm.deployedBytecode.object'] } }
    } }), 0, 0));
  for (const viaIR of [false, true]) {
    const label = `${version}/${viaIR ? 'via-IR' : 'legacy'}`;
    for (const [name, body] of rejects) {
      const out = build(`pragma solidity ^0.8.0; contract Bad { ${body} }`, viaIR);
      assert.ok((out.errors ?? []).some(e => e.severity === 'error'), `${label}: ${name} must reject`);
      rejections++;
    }
    const out = build(source, viaIR);
    assert.deepEqual((out.errors ?? []).filter(e => e.severity === 'error'), [], label);
    const contract = out.contracts['HexCall.sol'].AbiHexCall;
    const iface = new Interface(contract.abi);
    const code = hexToBytes('0x' + contract.evm.deployedBytecode.object);
    const vm = await createVM({ common: new Common({ chain: Mainnet, hardfork: Hardfork.Cancun }) });
    for (const name of [...positive, 'falseHex']) {
      const result = await vm.evm.runCode({ code,
        data: hexToBytes(iface.encodeFunctionData(name)), gasLimit: 30000000n });
      if (name === 'falseHex') {
        assert.ok(result.exceptionError, `${label}: falseHex must revert`);
        assert.equal(bytesToHex(result.returnValue), '0x4e487b71' + '1'.padStart(64, '0'),
          `${label}: assertion panic code`);
      } else {
        assert.equal(result.exceptionError, undefined, `${label}/${name}`);
        assert.equal(result.returnValue.length, 0, `${label}/${name}: no return values`);
      }
      runs++;
    }
    console.log(`${label}: ${positive.length} positive runs, assertion panic, ${rejects.length} rejected sources`);
  }
}
console.log(`${runs} EVM runs and ${rejections} compiler rejections passed`);
