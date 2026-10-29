#!/usr/bin/env node
/** Optional independent source fixtures; not a Lean dependency or a proof.
 * node scripts/check-memory-reference-arrays.mjs SOLJSON_FILE EXTERNAL_NODE_MODULES
 */
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { createRequire } from 'node:module';
import { resolve } from 'node:path';
const [compiler, modules] = process.argv.slice(2);
assert.ok(compiler && modules, 'expected compiler and external node_modules paths');
assert.equal(createHash('sha256').update(readFileSync(compiler)).digest('hex'),
  'c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8');
const require = createRequire(resolve(modules, 'reference.cjs'));
const { createVM } = require('@ethereumjs/vm');
const { Common, Mainnet, Hardfork } = require('@ethereumjs/common');
const { hexToBytes, bytesToHex } = require('@ethereumjs/util');
const { Interface } = require('ethers');
const solc = createRequire(import.meta.url)(resolve(compiler));
const version = solc.cwrap('solidity_version', 'string', [])();
assert.match(version, /^0\.8\.34\+commit\.80d5c536/);
const compile = solc.cwrap('solidity_compile', 'string', ['string', 'number', 'number']);
const source = readFileSync(new URL('../tests/memory-reference-arrays/ReferenceArrays.sol', import.meta.url), 'utf8');
let count = 0;
for (const viaIR of [false, true]) for (const optimized of [false, true]) {
  const label = `${viaIR ? 'viaIR' : 'legacy'}/optimizer=${optimized}`;
  const out = JSON.parse(compile(JSON.stringify({ language: 'Solidity',
    sources: { 'ReferenceArrays.sol': { content: source } }, settings: {
      viaIR, evmVersion: 'cancun', optimizer: { enabled: optimized, runs: 200 },
      outputSelection: { '*': { '*': ['abi', 'evm.deployedBytecode.object'] } }
    } }), 0, 0));
  assert.deepEqual((out.errors ?? []).filter(e => e.severity === 'error'), [], label);
  const c = out.contracts['ReferenceArrays.sol'].ReferenceArrays;
  const iface = new Interface(c.abi);
  const vm = await createVM({ common: new Common({ chain: Mainnet, hardfork: Hardfork.Cancun }) });
  const code = hexToBytes('0x' + c.evm.deployedBytecode.object);
  for (const [name, expected] of [['dynamicAliases',11013n],['fixedAliases',11013n],
      ['fixedChildAliases',11013n],['distinctFixedDefaults',0n]]) {
    const r = await vm.evm.runCode({ code, data: hexToBytes(iface.encodeFunctionData(name, [])), gasLimit: 30000000n });
    assert.equal(r.exceptionError, undefined, `${label}/${name}`);
    assert.equal(iface.decodeFunctionResult(name, r.returnValue)[0], expected, `${label}/${name}`);
    count++;
  }
  for (const name of ['parentBounds','fixedParentBounds','childBounds','fixedChildBounds']) {
    const r = await vm.evm.runCode({ code, data: hexToBytes(iface.encodeFunctionData(name, [])), gasLimit: 30000000n });
    assert.ok(r.exceptionError, `${label}/${name}`);
    assert.equal(bytesToHex(r.returnValue), '0x4e487b71' + '32'.padStart(64,'0'), `${label}/${name}`);
    count++;
  }
  console.log(`${label}: 4 alias/default results and 4 bounds reverts passed`);
}
console.log(`${count} source fixture executions passed with ${version}`);
