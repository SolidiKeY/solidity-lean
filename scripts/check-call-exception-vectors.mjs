#!/usr/bin/env node
/** Optional source/EVM reference tests. No Lean or package-local dependency writes.
 * node scripts/check-call-exception-vectors.mjs SOLJSON_FILE EXTERNAL_NODE_MODULES
 * Uses EthereumJS vm/common/util 10.1.3 and ethers 6.17.0, as check-abi-vectors.
 */
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { createRequire } from 'node:module';
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
const [compiler, modules] = process.argv.slice(2);
assert.ok(compiler && modules, 'expected compiler file and external node_modules directory');
const hash = createHash('sha256').update(readFileSync(compiler)).digest('hex');
const pins = new Map([
  ['c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8', /^0\.8\.34\+commit\.80d5c536/],
  ['6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390', /^0\.8\.38\+commit\.1835d247/]
]);
assert.ok(pins.has(hash), 'unsupported compiler bytes');
const require = createRequire(resolve(modules, 'reference.cjs'));
const { createVM } = require('@ethereumjs/vm');
const { Common, Mainnet, Hardfork } = require('@ethereumjs/common');
const { createAddressFromString, hexToBytes, bytesToHex } = require('@ethereumjs/util');
const { Interface, id } = require('ethers');
const solc = createRequire(import.meta.url)(resolve(compiler));
const compile = solc.cwrap('solidity_compile', 'string', ['string', 'number', 'number']);
const version = solc.cwrap('solidity_version', 'string', [])();
assert.match(version, pins.get(hash));
const sourcePath = fileURLToPath(new URL('../tests/solc/CallExceptions.sol', import.meta.url));
const content = readFileSync(sourcePath, 'utf8');
const panic = code => '0x4e487b71' + BigInt(code).toString(16).padStart(64, '0');
const word = code => BigInt(code).toString(16).padStart(64, '0');
let count = 0;
for (const viaIR of [false, true]) {
  const out = JSON.parse(compile(JSON.stringify({ language: 'Solidity',
    sources: { 'CallExceptions.sol': { content } }, settings: {
      viaIR, evmVersion: 'cancun', optimizer: { enabled: true },
      outputSelection: { '*': { '*': ['abi', 'evm.deployedBytecode.object'] } }
    } }), 0, 0));
  assert.deepEqual((out.errors ?? []).filter(e => e.severity === 'error'), []);
  const c = out.contracts['CallExceptions.sol'].CallExceptions;
  const iface = new Interface(c.abi);
  const code = hexToBytes('0x' + c.evm.deployedBytecode.object);
  const to = createAddressFromString('0x0000000000000000000000000000000000001000');
  const caller = createAddressFromString('0x0000000000000000000000000000000000002000');
  async function call(name, args, expected, errorData) {
    // A fresh VM makes storage and transaction caches independent per vector.
    // Install code at its actual address: self-calls must execute it.
    const vm = await createVM({ common: new Common({ chain: Mainnet, hardfork: Hardfork.Cancun }) });
    await vm.stateManager.putCode(to, code);
    const { execResult: r } = await vm.evm.runCall({ to, caller,
      data: hexToBytes(iface.encodeFunctionData(name, args)), gasLimit: 30000000n });
    if (errorData !== undefined) {
      assert.ok(r.exceptionError, `${name} must fail (viaIR=${viaIR})`);
      assert.equal(bytesToHex(r.returnValue).toLowerCase(), errorData.toLowerCase(), name);
    } else {
      assert.equal(r.exceptionError, undefined, `${name}: ${r.exceptionError} (viaIR=${viaIR})`);
      assert.deepEqual(Array.from(iface.decodeFunctionResult(name, bytesToHex(r.returnValue)),
        x => typeof x === 'bigint' ? x.toString() : x), expected.map(x => String(x)), name);
    }
    count++;
  }
  for (const name of ['requireTrueArg', 'requireFalseArg', 'revertArg', 'emitArg', 'callerArgument'])
    await call(name, [], [], panic(1));
  await call('failureOrder', [0,255], [], panic(0x12));
  await call('failureOrder', [1,255], [], panic(0x11));
  await call('failureOrder', [1,0], [], id('Pair(uint256,uint8)').slice(0,10)+word(1)+word(1));
  await call('reasonOrder', [0], [], panic(0x12));
  await call('reasonOrder', [1], [], panic(1));
  await call('enumRead', [2], [], panic(0x21));
  await call('enumRead', [1], [1]);
  await call('unsetCall', [7], [], panic(0x51));
  await call('unsetArg', [], [], panic(1));
  await call('assignedCall', [], [7]);
  for (const name of ['totalTrue','selectorArg','signedPayload','trueEffect','rawEnumPayload','rawUnsetPayload','snapshot','rollback','customBytesPayloads','requireBytesTrue'])
    await call(name, [], []);
  await call('totalFalse', [], [], id('E(uint256)').slice(0,10)+word(7));
  await call('signedLiteral', [], [], id('Signed(int256)').slice(0,10)+word(8));
  await call('selectorFail', [], [], id('Sel(bytes4)').slice(0,10)+iface.getFunction('echo').selector.slice(2).padEnd(64,'0'));
  const bytesWord = hex => hex.padEnd(64, '0');
  await call('smallLiteralFail', [], [], id('SmallBytes(bytes2)').slice(0,10)+bytesWord('00ab'));
  await call('smallDynamicFail', ['0xabcd'], [], id('SmallBytes(bytes2)').slice(0,10)+bytesWord('abcd'));
  await call('wideBytesFail', ['0xabcd'], [], id('WideBytes(bytes4)').slice(0,10)+bytesWord('abcd0000'));
  await call('requireBytesFail', ['0xabcd'], [], id('WideBytes(bytes4)').slice(0,10)+bytesWord('abcd0000'));
  await call('returnedBytesFail', [], [], id('WideBytes(bytes4)').slice(0,10)+bytesWord('abcd0000'));
  await call('fullBytesFail', [], [], id('FullBytes(bytes32)').slice(0,10)+bytesWord('00ab'));
  for (const [name,code] of [['failureCode',18],['reasonCode',18],['enumCode',33],['unsetCode',81],['unsetArgCode',1]])
    await call(name, [], [code]);
  for (const name of ['falseEffectExpectation','wrongEnumCode','wrongUnsetCode','wrongFailureCode','wrongCustomBytesPayload'])
    await call(name, [], [], panic(1));
}
console.log(`${count} ${version} legacy/viaIR Cancun call/exception vectors passed`);
