#!/usr/bin/env node
// Optional compiler/EVM observations; no dependencies are added to the core.
// Usage: node scripts/check-transient-world-vectors.mjs SOLJSON EXTERNAL_NODE_MODULES
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {resolve} from 'node:path';
const [compilerFile, modules] = process.argv.slice(2);
assert(compilerFile && modules, 'expected SOLJSON EXTERNAL_NODE_MODULES');
const sha = data => createHash('sha256').update(data).digest('hex');
assert.equal(sha(readFileSync(compilerFile)), '6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390');
const req = createRequire(resolve(modules, 'reference.cjs'));
const solc = req(resolve(compilerFile));
const version = solc.cwrap('solidity_version', 'string', [])();
assert.match(version, /^0\.8\.38\+commit\.1835d247/);
const compile = solc.cwrap('solidity_compile', 'string', ['string', 'number', 'number']);
const {createVM, runTx} = req('@ethereumjs/vm');
const {Common, Mainnet, Hardfork} = req('@ethereumjs/common');
const {createLegacyTx} = req('@ethereumjs/tx');
const {hexToBytes, bytesToHex, createAddressFromString, createAddressFromPrivateKey, createAccount} = req('@ethereumjs/util');
const {Interface} = req('ethers');
const sources = Object.fromEntries(['TransientFactory.sol', 'TransientWorldScenario.sol'].map(name =>
  [name, {content:readFileSync(new URL('../tests/solc/' + name, import.meta.url), 'utf8')}]));
const reports = [];
for (const viaIR of [false, true]) {
  const settings = {viaIR, evmVersion:'cancun', optimizer:{enabled:true},
    outputSelection:{'*':{'*':['abi', 'evm.deployedBytecode.object']}}};
  const out = JSON.parse(compile(JSON.stringify({language:'Solidity', sources, settings}), 0, 0));
  assert.deepEqual((out.errors ?? []).filter(e => e.severity === 'error'), []);
  const c = out.contracts['TransientWorldScenario.sol'].TransientWorldScenario;
  const iface = new Interface(c.abi);
  const common = new Common({chain:Mainnet, hardfork:Hardfork.Cancun});
  const vm = await createVM({common});
  const to = createAddressFromString('0x0000000000000000000000000000000000001234');
  // Public fixture key; funds exist only inside this in-memory reference VM.
  const key = hexToBytes('0x' + '46'.repeat(32));
  const caller = createAddressFromPrivateKey(key);
  await vm.stateManager.putAccount(caller, createAccount({balance:10n ** 30n}));
  await vm.stateManager.putAccount(to, createAccount({balance:0n}));
  // Scenario has no constructor effects; children execute actual CREATE code.
  await vm.stateManager.putCode(to, hexToBytes('0x' + c.evm.deployedBytecode.object));
  let nonce = 0n;
  const observations = [];
  async function transaction(name, expected = [], failure = null) {
    const tx = createLegacyTx({nonce:nonce++, gasPrice:1000000000n, gasLimit:30000000n,
      to, value:0n, data:hexToBytes(iface.encodeFunctionData(name))}, {common}).sign(key);
    const {execResult:r} = await runTx(vm, {tx, skipBlockGasLimitValidation:true});
    const bytes = bytesToHex(r.returnValue);
    if (failure) {
      assert.equal(r.exceptionError?.error, 'revert', name);
      assert.equal(bytes, failure === 'panic' ? '0x4e487b71' + '1'.padStart(64, '0') : '0x', name);
    } else {
      assert.equal(r.exceptionError, undefined, name);
      assert.deepEqual(Array.from(iface.decodeFunctionResult(name, bytes), String), expected.map(String), name);
    }
    observations.push({name, expected, failure, actual:bytes, exception:r.exceptionError?.error ?? null});
  }
  await transaction('makeOnly', [9]);
  await transaction('checkFresh', [9]);
  await transaction('uncaught', [], 'revert');
  await transaction('checkFresh', [9]);
  await transaction('caught', [false]);
  await transaction('checkLater', [11]);
  await transaction('falseShared', [], 'panic');
  await transaction('failWrite', [], 'revert');
  await transaction('checkLater', [11]);
  await transaction('compose', [11]);
  await transaction('checkLater', [11]);
  reports.push({pipeline:viaIR ? 'viaIR' : 'legacy', settings, observations});
}
console.log(JSON.stringify({version, compilerSha256:sha(readFileSync(compilerFile)),
  sources:Object.fromEntries(Object.entries(sources).map(([name, value]) => [name, sha(value.content)])),
  reset:'successive signed transactions on one VM per pipeline', reports}, null, 2));
