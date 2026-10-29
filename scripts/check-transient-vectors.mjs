#!/usr/bin/env node
// Pure optional reference: no downloads, installations or generated repo files.
// node scripts/check-transient-vectors.mjs SOLJSON_FILE EXTERNAL_NODE_MODULES
// The module directory supplies EthereumJS vm/common/tx/util and ethers.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {resolve} from 'node:path';
import {fileURLToPath} from 'node:url';

const [compilerFile, modules] = process.argv.slice(2);
assert(compilerFile && modules, 'expected SOLJSON_FILE EXTERNAL_NODE_MODULES');
const pins = new Map([
  ['c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8', /^0\.8\.34\+commit\.80d5c536/],
  ['6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390', /^0\.8\.38\+commit\.1835d247/]
]);
const hash = createHash('sha256').update(readFileSync(compilerFile)).digest('hex');
assert(pins.has(hash), 'unsupported compiler bytes');
const req = createRequire(resolve(modules, 'reference.cjs'));
const solc = req(resolve(compilerFile));
const version = solc.cwrap('solidity_version', 'string', [])();
assert.match(version, pins.get(hash));
const compile = solc.cwrap('solidity_compile', 'string', ['string', 'number', 'number']);
const {createVM, runTx} = req('@ethereumjs/vm');
const {Common, Mainnet, Hardfork} = req('@ethereumjs/common');
const {createLegacyTx} = req('@ethereumjs/tx');
const {hexToBytes, bytesToHex, createAddressFromString, createAddressFromPrivateKey, createAccount} =
  req('@ethereumjs/util');
const {Interface} = req('ethers');
const source = readFileSync(fileURLToPath(new URL('../tests/solc/TransientStorage.sol', import.meta.url)), 'utf8');
const errors = out => (out.errors ?? []).filter(e => e.severity === 'error');
function output(content, viaIR) {
  return JSON.parse(compile(JSON.stringify({language:'Solidity', sources:{'T.sol':{content}},
    settings:{viaIR, evmVersion:'osaka', optimizer:{enabled:true},
      outputSelection:{'*':{'*':['abi','evm.deployedBytecode.object']}}}}), 0, 0));
}
let executions = 0;
for (const viaIR of [false, true]) {
  const out = output(source, viaIR);
  assert.deepEqual(errors(out), []);
  const c = out.contracts['T.sol'].TransientStorage;
  const iface = new Interface(c.abi);
  const common = new Common({chain:Mainnet, hardfork:Hardfork.Osaka});
  const vm = await createVM({common});
  const to = createAddressFromString('0x0000000000000000000000000000000000001234');
  // Public deterministic fixture key, funded only in this in-memory VM.
  const key = hexToBytes('0x' + '46'.repeat(32));
  const caller = createAddressFromPrivateKey(key);
  await vm.stateManager.putAccount(caller, createAccount({balance:10n ** 30n}));
  await vm.stateManager.putAccount(to, createAccount({balance:0n}));
  await vm.stateManager.putCode(to, hexToBytes('0x' + c.evm.deployedBytecode.object));
  let nonce = 0n;
  async function transaction(name, args = [], expected = [], panic = false) {
    // Osaka EIP-7825 caps a transaction at 2^24 gas.
    const tx = createLegacyTx({nonce:nonce++, gasPrice:1000000000n, gasLimit:16777216n,
      to, value:0n, data:hexToBytes(iface.encodeFunctionData(name, args))}, {common}).sign(key);
    // Real top-level transactions exercise EIP-1153 reset. Do not manually
    // clear transient storage, replace the VM, or reinstall code between calls.
    const {execResult:r} = await runTx(vm, {tx, skipBlockGasLimitValidation:true});
    if (panic) {
      assert.equal(r.exceptionError?.error, 'revert', name);
      assert.equal(bytesToHex(r.returnValue), '0x4e487b71' + '1'.padStart(64, '0'), name);
    } else {
      assert.equal(r.exceptionError, undefined, `${name} viaIR=${viaIR}`);
      assert.deepEqual(Array.from(iface.decodeFunctionResult(name, bytesToHex(r.returnValue)), String),
        expected.map(String), name);
    }
    executions++;
  }
  await transaction('readBoth', [], [0, 0]);
  await transaction('reenter', [], [9]);
  await transaction('caught', [true], [7, 3]);
  await transaction('caught', [false], [11, 9]);
  await transaction('staticWrite', [], [false]);
  await transaction('falseReentrantValue', [], [], true);
  await transaction('falsePartialRollback', [], [], true);
  await transaction('writeBoth');
  await transaction('readBoth', [], [0, 3]);
}

const invalid = [
  'uint transient x = 1;',
  'uint[] transient x;',
  'uint transient constant x = 1;',
  'uint transient immutable x;',
  'uint transient x; function f() public view { x = 1; }',
  'uint transient x; function f() public pure returns(uint) { return x; }',
];
for (const viaIR of [false, true])
  for (const members of invalid)
    assert(errors(output('pragma solidity ^0.8.28; contract Invalid { ' + members + ' }', viaIR)).length > 0,
      'invalid transient declaration/effect was accepted: ' + members);
console.log(JSON.stringify({version, pipelines:['legacy','viaIR'], executions,
  invalidSources:invalid.length * 2, reset:'successive signed transactions on one VM per pipeline'}));
