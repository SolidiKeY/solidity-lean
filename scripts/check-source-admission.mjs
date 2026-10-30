#!/usr/bin/env node
import {verifyBudgetArtifact,runWithAttemptBudget} from './evm-reference/attempt-budget.mjs';
// Optional independent solc/EVM reference. No dependency is added to Lake.
// Usage: node scripts/check-source-admission.mjs SOLJSON SHA256 MODULES_DIR
// MODULES_DIR supplies @ethereumjs/{vm,common,util} and ethers.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {resolve, join} from 'node:path';

const [compilerFile, compilerSha, modulesDir] = process.argv.slice(2);
assert(compilerFile && modulesDir && /^[0-9a-f]{64}$/.test(compilerSha ?? ''),
  'expected SOLJSON SHA256 MODULES_DIR');
const pins = new Map([
  ['c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8', '0.8.34+commit.80d5c536.Emscripten.clang'],
  ['6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390', '0.8.38+commit.1835d247.Emscripten.clang'],
]);
assert(pins.has(compilerSha), 'unknown compiler pin');
assert.equal(createHash('sha256').update(readFileSync(compilerFile)).digest('hex'), compilerSha);
verifyBudgetArtifact(modulesDir);
const req = createRequire(join(resolve(modulesDir), 'package.json'));
const compiler = req(resolve(compilerFile));
assert.equal(compiler.cwrap('solidity_version', 'string', [])(), pins.get(compilerSha));
const compile = compiler.cwrap('solidity_compile', 'string', ['string', 'number', 'number']);
const {createVM} = req('@ethereumjs/vm');
const {Common, Mainnet, Hardfork} = req('@ethereumjs/common');
const {hexToBytes, createAddressFromString, createAccount} = req('@ethereumjs/util');
const {Interface} = req('ethers');
function output(source, viaIR = false, bytecode = true) {
  return JSON.parse(compile(JSON.stringify({language:'Solidity', sources:{'S.sol':{content:source}},
    settings:{viaIR, evmVersion:'cancun', optimizer:{enabled:false,runs:200},
      outputSelection:{'*':{'*':bytecode ? ['abi','evm.deployedBytecode.object'] : [], '':['ast']}}}}),0,0));
}
const errors = out => (out.errors ?? []).filter(error => error.severity === 'error');
const address = createAddressFromString('0x0000000000000000000000000000000000001234');
let executed = 0;
for (const viaIR of [false, true]) {
  for (const [contract, names] of [
    ['SourceLiterals', ['rationalRemainders','signedConstants','computedBounds','byteSequences',
      'extremeConstants','degeneratePowers','addressContext','falseRemainder']],
    ['SourceIdentifiers', ['noOpShadow','$compute','localMagic']],
  ]) {
    const source = readFileSync('tests/solc/' + contract + '.sol', 'utf8');
    const out = output(source, viaIR);
    assert.deepEqual(errors(out), [], 'source must compile to bytecode');
    const compiled = out.contracts['S.sol'][contract];
    const iface = new Interface(compiled.abi);
    const vm = await createVM({common:new Common({chain:Mainnet,hardfork:Hardfork.Cancun})});
    await vm.stateManager.putAccount(address, createAccount({balance:0n}));
    for (const name of names) {
      const result = await runWithAttemptBudget(vm, 'runCode', {to:address,
        code:hexToBytes('0x' + compiled.evm.deployedBytecode.object),
        data:hexToBytes(iface.encodeFunctionData(name, [])), gasLimit:30000000n}, {label:`${viaIR ? 'viaIR' : 'legacy'}:${contract}.${name}`});
      if (name === 'falseRemainder') {
        assert.equal(result.exceptionError?.error, 'revert');
        assert.equal(Buffer.from(result.returnValue).toString('hex'),
          '4e487b710000000000000000000000000000000000000000000000000000000000000001');
      } else assert.equal(result.exceptionError, undefined, name);
      executed++;
    }
  }
}
for (const statement of ['uint7 x;', 'uint x = 1e+2;', 'bytes memory x = hex"f";',
    'uint x = 1 << 4294967296;', 'uint x = 0 ** 0.5;', 'string memory x = "/*']) {
  const source = 'pragma solidity ^0.8.0; contract C { function f() public pure { ' + statement + ' } }';
  assert(errors(output(source)).length > 0, 'invalid source was accepted: ' + statement);
}
const invalidGates = ['pragma solidity >=0.9.0;',
  'pragma abicoder v1; pragma abicoder v2;',
  'pragma experimental ABIEncoderV2; pragma abicoder v2;',
  'pragma experimental FutureMode;'];
for (const gate of invalidGates)
  assert(errors(output(gate + ' contract C {}', false, false)).length > 0, gate);
const acceptedGates = ['pragma abicoder v1;',
  'pragma abicoder v2; pragma experimental ABIEncoderV2;',
  'pragma experimental SMTChecker;'];
for (const gate of acceptedGates)
  assert.deepEqual(errors(output(gate + ' contract C {}', false, false)), [], gate);
console.log(JSON.stringify({compiler:pins.get(compilerSha), evmVersion:'cancun',
  pipelines:['legacy','viaIR'], executions:executed, invalidSources:6,
  rejectedGates:invalidGates.length, acceptedGates:acceptedGates.length}));
