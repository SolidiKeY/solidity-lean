#!/usr/bin/env node
// Optional source reference for internal function values with memory-array
// arguments (docs/feature-work/finite-dispatch.md). Core Lean remains dependency-free.
// Usage: node scripts/check-function-value-references.mjs SOLJSON MODULES_DIR [cancun|osaka]
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {resolve, join} from 'node:path';
import {fileURLToPath} from 'node:url';

const [compilerFile, modulesDir, evmVersion = 'cancun'] = process.argv.slice(2);
assert(['cancun', 'osaka'].includes(evmVersion), 'expected cancun or osaka');
assert(compilerFile && modulesDir, 'expected pinned SOLJSON and external MODULES_DIR');
const compilerSha = 'c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8';
assert.equal(createHash('sha256').update(readFileSync(compilerFile)).digest('hex'), compilerSha);
const req = createRequire(join(resolve(modulesDir), 'package.json'));
const compiler = req(resolve(compilerFile));
const version = compiler.cwrap('solidity_version', 'string', [])();
assert.equal(version, '0.8.34+commit.80d5c536.Emscripten.clang');
const compile = compiler.cwrap('solidity_compile', 'string', ['string', 'number', 'number']);
const {createVM} = req('@ethereumjs/vm');
const {Common, Mainnet, Hardfork} = req('@ethereumjs/common');
const {hexToBytes, createAddressFromString, createAccount} = req('@ethereumjs/util');
const {Interface} = req('ethers');
const source = readFileSync(fileURLToPath(new URL('../tests/solc/FunctionValueReferences.sol', import.meta.url)), 'utf8');
const address = createAddressFromString('0x0000000000000000000000000000000000001234');
const vectors = [
  ['aliasing', [], [11n, 11n, 1n]],
  ['storageCopy', [], [11n, 1n, 2n]],
  // Legacy copies a storage argument to memory at its position; viaIR
  // copies after every argument ran, for a direct call and a dispatch alike.
  ['argumentOrder', [], {legacy:[101n, 9n], viaIR:[901n, 9n]}],
  ['argumentOrderDirect', [], {legacy:[101n, 9n], viaIR:[901n, 9n]}],
  // Legacy reads the callee value after the arguments, viaIR before them.
  ['calleeOrder', [], {legacy:[4002n], viaIR:[402n]}],
  ['branches', [true], [13n]],
  ['branches', [false], [7n]],
  ['unassigned', [], '4e487b71' + '0'.repeat(62) + '51'],
  ['unassignedStored', [], '4e487b71' + '0'.repeat(62) + '51'],
  ['calleeOrderScalar', [], {legacy:[12n], viaIR:[11n]}],
  ['deleted', [], '4e487b71' + '0'.repeat(62) + '51'],
  ['narrow', [], [200n]],
  ['storageAlias', [], [6n, 6n]],
  ['storageOrder', [], [901n, 9n]],
  ['arrayReturn', [true], [106n, 106n, 1n]],
  ['arrayReturn', [false], [5n, 110n, 1n]],
  ['bytesReturn', [], [3n, 65n]],
  ['structMemory', [], [2n, 2n, 43n]],
  ['structStorage', [], [8n, 8n]],
  ['nominalQ', [], [9n]],
  ['falseObservation', [], '4e487b71' + '0'.repeat(62) + '01'],
];
const zeroStorageValue = ['deleted', 'unassignedStored'];
const observations = [];
for (const viaIR of [false, true]) for (const optimizer of [false, true]) {
  const out = JSON.parse(compile(JSON.stringify({language:'Solidity',
    sources:{'FunctionValueReferences.sol':{content:source}}, settings:{viaIR,
      optimizer:{enabled:optimizer,runs:200},evmVersion,
      outputSelection:{'*':{'*':['abi','evm.deployedBytecode.object']}}}}),0,0));
  assert.deepEqual((out.errors ?? []).filter(e => e.severity === 'error'), []);
  const c = out.contracts['FunctionValueReferences.sol'].FunctionValueReferences;
  const iface = new Interface(c.abi);
  const vm = await createVM({common:new Common({chain:Mainnet, hardfork:evmVersion === 'osaka' ? Hardfork.Osaka : Hardfork.Cancun})});
  await vm.stateManager.putAccount(address, createAccount({balance:0n}));
  for (const [name,args,expectedAny] of vectors) {
    const expected = expectedAny?.legacy ? (viaIR ? expectedAny.viaIR : expectedAny.legacy) : expectedAny;
    const result = await vm.evm.runCode({to:address,
      code:hexToBytes('0x' + c.evm.deployedBytecode.object),
      data:hexToBytes(iface.encodeFunctionData(name,args)),gasLimit:30000000n});
    let observed;
    if (typeof expected === 'string' && !viaIR && zeroStorageValue.includes(name) &&
        result.exceptionError?.error?.startsWith('invalid JUMP')) {
      // Legacy codegen jumps to a zero *storage* function value (never
      // assigned or deleted): an exceptional halt without data. viaIR raises
      // Panic(0x51), as both pipelines do for an unassigned local value.
      // Both are failures; the model retains the Panic(0x51) bytes.
      observed = 'invalid JUMP';
    } else if (typeof expected === 'string') {
      assert.equal(result.exceptionError?.error, 'revert', name);
      observed = Buffer.from(result.returnValue).toString('hex');
      assert.equal(observed, expected, `${name} viaIR=${viaIR} optimizer=${optimizer}`);
    } else {
      assert.equal(result.exceptionError, undefined, name);
      observed = Array.from(iface.decodeFunctionResult(name,result.returnValue));
      assert.deepEqual(observed, expected, `${name} viaIR=${viaIR} optimizer=${optimizer}`);
    }
    observations.push({viaIR,optimizer,name,args,observed});
  }
}
console.log(JSON.stringify({compiler:version,compilerSha,evmVersion,executions:observations.length,
  sourceSha:createHash('sha256').update(source).digest('hex'),observations},
  (_,v) => typeof v === 'bigint' ? v.toString() : v, 2));
