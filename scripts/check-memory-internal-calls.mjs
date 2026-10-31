#!/usr/bin/env node
// Optional source reference. Core Lean remains dependency-free.
// Usage: node scripts/check-memory-internal-calls.mjs SOLJSON MODULES_DIR [cancun|osaka]
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
const source = readFileSync(fileURLToPath(new URL('../tests/solc/MemoryInternalCalls.sol', import.meta.url)), 'utf8');
const address = createAddressFromString('0x0000000000000000000000000000000000001234');
const vectors = [
  ['discardedReturn', [], [7n, 42n]],
  ['primitiveTypes', [], [-3n, true, 19n, 42n]],
  ['callerOwnership', [], [17n, 17n, 33n, 2n, 11n, 42n]],
  ['largeCost', [], [4097n]],
  ['directCopy', [], [9n, 4n]],
  ['forwarding', [], [21n]],
  ['voidCall', [], [17n, 42n]],
  ['mutation', [], [8n, 7n, 42n]],
  ['references', [], [12n, 2n]],
  ['copies', [], [9n, 9n, 4n]],
  ['branches', [true], [7n]],
  ['branches', [false], [7n]],
  ['boundsFailure', [], '4e487b71' + '0'.repeat(62) + '32'],
  ['calleeFailure', [], ''],
  ['failedReturnArgument', [], '4e487b71' + '0'.repeat(62) + '32'],
];
const observations = [];
for (const viaIR of [false, true]) for (const optimizer of [false, true]) {
  const out = JSON.parse(compile(JSON.stringify({language:'Solidity',
    sources:{'MemoryInternalCalls.sol':{content:source}}, settings:{viaIR,
      optimizer:{enabled:optimizer,runs:200},evmVersion,
      outputSelection:{'*':{'*':['abi','evm.deployedBytecode.object']}}}}),0,0));
  assert.deepEqual((out.errors ?? []).filter(e => e.severity === 'error'), []);
  const c = out.contracts['MemoryInternalCalls.sol'].MemoryInternalCalls;
  const iface = new Interface(c.abi);
  const vm = await createVM({common:new Common({chain:Mainnet, hardfork:evmVersion === 'osaka' ? Hardfork.Osaka : Hardfork.Cancun})});
  await vm.stateManager.putAccount(address, createAccount({balance:0n}));
  for (const [name,args,expected] of vectors) {
    const result = await vm.evm.runCode({to:address,
      code:hexToBytes('0x' + c.evm.deployedBytecode.object),
      data:hexToBytes(iface.encodeFunctionData(name,args)),gasLimit:30000000n});
    let observed;
    if (typeof expected === 'string') {
      assert.equal(result.exceptionError?.error, 'revert', name);
      observed = Buffer.from(result.returnValue).toString('hex');
      assert.equal(observed, expected, name);
    } else {
      assert.equal(result.exceptionError, undefined, name);
      observed = Array.from(iface.decodeFunctionResult(name,result.returnValue));
      assert.deepEqual(observed, expected, name);
    }
    observations.push({viaIR,optimizer,name,args,observed});
  }
}
console.log(JSON.stringify({compiler:version,compilerSha,evmVersion,executions:observations.length,
  sourceSha:createHash('sha256').update(source).digest('hex'),observations},
  (_,v) => typeof v === 'bigint' ? v.toString() : v, 2));
