#!/usr/bin/env node
/** Independent compiler/EVM oracle. All compilation/execution is in memory.
 * Usage: node scripts/check-public-getters.mjs SOLJSON_FILE MODULES_DIRECTORY
 * Uses the same optional external reference dependencies as check-abi-vectors.
 */
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {resolve} from 'node:path';
const [compilerFile, modules] = process.argv.slice(2);
assert(compilerFile && modules, 'expected compiler file and modules directory');
const pins = new Map([
  ['c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8', /^0\.8\.34\+commit\.80d5c536/],
  ['6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390', /^0\.8\.38\+commit\.1835d247/],
]);
const sha = createHash('sha256').update(readFileSync(compilerFile)).digest('hex');
assert(pins.has(sha), 'unsupported compiler pin');
const solc = createRequire(import.meta.url)(resolve(compilerFile));
assert.match(solc.cwrap('solidity_version','string',[])(), pins.get(sha));
const compile = solc.cwrap('solidity_compile','string',['string','number','number']);
const req = createRequire(resolve(modules, 'reference.cjs'));
const {createVM} = req('@ethereumjs/vm');
const {Common, Mainnet, Hardfork} = req('@ethereumjs/common');
const {hexToBytes, createAddressFromString, createAccount} = req('@ethereumjs/util');
const {Interface} = req('ethers');
const source = readFileSync(new URL('../tests/solc/PublicGetters.sol', import.meta.url), 'utf8');
const explicitPrefix = `
contract ExplicitBytesPrefix {
  function convert() public pure returns (bytes4) {
    string memory text = "ab";
    return bytes4(bytes(text));
  }
}`;
const errors = out => (out.errors ?? []).filter(error => error.severity === 'error');
const output = (text, viaIR) => JSON.parse(compile(JSON.stringify({language:'Solidity',
  sources:{'Getters.sol':{content:text}}, settings:{viaIR, evmVersion:'cancun',
    optimizer:{enabled:false,runs:200}, outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.methodIdentifiers']}}}}),0,0));
let executions = 0;
for (const viaIR of [false, true])
  assert(errors(output('pragma solidity ^0.8.0; contract InvalidPrefix { function f(uint8[] memory xs) public pure returns (bytes4) { return bytes4(xs); } }', viaIR)).length > 0,
    'uint8[] must not be accepted as a byte string');
for (const viaIR of [false, true])
  assert(errors(output('pragma solidity ^0.8.0; contract InvalidPrefix { function f(string memory text) public pure returns (bytes4) { return bytes4(text); } }', viaIR)).length > 0,
    'string requires an explicit bytes conversion');
for (const viaIR of [false,true]) {
  const out = output(source + explicitPrefix, viaIR);
  assert.deepEqual(errors(out), []);
  const code = out.contracts['Getters.sol'];
  const compiled = code.PublicGetters;
  const abi = compiled.abi;
  const getter = name => abi.find(row => row.type === 'function' && row.name === name);
  assert.deepEqual(getter('entry').outputs.map(row => [row.name,row.type]), [['value','uint32'],['live','bool']]);
  assert.deepEqual(getter('allowances').inputs.map(row => [row.name,row.type]), [['who','address'],['kind','uint16']]);
  assert.deepEqual(getter('sequences').inputs.map(row => row.type), ['uint256','uint256']);
  const caller = createAddressFromString('0x0000000000000000000000000000000000001234');
  const vm = await createVM({common:new Common({chain:Mainnet,hardfork:Hardfork.Cancun})});
  await vm.stateManager.putAccount(caller, createAccount({balance:1000000000000000000n}));
  async function deploy(contract, success = true) {
    const result = await vm.evm.runCall({caller, data:hexToBytes('0x'+code[contract].evm.bytecode.object), gasLimit:30000000n});
    assert.equal(result.execResult.exceptionError?.error, success ? undefined : 'revert', contract);
    assert.equal(success || Buffer.from(result.execResult.returnValue).toString('hex').startsWith('4e487b71'), true);
    executions++;
    return result.createdAddress;
  }
  const explicitAddress = await deploy('ExplicitBytesPrefix');
  const explicitAbi = new Interface(code.ExplicitBytesPrefix.abi);
  const explicit = await vm.evm.runCall({caller, to:explicitAddress,
    data:hexToBytes(explicitAbi.encodeFunctionData('convert',[])), gasLimit:30000000n});
  assert.equal(explicit.execResult.exceptionError, undefined);
  assert.equal(explicitAbi.decodeFunctionResult('convert',explicit.execResult.returnValue)[0], '0x61620000');
  executions++;
  const address = await deploy('PublicGetters');
  const iface = new Interface(abi);
  for (const name of ['scalar','viaInterface','primitives','nestedMapping','boolKeys','arrays',
    'structFields','inheritedGetters','fixedBounds','selectorBounds','identity','falseScalar','falseBoundsPanic']) {
    const result = await vm.evm.runCall({caller, to:address,
      data:hexToBytes(iface.encodeFunctionData(name, [])), gasLimit:30000000n});
    assert.equal(result.execResult.exceptionError?.error, name.startsWith('false') ? 'revert' : undefined, name);
    if (name.startsWith('false')) assert.equal(Buffer.from(result.execResult.returnValue).toString('hex'),
      '4e487b710000000000000000000000000000000000000000000000000000000000000001');
    executions++;
  }
  const prefixAddress = await deploy('GetterBytePrefixes');
  const prefixAbi = new Interface(code.GetterBytePrefixes.abi);
  for (const name of ['emptyPrefix','shortPrefix','leadingZeroPrefix','longPrefix','evaluateOnce','lazyPrefix']) {
    const result = await vm.evm.runCall({caller, to:prefixAddress,
      data:hexToBytes(prefixAbi.encodeFunctionData(name, [])), gasLimit:30000000n});
    assert.equal(result.execResult.exceptionError, undefined, name);
    executions++;
  }
  const referenceAddress = await deploy('GetterReferences');
  const referenceAbi = new Interface(code.GetterReferences.abi);
  const local = await vm.evm.runCall({caller, to:referenceAddress, data:hexToBytes(referenceAbi.encodeFunctionData('localBytes',[])), gasLimit:30000000n});
  assert.equal(local.execResult.exceptionError, undefined, 'ordinary bytes reads remain supported');
  executions++;
  await deploy('GetterCtorCollision');
  await deploy('GetterCtorFalse', false);
  await deploy('GetterCtorStructAlias');
  const slot = await deploy('GetterFunctionSlot');
  const slotAbi = new Interface(code.GetterFunctionSlot.abi);
  for (const name of ['getterSelector','falseStoredSelector']) {
    const result = await vm.evm.runCall({caller, to:slot, data:hexToBytes(slotAbi.encodeFunctionData(name,[])), gasLimit:30000000n});
    assert.equal(result.execResult.exceptionError?.error, name === 'falseStoredSelector' ? 'revert' : undefined, name);
    executions++;
  }
}
for (const body of [
  'uint[] public a; function f() external view returns(uint) { return this.a(); }',
  'mapping(uint => uint[]) public a; function f() external view returns(uint) { return this.a(1); }',
  'struct S { uint x; bool y; uint[] omitted; } S public s; function f() external view { (uint x,bool y,uint[] memory z)=this.s(); x;y;z; }',
]) assert(errors(output('pragma solidity ^0.8.0; contract C {'+body+'}',false)).length > 0,
  'invalid getter arity/output must be rejected');
console.log(JSON.stringify({sha, pipelines:2, executions, compilerRejections:7}));
