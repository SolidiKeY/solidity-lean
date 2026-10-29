#!/usr/bin/env node
// Independent source reference; no Lean process and no output files.
// Usage: node scripts/check-slice-copies.mjs SOLJSON SHA256 MODULES_DIR
// MODULES_DIR supplies @ethereumjs/{vm,common,util} and ethers.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {resolve, join} from 'node:path';
import {fileURLToPath} from 'node:url';

const [compilerFile, compilerSha, modulesDir] = process.argv.slice(2);
const pin = '6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390';
assert(compilerFile && modulesDir && compilerSha === pin, 'expected pinned 0.8.38 SOLJSON SHA256 MODULES_DIR');
assert.equal(createHash('sha256').update(readFileSync(compilerFile)).digest('hex'), pin);
const req = createRequire(join(resolve(modulesDir), 'package.json'));
const compiler = req(resolve(compilerFile));
const version = compiler.cwrap('solidity_version', 'string', [])();
assert.equal(version, '0.8.38+commit.1835d247.Emscripten.clang');
const compile = compiler.cwrap('solidity_compile', 'string', ['string', 'number', 'number']);
const {createVM} = req('@ethereumjs/vm');
const {Common, Mainnet, Hardfork} = req('@ethereumjs/common');
const {hexToBytes, createAddressFromString, createAccount} = req('@ethereumjs/util');
const {Interface} = req('ethers');
const source = readFileSync(fileURLToPath(new URL('../tests/solc/SliceCopies.sol', import.meta.url)), 'utf8');
function output(text, viaIR, bytecode = true) {
  return JSON.parse(compile(JSON.stringify({language:'Solidity', sources:{'SliceCopies.sol':{content:text}},
    settings:{viaIR, evmVersion:'osaka', optimizer:{enabled:false,runs:200},
      outputSelection:{'*':{'*':bytecode ? ['abi','evm.deployedBytecode.object'] : [], '':['ast']}}}}),0,0));
}
const errors = out => (out.errors ?? []).filter(e => e.severity === 'error');
const address = createAddressFromString('0x0000000000000000000000000000000000001234');
const xs = [3n,5n,7n,9n];
let executions = 0;
for (const viaIR of [false,true]) {
  const out = output(source, viaIR);
  assert.deepEqual(errors(out), [], 'positive source must compile to bytecode');
  const c = out.contracts['SliceCopies.sol'].SliceCopies;
  const iface = new Interface(c.abi);
  const vm = await createVM({common:new Common({chain:Mainnet, hardfork:Hardfork.Osaka})});
  await vm.stateManager.putAccount(address, createAccount({balance:0n}));
  for (const [name,args,expected] of [
    ['copies',[xs],null], ['passing',[xs],null], ['storageCopy',[xs],null],
    ['hashes',['0x0061626300'],null], ['narrow',[[0,255],[false,true],['0x0000','0x1234']],null],
    ['aliases',[[17n],[1n,2n]],null], ['lazy',[xs],null],
    ['invalidRange',[xs],''], ['falsePost',[[0n,5n,0n]],'4e487b71' + '0'.repeat(63) + '1'],
  ]) {
    const result = await vm.evm.runCode({to:address,
      code:hexToBytes('0x' + c.evm.deployedBytecode.object),
      data:hexToBytes(iface.encodeFunctionData(name,args)), gasLimit:30000000n});
    if (expected === null) assert.equal(result.exceptionError,undefined,name);
    else {
      assert.equal(result.exceptionError?.error,'revert',name);
      assert.equal(Buffer.from(result.returnValue).toString('hex'),expected,name);
    }
    executions++;
  }
  for (const body of [
    'uint[] calldata v = xs[:]; v[0] = 1;',
    'uint[] memory m = xs[:]; uint[] memory v = m[:];',
    'uint[] memory m = small[:];',
  ]) {
    const bad = 'pragma solidity ^0.8.0; contract C { function f(uint[] calldata xs, uint8[] calldata small) public pure { ' + body + ' } }';
    assert(errors(output(bad,viaIR,false)).length > 0,'invalid source accepted: ' + body);
  }
}
console.log(JSON.stringify({compiler:version,pipelines:['legacy','viaIR'],executions,invalidSourcesPerPipeline:3}));
