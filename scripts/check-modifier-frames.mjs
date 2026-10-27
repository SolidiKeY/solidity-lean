#!/usr/bin/env node
// Optional reference checks. Dependencies stay outside the Lean package.
// node scripts/check-modifier-frames.mjs SOLJSON_FILE EXTERNAL_NODE_MODULES
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {resolve} from 'node:path';
const [compiler, modules] = process.argv.slice(2);
assert.ok(compiler && modules, 'expected compiler and external node_modules');
const sha = createHash('sha256').update(readFileSync(compiler)).digest('hex');
assert.equal(sha, '6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390');
const require = createRequire(resolve(modules, 'reference.cjs'));
const {createVM} = require('@ethereumjs/vm');
const {Common, Mainnet, Hardfork} = require('@ethereumjs/common');
const {createAddressFromString, hexToBytes, bytesToHex} = require('@ethereumjs/util');
const {Interface} = require('ethers');
const solc = createRequire(import.meta.url)(resolve(compiler));
const compile = solc.cwrap('solidity_compile', 'string', ['string', 'number', 'number']);
const version = solc.cwrap('solidity_version', 'string', [])();
assert.equal(version, '0.8.38+commit.1835d247.Emscripten.clang');
const source = readFileSync(new URL('../tests/solc/ModifierFrames.sol', import.meta.url), 'utf8');
let count = 0;
for (const viaIR of [false, true]) {
  const result = JSON.parse(compile(JSON.stringify({language:'Solidity',
    sources:{'ModifierFrames.sol':{content:source}}, settings:{viaIR,
      optimizer:{enabled:true}, evmVersion:'cancun',
      outputSelection:{'*':{'*':['abi','evm.deployedBytecode.object']}}}}), 0, 0));
  assert.deepEqual((result.errors ?? []).filter(e => e.severity === 'error'), []);
  const c = result.contracts['ModifierFrames.sol'].ModifierFrames;
  const iface = new Interface(c.abi);
  const to = createAddressFromString('0x0000000000000000000000000000000000001000');
  async function check(name, args, expected, total, fail=false) {
    const vm = await createVM({common:new Common({chain:Mainnet, hardfork:Hardfork.Cancun})});
    await vm.stateManager.putCode(to, hexToBytes('0x'+c.evm.deployedBytecode.object));
    async function call(fn, xs) {
      return (await vm.evm.runCall({to, data:hexToBytes(iface.encodeFunctionData(fn,xs)),
        gasLimit:30000000n})).execResult;
    }
    const r = await call(name,args);
    if (fail) {
      assert.ok(r.exceptionError, `${name} viaIR=${viaIR} must revert`);
      assert.equal(bytesToHex(r.returnValue), '0x4e487b71'+(17n).toString(16).padStart(64,'0'));
    } else {
      assert.equal(r.exceptionError, undefined, `${name} viaIR=${viaIR}`);
      const actual = Array.from(iface.decodeFunctionResult(name,bytesToHex(r.returnValue)), String);
      assert.deepEqual(actual, expected.map(String), `${name} viaIR=${viaIR}`);
      if (total !== undefined) {
        const t = await call('total',[]);
        assert.equal(t.exceptionError, undefined);
        assert.equal(iface.decodeFunctionResult('total',bytesToHex(t.returnValue))[0], BigInt(total));
      }
    }
    count++;
  }
  await check('assignedReturn',[],[2,3]);
  await check('assignedSkipped',[],[viaIR?0:2]);
  await check('packed',[1],[1]);
  await check('packedArray',[[1]],[32]);
  await check('stringLength',['abc'],[3]);
  await check('functionSlot',[],[8]);
  await check('storageAlias',[],[viaIR?2:1]);
  await check('memoryReturn',[],[7]);
  await check('rollback',[],[0],0);
  await check('loop',[],[viaIR?1:10]);
  await check('multi',[false],[1]);
  await check('multi',[true],[viaIR?1:2]);
  await check('parameter',[0],[viaIR?0:1]);
  await check('nested',[],[viaIR?1:4]);
  await check('skips',[],[0]);
  await check('early',[],[viaIR?1:2],12);
  await check('argument',[1],[viaIR?2:3],viaIR?11:12);
  await check('memoryAlias',[[0]],[viaIR?2:1]);
  await check('narrow',[254],[254],undefined,!viaIR);
  await check('pair',[],viaIR?[1,true]:[2,false]);
  console.log(JSON.stringify({pipeline:viaIR?'viaIR':'legacy',vectors:20,compilerSha256:sha}));
}
console.log(`${count} pinned solc/EVM modifier vectors passed (${version}).`);
