// External engine observations only: no source/bytecode equivalence theorem.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createRequire} from 'node:module';
import {resolve} from 'node:path';
const runtime = process.argv[2];
assert.ok(runtime, 'expected separately provisioned runtime directory');
const req = createRequire(resolve(runtime, 'package.json'));
const version = name => JSON.parse(readFileSync(resolve(runtime, 'node_modules', name, 'package.json'), 'utf8')).version;
for (const name of ['@ethereumjs/evm', '@ethereumjs/common']) assert.equal(version(name), '10.1.3');
const {Common, Mainnet, Hardfork} = req('@ethereumjs/common');
const {createEVM, paramsEVM} = req('@ethereumjs/evm');
const fixtures = [
  {name:'push-exact-gas', fork:'Osaka', code:[0x60,0x2a,0x00], gas:3, stack:['42'], used:'3'},
  {name:'push-one-gas-short', fork:'Osaka', code:[0x60,0x2a,0x00], gas:2, error:'out of gas', used:'2'},
  {name:'push0-shanghai', fork:'Shanghai', code:[0x5f,0x00], gas:2, stack:['0'], used:'2'},
  {name:'push0-paris', fork:'Paris', code:[0x5f,0x00], gas:100, error:'invalid opcode', used:'100'},
  {name:'clz-osaka', fork:'Osaka', code:[0x60,0x01,0x1e,0x00], gas:8, stack:['255'], used:'8'},
  {name:'clz-prague', fork:'Prague', code:[0x60,0x01,0x1e,0x00], gas:100, error:'invalid opcode', used:'100'},
  {name:'runtime-truncated-push-zero-extension', fork:'Osaka', code:[0x60], gas:3, stack:['0'], used:'3'},
  {name:'empty-revert', fork:'Osaka', code:[0x5f,0x5f,0xfd], gas:4, error:'revert', used:'4'},
  {name:'jump-to-boundary', fork:'Osaka', code:[0x60,0x03,0x56,0x5b,0x00], gas:12, stack:[], used:'12'},
  {name:'jump-boundary-one-gas-short', fork:'Osaka', code:[0x60,0x03,0x56,0x5b,0x00], gas:11, error:'out of gas', used:'11'}
];
const results = [];
for (const f of fixtures) {
  assert.ok(Hardfork[f.fork], `missing pinned fork ${f.fork}`);
  const common = new Common({chain:Mainnet, hardfork:Hardfork[f.fork], params:paramsEVM});
  const evm = await createEVM({common});
  const r = await evm.runCode({code:Uint8Array.from(f.code), gasLimit:BigInt(f.gas)});
  const error = r.exceptionError?.error ?? null;
  assert.equal(error, f.error ?? null, f.name);
  assert.equal(String(r.executionGasUsed), f.used, f.name);
  if (f.stack) assert.deepEqual(r.runState.stack.getStack().map(String), f.stack, f.name);
  assert.equal(r.returnValue.length, 0, f.name);
  results.push({name:f.name, fork:common.hardfork(), code:f.code, gasLimit:f.gas,
    executionGasUsed:String(r.executionGasUsed), error,
    stack:r.runState.stack.getStack().map(String), pass:true});
}
console.log(JSON.stringify({reference:'EthereumJS', evm:version('@ethereumjs/evm'), common:version('@ethereumjs/common'),
  boundary:'Hand-specified execution fixtures only. No source-compiler refinement or gas theorem. Strict decoder rejection of a truncated PUSH differs from runtime zero extension.',
  fixtures:results.length, results}, null, 2));
