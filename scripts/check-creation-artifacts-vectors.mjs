// External Osaka CREATE transactions, supplementing the component kernel proofs.
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createRequire} from 'node:module';
const req = createRequire(new URL('../tests/creation-artifacts/evm/package.json', import.meta.url));
const {Common, Mainnet, Hardfork} = req('@ethereumjs/common');
const {createVM, runTx} = req('@ethereumjs/vm');
const {createLegacyTx} = req('@ethereumjs/tx');
const {hexToBytes, bytesToHex, createAddressFromPrivateKey, createAccount} = req('@ethereumjs/util');
const fixtures = readFileSync(new URL('../tests/creation-artifacts/vectors.jsonl', import.meta.url), 'utf8').trim().split('\n').map(JSON.parse);
// Public deterministic fixture key, used only by this in-memory VM.
const key = hexToBytes('0x' + '46'.repeat(32));
let passed = 0;
for (const f of fixtures) {
  const common = new Common({chain: Mainnet, hardfork: Hardfork.Osaka});
  const vm = await createVM({common});
  const caller = createAddressFromPrivateKey(key);
  await vm.stateManager.putAccount(caller, createAccount({balance: 10n ** 30n}));
  const tx = createLegacyTx({nonce: 0n, gasPrice: 1000000000n, gasLimit: 1000000n,
    value: 0n, data: hexToBytes(f.payload)}, {common}).sign(key);
  const result = await runTx(vm, {tx});
  assert.equal(bytesToHex(result.execResult.returnValue), f.expected, f.name);
  if (f.reverts) {
    assert.equal(result.execResult.exceptionError?.error, 'revert', f.name);
    if (result.createdAddress) assert.equal((await vm.stateManager.getCode(result.createdAddress)).length, 0, f.name);
  } else {
    assert.equal(result.execResult.exceptionError, undefined, f.name);
    assert.ok(result.createdAddress, f.name);
    assert.equal(bytesToHex(await vm.stateManager.getCode(result.createdAddress)), f.expected, f.name);
  }
  console.log(`PASS ${f.name}: ${f.reverts ? 'exact revert' : 'installed runtime'} (${(f.expected.length - 2) / 2} bytes)`);
  passed++;
}
console.log(`Osaka creation vectors PASS: ${passed}/${fixtures.length}; EthereumJS 10.1.3; finite external tests, not pinned-EVM proofs.`);
