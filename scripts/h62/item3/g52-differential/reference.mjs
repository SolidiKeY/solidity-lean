// Independent EVM evidence only. Always run a full message checkpoint, not runCode.
import { readFileSync, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { createRequire } from 'node:module';
import { resolve } from 'node:path';
import { pathToFileURL } from 'node:url';
const bulk = resolve(process.argv[2] ?? '');
if (!process.argv[2]) throw new Error('usage: node reference.mjs ABSOLUTE_H44_BULK');
const require = createRequire(resolve(bulk, 'reference/package.json'));
const load = async name => import(pathToFileURL(require.resolve(name)).href);
const { createVM } = await load('@ethereumjs/vm');
const { Common, Mainnet, Hardfork } = await load('@ethereumjs/common');
const { Account, createAddressFromString, hexToBytes, bytesToHex } = await load('@ethereumjs/util');
const { Interface } = await load('ethers');
const json = path => JSON.parse(readFileSync(resolve(bulk, path), 'utf8'));
// Refuse an unpinned direct dependency, even if module resolution succeeds.
for (const [name, version] of Object.entries(json('reference/package.json').dependencies)) {
  const lock = json('reference/package-lock.json').packages['node_modules/' + name];
  if (lock?.version !== version || !lock.integrity) throw new Error('unpinned reference dependency ' + name);
}
const digest = path => createHash('sha256').update(readFileSync(resolve(bulk, path))).digest('hex');
const receipt = json('evidence/compiler.json');
if (receipt.input_sha256 !== digest('generated/cases.json')) throw new Error('compiler cases binding mismatch');
if (Object.keys(receipt.artifacts ?? {}).length !== 192) throw new Error('incomplete compiler artifact binding');
for (const [path, expected] of Object.entries(receipt.artifacts)) {
  if (digest(path) !== expected) throw new Error('compiler artifact hash mismatch ' + path);
}
const cases = json('generated/cases.json').cases;
const results = {};
const address = createAddressFromString('0x00000000000000000000000000000000000000c0');
const caller = createAddressFromString('0x00000000000000000000000000000000000000ee');
const word = n => hexToBytes('0x' + BigInt(n).toString(16).padStart(64, '0'));
for (const mode of ['legacy', 'via-ir']) {
  for (const c of cases) {
    const compiled = json(`compiled/${mode}/${c.source}.json`).contracts[c.source].C;
    const vm = await createVM({ common: new Common({ chain: Mainnet, hardfork: Hardfork.Osaka }) });
    await vm.stateManager.putAccount(address, new Account());
    await vm.stateManager.putAccount(caller, new Account(0n, 10n ** 20n));
    await vm.stateManager.putCode(address, hexToBytes('0x' + compiled.evm.deployedBytecode.object));
    for (const [key, value] of Object.entries(c.initial_storage)) {
      await vm.stateManager.putStorage(address, word(key), word(value));
    }
    const storageBefore = await vm.stateManager.dumpStorage(address);
    const balanceBefore = (await vm.stateManager.getAccount(address)).balance;
    const iface = new Interface(compiled.abi);
    const call = await vm.evm.runCall({ caller, to: address,
      data: hexToBytes(iface.encodeFunctionData('f', [BigInt(c.x)])), gasLimit: BigInt(c.gas_limit) });
    const result = call.execResult;
    const error = result.exceptionError?.error;
    const storage = {};
    for (const key of Object.keys(c.initial_storage)) {
      const raw = bytesToHex(await vm.stateManager.getStorage(address, word(key)));
      storage[key] = BigInt(raw === '0x' ? '0x0' : raw).toString();
    }
    const logs = (result.logs ?? []).map(([a, topics, data]) => ({
      address: bytesToHex(a), topics: topics.map(bytesToHex), data: bytesToHex(data) }));
    const storageFull = await vm.stateManager.dumpStorage(address);
    const balanceAfter = (await vm.stateManager.getAccount(address)).balance;
    const rollback = error === undefined || (JSON.stringify(storageFull) === JSON.stringify(storageBefore) && balanceBefore === balanceAfter && logs.length === 0);
    results[`${mode}:${c.id}`] = { status: 'executed', fork: 'Osaka',
      halt: error === undefined ? 'return' : error === 'revert' ? 'revert' : 'exception',
      output: bytesToHex(result.returnValue), storage, storage_full: storageFull, logs, rollback,
      gas_metric: 'message-execution-gas', gas_used: result.executionGasUsed.toString(),
      engine: '@ethereumjs/vm@10.1.3', exception: error ?? null };
  }
}
writeFileSync(resolve(bulk, 'evidence/reference.json'), JSON.stringify({
  role: 'reference', producer: '@ethereumjs/vm@10.1.3',
  input_sha256: digest('generated/cases.json'), compiler_sha256: digest('evidence/compiler.json'), results
}, null, 2) + '\n');
const counts = {};
for (const row of Object.values(results)) counts[row.halt] = (counts[row.halt] ?? 0) + 1;
console.log(JSON.stringify({ engine: '@ethereumjs/vm@10.1.3', fork: 'Osaka', cases: Object.keys(results).length, counts }));
