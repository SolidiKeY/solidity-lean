// Bounded real Prog.run vs native solc/runtime EVM differential backfill.
// Existing producer code and its assumptions remain unchanged.
import { readFileSync, writeFileSync, mkdirSync } from 'node:fs';
import { createRequire } from 'node:module';
import { createHash } from 'node:crypto';
import { execFileSync } from 'node:child_process';
import { resolve } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
const bulk = resolve(process.argv[2] ?? '');
const corpus = process.argv[3] ?? 'typed';
if (!['typed', 'boundary'].includes(corpus)) throw new Error('unknown admitted corpus');
const caseCount = corpus === 'typed' ? 160 : 480;
if (!process.argv[2]) throw new Error('usage: node typed.mjs H44_BULK');
const require = createRequire(resolve(bulk, 'reference/package.json'));
const load = async name => import(pathToFileURL(require.resolve(name)).href);
const { createVM } = await load('@ethereumjs/vm');
const { Common, Mainnet, Hardfork } = await load('@ethereumjs/common');
const { Account, createAddressFromString, hexToBytes, bytesToHex } = await load('@ethereumjs/util');
const { RLP } = await load('@ethereumjs/rlp');
const { Interface, keccak256 } = await load('ethers');
const hash = data => createHash('sha256').update(data).digest('hex');
const read = path => readFileSync(resolve(bulk, path));
const json = path => JSON.parse(read(path));
const write = (path, obj) => writeFileSync(resolve(bulk, path), JSON.stringify(obj, null, 2) + '\n');
const solc = resolve(bulk, 'upstream/solc');
if (hash(read('upstream/solc')) !== '65c3180a336eabb6bdc4bbd49cc405aeb233976964ae6c11fba2a6c8be8f3243') throw new Error('native solc checksum');
if (!execFileSync(solc, ['--version'], { encoding: 'utf8' }).split('\n').includes('Version: 0.8.38+commit.1835d247.Linux.g++')) throw new Error('native solc version');
const build = json('evidence/lean/results.json');
if (!build.complete || build.modules.some(row => row.exit !== 0 || row.stopped)) throw new Error('real producer fresh build incomplete');
const repo = resolve(fileURLToPath(new URL('../../../../', import.meta.url)));
for (const [name, expected] of Object.entries(json('evidence/producer-sources.json').source_sha256)) {
  if (hash(readFileSync(resolve(repo, name))) !== expected) throw new Error('producer source changed ' + name);
}
if (corpus === 'boundary') {
 const binding=json('evidence/boundary-generator.json');
 if(binding.driver !== 'tests/h62/item3/g52-differential/BoundaryWitness.lean' || binding.case_count !== 480 || binding.original_overlap !== 0 || binding.bounded_run.exit !== 0 || binding.bounded_run.stopped !== null) throw new Error('incomplete boundary producer receipt');
 if(hash(readFileSync(resolve(repo,binding.driver)))!==binding.driver_sha256 || hash(read('evidence/boundary-cases.jsonl'))!==binding.output_sha256) throw new Error('boundary generator binding mismatch');
}
const records = read(`evidence/${corpus}-cases.jsonl`).toString().trim().split('\n').map(JSON.parse);
if (records.length !== caseCount || records.some((r, i) => r.schema !== 1 || r.index !== i || r.seed !== 0) || new Set(records.map(r => r.source)).size !== caseCount) throw new Error('incomplete/duplicate typed enumeration');
const address = createAddressFromString('0x00000000000000000000000000000000000000c0');
const caller = createAddressFromString('0x00000000000000000000000000000000000000ee');
const wordHex = n => '0x' + BigInt(n).toString(16).padStart(64, '0');
const encodedWords = values => '0x' + values.map(n => wordHex(n).slice(2)).join('');
function encodedStore(values) {
  const result = {};
  values.forEach((n, i) => {
    if (BigInt(n) === 0n) return;
    let hex = BigInt(n).toString(16); if (hex.length % 2) hex = '0' + hex;
    result[keccak256(wordHex(i))] = bytesToHex(RLP.encode(hexToBytes('0x' + hex)));
  });
  return result;
}
const equal = (a, b) => JSON.stringify(a) === JSON.stringify(b);
const sameMap = (a, b) => equal(Object.entries(a).sort(), Object.entries(b).sort());
function fields(expected, actual) {
  const failed = [];
  for (const key of ['halt', 'output', 'logs', 'rollback']) if (!equal(expected[key], actual[key])) failed.push(key);
  if (!sameMap(expected.storage_full, actual.storage_full)) failed.push('storage_full');
  return failed;
}
const results = [];
for (const record of records) {
  if (record.expected.storage.length !== 2 || typeof record.expected.failed !== 'boolean' || !/^0x(?:[0-9a-f]{2})*$/.test(record.expected.revertData)) throw new Error('unadapted typed observation');
  const words = record.expected.storage.map((text, i) => {
    const match = new RegExp('^' + ['x', 'y'][i] + ' = (0|[1-9][0-9]*)$').exec(text);
    if (!match) throw new Error('unadapted storage shape'); return match[1];
  });
  const expected = { halt: record.expected.failed ? 'revert' : 'return',
    output: record.expected.failed ? record.expected.revertData : encodedWords(words),
    storage_full: encodedStore(words), logs: [], rollback: true };
  for (const viaIR of [false, true]) {
    const mode = viaIR ? 'via-ir' : 'legacy';
    const request = { language: 'Solidity', sources: { 'typed.sol': { content: record.source } }, settings: {
      viaIR, evmVersion: 'osaka', optimizer: { enabled: true, runs: 200 },
      metadata: { bytecodeHash: 'none' }, outputSelection: { '*': { '*': ['abi', 'evm.deployedBytecode.object'] } } } };
    const output = JSON.parse(execFileSync(solc, ['--standard-json'], { input: JSON.stringify(request), encoding: 'utf8', timeout: 60000, maxBuffer: 16 * 1024 * 1024 }));
    if ((output.errors ?? []).some(e => e.severity === 'error')) throw new Error('solc rejected typed record ' + record.index);
    const artifact = output.contracts['typed.sol'].Generated;
    const dir = resolve(bulk, `${corpus}-compiled`); mkdirSync(dir, { recursive: true });
    write(`${corpus}-compiled/${record.index}-${mode}.input.json`, request);
    write(`${corpus}-compiled/${record.index}-${mode}.json`, output);
    const vm = await createVM({ common: new Common({ chain: Mainnet, hardfork: Hardfork.Osaka }) });
    await vm.stateManager.putAccount(address, new Account());
    await vm.stateManager.putAccount(caller, new Account(0n, 10n ** 20n));
    await vm.stateManager.putCode(address, hexToBytes('0x' + artifact.evm.deployedBytecode.object));
    for (const [i, n] of [record.a, record.b].entries()) await vm.stateManager.putStorage(address, hexToBytes(wordHex(i)), hexToBytes(wordHex(n)));
    const before = await vm.stateManager.dumpStorage(address);
    const iface = new Interface(artifact.abi);
    const { execResult: r } = await vm.evm.runCall({ caller, to: address, data: hexToBytes(iface.encodeFunctionData('run', [])), gasLimit: 1000000n });
    const storage = await vm.stateManager.dumpStorage(address);
    const logs = (r.logs ?? []).map(([a, topics, data]) => ({ address: bytesToHex(a), topics: topics.map(bytesToHex), data: bytesToHex(data) }));
    const error = r.exceptionError?.error;
    const actual = { halt: error === undefined ? 'return' : error === 'revert' ? 'revert' : 'exception', output: bytesToHex(r.returnValue),
      storage_full: storage, logs, rollback: error === undefined || (sameMap(before, storage) && logs.length === 0),
      gas_used: r.executionGasUsed.toString(), gas_metric: 'message-execution-gas' };
    const mismatch = fields(expected, actual);
    results.push({ index: record.index, seed: record.seed, kind: record.kind, a: record.a, b: record.b, mode,
      source_sha256: hash(record.source), input_sha256: hash(JSON.stringify(request)),
      status: mismatch.length ? 'mismatch' : 'match', fields: mismatch, expected, actual,
      gas_status: 'unsupported-source-gas-free', deployment_status: 'not-executed-runtime-only' });
  }
}
// Controls remain separate from real observation counts.
const control = { halt: 'return', output: '0x', logs: [], rollback: true, storage_full: {} };
for (const [key, value] of [['halt', 'revert'], ['output', '0x01'], ['logs', [{}]], ['rollback', false], ['storage_full', { bad: 'value' }]]) {
  if (!fields(control, { ...control, [key]: value }).includes(key)) throw new Error('negative control failed ' + key);
}
const counts = {};
for (const row of results) counts[row.status] = (counts[row.status] ?? 0) + 1;
// Bounded minimization over real pre-executed producer records only, preserving family, pipeline and mismatch signature.
const minimized = results.filter(r => r.status === 'mismatch').map(row => {
  const candidates = results.filter(c => c.kind === row.kind && c.mode === row.mode && equal(c.fields, row.fields));
  candidates.sort((a, b) => (BigInt(a.a).toString(2).length + BigInt(a.b).toString(2).length) - (BigInt(b.a).toString(2).length + BigInt(b.b).toString(2).length) || a.index-b.index);
  return { original_index: row.index, candidate_index: candidates[0].index, mode: row.mode, fields: row.fields,
    scope: 'finite real-producer boundary pool; same family/pipeline/field signature; root cause unclassified', status: 'needs-owner-classification' };
});
const report = { schema: 1, scope: corpus + ': existing SolCases primitive-root fragment, seed 0', source_producer: 'Solidity.Tools.SolCases.emit -> Prog.run withPanics',
  producer_input_sha256: hash(read(`evidence/${corpus}-cases.jsonl`)), build_receipt_sha256: hash(read('evidence/lean/results.json')), producer_sources_sha256: hash(read('evidence/producer-sources.json')),
  native_solc_sha256: hash(read('upstream/solc')), reference_lock_sha256: hash(read('reference/package-lock.json')),
  fork: 'Osaka', counts, expected: caseCount * 2, full_g52_complete: false, results, minimized,
  limitations: ['gas-free source semantics: reference gas retained only', 'runtime bytecode only; no deployment/world or EEST execution', 'no source event constructs in admitted printer fragment', 'finite minimization does not classify root causes'] };
write(`evidence/${corpus}-differential.json`, report);
console.log(JSON.stringify({ scope: report.scope, counts, expected: caseCount * 2, full_g52_complete: false }));
