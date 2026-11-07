// Pinned EEST Osaka reference conformance. No source-semantics pass is inferred.
import { executeBlockchain } from './blockchain_adapter.mjs';
import { classifyRejection } from './eest_rejection.mjs';
import { comparePost, validateConfig, guardedResult } from './eest_observation.mjs';
import { createReadStream, readFileSync, createWriteStream, writeFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { createGunzip } from 'node:zlib';
import { createInterface } from 'node:readline';
import { createRequire } from 'node:module';
import { fork } from 'node:child_process';
import { resolve, dirname } from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
const workerMode = process.argv[2] === '--worker';
const bulk = resolve(process.argv[workerMode ? 3 : 2] ?? '');
if (!process.argv[workerMode ? 3 : 2]) throw new Error('usage: node eest_reference.mjs H44_BULK [LIMIT] [LABEL]');
const json = path => JSON.parse(readFileSync(resolve(bulk, path), 'utf8'));
async function digest(path) {
  const hash = createHash('sha256');
  for await (const data of createReadStream(resolve(bulk, path))) hash.update(data);
  return hash.digest('hex');
}
let modules;
let activeBudget;
async function execute(record) {
  const blockchainInput = record.fixture !== undefined;
  const expected = blockchainInput ? {} : { state_root: record.post.hash, logs_hash: record.post.logs };
  if (!validateConfig(blockchainInput ? record.fixture.config : record.config)) return { status: 'unsupported', reason: 'unsupported-fork-configuration', expected };
  if (!modules) {
    const require = createRequire(resolve(bulk, 'reference/package.json'));
    const load = name => import(pathToFileURL(require.resolve(name)).href);
    // EthereumJS CJS dependencies and the ESM KZG library share noble modules;
    // their initial loads must be serial to avoid Node's ESM/CJS loader race.
    const loaded = [];
    for (const name of ['@ethereumjs/vm', '@ethereumjs/common', '@ethereumjs/util',
      '@ethereumjs/tx', '@ethereumjs/block', '@ethereumjs/rlp', 'ethers',
      'micro-eth-signer/kzg.js', '@paulmillr/trusted-setups/fast-peerdas.js', '@ethereumjs/blockchain']) loaded.push(await load(name));
    const [vm, common, util, tx, block, rlp, ethers, kzgLibrary, setup, blockchain] = loaded;
    // Count calls to the unchanged executor. The engine's optional step-event
    // tracer reads REVERT memory before gas checks and can allocate huge arrays.
    // This budget wrapper changes no opcode implementation or successful result.
    const { Interpreter } = await import(pathToFileURL(resolve(dirname(require.resolve('@ethereumjs/evm')), 'interpreter.js')).href);
    const originalRunStep = Interpreter.prototype.runStep;
    if (typeof originalRunStep !== 'function') throw new Error('unsupported reference instruction budget API');
    Interpreter.prototype.runStep = async function (...args) {
      if (activeBudget && ++activeBudget.steps > 5000000) throw new Error('H44_HOST_STEP_LIMIT');
      return Reflect.apply(originalRunStep, this, args);
    };
    modules = { ...blockchain, ...vm, ...common, ...util, ...tx, ...block, RLP: rlp.RLP, keccak256: ethers.keccak256, kzg: new kzgLibrary.KZG(setup.trustedSetup) };
  }
  if (blockchainInput) {
    activeBudget = { steps: 0 };
    return executeBlockchain(record, modules, activeBudget);
  }
  const { createVM, runTx, Common, Mainnet, Hardfork, Account, createAddressFromString,
          hexToBytes, bytesToHex, createTxFromRLP, createBlock, RLP, keccak256, kzg } = modules;
  const common = new Common({ chain: Mainnet, hardfork: Hardfork.Osaka, customCrypto: { kzg } });
  const word = n => hexToBytes('0x' + BigInt(n).toString(16).padStart(64, '0'));
  const hashes = record.env.blockHashes ?? {};
  const blockchain = { getBlock: async number => ({ hash: () => word(hashes[String(number)] ?? hashes['0x'+BigInt(number).toString(16)] ?? 0) }), shallowCopy() { return this; } };
  const vm = await createVM({ common, blockchain });
  if (vm.evm.DEBUG) throw new Error('reference DEBUG tracer must be disabled');
  activeBudget = { steps: 0 };
  for (const [address, value] of Object.entries(record.pre)) {
    const a = createAddressFromString(address);
    await vm.stateManager.putAccount(a, new Account(BigInt(value.nonce), BigInt(value.balance)));
    if (value.code !== '0x') await vm.stateManager.putCode(a, hexToBytes(value.code));
    for (const [slot, contents] of Object.entries(value.storage)) await vm.stateManager.putStorage(a, word(slot), word(contents));
  }
  const e = record.env;
  const block = createBlock({ header: { number: BigInt(e.currentNumber), timestamp: BigInt(e.currentTimestamp),
    gasLimit: BigInt(e.currentGasLimit), coinbase: e.currentCoinbase, difficulty: 0n,
    mixHash: word(e.currentRandom ?? 0), baseFeePerGas: BigInt(e.currentBaseFee ?? 0),
    excessBlobGas: BigInt(e.currentExcessBlobGas ?? 0), blobGasUsed: 0n,
    parentBeaconBlockRoot: word(e.parentBeaconBlockRoot ?? 0) } }, { common });
  const beforeRoot = bytesToHex(await vm.stateManager.getStateRoot());
  let result; let tx;
  try {
    tx = createTxFromRLP(hexToBytes(record.post.txbytes), { common });
    result = await runTx(vm, { tx, block });
  } catch (error) {
    if (!record.post.expectException) throw error;
    const facts = { transactionType: Number.parseInt(record.post.txbytes.slice(2,4),16) };
    if (tx && error.message.startsWith('INTRINSIC_GAS_TOO_LOW:')) {
      facts.gasLimit = tx.gasLimit.toString(); facts.intrinsicGas = tx.getIntrinsicGas().toString();
      facts.floorGas = modules.getCalldataFloorGas(tx, tx.getSenderAddress()).toString();
    }
    const afterRoot = bytesToHex(await vm.stateManager.getStateRoot());
    const classified = classifyRejection(record.post.expectException, error.message, facts, beforeRoot,
      afterRoot, record.post.hash, record.post.logs, keccak256(RLP.encode([])));
    return { ...classified, expected_exception: record.post.expectException, engine_reason: error.message,
      validation_facts: facts, observed: { state_root: afterRoot, before_state_root: beforeRoot, logs_hash: keccak256(RLP.encode([])) }, expected };

  }
  if (record.post.expectException) return { status: 'reference_mismatch', fields: ['transaction_admission'],
    reason: 'expected-invalid transaction accepted', expected_exception: record.post.expectException, expected };

  const observed = { state_root: bytesToHex(await vm.stateManager.getStateRoot()),
    logs_hash: keccak256(RLP.encode(result.execResult.logs ?? [])),
    output: bytesToHex(result.execResult.returnValue), execution_exception: result.execResult.exceptionError?.error ?? null,
    total_gas_spent: result.totalGasSpent.toString(), execution_gas_used: result.execResult.executionGasUsed.toString(),
    logs: (result.execResult.logs ?? []).map(([a, topics, data]) => ({ address: bytesToHex(a), topics: topics.map(bytesToHex), data: bytesToHex(data) })), steps: activeBudget.steps };
  const fields = comparePost(expected, observed);
  return { status: fields.length ? 'reference_mismatch' : 'reference_match', fields, expected, observed,
    observation_limits: ['fixture has no direct return/revert byte expectation or independent gas-used expectation', 'source executable semantics not connected'] };
}
if (workerMode) {
  process.on('message', async record => {
    try { process.send(await execute(record)); }
    catch (error) { process.send({ status: error.message.includes('H44_HOST_STEP_LIMIT') ? 'unsupported' : 'engine_error', reason: error.message.slice(0, 3000), stack: error.stack?.slice(0, 5000), last_steps: error.last_steps }); }
  });
} else {
  const limit = process.argv[3] === undefined ? Infinity : Number(process.argv[3]);
  const label = process.argv[4] ?? 'full';
  const only = (process.argv[5] === undefined || process.argv[5] === 'all') ? null : Number(process.argv[5]);
  if (only !== null && (!Number.isInteger(only) || only < 0)) throw new Error('invalid index');
  const invalidOnly = process.argv[6] === 'invalid-only';
  const format = process.argv[7] ?? 'state_test';
  if (!['state_test','blockchain_test'].includes(format) ) throw new Error('unsupported input format/filter');
  const blockchainInput = format === 'blockchain_test';
  const receiptPath = blockchainInput ? 'evidence/blockchain-export.json' : 'evidence/eest-export.json';
  const censusPath = blockchainInput ? 'evidence/archive-census.json' : 'evidence/eest-census.json';
  const streamPath = blockchainInput ? 'blockchain-inputs.jsonl.gz' : 'eest-inputs.jsonl.gz';
  const mem = readFileSync('/proc/meminfo', 'utf8');
  if (Number(/^SwapTotal:\s+(\d+)/m.exec(mem)[1]) !== 0) throw new Error('no-swap prerequisite');
  if (!(limit > 0) || !/^[a-z0-9-]+$/.test(label)) throw new Error('invalid limit/label');
  const receipt = json(receiptPath);
  if (receipt.archive_sha256 !== '5dd08fee0fb41bc2a59bc4ab1dc75b19723fc71fe6af2f855454d3283fba09b9' ||
      receipt.stream_sha256 !== await digest(streamPath) ||
      receipt.census_sha256 !== await digest(censusPath)) throw new Error('export provenance binding mismatch');
  const census = json(censusPath);
  if (blockchainInput) {
    if(census.inventory_sha256 !== await digest('archive-inventory.jsonl.gz')) throw new Error('inventory binding mismatch');
    census.cases=[];
    const inventory=createInterface({input:createReadStream(resolve(bulk,'archive-inventory.jsonl.gz')).pipe(createGunzip()),crlfDelay:Infinity});
    for await(const line of inventory) {const row=JSON.parse(line);if(row.role==='fixture' && row.format===format && row.selection==='exact-osaka')census.cases.push({...row,variant:0});}
  }
  if (receipt.cases !== census.cases.length || only >= receipt.cases) throw new Error('census count/index binding');
  const lockDigest = await digest('reference/package-lock.json');
  const stream = createReadStream(resolve(bulk, streamPath)).pipe(createGunzip());
  const lines = createInterface({ input: stream, crlfDelay: Infinity });
  const output = createWriteStream(resolve(bulk, `evidence/eest-reference-${label}.jsonl`));
  let child; let peakAggregateRss = 0;
  function start() { child = fork(fileURLToPath(import.meta.url), ['--worker', bulk], { execArgv: ['--max-old-space-size=4096'], stdio: ['ignore', 'ignore', 'inherit', 'ipc'] }); }
  function one(record) {
    if (!child) start();
    return new Promise(resolveResult => {
      const current = child;
      let finished = false; let stopReason;
      const finish = result => {
        if (finished) return; finished = true; clearTimeout(timer); clearInterval(guard);
        current.removeListener('message', onMessage); current.removeListener('exit', onExit); current.removeListener('error', onError);
        resolveResult(result);
      };
      const onMessage = result => {
        // A requested kill must finish through onExit, which resets child.
        if (stopReason) return;
        finish(guardedResult(result, stopReason));
      };
      const onExit = (code, signal) => { child = undefined; finish({ status: 'unsupported', reason: stopReason ?? `worker-exit:${code}:${signal}` }); };
      const onError = error => { child = undefined; finish({ status: 'engine_error', reason: error.message }); };
      const timer = setTimeout(() => { stopReason = 'host-timeout-60000ms'; current.kill('SIGKILL'); }, 60000);
      const guard = setInterval(() => {
        try {
          const rss = [process.pid, current.pid].reduce((sum, pid) => sum + Number(/^VmRSS:\s+(\d+)/m.exec(readFileSync(`/proc/${pid}/status`, 'utf8'))?.[1] ?? 0)*1024, 0);
          peakAggregateRss = Math.max(peakAggregateRss, rss);
          const available = Number(/^MemAvailable:\s+(\d+)/m.exec(readFileSync('/proc/meminfo', 'utf8'))[1])*1024;
          if (rss > 12*1024**3 || available < 4*1024**3) { stopReason = 'host-memory-guard'; current.kill('SIGKILL'); }
        } catch (error) { if (error.code !== 'ENOENT') { stopReason = 'host-resource-monitor-error'; current.kill('SIGKILL'); } }
      }, 500);
      current.once('message', onMessage); current.once('exit', onExit); current.once('error', onError); current.send(record);
    });
  }
  const counts = {};
  const seen = new Set();
  const started = Date.now();
  for await (const line of lines) {
    if (seen.size >= limit) break;
    const record = JSON.parse(line);
    if (only !== null && record.index !== only) continue;
    if (invalidOnly && !(blockchainInput ? record.fixture.blocks.some(b=>b.expectException||b.expectExceptionALL) : record.post.expectException)) continue;
    const original = census.cases[record.index];
    if (!original || original.path !== record.path || original.case !== record.case || original.variant !== record.variant || (!blockchainInput && original.sha256 !== record.fixture_sha256)) throw new Error('fixture identity mismatch');
    if (!Number.isInteger(record.index) || seen.has(record.index)) throw new Error('duplicate/invalid fixture index');
    seen.add(record.index);
    const result = await one(record);
    counts[result.status] = (counts[result.status] ?? 0) + 1;
    const row = { index: record.index, path: record.path, case: record.case, variant: record.variant,
      fixture_sha256: record.fixture_sha256, fork: 'Osaka', engine: '@ethereumjs/vm@10.1.3',
      source_semantics: 'unsupported-adapter-pending', ...result };
    if (!output.write(JSON.stringify(row)+'\n')) await new Promise(resolveDrain => output.once('drain', resolveDrain));
    if (seen.size % 100 === 0) console.log(JSON.stringify({ cases: seen.size, counts, seconds: (Date.now()-started)/1000 }));
  }
  lines.close(); stream.destroy(); if (child) await new Promise(done => { child.once('exit', done); child.kill(); });
  await new Promise(done => output.end(done));
  const summary = { expected: receipt.cases, selected: seen.size, unselected: receipt.cases-seen.size, counts,
    reference_complete: seen.size === receipt.cases && counts.reference_match === receipt.cases,
    differential_complete: false, source_semantics_unsupported: receipt.cases,
    export_sha256: await digest(receiptPath), reference_lock_sha256: lockDigest,
    seconds: (Date.now()-started)/1000, label, format, peak_aggregate_rss: peakAggregateRss,
    adapter_sha256: createHash('sha256').update(readFileSync(fileURLToPath(import.meta.url))).digest('hex'),
    instruction_budget: '5000000 original Interpreter.runStep calls; forwarding wrapper; optional step-event tracer disabled',
    rejection_adapter_sha256: await digest(resolve(dirname(fileURLToPath(import.meta.url)),'eest_rejection.mjs')),
    blockchain_adapter_sha256: blockchainInput ? createHash('sha256').update(readFileSync(new URL('./blockchain_adapter.mjs',import.meta.url))).digest('hex') : null,
    reference_provider: blockchainInput ? '@ethereumjs/blockchain@10.1.3' : null,
    blockhash_convention: blockchainInput ? 'real validated fixture genesis/history provider; constant Osaka from genesis' : 'state-test absent history returns zero; all pinned envs omit blockHashes' };
  writeFileSync(resolve(bulk, `evidence/eest-reference-${label}-summary.json`), JSON.stringify(summary, null, 2)+'\n');
  console.log(JSON.stringify(summary));
  if (counts.reference_mismatch || counts.engine_error) process.exitCode = 1;
  else if (!summary.reference_complete) process.exitCode = 2;
}
