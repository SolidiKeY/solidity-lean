#!/usr/bin/env node
/** Pinned-solc/EVM observations of ABI entry decoding (lane CF1).
 *
 * Usage:
 *   node scripts/abi-entry-probe.mjs SOLJSON_FILE NODE_MODULES_DIRECTORY [--fixtures] [--probes] [--access] [--aggregate] [--inherited] [--out FILE]
 *
 * `--fixtures` replays the retained Group 10 entry-decoding fixtures from the
 * verified upstream snapshot (`.lake/upstream/solidity`, see
 * `scripts/solidity-upstream.mjs verify`) with their exact calldata bytes.
 * `--access` runs `tests/abi-0.8.38/AccessEntry.sol` (lane FU2-C): when a calldata
 * element that fails only on access is read, encoded or copied.
 * `--aggregate` runs the calldata named-argument reverts of
 * `tests/upstream/AggregateErrorControls.sol` (lane FU2-C, the pins of
 * `tests/upstream/AggregateErrorControls.lean`).
 * `--inherited` checks `tests/abi-0.8.38/InheritedSelectors.sol` (inherited and
 * renamed function values) against its pinned selectors.
 * `--probes` runs `tests/abi-0.8.38/LazyEntry.sol`, whose vectors pin when
 * solc's generated decoder checks offsets, lengths and elements.
 * Every vector runs in four configurations: legacy and viaIR, each with the
 * optimizer off and on. The result per vector is the ordered observation
 * (success flag, return bytes or revert bytes). This is reference evidence for
 * `docs/feature-work/abi-hashes.md` ("Entry decoding: lazy and noncanonical
 * layouts"); it is not Lean coverage. Dependencies stay outside the package:
 * @ethereumjs/{vm,common,util} 10.1.3 and ethers 6.17.0.
 */
import assert from 'node:assert/strict';
import {readFileSync, writeFileSync, existsSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {resolve, join, dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
import {parseFixture, withPreamble, semanticVectors, runtimePipelines, COMPILER_SHA} from './solidity-upstream.mjs';

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const args = process.argv.slice(2);
const [compilerFile, modules] = args;
if (!compilerFile || !modules) throw new Error('expected compiler file and external node_modules directory');
const flag = f => args.includes(f);
const outIndex = args.indexOf('--out');
const outFile = outIndex >= 0 ? args[outIndex + 1] : null;
const sha = b => createHash('sha256').update(b).digest('hex');
assert.equal(sha(readFileSync(compilerFile)), COMPILER_SHA);
const require = createRequire(resolve(modules, 'reference.cjs'));
const {createVM} = require('@ethereumjs/vm');
const {Common, Mainnet, Hardfork} = require('@ethereumjs/common');
const {hexToBytes, bytesToHex, createAddressFromString} = require('@ethereumjs/util');
const {id} = require('ethers');
const solc = createRequire(import.meta.url)(resolve(compilerFile));
const compileRaw = solc.cwrap('solidity_compile', 'string', ['string', 'number', 'number']);

export const CONFIGS = [
  {name: 'legacy', viaIR: false, optimize: false},
  {name: 'legacy-opt', viaIR: false, optimize: true},
  {name: 'viaIR', viaIR: true, optimize: false},
  {name: 'viaIR-opt', viaIR: true, optimize: true},
];

function compile(sources, contract, mainSource, config) {
  const out = JSON.parse(compileRaw(JSON.stringify({language: 'Solidity', sources, settings: {
    viaIR: config.viaIR, evmVersion: 'osaka', optimizer: {enabled: config.optimize, runs: 200},
    outputSelection: {'*': {'*': ['abi', 'evm.bytecode.object']}}}}), 0, 0));
  const errors = (out.errors ?? []).filter(e => e.severity === 'error');
  if (errors.length) return {error: errors.map(e => e.formattedMessage).join('\n')};
  const c = out.contracts[mainSource][contract];
  return {abi: c.abi, bytecode: c.evm.bytecode.object};
}

const SENDER = createAddressFromString('0x1111111111111111111111111111111111111111');
async function deploy(bytecode) {
  const vm = await createVM({common: new Common({chain: Mainnet, hardfork: Hardfork.Osaka})});
  const r = await vm.evm.runCall({data: hexToBytes('0x' + bytecode), gasLimit: 30000000n, caller: SENDER});
  if (r.execResult.exceptionError) throw new Error('deployment failed: ' + r.execResult.exceptionError.error);
  return {vm, address: r.createdAddress};
}
async function call({vm, address}, data, value = 0n) {
  const r = await vm.evm.runCall({to: address, data, gasLimit: 30000000n, caller: SENDER, value});
  const failed = !!r.execResult.exceptionError;
  return {failed, data: bytesToHex(r.execResult.returnValue)};
}
const selector = signature => id(signature).slice(0, 10);
const hex = bytes => '0x' + Buffer.from(bytes).toString('hex');

/** Run one source in every configuration; `vectors` are {signature, calldata (hex, no selector)}. */
export async function observe(sources, mainSource, contract, vectors) {
  const results = {};
  for (const config of CONFIGS) {
    const compiled = compile(sources, contract, mainSource, config);
    if (compiled.error) { results[config.name] = {error: compiled.error}; continue; }
    const deployed = await deploy(compiled.bytecode);
    const observed = [];
    for (const v of vectors) {
      const data = hexToBytes(v.signature === '' ? v.calldata : selector(v.signature) + v.calldata.slice(2));
      observed.push({label: v.label ?? v.signature, ...(await call(deployed, data))});
    }
    results[config.name] = observed;
  }
  return results;
}

/** Agreement across configurations, as one line per vector. */
function summarize(results) {
  const names = Object.keys(results).filter(n => Array.isArray(results[n]));
  const base = results[names[0]];
  return base.map((o, i) => {
    const same = names.every(n => results[n][i].failed === o.failed && results[n][i].data === o.data);
    return {label: o.label, failed: o.failed, data: o.data, agree: same,
      ...(same ? {} : {perConfig: Object.fromEntries(names.map(n => [n, results[n][i]]))})};
  });
}

export const FIXTURES = [
  'abicoder/calldataDecoding/array/calldata_array_length_v2.sol',
  'abicoder/calldataDecoding/array/calldata_array_indexing_1d_2d_v2.sol',
  'abicoder/calldataDecoding/array/calldata_array_indexing_3d_v2.sol',
  'abicoder/calldataDecoding/array/calldata_nested_array_static_reencode_v2.sol',
  'abicoder/validation/array_exceeds_calldatasize_no_revert_string.sol',
  'array/calldata_array_bounds_check_nested_bytes.sol',
  'array/concat/bytes_concat_nested.sol',
  'array/copying/calldata_2d_bytes_to_memory_2.sol',
  'array/copying/nested_array_calldata_to_memory.sol',
  'smoke/bytes_and_strings.sol',
  'strings/concat/string_concat_nested.sol',
  'arithmetics/checked_add_v1.sol',
  'cleanup/cleanup_address_types_v1.sol',
  'cleanup/cleanup_bytes_types_v1.sol',
  'operators/shifts/shift_right_garbled_v1.sol',
  'operators/shifts/shift_right_garbled_signed_v1.sol',
  'operators/shifts/shift_right_negative_lvalue_signextend_int8_v1.sol',
  'operators/shifts/shift_right_negative_lvalue_signextend_int16_v1.sol',
  'operators/shifts/shift_right_negative_lvalue_signextend_int32_v1.sol',
  'userDefinedValueType/cleanup_abicoderv1.sol',
  'userDefinedValueType/conversion_abicoderv1.sol',
  'viaYul/function_entry_checks.sol',
];

async function fixtures() {
  const directory = join(ROOT, '.lake/upstream/solidity/test/libsolidity/semanticTests');
  if (!existsSync(directory)) throw new Error('run `node scripts/solidity-upstream.mjs verify` first');
  const report = [];
  for (const path of FIXTURES) {
    const text = readFileSync(join(directory, path), 'utf8');
    const fixture = parseFixture(text);
    const v1 = fixture.settings.ABIEncoderV1Only === 'true';
    const sources = Object.fromEntries([...fixture.sources].map(([n, s]) => [n, {content: withPreamble(s, v1)}]));
    const pipelines = runtimePipelines(fixture.settings);
    // The ABI, independent of pipeline, selects each vector's calldata bytes.
    const out = JSON.parse(compileRaw(JSON.stringify({language: 'Solidity', sources, settings: {
      evmVersion: 'osaka', outputSelection: {'*': {'*': ['abi'], '': ['ast']}}}}), 0, 0));
    const ast = out.sources[fixture.mainSource].ast;
    const contract = ast.nodes.filter(n => n.nodeType === 'ContractDefinition' && n.contractKind === 'contract' && !n.abstract).at(-1).name;
    let vectors;
    try { vectors = semanticVectors({...fixture, abiCoderV1: v1}, out.contracts[fixture.mainSource][contract].abi); }
    catch (e) { report.push({path, error: e.message}); continue; }
    const calls = vectors.map(v => {
      if (v.calldata) return {signature: v.signature, calldata: hex(v.calldata), expected: {failure: v.failure, bytes: hex(v.expectedBytes)}};
      // Scalar vectors: rebuild their words exactly as the fixture spells them.
      const words = v.args.map(a => a === 'true' ? 1n : a === 'false' ? 0n : BigInt.asUintN(256, BigInt(a)));
      return {signature: v.signature, calldata: '0x' + words.map(w => w.toString(16).padStart(64, '0')).join(''),
        expected: {failure: v.failure, values: v.expected}};
    }).filter(c => c.signature !== 'constructor');
    const results = await observe(sources, fixture.mainSource, contract, calls);
    const required = Object.keys(results).filter(n => pipelines.some(p => n.startsWith(p)));
    const restricted = Object.fromEntries(required.map(n => [n, results[n]]));
    const observations = summarize(restricted);
    // Every required configuration agrees, and agrees with the fixture.
    observations.forEach((o, i) => {
      const want = calls[i].expected;
      assert.equal(o.agree, true, `${path} ${o.label}: configurations disagree`);
      assert.equal(o.failed, want.failure, `${path} ${o.label}: failure`);
      if (want.bytes !== undefined) assert.equal(o.data, want.bytes, `${path} ${o.label}: bytes`);
      if (want.values !== undefined && !want.failure) assert.equal(o.data,
        '0x' + want.values.map(v => BigInt(v).toString(16).padStart(64, '0')).join(''), `${path} ${o.label}: values`);
    });
    report.push({path, requiredPipelines: pipelines, contract, calls, observations, configs: required});
  }
  return report;
}

async function probes(name = 'LazyEntry', source = `tests/abi-0.8.38/${name}.sol`) {
  const file = join(ROOT, source);
  const sources = {[`${name}.sol`]: {content: readFileSync(file, 'utf8')}};
  const spec = JSON.parse(readFileSync(join(ROOT, `tests/abi-0.8.38/${name}.vectors.json`), 'utf8'));
  const report = [];
  for (const group of spec.groups) {
    const results = await observe(sources, `${name}.sol`, group.contract, group.vectors);
    const summary = summarize(results);
    summary.forEach((o, i) => {
      const want = group.vectors[i].expect;
      // A vector whose outcome depends on the pipeline's operand order pins
      // each pipeline (both optimizer settings) separately.
      const byPipeline = group.vectors[i].expectByPipeline;
      if (byPipeline) for (const config of Object.keys(results)) {
        const w = byPipeline[config.startsWith('viaIR') ? 'viaIR' : 'legacy'];
        assert.equal(results[config][i].failed, w.failed, `${group.contract} ${o.label} ${config}: failure`);
        assert.equal(results[config][i].data, w.data, `${group.contract} ${o.label} ${config}: data`);
      }
      if (want) {
        assert.equal(o.agree, true, `${group.contract} ${o.label}: configurations disagree`);
        assert.equal(o.failed, want.failed, `${group.contract} ${o.label}: failure`);
        if (want.data !== undefined) assert.equal(o.data, want.data, `${group.contract} ${o.label}: data`);
      }
    });
    report.push({contract: group.contract, observations: summary});
  }
  return report;
}

/** Inherited and renamed function values (`tests/abi-0.8.38/InheritedSelectors.sol`):
 * every configuration returns the source declaration's selector and encoding. */
export const INHERITED = [
  ['baseSelector()', ['b3de648b' + '0'.repeat(56)]],
  ['derivedSelector()', ['b3de648b' + '0'.repeat(56)]],
  ['inheritedSelector()', ['05a0581e' + '0'.repeat(56)]],
  ['encodeOverrideHead()', ['ab088fbd' + '0'.repeat(56), 36n, 9n]],
  ['encodeInheritedHead()', ['05a0581e' + '0'.repeat(56), 36n, 1n]],
  ['valueSelector()', ['b3de648b' + '0'.repeat(56)]],
  ['inheritedValueSelector()', ['05a0581e' + '0'.repeat(56)]],
  ['encodeValue()', ['05a0581e' + '0'.repeat(56), 32n]],
  ['overloadCalls()', [3n, 1n]],
  ['superCall()', [4n]],
  ['callValue()', [1n]],
  ['callOwnValue()', [3n]],
];
async function inherited() {
  const file = join(ROOT, 'tests/abi-0.8.38/InheritedSelectors.sol');
  const results = await observe({'InheritedSelectors.sol': {content: readFileSync(file, 'utf8')}},
    'InheritedSelectors.sol', 'Derived', INHERITED.map(([signature]) => ({signature, calldata: '0x'})));
  const summary = summarize(results);
  summary.forEach((o, i) => {
    const words = INHERITED[i][1].map(w => typeof w === 'bigint' ? w.toString(16).padStart(64, '0') : w);
    assert.equal(o.agree, true, `${o.label}: configurations disagree`);
    assert.equal(o.failed, false, `${o.label}: failed`);
    assert.equal(o.data, '0x' + words.join(''), `${o.label}: data`);
  });
  return summary;
}

const output = {compilerSha256: COMPILER_SHA, configs: CONFIGS};
if (flag('--inherited')) output.inherited = await inherited();
if (flag('--fixtures')) output.fixtures = await fixtures();
if (flag('--probes')) output.probes = await probes();
if (flag('--access')) output.access = await probes('AccessEntry');
if (flag('--aggregate')) output.aggregate = await probes('AggregateCalldataErrors', 'tests/upstream/AggregateErrorControls.sol');
const text = JSON.stringify(output, null, 2) + '\n';
if (outFile) writeFileSync(outFile, text); else process.stdout.write(text);
