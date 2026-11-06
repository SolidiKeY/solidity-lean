#!/usr/bin/env node
/** Pinned-solc/EVM observations of enums nested in ABI types (lane FU2-D).
 *
 * Usage:
 *   node scripts/enum-abi-probe.mjs SOLJSON_FILE NODE_MODULES_DIRECTORY [--write]
 *
 * Runs `tests/abi-0.8.38/EnumArrays.sol` with the vectors of
 * `tests/abi-0.8.38/EnumArrays.vectors.json`, each sequence on a fresh
 * deployment, in four configurations (legacy and viaIR, optimizer off and
 * on), and checks every observation (success flag and return or revert bytes)
 * against the file's `expect`; `--write` records the observations instead.
 * Reference evidence for `docs/feature-work/abi-hashes.md` ("Enums nested in
 * ABI types"), not Lean coverage. Dependencies stay outside the package:
 * @ethereumjs/{vm,common,util} 10.1.3 and ethers 6.17.0, as
 * `scripts/abi-entry-probe.mjs`.
 */
import assert from 'node:assert/strict';
import {readFileSync, writeFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {resolve, join, dirname} from 'node:path';
import {fileURLToPath} from 'node:url';

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const COMPILER_SHA = '6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390';
const args = process.argv.slice(2);
const [compilerFile, modules] = args;
if (!compilerFile || !modules) throw new Error('expected compiler file and external node_modules directory');
const write = args.includes('--write');
assert.equal(createHash('sha256').update(readFileSync(compilerFile)).digest('hex'), COMPILER_SHA);
const require = createRequire(resolve(modules, 'reference.cjs'));
const {createVM} = require('@ethereumjs/vm');
const {Common, Mainnet, Hardfork} = require('@ethereumjs/common');
const {hexToBytes, bytesToHex, createAddressFromString} = require('@ethereumjs/util');
const {id, AbiCoder} = require('ethers');
const solc = createRequire(import.meta.url)(resolve(compilerFile));
const compileRaw = solc.cwrap('solidity_compile', 'string', ['string', 'number', 'number']);

const CONFIGS = [
  {name: 'legacy', viaIR: false, optimize: false},
  {name: 'legacy-opt', viaIR: false, optimize: true},
  {name: 'viaIR', viaIR: true, optimize: false},
  {name: 'viaIR-opt', viaIR: true, optimize: true},
];
const SENDER = createAddressFromString('0x1111111111111111111111111111111111111111');
const coder = AbiCoder.defaultAbiCoder();

function compile(source, contract, config) {
  const out = JSON.parse(compileRaw(JSON.stringify({language: 'Solidity',
    sources: {'EnumArrays.sol': {content: source}}, settings: {
      viaIR: config.viaIR, evmVersion: 'osaka', optimizer: {enabled: config.optimize, runs: 200},
      outputSelection: {'*': {'*': ['evm.bytecode.object']}}}}), 0, 0));
  const errors = (out.errors ?? []).filter(e => e.severity === 'error');
  if (errors.length) throw new Error(errors.map(e => e.formattedMessage).join('\n'));
  return out.contracts['EnumArrays.sol'][contract].evm.bytecode.object;
}

async function deploy(bytecode) {
  const vm = await createVM({common: new Common({chain: Mainnet, hardfork: Hardfork.Osaka})});
  const r = await vm.evm.runCall({data: hexToBytes('0x' + bytecode), gasLimit: 30000000n, caller: SENDER});
  if (r.execResult.exceptionError) throw new Error('deployment failed: ' + r.execResult.exceptionError.error);
  return {vm, address: r.createdAddress};
}

/** A call's calldata: the selector, then either `raw` (hex words, as
written) or the `args` encoded at the signature's parameter types. */
function calldata(v) {
  const sel = id(v.signature).slice(0, 10);
  if (v.raw !== undefined) return sel + v.raw.replace(/^0x/, '');
  const types = v.signature.slice(v.signature.indexOf('(') + 1, -1);
  const tys = types === '' ? [] : splitTypes(types);
  return sel + coder.encode(tys, v.args ?? []).slice(2);
}
function splitTypes(s) {
  const out = []; let depth = 0, cur = '';
  for (const c of s) {
    if (c === ',' && depth === 0) { out.push(cur); cur = ''; continue; }
    if (c === '(') depth++; if (c === ')') depth--;
    cur += c;
  }
  out.push(cur);
  return out;
}

const source = readFileSync(join(ROOT, 'tests/abi-0.8.38/EnumArrays.sol'), 'utf8');
const specFile = join(ROOT, 'tests/abi-0.8.38/EnumArrays.vectors.json');
const spec = JSON.parse(readFileSync(specFile, 'utf8'));
let failures = 0;
for (const seq of spec.sequences) {
  const perConfig = {};
  for (const config of CONFIGS) {
    const deployed = await deploy(compile(source, spec.contract, config));
    const observed = [];
    for (const v of seq.calls) {
      const r = await deployed.vm.evm.runCall({to: deployed.address, data: hexToBytes(calldata(v)),
        gasLimit: 30000000n, caller: SENDER});
      observed.push({failed: !!r.execResult.exceptionError, data: bytesToHex(r.execResult.returnValue)});
    }
    perConfig[config.name] = observed;
  }
  seq.calls.forEach((v, i) => {
    const obs = CONFIGS.map(c => perConfig[c.name][i]);
    const agree = obs.every(o => o.failed === obs[0].failed && o.data === obs[0].data);
    if (!agree) { failures++; console.log(`disagree: ${seq.label} / ${v.label}`, perConfig); }
    if (write) v.expect = obs[0];
    else if (v.expect.failed !== obs[0].failed || v.expect.data !== obs[0].data) {
      failures++;
      console.log(`mismatch: ${seq.label} / ${v.label}: expected ${JSON.stringify(v.expect)}, observed ${JSON.stringify(obs[0])}`);
    } else console.log(`ok: ${seq.label} / ${v.label}: ${obs[0].failed ? 'revert' : 'return'} ${obs[0].data}`);
  });
}
if (write) writeFileSync(specFile, JSON.stringify(spec, null, 1) + '\n');
if (failures) { console.log(`${failures} failure(s)`); process.exit(1); }
console.log(write ? 'recorded' : 'all vectors agree in four configurations');
