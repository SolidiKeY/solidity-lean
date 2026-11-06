#!/usr/bin/env node
// Evidence for the Source readback of dirty narrow/bool locals (user decision
// H109, 2026-11-06): what pinned solc 0.8.38 does, in each pipeline, when a
// memory-safe assembly block leaves a dirty word in a `uintN`, `intN` or
// `bool` local that Solidity code reads afterwards. Reference execution only
// (`@ethereumjs/evm`, Osaka, optimizer off); it is not a Lean proof.
//
// Usage: node scripts/evm-reference/dirty-locals.mjs --compiler FILE --out FILE
import {readFileSync, writeFileSync} from 'node:fs';
import {resolve} from 'node:path';
import {createRequire} from 'node:module';
import {createHash} from 'node:crypto';
import {createAddressFromString, hexToBytes, bytesToHex} from '@ethereumjs/util';
import {machine} from './replay.mjs';
import {COMPILER_SHA} from '../solidity-upstream.mjs';

const VERSION = '0.8.38+commit.1835d247.Emscripten.clang';
const sha = b => createHash('sha256').update(b).digest('hex');

// Each probe writes `dirty` into a local of type `ty` in assembly, then reads
// it through `read`; the function returns uint256/int256/bool as stated.
export const PROBES = [
  {name: 'u8_widen', ty: 'uint8', dirty: '0x1ff', ret: 'uint256', read: 'r = x;'},
  {name: 'u8_add', ty: 'uint8', dirty: '0x1ff', ret: 'uint256', read: 'r = uint256(x) + 0;'},
  {name: 'u8_eq', ty: 'uint8', dirty: '0x1ff', ret: 'bool', read: 'r = (x == 0xff);'},
  {name: 'u8_ret', ty: 'uint8', dirty: '0x1ff', ret: 'uint8', read: 'r = x;'},
  {name: 'u16_widen', ty: 'uint16', dirty: '0xabcd1234', ret: 'uint256', read: 'r = x;'},
  {name: 'i8_widen_neg', ty: 'int8', dirty: '0x80', ret: 'int256', read: 'r = x;'},
  {name: 'i8_widen_pos', ty: 'int8', dirty: '0x17f', ret: 'int256', read: 'r = x;'},
  {name: 'i8_lt', ty: 'int8', dirty: '0xff', ret: 'bool', read: 'r = (x < 0);'},
  {name: 'i8_ret', ty: 'int8', dirty: '0x1ff', ret: 'int8', read: 'r = x;'},
  {name: 'b_cond', ty: 'bool', dirty: '2', ret: 'uint256', read: 'r = x ? 1 : 0;'},
  {name: 'b_eq_true', ty: 'bool', dirty: '2', ret: 'bool', read: 'r = (x == true);'},
  {name: 'b_not', ty: 'bool', dirty: '2', ret: 'bool', read: 'r = !x;'},
  {name: 'b_ret', ty: 'bool', dirty: '2', ret: 'bool', read: 'r = x;'},
  {name: 'b_widen', ty: 'bool', dirty: '2', ret: 'uint256', read: 'r = x ? 7 : 9;'},
];

export function source() {
  const fns = PROBES.map(p =>
    `  function ${p.name}() external pure returns (${p.ret} r) { ${p.ty} x; ` +
    `assembly ("memory-safe") { x := ${p.dirty} } ${p.read} }`).join('\n');
  return `// SPDX-License-Identifier: GPL-3.0\npragma solidity 0.8.38;\ncontract Dirty {\n${fns}\n}\n`;
}

const selector = (keccak, sig) => keccak(sig).slice(0, 10);

async function run(compile, pipeline) {
  const input = {language: 'Solidity', sources: {'dirty.sol': {content: source()}},
    settings: {optimizer: {enabled: false}, viaIR: pipeline === 'viaIR', evmVersion: 'osaka',
      metadata: {appendCBOR: false},
      outputSelection: {'*': {'*': ['evm.bytecode.object', 'evm.methodIdentifiers']}}}};
  const out = JSON.parse(compile(JSON.stringify(input), 0, 0));
  const errors = (out.errors ?? []).filter(e => e.severity === 'error');
  if (errors.length) throw new Error(errors.map(e => e.formattedMessage).join('\n'));
  const c = out.contracts['dirty.sol'].Dirty;
  const vm = await machine();
  const created = await vm.call({data: hexToBytes('0x' + c.evm.bytecode.object)});
  const to = created.result.createdAddress;
  const results = {};
  for (const p of PROBES) {
    const sig = Object.keys(c.evm.methodIdentifiers).find(s => s.startsWith(p.name + '('));
    const {result} = await vm.call({to, data: hexToBytes('0x' + c.evm.methodIdentifiers[sig])});
    results[p.name] = {failed: !!result.execResult.exceptionError,
      returnData: bytesToHex(result.execResult.returnValue)};
  }
  return {pipeline, creationSha256: sha(c.evm.bytecode.object), results};
}

async function main(args) {
  const opt = {};
  for (let i = 0; i < args.length; i += 2) opt[args[i].slice(2)] = args[i + 1];
  if (!opt.compiler || !opt.out) throw new Error('usage: dirty-locals.mjs --compiler FILE --out FILE');
  const bytes = readFileSync(opt.compiler);
  if (sha(bytes) !== COMPILER_SHA) throw new Error('compiler SHA mismatch');
  const solc = createRequire(import.meta.url)(resolve(opt.compiler));
  if (solc.cwrap('solidity_version', 'string', [])() !== VERSION) throw new Error('compiler version mismatch');
  const compile = solc.cwrap('solidity_compile', 'string', ['string', 'number', 'number']);
  const report = {version: 1, compiler: VERSION, compilerSha256: COMPILER_SHA,
    sourceSha256: sha(source()), source: source(), probes: PROBES,
    pipelines: [await run(compile, 'legacy'), await run(compile, 'viaIR')]};
  writeFileSync(opt.out, JSON.stringify(report, null, 2) + '\n');
}

if (import.meta.url === `file://${process.argv[1]}`) await main(process.argv.slice(2));
