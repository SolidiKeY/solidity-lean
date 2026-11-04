/**
 * Assumption policy (docs/options.md O10) and target profile (O13) of the
 * public CLI. This mirrors `Solidity/Calculus/Assumptions.lean`: a record of
 * one reading per option (`Assumptions`), the records a proof entails
 * (`Assumptions.weakenings`: equal, or `tails=solc` weakened to `clean`), a
 * policy's acceptance (`Policy.allows`) and verdict (`Policy.verdict`): a row
 * is proved only when some record it entails is accepted, so a row that holds
 * only under a refused reading is reported `refused`, never `proved`.
 * The shared decision table is pinned on both sides
 * (`Solidity/Examples/Tactics/Assumptions.lean`, `solidity-lean.test.mjs`).
 */
import { existsSync, readFileSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');

/** Options and their readings, in `Assumptions`' field order. */
export const MODES = Object.freeze({
  callback: ['noCallback', 'withCallback'],
  overflow: ['default', 'checked', 'ignoring'],
  tails: ['solc', 'clean'],
  order: ['legacy', 'viaIR'],
  hash: ['opaque'],
  zeroAddress: ['noCode'],
});

/** `KEY=VALUE[,KEY=VALUE…]` into checked atoms `{key, value}`. */
export function parseAtoms(text, flag = '--require') {
  return text.split(',').map(part => {
    const match = /^([A-Za-z]+)=([A-Za-z]+)$/.exec(part.trim());
    if (!match) throw new Error(`${flag} needs KEY=VALUE, got: ${part}`);
    const [, key, value] = match;
    if (!Object.hasOwn(MODES, key)) throw new Error(`${flag}: unknown assumption ${key}; use one of ${Object.keys(MODES).join(', ')}`);
    if (!MODES[key].includes(value)) throw new Error(`${flag}: ${key} is one of ${MODES[key].join(', ')}, not ${value}`);
    return {key, value};
  });
}

const atomText = a => `${a.key}=${a.value}`;

/** A policy; two requirements on one option, or a required reading denied,
 * is an invalid invocation (no row could be admitted). */
export function policyOf(require = [], deny = []) {
  const required = {};
  for (const a of require) {
    if (required[a.key] !== undefined && required[a.key] !== a.value)
      throw new Error(`--require: ${a.key} required as both ${required[a.key]} and ${a.value}`);
    required[a.key] = a.value;
  }
  const denied = new Set(deny.map(atomText));
  for (const a of require) if (denied.has(atomText(a)))
    throw new Error(`${atomText(a)} is both required and denied`);
  return {require:[...new Set(require.map(atomText))], deny:[...denied], required, denied};
}

/** The record a runner row is stated under (`Frontend/Testing.lean`): a
 * calling-back obligation is `ValidT .noCallback`, a plain one `Fml.Valid`,
 * which is the same reading where nothing calls back (`validA_of_validTail`);
 * `reading` is its tail mode; the solc import elaborates legacy order with no
 * overflow block; hash and address 0 have one reading. */
export function rowAssumptions(row) {
  return {callback:'noCallback', overflow:'default', tails:row.reading === 'clean' ? 'clean' : 'solc',
    order:'legacy', hash:'opaque', zeroAddress:'noCode'};
}

/** `Assumptions.weakenings`. */
export function weakenings(a) {
  return a.tails === 'solc' ? [a, {...a, tails:'clean'}] : [a];
}

/** `Policy.allows`. */
export function allows(policy, a) {
  return Object.keys(MODES).every(key => !policy.denied.has(`${key}=${a[key]}`)
    && (policy.required[key] === undefined || policy.required[key] === a[key]));
}

/** `Policy.admits`, returning the accepted record (or null). */
export function admitted(policy, a) {
  return weakenings(a).find(b => allows(policy, b)) ?? null;
}

/** `Policy.verdict` on a row: a proved row stays proved under an accepted
 * record; otherwise it is `refused`, naming the readings refused. */
export function applyPolicy(row, policy) {
  const under = admitted(policy, row.assumptions);
  const refusedBy = [...new Set(weakenings(row.assumptions).flatMap(b => Object.keys(MODES)
    .filter(key => policy.denied.has(`${key}=${b[key]}`)
      || (policy.required[key] !== undefined && policy.required[key] !== b[key]))
    .map(key => `${key}=${b[key]}`)))];
  const result = {...row, policy: under ? {admitted:true, under} : {admitted:false, refused:refusedBy}};
  if (row.status !== 'proved' || under) return result;
  return {...result, status:'refused',
    reason:`holds only under refused assumptions: ${refusedBy.join(', ')}${row.reason ? `; ${row.reason}` : ''}`};
}

/** The compiler file solkey's build pins (`scripts/solc-ast.mjs` reads the
 * same `ext.soljsonFile`), as a version, or null when no checkout is found. */
export function pinnedSolc(options = {}, env = process.env) {
  const solkey = resolve(options.solkey ?? env.SOLKEY_ROOT ?? resolve(ROOT, '../solkey'));
  const gradle = resolve(solkey, 'keyext.solidity.core/build.gradle');
  if (!existsSync(gradle)) return null;
  const file = readFileSync(gradle, 'utf8').match(/ext\.soljsonFile\s*=\s*"soljson-v([^"]+)\.js"/)?.[1];
  return file ?? null;
}

/** The target profile (O13, `TargetProfile`): compiler, pipeline (which
 * selects the O9 order, here the rows' `legacy`) and EVM fork (Osaka, the
 * pinned and only one: `scripts/solc-ast.mjs`'s default `evmVersion`). */
export function targetProfile(options = {}, env = process.env) {
  return {solc:pinnedSolc(options, env), pipeline:'legacy', evmFork:'osaka'};
}
