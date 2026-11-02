#!/usr/bin/env node
// Owned structural guard for original C77/C78 claims; Lean checks the proofs.
import { readFileSync } from 'node:fs';
import { createHash } from 'node:crypto';
import { resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { blankLean } from './check-trust.mjs';
import { pins, STANDARD } from './check-axiom-pins.mjs';
export function statements(text) {
  const code = blankLean(text), found = {};
  for (const match of code.matchAll(/^theorem\s+(\w+)\b/gmu)) {
    const end = /:=\s*by\b/u.exec(code.slice(match.index));
    if (!end) throw new Error(`Missing proof boundary: ${match[1]}`);
    const statement = code.slice(match.index, match.index + end.index).replace(/\s+/gu, ' ').trim();
    found[match[1]] = createHash('sha256').update(statement).digest('hex');
  }
  return found;
}
export function check(sources, registry) {
  const errors = [];
  for (const [file, expected] of Object.entries(registry.files)) {
    const text = sources[file];
    if (typeof text !== 'string') { errors.push(`${file}: missing source`); continue; }
    const actual = statements(text);
    if (Object.keys(actual).sort().join() !== Object.keys(expected).sort().join()) errors.push(`${file}: declaration set drift`);
    for (const [name, row] of Object.entries(expected)) if (actual[name] !== row.sha256) errors.push(`${file}:${name}: statement/observation drift`);
    const guarded = pins(text);
    if (guarded.map(p => p.target).sort().join() !== Object.keys(expected).sort().join()) errors.push(`${file}: axiom target multiset drift`);
    for (const row of guarded) {
      if (!Object.hasOwn(expected, row.target)) errors.push(`${file}: unexpected pin ${row.target}`);
      else {
        const old = expected[row.target];
        if (row.name !== old.pinName || JSON.stringify(row.axioms) !== JSON.stringify(old.axioms)) errors.push(`${file}:${row.target}: exact axiom pin drift`);
      }
      if (row.axioms === null || row.axioms.some(x => !STANDARD.includes(x))) errors.push(`${file}: unsafe/unparsed axiom guard`);
    }
    const code = blankLean(text);
    if (/\b(sorry|admit|native_decide|implemented_by)\b/u.test(code) || /^\s*(axiom|opaque)\b/mu.test(code)) errors.push(`${file}: proof trust shortcut`);
    if (/\bset_option\s+(maxHeartbeats|maxRecDepth)\b/u.test(code)) errors.push(`${file}: proof budget change`);
  }
  const app = sources['Solidity/Backend/MemoryOps/DisjointSnapshotPathApplications.lean'] ?? '';
  if ((blankLean(app).match(/\brunCaptures_disjoint_path\b/gu) ?? []).length !== 2) errors.push('Missing explicit reference and nested MPath producer applications');
  return errors;
}
if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const registry = JSON.parse(readFileSync('tests/v11-disjoint-schedules-statements.json', 'utf8'));
  const sources = Object.fromEntries(Object.keys(registry.files).map(file => [file, readFileSync(file, 'utf8')]));
  const errors = check(sources, registry);
  for (const e of errors) console.error(e);
  console.log(`V11 disjoint schedules: ${Object.keys(sources).length} modules, ${Object.values(registry.files).reduce((n, x) => n + Object.keys(x).length, 0)} original statements, ${errors.length} findings`);
  process.exit(errors.length ? 1 : 0);
}
