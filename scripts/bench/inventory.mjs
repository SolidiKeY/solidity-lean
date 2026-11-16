#!/usr/bin/env node
/** U01 inventory only: records the distinction between missing source-to-verdict
 * measurements and historical kernel component timings. Does not run Lean. */
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const required = [
  'scripts/testsuite-performance.mjs', 'scripts/report-testsuite-performance.mjs',
  'scripts/measure-simple.mjs', 'scripts/measure-native.mjs',
  'scripts/measure-replay-costs.py', 'scripts/build-measure.py',
  'tests/automation/ReplayCosts.lean', 'Solidity/Frontend/Testing.lean',
  'vscode/src/native-plugin.cjs', 'scripts/build-direct-native.py',
  'docs/audits/build-speed.md', 'docs/feature-work/trust-usability.md',
];
const inspect = relative => {
  const file = path.join(root, relative);
  if (!fs.existsSync(file)) return {path: relative, present: false};
  const bytes = fs.readFileSync(file);
  return {path: relative, present: true, sha256: createHash('sha256').update(bytes).digest('hex')};
};
const tools = required.map(inspect);
const report = {
  kind: 'inventory-only', sourceToVerdictBaseline: false,
  tools,
  requestedCitation: inspect('docs/kernel-replay-performance.md'),
  historicalData: fs.readdirSync(path.join(root, 'docs/benchmarks'))
    .filter(name => name.endsWith('.json')).sort(),
  knownGapsAtPinnedBase: ['matched full-suite source-to-verdict baseline',
    'separate walk/closing telemetry for every backend and obligation kind',
    'per-function peak RSS with stated process/cache boundaries',
    'dynamic walk-step counts', 'verified token/vault/multisig selection',
    'user-approved calibrated budgets'],
};
console.log(JSON.stringify(report, null, 2));
if (tools.some(tool => !tool.present)) process.exitCode = 1;
