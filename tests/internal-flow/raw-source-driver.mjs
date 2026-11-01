// Fresh source elaboration, not an olean-import or persistent-frontend check.
import {readdirSync, openSync, closeSync, readFileSync, existsSync, writeFileSync} from 'node:fs';
import {isAbsolute} from 'node:path';
import {constants} from 'node:os';
import {createHash} from 'node:crypto';
import {spawnSync} from 'node:child_process';
const out = process.argv[2];
if (process.argv.length !== 3 || !out || !isAbsolute(out)) {
  console.error('one absolute evidence directory required'); process.exit(2);
}
const core = 'Solidity/Backend/InternalFlow';
const coreFiles = () => readdirSync(core).filter(n => n.endsWith('.lean')).sort()
  .map(n => `${core}/${n}`);
const files = coreFiles();
if (files.length === 0) { console.error('no owned Lean sources'); process.exit(2); }
const fixtures = ['tests/internal-flow/AxiomReports.lean',
  'tests/internal-flow/PublishedMemoryCalls.lean',
  'tests/internal-flow/MutatingMemoryCalls.lean',
  'tests/internal-flow/TupleMemoryCalls.lean'];
files.push(...fixtures);
const inputs = [...files, 'lakefile.lean', 'lakefile.toml', 'lake-manifest.json', 'lean-toolchain'];
const digest = data => createHash('sha256').update(data).digest('hex');
const snapshot = () => Object.fromEntries(inputs.map(p => [p, existsSync(p) ? digest(readFileSync(p)) : null]));
const before = snapshot();
const environment = Object.fromEntries(['PATH', 'LEAN_PATH', 'LEAN_SRC_PATH',
  'LEAN_SYSROOT', 'LEAN_NUM_THREADS', 'LD_LIBRARY_PATH'].map(k =>
  [k, process.env[k] === undefined ? null : digest(process.env[k])]));
const stages = [];
for (const file of files) {
  const name = file.split('/').at(-1).slice(0, -5);
  console.log(`lean -j1 --tstack=131072 ${file}`);
  const fd = openSync(`${out}/final-${name}-diagnostics.log`, 'w');
  let result;
  try {
    // Inherit precisely Lake's augmented environment and the original stdin.
    // No -o, imported substitute, parallelism, per-file timeout or retry.
    result = spawnSync('lean', ['-j1', '--tstack=131072', file],
      {env: process.env, stdio: [0, fd, fd]});
  } finally { closeSync(fd); }
  stages.push({file, pid: result.pid, exit: result.status, signal: result.signal});
  if (result.error || result.signal || result.status !== 0) {
    if (result.error) console.error(result.error.message);
    if (result.signal) console.error(`fresh Lean terminated by ${result.signal}`);
    process.exit(result.status ?? (result.signal ? 128 + (constants.signals[result.signal] ?? 1) : 1));
  }
}
const after = snapshot();
const unchanged = JSON.stringify(before) === JSON.stringify(after) &&
  JSON.stringify(files) === JSON.stringify([...coreFiles(), ...fixtures]);
writeFileSync(`${out}/raw-source-batch.json`, JSON.stringify({fresh_cli_processes: stages,
  compiler_arguments: ['-j1', '--tstack=131072'], environment_sha256: environment,
  before, after, unchanged}, null, 2) + '\n');
if (!unchanged) { console.error('raw source/config changed during check'); process.exit(1); }
