#!/usr/bin/env node
/** Prepare U01 admission evidence using the existing compiler/frontend API.
 * Listing readiness is never a proof, a native verdict, or a timing baseline. */
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {execFileSync} from 'node:child_process';
import {runSolidityTests, solidityFiles, testsPassed} from '../test-solidity.mjs';
import {sourceHash} from '../source-locations.mjs';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');

export function admissionResult(report, attemptFinished) {
  const counts = new Map();
  for (const row of report.results) counts.set(row.status, (counts.get(row.status) ?? 0) + 1);
  return {
    kind: 'u01-admission-only', verification: 'not-run', sourceToVerdictBaseline: false,
    attemptFinished, listingPassed: attemptFinished && testsPassed(report, true),
    rows: report.results.length, readyRows: counts.get('ready') ?? 0,
    byStatus: Object.fromEntries(counts), results: report.results, errors: report.errors,
  };
}

export function sourceIdentityErrors(inputs, results, readBytes = file => fs.readFileSync(file)) {
  const expected = new Map(inputs.map(input => [path.resolve(input.path), input.sha256]));
  const errors = [];
  for (const input of inputs) {
    try {
      const observed = sourceHash(readBytes(input.path));
      if (observed !== input.sha256) errors.push({stage: 'source-identity', source: input.path,
        reason: 'source changed during admission', expectedSha256: input.sha256, observedSha256: observed});
    } catch (error) {
      errors.push({stage: 'source-identity', source: input.path, reason: error.message});
    }
  }
  for (const row of results) {
    const hash = row.source ? expected.get(path.resolve(row.source)) : undefined;
    if (!hash || row.sourceHash !== hash) errors.push({stage: 'source-identity', source: row.source ?? null,
      function: row.function ?? null, reason: 'frontend row does not match the recorded input source',
      expectedSha256: hash ?? null, observedSha256: row.sourceHash ?? null});
  }
  return errors;
}

function main(args) {
  const options = {list: true, build: false, timeoutMs: 300000,
    solkey: path.join(root, 'tests/migration/solkey')};
  let output = path.join(root, '.lake/bench/admission.json');
  const paths = [];
  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    if (arg === '--help') {
      console.log('Usage: node scripts/bench/admission.mjs [--out FILE] [--soljson DIR] [--contract NAME] [--function SELECTOR] [--timeout-ms N] FILE_OR_DIR ...');
      console.log('Build Solidity.Frontend.Testing first. Uses the vendored SolKeY compiler pin; listing only, never verification.');
      return 0;
    }
    if (['--out', '--soljson', '--contract', '--function', '--timeout-ms'].includes(arg)) {
      const value = args[++i];
      if (!value || value.startsWith('--')) throw new Error(arg + ' needs a value');
      if (arg === '--out') output = path.resolve(value);
      else if (arg === '--timeout-ms') options.timeoutMs = Number(value);
      else options[arg.slice(2)] = value;
    } else if (arg.startsWith('--')) throw new Error('Unknown option: ' + arg);
    else paths.push(arg);
  }
  const selection = {paths: paths.map(file => path.resolve(file)), contract: options.contract ?? null,
    function: options.function ?? null, timeoutMs: options.timeoutMs, solkey: options.solkey,
    soljson: path.resolve(options.soljson ?? path.join(options.solkey, 'keyext.solidity.core/build/soljson'))};
  options.soljson = selection.soljson;
  let inputs = [], head = null, runnerSha256 = null;
  fs.mkdirSync(path.dirname(output), {recursive: true});
  const save = (report, finished) => {
    const result = {...admissionResult(report, finished), head, inputs, selection, runnerSha256};
    const temporary = output + '.' + process.pid + '.tmp';
    fs.writeFileSync(temporary, JSON.stringify(result, null, 2) + '\n');
    fs.renameSync(temporary, output);
    return result;
  };
  // Invalidate old success before discovery, hashing or Git setup can fail.
  let latest = {results: [], errors: []};
  save(latest, false);
  process.env.LEAN_NUM_THREADS = '1';
  let report;
  try {
    if (!Number.isSafeInteger(options.timeoutMs) || options.timeoutMs <= 0 || options.timeoutMs > 300000)
      throw new Error('timeout must be 1..300000 milliseconds; proof budgets are unchanged');
    if (!paths.length) throw new Error('At least one Solidity source or directory is required');
    inputs = solidityFiles(paths).map(file => ({path: file, sha256: sourceHash(fs.readFileSync(file))}));
    head = execFileSync('git', ['rev-parse', 'HEAD'], {cwd: root, encoding: 'utf8'}).trim();
    runnerSha256 = sourceHash(fs.readFileSync(fileURLToPath(import.meta.url)));
    report = runSolidityTests(paths, {...options, onProgress: r => {
      latest = {results: [...r.results], errors: [...r.errors]};
      save(latest, false);
    }});
  } catch (error) {
    report = {results: latest.results, errors: [...latest.errors, {stage: 'admission', reason: error.message}]};
  }
  report = {...report, errors: [...report.errors, ...sourceIdentityErrors(inputs, report.results)]};
  const result = save(report, true);
  console.log(JSON.stringify({output, rows: result.rows, readyRows: result.readyRows,
    listingPassed: result.listingPassed, verification: result.verification}));
  return result.listingPassed ? 0 : 1;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try { process.exitCode = main(process.argv.slice(2)); }
  catch (error) { console.error(error.message); process.exitCode = 2; }
}
