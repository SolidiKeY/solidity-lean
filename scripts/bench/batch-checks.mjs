#!/usr/bin/env node
/** Retain every admission row while collecting existing batched check timers.
 * These timers exclude shared source compilation/import work; never a U01 baseline. */
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {execFileSync} from 'node:child_process';
import {runSolidityTests} from '../test-solidity.mjs';
import {sourceIdentityErrors} from './admission.mjs';
import {sourceHash} from '../source-locations.mjs';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const key = row => JSON.stringify([row.source ? path.resolve(row.source) : null, row.sourceHash, row.contract, row.sourceId ?? row.signature]);
export function observations(inventory, raw) {
  const counts = new Map();
  for (const row of inventory) counts.set(key(row), (counts.get(key(row)) ?? 0)+1);
  const duplicateInventoryKeys = [...counts].filter(([,count])=>count>1).map(([id])=>id);
  const groups = new Map();
  for (const row of raw.results) groups.set(key(row), [...(groups.get(key(row)) ?? []), row]);
  const known = new Set(inventory.map(key));
  const unexpected = raw.results.filter(row => !known.has(key(row)));
  const rows = inventory.map(input => {
    const found = groups.get(key(input)) ?? [];
    const proved = counts.get(key(input)) === 1 && found.length === 1 && found[0].status === 'proved'
      && [undefined, 'certified'].includes(found[0].verification)
      && [undefined, 'possible', 'notApplicable'].includes(found[0].preconditions);
    return {input, observations: found, certifiedCheckPassed: proved,
      functionReportedElapsedMs: counts.get(key(input)) === 1 && found.length === 1
        && ['proved','refuted','pending','error'].includes(found[0].status)
        && [undefined,'certified'].includes(found[0].verification)
        && Number.isSafeInteger(found[0].elapsedMs) && found[0].elapsedMs >= 0
          ? found[0].elapsedMs : null,
      sourceToVerdictWallMs: null, maxRss: null, phases: null, walkSteps: null};
  });
  return {rows, unexpected, duplicateInventoryKeys,
    missingReadyRows: rows.filter(r => r.input.status === 'ready' && r.observations.length === 0).length,
    ambiguousRows: rows.filter(r => r.observations.length > 1 || counts.get(key(r.input)) > 1).length};
}

function admissionSelection(selection = {}) {
  const result = {contract: selection.contract ?? null, function: selection.function ?? null,
    timeoutMs: selection.timeoutMs ?? 300000};
  for (const name of ['contract','function']) {
    if (result[name] !== null && (typeof result[name] !== 'string' || !result[name].length))
      throw new Error('invalid admission '+name+' selector');
  }
  if (!Number.isSafeInteger(result.timeoutMs) || result.timeoutMs < 1)
    throw new Error('invalid admission timeout');
  result.timeoutMs = Math.min(result.timeoutMs, 300000);
  return result;
}

// Keep the actual API call injectable for no-Lean selector regression controls.
export function runAdmissionChecks(admission, {soljson, onProgress}, run = runSolidityTests) {
  const selection = admissionSelection(admission.selection);
  return run(admission.inputs.map(i=>i.path), {build: false,
    contract: selection.contract ?? undefined, function: selection.function ?? undefined,
    timeoutMs: selection.timeoutMs, batchSize: 32, soljson,
    solkey: path.join(root, 'tests/migration/solkey'), onProgress});
}

function main(args) {
  let admission, work, soljson;
  for (let i = 0; i < args.length; i++) {
    if (args[i] === '--admission') admission = path.resolve(args[++i]);
    else if (args[i] === '--work') work = path.resolve(args[++i]);
    else if (args[i] === '--soljson') soljson = path.resolve(args[++i]);
    else throw new Error('Usage: batch-checks.mjs --admission FILE --work NEW_DIR --soljson DIR');
  }
  if (!admission || !work || !soljson) throw new Error('admission, work and soljson required');
  fs.mkdirSync(work); // A new directory cannot alias or overwrite an existing input/report.
  let inventory = [], inputs = [], raw = {results: [], errors: []};
  const report = {kind: 'u01-partial-batched-check-timers', sourceToVerdictBaseline: false,
    suiteComplete: false, attemptFinished: false, allReadyChecksPassed: false,
    timerScope: 'existing frontend row.elapsedMs; excludes source compilation and shared imports; not end-to-end',
    batchSize: 32, perToolTimeoutMs: 300000, attempts: [], apiWallMs: null, aggregatePeakRss: null,
    rows: [], unexpected: [], errors: [], node: process.version};
  const save = () => {
    Object.assign(report, observations(inventory, raw));
    report.errors = raw.errors;
    fs.writeFileSync(path.join(work, 'report.tmp'), JSON.stringify(report, null, 2)+'\n');
    fs.renameSync(path.join(work, 'report.tmp'), path.join(work, 'report.json'));
  };
  save();
  try {
    const bytes = fs.readFileSync(admission), data = JSON.parse(bytes);
    if (data.kind !== 'u01-admission-only' || data.attemptFinished !== true)
      throw new Error('finished admission-only inventory required');
    inventory = data.results; inputs = data.inputs;
    report.selection = admissionSelection(data.selection);
    report.perToolTimeoutMs = report.selection.timeoutMs;
    report.admissionSha256 = sourceHash(bytes);
    report.toolHead = execFileSync('git', ['rev-parse', 'HEAD'], {cwd: root, encoding: 'utf8'}).trim();
    report.driverSha256 = sourceHash(fs.readFileSync(fileURLToPath(import.meta.url)));
    report.runtime = Object.fromEntries(['lean','lake'].map(tool=>{
      try {return [tool,execFileSync(tool,['--version'],{encoding:'utf8'}).trim()];}
      catch {return [tool,null];}
    }));
    report.toolWorktreeStatus = execFileSync('git',['status','--porcelain'],{cwd:root,encoding:'utf8'}).split('\n').filter(Boolean);
    report.cliSha256 = sourceHash(fs.readFileSync(path.join(root, 'scripts/test-solidity.mjs')));
    report.compilerFiles = Object.fromEntries(fs.readdirSync(soljson).filter(n=>n.endsWith('.js')).sort()
      .map(n=>[n, sourceHash(fs.readFileSync(path.join(soljson,n)))]));
    raw.errors.push(...(data.errors ?? []), ...sourceIdentityErrors(inputs, inventory));
    save();
    if (report.duplicateInventoryKeys.length) raw.errors.push({stage:'inventory',reason:'duplicate declaration identity'});
    if (raw.errors.length) throw new Error('invalid admission snapshot; no checks started');
    process.env.LEAN_NUM_THREADS = '1';
    for (let attempt = 0; attempt < 2; attempt++) {
      const started = performance.now();
      raw = runAdmissionChecks(data, {soljson,
        onProgress: progress => {raw = {results: [...progress.results], errors: [...progress.errors]}; save();}});
      const apiWallMs = performance.now()-started;
      report.attempts.push({apiWallMs, results: raw.results, errors: [...raw.errors]});
      report.apiWallMs = report.attempts.reduce((sum,a)=>sum+a.apiWallMs,0);
      save();
      const busExit = raw.errors.some(e=>e.tool?.exitCode===135 || e.tool?.signal==='SIGBUS');
      if (!busExit || attempt === 1) break;
    }
    raw.errors.push(...sourceIdentityErrors(inputs, raw.results));
    if (sourceHash(fs.readFileSync(admission)) !== report.admissionSha256)
      raw.errors.push({stage: 'identity', reason: 'admission changed during checks'});
    if (execFileSync('git', ['rev-parse','HEAD'], {cwd:root,encoding:'utf8'}).trim() !== report.toolHead)
      raw.errors.push({stage:'identity',reason:'checkout HEAD changed'});
    const compilerAfter = Object.fromEntries(fs.readdirSync(soljson).filter(n=>n.endsWith('.js')).sort()
      .map(n=>[n, sourceHash(fs.readFileSync(path.join(soljson,n)))]));
    if (JSON.stringify(compilerAfter) !== JSON.stringify(report.compilerFiles))
      raw.errors.push({stage:'identity',reason:'compiler file set or bytes changed'});
    if (sourceHash(fs.readFileSync(path.join(root,'scripts/test-solidity.mjs'))) !== report.cliSha256
        || sourceHash(fs.readFileSync(fileURLToPath(import.meta.url))) !== report.driverSha256)
      raw.errors.push({stage:'identity',reason:'driver or CLI changed'});
    report.attemptFinished = true;
    save();
    const ready = report.rows.filter(r=>r.input.status==='ready');
    report.allReadyChecksPassed = ready.length > 0 && raw.errors.length === 0
      && report.unexpected.length === 0 && ready.every(r=>r.certifiedCheckPassed);
  } catch (error) {raw.errors.push({stage:'batch-runner',reason:error.message});}
  save();
  return report.allReadyChecksPassed ? 0 : 1;
}
if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try {process.exitCode = main(process.argv.slice(2));}
  catch (error) {console.error(error.message);process.exitCode = 2;}
}
