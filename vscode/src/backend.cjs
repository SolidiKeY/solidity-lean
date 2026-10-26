'use strict';
const { spawn, spawnSync } = require('node:child_process');
const { resolve, join } = require('node:path');
const { existsSync } = require('node:fs');

const statuses = new Set(['proved', 'pending', 'skipped', 'skip', 'internal', 'unsupported', 'excluded', 'ready', 'notRun', 'error']);
const preconditions = new Set(['possible', 'impossible', 'unknown', 'notApplicable', 'notRun']);

function parseReport(stdout) {
  let report;
  try { report = JSON.parse(stdout); } catch { throw new Error('Verifier returned invalid JSON'); }
  if (!report || !Array.isArray(report.results) || !Array.isArray(report.errors)) throw new Error('Verifier returned an invalid report');
  for (const row of report.results) {
    if (!row || typeof row.source !== 'string' || typeof row.contract !== 'string' || typeof row.function !== 'string' || !statuses.has(row.status)) throw new Error('Verifier returned an invalid obligation');
    if (row.preconditions !== undefined && !preconditions.has(row.preconditions)) throw new Error('Verifier returned an invalid precondition audit');
    if (row.preconditionReason !== undefined && typeof row.preconditionReason !== 'string') throw new Error('Verifier returned an invalid precondition reason');
  }
  for (const error of report.errors) if (!error || typeof error.reason !== 'string') throw new Error('Verifier returned an invalid error');
  return report;
}

/** The backend uses detached Lean children; terminate the entire descendant tree. */
function terminateTree(child) {
  if (!child.pid) return;
  if (process.platform === 'win32') {
    spawnSync('taskkill', ['/pid', String(child.pid), '/T', '/F'], { windowsHide: true, timeout: 5000 });
    return;
  }
  // Freeze the CLI before discovering children so it cannot launch another batch.
  try { process.kill(-child.pid, 'SIGSTOP'); } catch {}
  const ps = spawnSync('ps', ['-eo', 'pid=,ppid='], { encoding: 'utf8', timeout: 5000 });
  const children = new Map();
  for (const line of (ps.stdout || '').trim().split('\n')) {
    const [pid, parent] = line.trim().split(/\s+/).map(Number);
    if (!children.has(parent)) children.set(parent, []);
    children.get(parent).push(pid);
  }
  function kill(pid) {
    try { process.kill(pid, 'SIGSTOP'); } catch {}
    for (const descendant of children.get(pid) || []) kill(descendant);
    // Detached children lead their own groups; ordinary children are killed by pid.
    try { process.kill(-pid, 'SIGKILL'); } catch {}
    try { process.kill(pid, 'SIGKILL'); } catch {}
  }
  kill(child.pid);
}

function runBackend({ backendPath, nodePath = 'node', source, listing = false, auditPreconditions = false, contract, function: functionName, timeoutMs = 600000, signal }) {
  if (!Number.isSafeInteger(timeoutMs) || timeoutMs < 1) return Promise.reject(new Error('Verification timeout must be positive milliseconds'));
  const root = resolve(backendPath);
  const script = join(root, 'scripts', 'test-solidity.mjs');
  if (!existsSync(script)) return Promise.reject(new Error(`Solidity Lean backend not found: ${script}`));
  const args = [script, '--json', '--timeout-ms', String(timeoutMs)];
  if (listing) args.push('--list');
  if (auditPreconditions && !listing) args.push('--audit-preconditions');
  if (contract) args.push('--contract', contract);
  if (functionName) args.push('--function', functionName);
  args.push(resolve(source));
  return new Promise((resolvePromise, reject) => {
    if (signal?.aborted) { reject(Object.assign(new Error('Verification cancelled'), { code: 'CANCELLED' })); return; }
    const child = spawn(nodePath, args, { cwd: root, detached: process.platform !== 'win32', windowsHide: true, shell: false });
    let stdout = '', stderr = '', finished = false;
    const finish = (error, report) => {
      if (finished) return;
      finished = true;
      clearTimeout(timer);
      signal?.removeEventListener('abort', cancel);
      if (error) reject(error); else resolvePromise(report);
    };
    const stop = (message, code) => {
      if (finished) return;
      terminateTree(child);
      finish(Object.assign(new Error(message), { code }));
    };
    const cancel = () => stop('Verification cancelled', 'CANCELLED');
    const timer = setTimeout(() => stop(`Verification timed out after ${timeoutMs} ms`, 'TIMEOUT'), timeoutMs);
    signal?.addEventListener('abort', cancel, { once: true });
    child.on('error', error => finish(error));
    child.stdout.setEncoding('utf8');
    child.stderr.setEncoding('utf8');
    child.stdout.on('data', chunk => {
      stdout += chunk;
      if (Buffer.byteLength(stdout) > 32 * 1024 * 1024) stop('Verifier output exceeded 32 MiB', 'OUTPUT_LIMIT');
    });
    child.stderr.on('data', chunk => { stderr = (stderr + chunk).slice(-16000); });
    child.on('close', (code, killedBy) => {
      if (finished) return;
      if (code !== 0 && code !== 1) { finish(new Error(`Verifier ${killedBy ? `terminated by ${killedBy}` : `exited ${code}`}${stderr ? `: ${stderr.trim()}` : ''}`)); return; }
      try {
        const report = parseReport(stdout);
        if (auditPreconditions && !listing && report.results.some(row => row.preconditions === undefined))
          throw new Error('Verifier did not return the requested precondition audit');
        finish(null, report);
      } catch (error) { finish(error); }
    });
  });
}

module.exports = { runBackend, parseReport, terminateTree };
