'use strict';
const { spawn, spawnSync } = require('node:child_process');
const { resolve, join } = require('node:path');
const { existsSync,readdirSync } = require('node:fs');
const { parseReport } = require('./report.cjs');
const {processState}=require('./process-state.cjs');

/** Stop only a known-owned positive PID and its descendants or explicitly owned session. */
function terminateTree(child) {
  if (!Number.isSafeInteger(child.pid) || child.pid <= 0) return;
  if (process.platform === 'win32') {
    spawnSync('taskkill', ['/pid', String(child.pid), '/T', '/F'], { windowsHide: true, timeout: 5000 });
    return;
  }
  const identity=processState(child.pid);if(identity&&child.processBirth&&identity.birth!==child.processBirth)throw new Error('Owned process identity changed; refusing cleanup');
  if(!child.ownedGroup&&(child.exitCode!==undefined&&child.exitCode!==null||child.signalCode!==undefined&&child.signalCode!==null))return;
  if(child.ownedGroup)try{process.kill(-child.pid,'SIGSTOP');}catch{}
  if(process.platform==='linux'){
    const stop=record=>{if(!record)return;const now=processState(record.pid);if(!now||now.birth!==record.birth)return;
      try{process.kill(record.pid,'SIGSTOP');}catch{}
      // CONFIG_PROC_CHILDREN is optional; use PPID records rather than assuming task/*/children exists.
      const children=readdirSync('/proc').filter(name=>/^\d+$/.test(name)).map(Number).map(processState).filter(candidate=>candidate?.ppid===record.pid);
      for(const candidate of children)stop(candidate);
      if(processState(record.pid)?.birth===record.birth)try{process.kill(record.pid,'SIGKILL');}catch{}
    };stop(identity);
    if(child.ownedGroup)try{process.kill(-child.pid,'SIGKILL');}catch{}
    return;
  }
  // Non-Linux fallback retains the existing bounded descendant snapshot; VM evidence is Linux-only.
  try{process.kill(child.pid,'SIGSTOP');}catch{}
  const ps=spawnSync('ps',['-eo','pid=,ppid='],{encoding:'utf8',timeout:5000}),children=new Map();
  for(const line of(ps.stdout||'').trim().split('\n')){const[pid,parent]=line.trim().split(/\s+/).map(Number);if(!children.has(parent))children.set(parent,[]);children.get(parent).push(pid);}
  function kill(pid){try{process.kill(pid,'SIGSTOP');}catch{}for(const descendant of children.get(pid)||[])kill(descendant);try{process.kill(pid,'SIGKILL');}catch{}}
  kill(child.pid);if(child.ownedGroup)try{process.kill(-child.pid,'SIGKILL');}catch{}
}

function runBackend({ backendPath, nodePath = 'node', source, listing = false, auditPreconditions = false, counterexamples = false, contract, function: functionName, timeoutMs = 600000, signal }) {
  if (!Number.isSafeInteger(timeoutMs) || timeoutMs < 1) return Promise.reject(new Error('Verification timeout must be positive milliseconds'));
  const root = resolve(backendPath);
  const script = join(root, 'scripts', 'test-solidity.mjs');
  if (!existsSync(script)) return Promise.reject(new Error(`Solidity Lean backend not found: ${script}`));
  const args = [script, '--json', '--timeout-ms', String(timeoutMs)];
  if (listing) args.push('--list');
  if (auditPreconditions && !listing) args.push('--audit-preconditions');
  if (counterexamples && !listing) args.push('--counterexamples');
  if (contract) args.push('--contract', contract);
  if (functionName) args.push('--function', functionName);
  args.push(resolve(source));
  return new Promise((resolvePromise, reject) => {
    if (signal?.aborted) { reject(Object.assign(new Error('Verification cancelled'), { code: 'CANCELLED' })); return; }
    const child = spawn(nodePath, args, { cwd: root, detached: process.platform !== 'win32', windowsHide: true, shell: false });
    child.ownedGroup=process.platform!=='win32';child.processBirth=processState(child.pid)?.birth;
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
        if ((!counterexamples || listing) && report.results.some(row => row.status === 'refuted'))
          throw new Error('Verifier returned unrequested certified model prestate evidence');
        if (auditPreconditions && !listing && report.results.some(row => row.preconditions === undefined))
          throw new Error('Verifier did not return the requested precondition audit');
        finish(null, report);
      } catch (error) { finish(error); }
    });
  });
}

module.exports = { runBackend, parseReport, terminateTree };
