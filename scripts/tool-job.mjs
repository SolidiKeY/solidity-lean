/** Supervisor for synchronous callers: own the tool group and clean it up on
 * timeout or terminal interruption, even while the caller is in spawnSync. */
import {spawn} from 'node:child_process';
import {writeFileSync} from 'node:fs';

const [checkpoint, milliseconds, command, ...args] = process.argv.slice(2);
const group = process.platform !== 'win32';
let child, finished = false;
function cleanup() {
  if (!child?.pid) return;
  try {
    if (group) process.kill(-child.pid, 'SIGKILL');
    else child.kill('SIGKILL');
  } catch (e) { if (e.code !== 'ESRCH') throw e; }
}
function finish(exitCode, signal = null, errorCode = null, timedOut = false) {
  if (finished) return;
  finished = true;
  cleanup();
  writeFileSync(checkpoint, JSON.stringify({exitCode, signal, errorCode, timedOut}));
  process.exit(exitCode ?? (signal === 'SIGINT' ? 130 : 1));
}
process.on('exit', cleanup);
for (const signal of ['SIGINT', 'SIGTERM', 'SIGHUP'])
  process.on(signal, () => finish(null, signal));
child = spawn(command, args, {detached:group, stdio:'inherit'});
child.on('error', e => { console.error(e.message); finish(null, null, e.code); });
child.on('exit', (code, signal) => finish(code, signal));
setTimeout(() => finish(null, 'SIGKILL', 'ETIMEDOUT', true), Number(milliseconds));
