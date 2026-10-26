import {test} from 'node:test';
import assert from 'node:assert/strict';
import {spawn} from 'node:child_process';
import {mkdtempSync, writeFileSync, readFileSync, existsSync, rmSync} from 'node:fs';
import {join} from 'node:path';
import {tmpdir} from 'node:os';
import {once} from 'node:events';

test('terminal interruption kills the tool group while its caller waits synchronously',
  {skip:process.platform === 'win32'}, async () => {
    const dir = mkdtempSync(join(tmpdir(), 'solidity-interrupt-'));
    const pidFile = join(dir, 'descendant.pid'), marker = join(dir, 'late-output');
    let caller, descendant;
    try {
      const job = join(dir, 'job.mjs'), launcher = join(dir, 'launcher.mjs');
      const code = `process.on('SIGINT',()=>{});require('node:fs').writeFileSync(${JSON.stringify(pidFile)},String(process.pid));setTimeout(()=>require('node:fs').writeFileSync(${JSON.stringify(marker)},'alive'),1000);setInterval(()=>{},1000)`;
      writeFileSync(job, `import {spawn} from 'node:child_process';
spawn(process.execPath,['-e',${JSON.stringify(code)}],{stdio:'ignore'});
process.on('SIGINT',()=>{});setInterval(()=>{},1000);`);
      writeFileSync(launcher, `import {runTool} from ${JSON.stringify(new URL('./test-solidity.mjs', import.meta.url).href)};
runTool(process.execPath,[${JSON.stringify(job)}],10000);`);
      caller = spawn(process.execPath, [launcher], {detached:true, stdio:'ignore'});
      const exited = once(caller, 'exit');
      const deadline = Date.now() + 5000;
      while (!existsSync(pidFile) && Date.now() < deadline)
        await new Promise(resolve => setTimeout(resolve, 20));
      assert.ok(existsSync(pidFile), 'descendant did not start');
      descendant = Number(readFileSync(pidFile, 'utf8'));
      process.kill(-caller.pid, 'SIGINT');
      await exited;
      await new Promise(resolve => setTimeout(resolve, 1100));
      assert.equal(existsSync(marker), false, 'descendant survived terminal interruption');
    } finally {
      for (const pid of [caller?.pid ? -caller.pid : null, descendant]) if (pid) {
        try { process.kill(pid, 'SIGKILL'); } catch (e) { if (e.code !== 'ESRCH') throw e; }
      }
      rmSync(dir, {recursive:true, force:true});
    }
  });
