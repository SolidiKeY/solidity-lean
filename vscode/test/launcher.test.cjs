'use strict';
const {test} = require('node:test');
const assert = require('node:assert/strict');
const {mkdtempSync, writeFileSync, readFileSync, rmSync} = require('node:fs');
const {join} = require('node:path');
const {tmpdir} = require('node:os');
const {spawnSync} = require('node:child_process');

for (const succeeds of [false, true]) test(`offline host launcher ${succeeds ? 'retains fresh evidence' : 'rejects stale success evidence'}`, {skip:process.platform === 'win32'}, () => {
  const root = mkdtempSync(join(tmpdir(), 'solidity-launcher-'));
  try {
    const executable = join(root, 'fake-code');
    const output = join(root, 'result.json');
    writeFileSync(output, JSON.stringify({passed:true, checks:['stale']}));
    writeFileSync(executable, '#!/bin/sh\n' + (succeeds ?
      'printf \'{"passed":true,"checks":["fresh"]}\' > "$SOLIDITY_LEAN_HOST_RESULT"\n' : 'exit 0\n'), {mode:0o700});
    const result = spawnSync(process.execPath, [join(__dirname, 'run-host.cjs')], {
      env:{...process.env, VSCODE_EXECUTABLE_PATH:executable, SOLIDITY_LEAN_HOST_RESULT:output},
      encoding:'utf8', timeout:5000,
    });
    assert.equal(result.status, succeeds ? 0 : 1, result.stderr);
    assert.deepEqual(JSON.parse(readFileSync(output,'utf8')).checks, [succeeds ? 'fresh' : 'stale']);
  } finally { rmSync(root, {recursive:true, force:true}); }
});
