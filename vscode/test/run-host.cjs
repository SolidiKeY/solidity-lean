'use strict';
const { resolve, join } = require('node:path');
const { spawnSync } = require('node:child_process');
const { mkdtempSync, readFileSync, writeFileSync, rmSync } = require('node:fs');
const { tmpdir } = require('node:os');

const extensionDevelopmentPath = resolve(__dirname, '..');
const extensionTestsPath = resolve(__dirname, 'host.cjs');
const repo = resolve(__dirname, '../..');
const launchArgs = [repo, '--disable-gpu', '--disable-workspace-trust', '--skip-welcome', '--skip-release-notes',
  ...(process.env.VSCODE_TEST_NO_SANDBOX === '1' ? ['--no-sandbox'] : [])];

async function main() {
  const scratch = mkdtempSync(join(tmpdir(), 'solidity-host-result-'));
  const requestedResult = process.env.SOLIDITY_LEAN_HOST_RESULT;
  const resultPath = join(scratch, 'result.json');
  process.env.SOLIDITY_LEAN_HOST_RESULT = resultPath;
  try {
    // A local Code-compatible executable makes the test usable completely offline.
    if (process.env.VSCODE_EXECUTABLE_PATH) {
      const result = spawnSync(process.env.VSCODE_EXECUTABLE_PATH, [
        ...launchArgs,
        `--extensionDevelopmentPath=${extensionDevelopmentPath}`,
        `--extensionTestsPath=${extensionTestsPath}`,
        ...(process.env.VSCODE_TEST_USER_DATA_DIR ? ['--user-data-dir', process.env.VSCODE_TEST_USER_DATA_DIR] : []),
        ...(process.env.VSCODE_TEST_EXTENSIONS_DIR ? ['--extensions-dir', process.env.VSCODE_TEST_EXTENSIONS_DIR] : []),
      ], {stdio:'inherit', timeout:900000});
      if (result.error) throw result.error;
      if (result.status !== 0) throw new Error(`Editor host exited ${result.status ?? result.signal}`);
    } else {
      const { runTests } = require('@vscode/test-electron');
      await runTests({extensionDevelopmentPath, extensionTestsPath, launchArgs});
    }
    const report = JSON.parse(readFileSync(resultPath, 'utf8'));
    if (report.passed !== true) throw new Error(report.error || 'Editor host did not pass');
    if (requestedResult) writeFileSync(requestedResult, JSON.stringify(report));
    writeFileSync(1, `Editor host passed ${report.checks?.length ?? 0} checks\n`);
  } finally { rmSync(scratch, {recursive:true, force:true}); }
}
main().catch(error => {
  require('node:fs').writeSync(2, `${error.stack}\n`);
  process.exitCode = 1;
});
