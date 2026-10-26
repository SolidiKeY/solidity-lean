'use strict';
// Entry point for --extensionTestsPath; run in an isolated VS Code user profile.
const assert = require('node:assert/strict');
const { mkdtempSync, mkdirSync, writeFileSync, rmSync } = require('node:fs');
const { tmpdir } = require('node:os');
const { join } = require('node:path');
async function run() {
  const vscode = require('vscode');
  const root = mkdtempSync(join(tmpdir(), 'solidity-lean-host-'));
  mkdirSync(join(root, 'scripts'));
  const source = join(root, 'Contract.sol');
  writeFileSync(source, 'contract C { function f() public {} }\n');
  const script = join(root, 'scripts/test-solidity.mjs');
  function backend(status) {
    writeFileSync(script, `import {readFileSync,writeSync} from 'node:fs';import {createHash} from 'node:crypto';const source=process.argv.at(-1);const hash=createHash('sha256').update(readFileSync(source)).digest('hex');writeSync(1,JSON.stringify({results:[{source,sourceHash:hash,contract:'C',function:'f',signature:'f()',status:${JSON.stringify(status)},range:{start:{line:0,character:13},end:{line:0,character:35}},reason:${JSON.stringify(status === 'pending' ? 'open proof goals' : '')}}],errors:[]}));`);
  }
  const config = vscode.workspace.getConfiguration('solidityLean');
  const keys = ['backendPath', 'nodePath', 'verifyOnSave'];
  const previous = Object.fromEntries(keys.map(key => [key, config.inspect(key)?.globalValue]));
  try {
    await config.update('backendPath', root, vscode.ConfigurationTarget.Global);
    await config.update('nodePath', process.env.SOLIDITY_LEAN_NODE_EXECUTABLE || 'node', vscode.ConfigurationTarget.Global);
    await config.update('verifyOnSave', false, vscode.ConfigurationTarget.Global);
    const extension = vscode.extensions.getExtension('SolidiKeY.solidity-lean');
    assert.ok(extension, 'extension package must be installed in the development host');
    const api = await extension.activate();
    assert.ok(api.controller, 'activation creates a real TestController');
    const document = await vscode.workspace.openTextDocument(source);
    await vscode.window.showTextDocument(document);
    backend('proved');
    await vscode.commands.executeCommand('solidityLean.verify');
    assert.equal(vscode.languages.getDiagnostics(document.uri).length, 0);
    assert.equal(api.controller.items.get(document.uri.toString()).children.size, 1);
    const hovers = await vscode.commands.executeCommand('vscode.executeHoverProvider', document.uri, new vscode.Position(0, 20));
    assert.ok(hovers.some(hover => hover.contents.some(content => /proved/.test(content.value || String(content)))), 'actual hover provider reports proof status');
    backend('pending');
    await vscode.commands.executeCommand('solidityLean.verify');
    const diagnostic = vscode.languages.getDiagnostics(document.uri).find(d => d.source === 'Solidity Lean');
    assert.equal(diagnostic.severity, vscode.DiagnosticSeverity.Warning);
    assert.match(diagnostic.message, /pending/);
    const edit = new vscode.WorkspaceEdit();
    edit.insert(document.uri, new vscode.Position(0, 0), '// changed\n');
    await vscode.workspace.applyEdit(edit);
    assert.equal(vscode.languages.getDiagnostics(document.uri).filter(d => d.source === 'Solidity Lean').length, 0, 'edits clear stale verification');
    const checks = ['activation', 'command', 'backend process', 'Test Explorer items', 'hover', 'diagnostics', 'edit invalidation'];
    if (process.env.SOLIDITY_LEAN_REAL_BACKEND) {
      await vscode.commands.executeCommand('workbench.action.revertAndCloseActiveEditor');
      await config.update('backendPath', process.env.SOLIDITY_LEAN_REAL_BACKEND, vscode.ConfigurationTarget.Global);
      const realSource = join(root, 'Real.sol');
      writeFileSync(realSource, 'pragma solidity ^0.8.34;\ncontract Real { function passes() public pure { assert(true); } function staysOpen() public pure { assert(false); } }\n');
      const realDocument = await vscode.workspace.openTextDocument(realSource);
      await vscode.window.showTextDocument(realDocument);
      const report = await api.verify(realDocument);
      assert.deepEqual(report.errors, []);
      assert.equal(report.results.find(row => row.function === 'passes').status, 'proved');
      assert.equal(report.results.find(row => row.function === 'staysOpen').status, 'pending');
      assert.ok(report.results.filter(row => row.sourceId >= 0).every(row => row.range && row.sourceHash));
      const realDiagnostics = vscode.languages.getDiagnostics(realDocument.uri).filter(d => d.source === 'Solidity Lean');
      assert.equal(realDiagnostics.length, 1);
      assert.equal(realDiagnostics[0].severity, vscode.DiagnosticSeverity.Warning);
      assert.equal(realDiagnostics[0].range.start.line, 1);
      checks.push('real solc + Lean proof', 'real pending obligation', 'real declaration ranges');
    }
    if (process.env.SOLIDITY_LEAN_HOST_RESULT) writeFileSync(process.env.SOLIDITY_LEAN_HOST_RESULT, JSON.stringify({ passed: true, checks }));
  } catch (error) {
    if (process.env.SOLIDITY_LEAN_HOST_RESULT) writeFileSync(process.env.SOLIDITY_LEAN_HOST_RESULT, JSON.stringify({ passed: false, error: error.stack }));
    throw error;
  } finally {
    await vscode.commands.executeCommand('workbench.action.revertAndCloseActiveEditor');
    for (const key of keys) await config.update(key, previous[key], vscode.ConfigurationTarget.Global);
    rmSync(root, { recursive: true, force: true });
  }
}
module.exports = { run };
