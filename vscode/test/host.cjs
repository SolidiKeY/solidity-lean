'use strict';
// Entry point for --extensionTestsPath; run in an isolated VS Code user profile.
const assert = require('node:assert/strict');
const { mkdtempSync, mkdirSync, writeFileSync, rmSync } = require('node:fs');
const { tmpdir } = require('node:os');
const { join } = require('node:path');
const { evidence } = require('./witness.cjs');
async function run() {
  const vscode = require('vscode');
  const root = mkdtempSync(join(tmpdir(), 'solidity-lean-host-'));
  mkdirSync(join(root, 'scripts'));
  const source = join(root, 'Contract.sol');
  writeFileSync(source, 'contract C { function f() public {} }\n');
  const script = join(root, 'scripts/test-solidity.mjs');
  function backend(status, preconditions) {
    const audit = preconditions ? {preconditions,preconditionReason:'kernel-checked fixture'} : {};
    const witness = status === 'refuted' ? {counterexample:evidence({arguments:[], lines:['[run](command:evil)', '\u001b[31mmodel']})} : {};
    writeFileSync(script, `import {readFileSync,writeSync} from 'node:fs';import {createHash} from 'node:crypto';const source=process.argv.at(-1);const hash=createHash('sha256').update(readFileSync(source)).digest('hex');writeSync(1,JSON.stringify({results:[{source,sourceHash:hash,contract:'C',function:'f',signature:'f()',status:${JSON.stringify(status)},range:{start:{line:0,character:13},end:{line:0,character:35}},reason:${JSON.stringify(status === 'pending' ? 'open proof goals' : '')},...${JSON.stringify(audit)},...${JSON.stringify(witness)}}],errors:[]}));`);
  }
  const config = vscode.workspace.getConfiguration('solidityLean');
  const keys = ['backendPath', 'nodePath', 'verifyOnSave', 'auditPreconditions', 'counterexamples'];
  const previous = Object.fromEntries(keys.map(key => [key, config.inspect(key)?.globalValue]));
  try {
    await config.update('backendPath', root, vscode.ConfigurationTarget.Global);
    await config.update('nodePath', process.env.SOLIDITY_LEAN_NODE_EXECUTABLE || 'node', vscode.ConfigurationTarget.Global);
    await config.update('verifyOnSave', false, vscode.ConfigurationTarget.Global);
    await config.update('auditPreconditions', false, vscode.ConfigurationTarget.Global);
    await config.update('counterexamples', false, vscode.ConfigurationTarget.Global);
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
    backend('refuted');
    await config.update('counterexamples', true, vscode.ConfigurationTarget.Global);
    await vscode.commands.executeCommand('solidityLean.verify');
    const refuted = vscode.languages.getDiagnostics(document.uri).find(d => d.source === 'Solidity Lean');
    assert.equal(refuted.code, 'refuted');
    assert.equal(refuted.severity, vscode.DiagnosticSeverity.Error);
    assert.match(refuted.message, /certified model prestate/);
    const witnessHovers = await vscode.commands.executeCommand('vscode.executeHoverProvider', document.uri, new vscode.Position(0, 20));
    assert.ok(witnessHovers.some(hover => hover.contents.some(content => content.value?.includes('\\[run\\]') && !content.isTrusted && !content.supportHtml)), 'model text is escaped in the actual MarkdownString');
    await config.update('counterexamples', false, vscode.ConfigurationTarget.Global);
    backend('proved', 'impossible');
    await config.update('auditPreconditions', true, vscode.ConfigurationTarget.Global);
    await vscode.commands.executeCommand('solidityLean.verify');
    const vacuous = vscode.languages.getDiagnostics(document.uri).find(d => d.source === 'Solidity Lean');
    assert.equal(vacuous.code, 'preconditions-impossible');
    assert.match(vacuous.message, /vacuous/);
    await config.update('auditPreconditions', false, vscode.ConfigurationTarget.Global);
    const edit = new vscode.WorkspaceEdit();
    edit.insert(document.uri, new vscode.Position(0, 0), '// changed\n');
    await vscode.workspace.applyEdit(edit);
    assert.equal(vscode.languages.getDiagnostics(document.uri).filter(d => d.source === 'Solidity Lean').length, 0, 'edits clear stale verification');
    const checks = ['activation', 'command', 'backend process', 'Test Explorer items', 'hover', 'diagnostics', 'precondition audit diagnostics', 'certified model prestate diagnostics', 'escaped model hover', 'edit invalidation'];
    if (process.env.SOLIDITY_LEAN_REAL_BACKEND) {
      await vscode.commands.executeCommand('workbench.action.revertAndCloseActiveEditor');
      await config.update('backendPath', process.env.SOLIDITY_LEAN_REAL_BACKEND, vscode.ConfigurationTarget.Global);
      const realSource = join(root, 'Real.sol');
      writeFileSync(realSource, 'pragma solidity ^0.8.34;\ncontract Real { function passes() public pure { assert(true); } function staysOpen() public pure { assert(false); }\n/// @custom:key ensures \\in uint (\\result; 1, 2)\nfunction choice() public pure returns(uint) { return 1; } }\n');
      const realDocument = await vscode.workspace.openTextDocument(realSource);
      await vscode.window.showTextDocument(realDocument);
      const report = await api.verify(realDocument);
      assert.deepEqual(report.errors, []);
      assert.equal(report.results.find(row => row.function === 'passes').status, 'proved');
      assert.equal(report.results.find(row => row.function === 'staysOpen').status, 'pending');
      assert.equal(report.results.find(row => row.function === 'choice').status, 'proved');
      assert.ok(report.results.filter(row => row.sourceId >= 0).every(row => row.range && row.sourceHash));
      const realDiagnostics = vscode.languages.getDiagnostics(realDocument.uri).filter(d => d.source === 'Solidity Lean');
      assert.equal(realDiagnostics.length, 1);
      assert.equal(realDiagnostics[0].severity, vscode.DiagnosticSeverity.Warning);
      assert.equal(realDiagnostics[0].range.start.line, 1);
      checks.push('real solc + Lean proof', 'real pending obligation', 'real declaration ranges', 'real finite membership proof');
      const auditSource = join(root, 'EntryAudit.sol');
      writeFileSync(auditSource, 'pragma solidity ^0.8.34;\ncontract EntryAudit {\n/// @custom:key requires x > 10 && x < 3\n/// @custom:key ensures false\nfunction vacuous(uint x) public pure { assert(false); }\n/// @custom:key requires x > 0\n/// @custom:key ensures \\result == x\nfunction possible(uint x) public pure returns(uint) { return x; }\n}\n');
      await config.update('auditPreconditions', true, vscode.ConfigurationTarget.Global);
      const auditDocument = await vscode.workspace.openTextDocument(auditSource);
      await vscode.window.showTextDocument(auditDocument);
      const audited = await api.verify(auditDocument);
      assert.deepEqual(audited.errors, []);
      assert.equal(audited.results.find(row => row.function === 'vacuous').status, 'proved');
      assert.equal(audited.results.find(row => row.function === 'vacuous').preconditions, 'impossible');
      assert.equal(audited.results.find(row => row.function === 'possible').preconditions, 'possible');
      const auditDiagnostics = vscode.languages.getDiagnostics(auditDocument.uri).filter(d => d.source === 'Solidity Lean');
      assert.equal(auditDiagnostics.length, 1);
      assert.equal(auditDiagnostics[0].code, 'preconditions-impossible');
      assert.match(auditDiagnostics[0].message, /vacuous/);
      checks.push('real impossible entry certificate', 'real possible entry certificate', 'vacuous proof diagnostic');
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
