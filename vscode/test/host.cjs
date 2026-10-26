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
      const witnessSource = join(root, 'ModelWitness.sol');
      writeFileSync(witnessSource, 'pragma solidity ^0.8.34;\ncontract ModelWitness {\n/// @custom:key requires x == 2\n/// @custom:key ensures false\nfunction wrong(uint x) public pure {}\n}\n');
      await config.update('auditPreconditions', false, vscode.ConfigurationTarget.Global);
      await config.update('counterexamples', true, vscode.ConfigurationTarget.Global);
      const witnessDocument = await vscode.workspace.openTextDocument(witnessSource);
      await vscode.window.showTextDocument(witnessDocument);
      const witnessed = await api.verify(witnessDocument);
      assert.deepEqual(witnessed.errors, []);
      const wrong = witnessed.results.find(row => row.function === 'wrong');
      assert.equal(wrong.status, 'refuted');
      assert.equal(wrong.counterexample.arguments[0].value, '2');
      assert.equal(wrong.counterexample.arguments[0].sourceName, 'x');
      assert.match(wrong.counterexample.certificateDeclaration, /refuted$/);
      const modelDiagnostic = vscode.languages.getDiagnostics(witnessDocument.uri).find(d => d.code === 'refuted');
      assert.equal(modelDiagnostic.severity, vscode.DiagnosticSeverity.Error);
      assert.equal(modelDiagnostic.range.start.line, 4);
      const modelHovers = await vscode.commands.executeCommand('vscode.executeHoverProvider', witnessDocument.uri, new vscode.Position(4, 15));
      assert.ok(modelHovers.some(hover => hover.contents.some(content => /certified model prestate/.test((content.value || String(content)).replace(/&nbsp;/g, ' ')))),
        JSON.stringify({hovers:modelHovers,rows:witnessed.results.map(row => ({status:row.status,sourceId:row.sourceId,range:row.range}))}));
      checks.push('real exact-goal refutation certificate', 'real model argument source mapping', 'real model diagnostic and hover');
      const tupleSource = join(root, 'TupleMetrics.sol');
      writeFileSync(tupleSource, 'pragma solidity ^0.8.34;\ncontract TupleMetrics {\n/// @custom:key box\nfunction passes() public pure {\nuint n = 1;\n/// @custom:key invariant n <= 1\n/// @custom:key decreases (n, 0)\nwhile(n > 0) { n--; }\nassert(n == 0);\n}\nfunction rejected(bool flag) public pure {\n/// @custom:key invariant true\n/// @custom:key decreases (0, flag)\nwhile(false) {}\n}\n}\n');
      await config.update('counterexamples', false, vscode.ConfigurationTarget.Global);
      const tupleDocument = await vscode.workspace.openTextDocument(tupleSource);
      await vscode.window.showTextDocument(tupleDocument);
      const tuples = await api.verify(tupleDocument);
      assert.equal(tuples.results.find(row => row.function === 'passes').status, 'proved');
      const rejected = tuples.results.find(row => row.function === 'rejected');
      assert.ok(['error', 'unsupported', 'excluded'].includes(rejected.status));
      const tupleDiagnostic = vscode.languages.getDiagnostics(tupleDocument.uri).find(d => d.code === rejected.status);
      assert.ok(tupleDiagnostic);
      assert.equal(tupleDiagnostic.range.start.line, 10);
      const tupleHovers = await vscode.commands.executeCommand('vscode.executeHoverProvider', tupleDocument.uri, new vscode.Position(3, 15));
      assert.ok(tupleHovers.some(hover => hover.contents.some(content => /proved/.test(content.value || String(content)))));
      checks.push('real tuple-annotated safety proof', 'real invalid tuple component diagnostic', 'real tuple result hover');
      const shadowSource = join(root, 'Shadowing.sol');
      writeFileSync(shadowSource, 'pragma solidity ^0.8.34;\ncontract Shadowing {\nfunction passes() public pure { uint v = 1; { uint v = 2; assert(v == 2); } assert(v == 1); }\n/// @custom:key requires v == 2\n/// @custom:key ensures false\nfunction wrong(uint v, uint v_) public pure { { uint v = 7; assert(v == 7); } }\n}\n');
      await config.update('counterexamples', true, vscode.ConfigurationTarget.Global);
      const shadowDocument = await vscode.workspace.openTextDocument(shadowSource);
      await vscode.window.showTextDocument(shadowDocument);
      const shadowed = await api.verify(shadowDocument);
      assert.deepEqual(shadowed.errors, []);
      assert.equal(shadowed.results.find(row => row.function === 'passes').status, 'proved');
      const shadowWrong = shadowed.results.find(row => row.function === 'wrong');
      assert.equal(shadowWrong.status, 'refuted');
      assert.deepEqual(shadowWrong.counterexample.arguments.map(argument => argument.sourceName), ['v', 'v_']);
      assert.deepEqual(shadowWrong.counterexample.arguments.map(argument => argument.paramIndex), [0, 1]);
      assert.equal(shadowWrong.counterexample.arguments[0].value, '2');
      assert.match(shadowWrong.counterexample.arguments[0].modelName, /^solcLocal[0-9]+_*$/);
      const shadowDiagnostics = vscode.languages.getDiagnostics(shadowDocument.uri).filter(d => d.source === 'Solidity Lean');
      assert.equal(shadowDiagnostics.length, 1);
      assert.equal(shadowDiagnostics[0].code, 'refuted');
      assert.equal(shadowDiagnostics[0].range.start.line, 5);
      const shadowHovers = await vscode.commands.executeCommand('vscode.executeHoverProvider', shadowDocument.uri, new vscode.Position(5, 15));
      assert.ok(shadowHovers.some(hover => hover.contents.some(content => /certified model prestate/.test((content.value || String(content)).replace(/&nbsp;/g, ' ')))));
      checks.push('real lexical shadowing proof', 'real renamed witness source positions', 'real shadowed function diagnostic and hover');
      const tupleDiamondSource = join(root, 'TupleDiamond.sol');
      writeFileSync(tupleDiamondSource, `pragma solidity ^0.8.34;
contract TupleDiamond {
function defaultDiamond() public pure {
uint n = 1;
/// @custom:key invariant n <= 1
/// @custom:key decreases (n, 0)
while(n > 0) { n--; }
assert(n == 0);
}
function badEqualTuple() public pure {
uint n = 1;
/// @custom:key invariant n <= 1
/// @custom:key decreases (0, 0)
while(n > 0) { n--; }
assert(n == 0);
}
}
`);
      await config.update('counterexamples', false, vscode.ConfigurationTarget.Global);
      await config.update('auditPreconditions', false, vscode.ConfigurationTarget.Global);
      const diamondDocument = await vscode.workspace.openTextDocument(tupleDiamondSource);
      await vscode.window.showTextDocument(diamondDocument);
      const diamonds = await api.verify(diamondDocument);
      assert.deepEqual(diamonds.errors, []);
      const defaultDiamond = diamonds.results.find(row => row.function === 'defaultDiamond');
      assert.equal(defaultDiamond.tag, 'diamond', 'the positive test uses the ordinary default diamond modality');
      assert.equal(defaultDiamond.status, 'proved');
      const equalTuple = diamonds.results.find(row => row.function === 'badEqualTuple');
      assert.equal(equalTuple.tag, 'diamond');
      assert.equal(equalTuple.status, 'pending', 'an equal tuple cannot discharge the strict decrease VC');
      assert.equal(equalTuple.counterexample, undefined, 'an open decrease VC is not a certified refutation');
      const diamondDiagnostics = vscode.languages.getDiagnostics(diamondDocument.uri).filter(d => d.source === 'Solidity Lean');
      assert.equal(diamondDiagnostics.length, 1);
      assert.equal(diamondDiagnostics[0].code, 'pending');
      assert.equal(diamondDiagnostics[0].severity, vscode.DiagnosticSeverity.Warning);
      assert.equal(diamondDiagnostics[0].range.start.line, 9);
      const defaultHovers = await vscode.commands.executeCommand('vscode.executeHoverProvider', diamondDocument.uri, new vscode.Position(2, 15));
      assert.ok(defaultHovers.some(hover => hover.contents.some(content => /proved/.test(content.value || String(content)))));
      const equalHovers = await vscode.commands.executeCommand('vscode.executeHoverProvider', diamondDocument.uri, new vscode.Position(9, 15));
      assert.ok(equalHovers.some(hover => hover.contents.some(content => /pending/.test(content.value || String(content)))));
      assert.ok(equalHovers.every(hover => hover.contents.every(content => !/certified model prestate/.test((content.value || String(content)).replace(/&nbsp;/g, ' ')))));
      const diamondItems = [...api.controller.items.get(diamondDocument.uri.toString()).children].map(([, item]) => item);
      assert.equal(diamondItems.find(item => item.label === 'TupleDiamond.defaultDiamond()').description, 'proved');
      assert.equal(diamondItems.find(item => item.label === 'TupleDiamond.badEqualTuple()').description, 'pending');
      checks.push('real default-diamond tuple VC proof', 'real equal tuple pending diagnostic', 'real tuple diamond proof and pending hovers', 'real tuple diamond Test Explorer statuses');
      const filteredSource = join(root, 'FilteredHost.sol');
      writeFileSync(filteredSource, `pragma solidity ^0.8.34;
contract FilteredHost {
  /// @custom:key ensures \\result \\in uint(v; 1, 2; v > 1)
  function provesChoice() public pure returns(uint) { return 2; }
  /// @custom:key ensures \\result \\in uint(v; 1, 2; v > 1)
  function pendingChoice() public pure returns(uint) { return 1; }
  /// @custom:key ensures \\exists uint result; result == 1 && \\result == 1
  function captureResult() public pure returns(uint) { return 2; }
}
`);
      await config.update('counterexamples', false, vscode.ConfigurationTarget.Global);
      await config.update('auditPreconditions', false, vscode.ConfigurationTarget.Global);
      const filteredDocument = await vscode.workspace.openTextDocument(filteredSource);
      await vscode.window.showTextDocument(filteredDocument);
      const filtered = await api.verify(filteredDocument);
      assert.ok(filtered, 'a backend exit of 1 must retain the mixed source report');
      assert.equal(filtered.results.length, 3, 'a malformed sibling must not erase completed obligations');
      const filteredRows = new Map(filtered.results.map(row => [row.function, row]));
      assert.deepEqual([...filteredRows.keys()].sort(), ['captureResult', 'pendingChoice', 'provesChoice']);
      assert.ok(filtered.errors.some(error => error.stage === 'lean' && error.tool?.exitCode === 1),
        'the compiler failure must propagate alongside retained sibling rows');
      const filteredDiagnostics = vscode.languages.getDiagnostics(filteredDocument.uri).filter(d => d.source === 'Solidity Lean');
      const filteredItems = [...api.controller.items.get(filteredDocument.uri.toString()).children].map(([, item]) => item);
      assert.equal(filteredItems.length, 3);
      for (const [name, status, line] of [['provesChoice', 'proved', 3], ['pendingChoice', 'pending', 5], ['captureResult', 'error', 7]]) {
        const row = filteredRows.get(name);
        assert.equal(row.status, status, `${name}: ${row.reason}`);
        assert.equal(row.counterexample, undefined, 'no model evidence was requested');
        assert.ok(Number.isSafeInteger(row.sourceId) && row.sourceId >= 0 && row.sourceHash);
        const declarationRange = new vscode.Range(line, 2, line, filteredDocument.lineAt(line).text.length);
        assert.deepEqual(row.range, {
          start: {line, character: 2},
          end: {line, character: filteredDocument.lineAt(line).text.length},
        }, `${name}: preserve the actual compiler declaration range`);
        const item = filteredItems.find(item => item.label === `FilteredHost.${name}()`);
        assert.ok(item, `${name}: Test Explorer retains the sibling item`);
        assert.equal(item.description, status);
        assert.ok(item.range.isEqual(declarationRange));
        const rowHovers = await vscode.commands.executeCommand('vscode.executeHoverProvider', filteredDocument.uri, new vscode.Position(line, 20));
        assert.ok(rowHovers.some(hover => hover.range?.isEqual(declarationRange) && hover.contents.some(content => {
          const text = content.value || String(content);
          return text.includes(name) && text.includes(status);
        })), `${name}: actual hover provider retains its own status and source range`);
        assert.ok(rowHovers.every(hover => hover.contents.every(content =>
          !/certified model prestate/.test((content.value || String(content)).replace(/&nbsp;/g, ' ')))));
        const rowDiagnostic = filteredDiagnostics.find(d => d.code === status && d.range.isEqual(declarationRange));
        if (status === 'proved')
          assert.ok(!filteredDiagnostics.some(d => d.range.isEqual(declarationRange)), 'a proved sibling has no obligation diagnostic');
        else {
          assert.ok(rowDiagnostic, `${name}: diagnostic keeps its compiler range`);
          assert.equal(rowDiagnostic.severity, status === 'pending' ? vscode.DiagnosticSeverity.Warning : vscode.DiagnosticSeverity.Error);
        }
      }
      const captureDiagnostic = filteredDiagnostics.find(d => d.code === 'error' && d.range.start.line === 7);
      assert.match(captureDiagnostic.message, /reserved specification binder name result/);
      assert.ok(filteredDiagnostics.some(d => d.code === 'lean' && d.severity === vscode.DiagnosticSeverity.Error),
        'the backend compiler error remains visible as well as the per-function diagnostic');
      checks.push('real filtered membership proof and pending sibling', 'real reserved quantifier capture rejection',
        'real mixed-failure retained source ranges', 'real filtered diagnostics and hovers', 'real filtered Test Explorer statuses');
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
