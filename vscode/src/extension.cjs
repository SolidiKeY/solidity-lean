'use strict';
const { resolve, extname } = require('node:path');
const { createHash } = require('node:crypto');
const { runBackend } = require('./backend.cjs');
const model = require('./model.cjs');

const hash = text => createHash('sha256').update(text, 'utf8').digest('hex');

/** Injectable VS Code boundary; production and tests exercise the same controller. */
function createExtension(vscode, context, backend = runBackend) {
  const diagnostics = vscode.languages.createDiagnosticCollection('solidity-lean');
  const controller = vscode.tests.createTestController('solidityLean', 'Solidity Lean');
  const output = vscode.window.createOutputChannel('Solidity Lean');
  const active = new Map(), reports = new Map(), metadata = new Map();
  const key = uri => uri.toString();
  const isSolidity = doc => doc?.uri.scheme === 'file' && extname(doc.uri.fsPath).toLowerCase() === '.sol';
  const toRange = range => new vscode.Range(range.start.line, range.start.character, range.end.line, range.end.character);
  function settings(doc) {
    const cfg = vscode.workspace.getConfiguration('solidityLean', doc.uri);
    const workspace = vscode.workspace.getWorkspaceFolder(doc.uri)?.uri.fsPath;
    const configured = cfg.get('backendPath', '');
    if (!configured && !workspace) throw new Error('Set solidityLean.backendPath to the Solidity Lean repository directory');
    return { backendPath: resolve(workspace || '.', configured || '.'), nodePath: cfg.get('nodePath', 'node'), timeoutMs: cfg.get('timeoutMs', 600000) };
  }
  function cancel(uri) {
    if (uri) active.get(key(uri))?.abort();
    else for (const job of active.values()) job.abort();
  }
  function clear(uri) {
    cancel(uri);
    diagnostics.delete(uri);
    reports.delete(key(uri));
    const item = controller.items.get(key(uri));
    if (item) {
      item.children.forEach(child => metadata.delete(child.id));
      controller.items.delete(item.id);
      metadata.delete(item.id);
    }
  }
  function showError(error) {
    if (error.code === 'CANCELLED') return;
    output.appendLine(error.message);
    vscode.window.showErrorMessage(`Solidity Lean: ${error.message}`);
  }
  function publish(doc, report) {
    reports.set(key(doc.uri), report);
    const converted = model.diagnostics(report).filter(d => !d.source || resolve(d.source) === resolve(doc.uri.fsPath)).map(d => {
      const diag = new vscode.Diagnostic(toRange(d.range), d.message, d.severity === 'error' ? vscode.DiagnosticSeverity.Error : vscode.DiagnosticSeverity.Warning);
      diag.source = 'Solidity Lean'; diag.code = d.code;
      return diag;
    });
    diagnostics.set(doc.uri, converted);
    const fileId = key(doc.uri);
    let file = controller.items.get(fileId);
    if (!file) { file = controller.createTestItem(fileId, vscode.workspace.asRelativePath(doc.uri), doc.uri); controller.items.add(file); }
    metadata.set(fileId, { uri: doc.uri });
    const previous = [];
    file.children.forEach(item => previous.push(item.id));
    const items = report.results.map(row => {
      const id = `${fileId}#${encodeURIComponent(row.contract)}:${encodeURIComponent(row.signature || row.function)}`;
      const item = file.children.get(id) || controller.createTestItem(id, model.label(row), doc.uri);
      item.range = toRange(model.rangeOf(row));
      item.description = row.status;
      metadata.set(id, { uri: doc.uri, row });
      return item;
    });
    for (const id of previous) if (!items.some(item => item.id === id)) metadata.delete(id);
    file.children.replace(items);
  }
  async function verify(doc, options = {}) {
    if (!vscode.workspace.isTrusted) throw new Error('Verification requires a trusted workspace');
    if (!isSolidity(doc)) throw new Error('Open a Solidity file on disk to verify');
    if (doc.isDirty && !(await doc.save())) throw new Error('Save the Solidity file before verification');
    const config = settings(doc);
    const id = key(doc.uri), version = doc.version, text = doc.getText();
    cancel(doc.uri);
    const abort = new AbortController();
    active.set(id, abort);
    const registration = options.token?.onCancellationRequested(() => abort.abort());
    if (options.token?.isCancellationRequested) abort.abort();
    try {
      output.appendLine(`${options.listing ? 'Discovering' : 'Verifying'} ${doc.uri.fsPath}`);
      const report = await backend({ ...config, source: doc.uri.fsPath, listing: options.listing, contract: options.contract, function: options.function, signal: abort.signal });
      if (abort.signal.aborted || active.get(id) !== abort || doc.version !== version || doc.getText() !== text || doc.isClosed) return null;
      if (report.results.some(row => resolve(row.source) !== resolve(doc.uri.fsPath))) throw new Error('Verifier report refers to a different source file');
      if (report.results.some(row => row.sourceHash !== hash(text))) throw new Error('Verifier source hash does not match the open file; use a current backend and save the file');
      // An individual test updates only its own row, retaining sibling obligations.
      const existing = reports.get(id);
      const merged = options.function && existing ? {
        ...report,
        results: [...existing.results.filter(old => !report.results.some(row => row.contract === old.contract && (row.signature || row.function) === (old.signature || old.function))), ...report.results]
      } : report;
      publish(doc, merged);
      for (const row of report.results) output.appendLine(model.detail(row));
      for (const error of report.errors) output.appendLine(`Error: ${error.reason}`);
      return report;
    } finally {
      registration?.dispose();
      if (active.get(id) === abort) active.delete(id);
    }
  }
  async function activeCommand(listing) {
    const doc = vscode.window.activeTextEditor?.document;
    try {
      await vscode.window.withProgress({ location: vscode.ProgressLocation.Notification, title: listing ? 'Discovering Solidity obligations' : 'Verifying Solidity', cancellable: true }, (_, token) => verify(doc, { listing, token }));
    } catch (error) { showError(error); }
  }
  async function discover() {
    if (!vscode.workspace.isTrusted) return;
    const uris = await vscode.workspace.findFiles('**/*.sol', '**/{.git,.lake,node_modules}/**', 200);
    for (const uri of uris) {
      try { await verify(await vscode.workspace.openTextDocument(uri), { listing: true }); }
      catch (error) { showError(error); }
    }
  }
  controller.resolveHandler = async item => { if (!item) await discover(); };
  controller.refreshHandler = discover;
  controller.createRunProfile('Verify', vscode.TestRunProfileKind.Run, async (request, token) => {
    const run = controller.createTestRun(request);
    const items = request.include || [...controller.items];
    const excluded = new Set((request.exclude || []).map(item => item.id));
    async function runItem(item) {
      if (excluded.has(item.id)) return;
      const meta = metadata.get(item.id);
      if (!meta) return;
      if (!meta.row) {
        for (const [, child] of item.children) await runItem(child);
        return;
      }
      if (token.isCancellationRequested) { run.skipped(item); return; }
      run.started(item);
      try {
        const doc = await vscode.workspace.openTextDocument(meta.uri);
        const report = await verify(doc, { contract: meta.row.contract, function: meta.row.signature || meta.row.function, token });
        if (!report) { run.skipped(item); return; }
        const row = report.results.find(row => row.contract === meta.row.contract && (row.signature || row.function) === (meta.row.signature || meta.row.function));
        if (report.errors.length || !row) run.errored(item, new vscode.TestMessage(report.errors.map(e => e.reason).join('\n') || 'Verifier returned no selected obligation'));
        else {
          const kind = model.resultKind(row);
          if (kind === 'passed') run.passed(item, row.elapsedMs);
          else if (kind === 'skipped') run.skipped(item);
          else run[kind](item, new vscode.TestMessage(model.detail(row)), row.elapsedMs);
        }
      } catch (error) {
        if (error.code === 'CANCELLED') run.skipped(item);
        else run.errored(item, new vscode.TestMessage(error.message));
      }
    }
    try {
      for (const entry of items) await runItem(Array.isArray(entry) ? entry[1] : entry);
    } finally { run.end(); }
  }, true);
  context.subscriptions.push(
    diagnostics, controller, output,
    vscode.commands.registerCommand('solidityLean.verify', () => activeCommand(false)),
    vscode.commands.registerCommand('solidityLean.list', () => activeCommand(true)),
    vscode.commands.registerCommand('solidityLean.cancel', () => cancel()),
    vscode.workspace.onDidSaveTextDocument(doc => {
      if (isSolidity(doc) && vscode.workspace.getConfiguration('solidityLean', doc.uri).get('verifyOnSave', false)) verify(doc).catch(showError);
    }),
    vscode.workspace.onDidChangeTextDocument(event => { if (event.contentChanges.length) clear(event.document.uri); }),
    vscode.workspace.onDidCloseTextDocument(doc => clear(doc.uri)),
    vscode.languages.registerHoverProvider({ scheme: 'file', pattern: '**/*.sol' }, {
      provideHover(doc, position) {
        const row = reports.get(key(doc.uri))?.results.find(row => toRange(model.rangeOf(row)).contains(position));
        if (!row) return null;
        const markdown = new vscode.MarkdownString();
        markdown.appendText(model.detail(row));
        return new vscode.Hover(markdown, toRange(model.rangeOf(row)));
      }
    }),
    { dispose: () => cancel() }
  );
  return { verify, cancel, controller, diagnostics, reports };
}
function activate(context) { return createExtension(require('vscode'), context); }
module.exports = { activate, createExtension };
