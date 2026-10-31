'use strict';
const { resolve, extname } = require('node:path');
const { createHash } = require('node:crypto');
const { runBackend } = require('./backend.cjs');
const model = require('./model.cjs');
const { validateCounterexample } = require('./counterexample.cjs');

const hash = text => createHash('sha256').update(text, 'utf8').digest('hex');

/** Injectable VS Code boundary; production and tests exercise the same controller. */
function createExtension(vscode, context, backend = runBackend, service = null) {
  const diagnostics = vscode.languages.createDiagnosticCollection('solidity-lean');
  const controller = vscode.tests.createTestController('solidityLean', 'Solidity Lean');
  const output = vscode.window.createOutputChannel('Solidity Lean');
  const active = new Map(), saving = new Map(), reports = new Map(), metadata = new Map(), documents = new Map();
  let editorServices;
  let discoveryVersion = 0;
  const key = uri => uri.toString();
  const isSolidity = doc => doc?.uri.scheme === 'file' && extname(doc.uri.fsPath).toLowerCase() === '.sol';
  const toRange = range => new vscode.Range(range.start.line, range.start.character, range.end.line, range.end.character);
  function settings(doc) {
    const cfg = vscode.workspace.getConfiguration('solidityLean', doc.uri);
    const workspace = vscode.workspace.getWorkspaceFolder(doc.uri)?.uri.fsPath;
    const configured = cfg.get('backendPath', '');
    if (!configured && !workspace) throw new Error('Set solidityLean.backendPath to the Solidity Lean repository directory');
    const automatic = cfg.get('verifyOnSave', false) ? 'onsave' : cfg.get('automaticVerification', 'never');
    return { backendPath: resolve(workspace || '.', configured || '.'), nodePath: cfg.get('nodePath', 'node'), timeoutMs: cfg.get('timeoutMs', 600000), auditPreconditions: cfg.get('auditPreconditions', false), counterexamples: cfg.get('counterexamples', false),
      workers: cfg.get('workers', 1), automaticVerification: {onchange:'change',onsave:'save',never:'never'}[automatic] || 'never' };
  }
  function cancel(uri) {
    service?.cancel(uri);
    if (uri) { saving.delete(key(uri)); active.get(key(uri))?.abort(); }
    else {
      discoveryVersion++;
      saving.clear();
      for (const job of active.values()) job.abort();
    }
  }
  function clear(uri) {
    cancel(uri);
    diagnostics.delete(uri);
    reports.delete(key(uri));
    editorServices?.clear(uri);
    const item = controller.items.get(key(uri));
    if (item) {
      item.children.forEach(child => metadata.delete(child.id));
      controller.items.delete(item.id);
      metadata.delete(item.id);
    }
  }
  function showError(error) {
    if (error.code === 'CANCELLED' || [-32800,-32801].includes(error.code)) return;
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
    if (!service) diagnostics.set(doc.uri, converted);
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
      item.description = model.status(row);
      metadata.set(id, { uri: doc.uri, row });
      return item;
    });
    for (const id of previous) if (!items.some(item => item.id === id)) metadata.delete(id);
    file.children.replace(items);
  }
  function accept(doc, report, config, options = {}) {
    if (report.results.some(row => resolve(row.source) !== resolve(doc.uri.fsPath))) throw new Error('Verifier report refers to a different source file');
    const hashes = new Set([hash(doc.getText()), hash('\uFEFF' + doc.getText())]);
    if (report.results.some(row => !hashes.has(row.sourceHash))) throw new Error('Verifier source hash does not match the open file; use a current backend and save the file');
    for (const row of report.results) validateCounterexample(row);
    if ((!config.counterexamples || options.listing) && report.results.some(row => row.status === 'refuted')) throw new Error('Verifier returned unrequested certified model prestate evidence');
    const existing = reports.get(key(doc.uri));
    const merged = options.function && existing ? {...report,results:[...existing.results.filter(old => !report.results.some(row => row.contract === old.contract && (row.signature || row.function) === (old.signature || old.function))),...report.results]} : report;
    publish(doc, merged);
  }
  async function verify(doc, options = {}) {
    if (!vscode.workspace.isTrusted) throw new Error('Verification requires a trusted workspace');
    if (!isSolidity(doc)) throw new Error('Open a Solidity file on disk to verify');
    documents.set(key(doc.uri), doc);
    const cancellationVersion = discoveryVersion;
    const request = {}, requestId = key(doc.uri);
    saving.set(requestId, request);
    try {
      const superseded = () => saving.get(requestId) !== request || cancellationVersion !== discoveryVersion || options.token?.isCancellationRequested || doc.isClosed;
      let attempts = 0;
      while (!service && doc.isDirty) {
        const saved = await doc.save();
        if (superseded()) return null;
        if (!saved) throw new Error('Save the Solidity file before verification');
        // VS Code can resolve a joined save for an older buffer snapshot.
        // Complete the current save before capturing the backend's source hash.
        if (++attempts >= 3 && doc.isDirty) throw new Error('The Solidity file is still changing; retry verification after saving');
      }
      // Edits, closure, cancellation or a newer request can supersede this
      // request while VS Code is saving, before an active backend exists.
      if (superseded()) return null;
    } finally { if (saving.get(requestId) === request) saving.delete(requestId); }
    const config = settings(doc);
    const id = key(doc.uri), version = doc.version, text = doc.getText();
    cancel(doc.uri);
    const abort = new AbortController();
    active.set(id, abort);
    const registration = options.token?.onCancellationRequested(() => abort.abort());
    if (options.token?.isCancellationRequested) abort.abort();
    try {
      output.appendLine(`${options.listing ? 'Discovering' : 'Verifying'} ${doc.uri.fsPath}`);
      const report = await backend({ ...config, ...(service ? {document:doc} : {}), source: doc.uri.fsPath, listing: options.listing, contract: options.contract, function: options.function, signal: abort.signal });
      if (abort.signal.aborted || active.get(id) !== abort || doc.version !== version || doc.getText() !== text || doc.isClosed) return null;
      accept(doc, report, config, options);
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
    const generation = ++discoveryVersion;
    const uris = await vscode.workspace.findFiles('**/*.sol', '**/{.git,.lake,node_modules}/**');
    for (const uri of uris) {
      if (generation !== discoveryVersion) break;
      try {
        const doc = await vscode.workspace.openTextDocument(uri);
        if (generation !== discoveryVersion) break;
        await verify(doc, { listing: true });
      }
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
        // Publishing each result replaces this collection. Iterate the run's snapshot.
        for (const [, child] of [...item.children]) await runItem(child);
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
      if (service && isSolidity(doc)) service.save(doc);
      else if (isSolidity(doc) && vscode.workspace.getConfiguration('solidityLean', doc.uri).get('verifyOnSave', false)) verify(doc).catch(showError);
    }),
    vscode.workspace.onDidChangeTextDocument(event => {
      if (event.contentChanges.length) {clear(event.document.uri);if(service && isSolidity(event.document)) {documents.set(key(event.document.uri),event.document);service.open(event.document).catch(showError);}}
    }),
    vscode.workspace.onDidCloseTextDocument(doc => {clear(doc.uri);documents.delete(key(doc.uri));service?.close(doc.uri);}),
    vscode.languages.registerHoverProvider({ scheme: 'file', pattern: '**/*.sol' }, {
      provideHover(doc, position, token) {
        if (service) {
          const controller=new AbortController(),registration=token?.onCancellationRequested(()=>controller.abort());
          if(token?.isCancellationRequested)controller.abort();
          return service.request('textDocument/hover', doc, {position}, {signal:controller.signal}).then(result => {
          if (!result) return null;
          const markdown=new vscode.MarkdownString();markdown.appendText(result.contents.value);
          return new vscode.Hover(markdown,toRange(result.range));
        }).catch(error => {if(![-32800,-32801].includes(error.code))showError(error);return null;}).finally(()=>registration?.dispose());
        }
        const matches = reports.get(key(doc.uri))?.results.filter(row => toRange(model.rangeOf(row)).contains(position));
        // A synthesized constructor spans the contract. Prefer the function
        // declaration under the cursor to that broader deployment result.
        const row = matches?.find(row => Number.isSafeInteger(row.sourceId) && row.sourceId >= 0) || matches?.[0];
        if (!row) return null;
        const markdown = new vscode.MarkdownString();
        markdown.appendText(model.detail(row));
        return new vscode.Hover(markdown, toRange(model.rangeOf(row)));
      }
    }),
    { dispose: () => cancel() }
  );
  if(service) {
    editorServices=require('./editor-services.cjs').install(vscode,context,service,showError);
    const open=doc=>{if(isSolidity(doc)){documents.set(key(doc.uri),doc);service.open(doc).catch(showError);}};
    const receive=params=>{
      const doc=documents.get(params.uri);if(!doc||doc.isClosed||doc.version!==params.version||hash(doc.getText())!==params.sourceHash)return;
      try{accept(doc,params.report,settings(doc),params.selection);}catch(error){showError(error);}
    };
    const receiveDiagnostics=params=>{
      const doc=documents.get(params.uri);if(!doc||doc.isClosed||doc.version!==params.version)return;
      diagnostics.set(doc.uri,params.diagnostics.map(row=>{const d=new vscode.Diagnostic(toRange(row.range),row.message,row.severity-1);d.source=row.source;d.code=row.code;return d;}));
    };
    service.on('report',receive);service.on('diagnostics',receiveDiagnostics);service.on('serverError',showError);service.on('log',message=>output.appendLine(message));
    context.subscriptions.push(vscode.workspace.onDidOpenTextDocument(open),
      vscode.commands.registerCommand('solidityLean.restartServer',async()=>{cancel();for(const doc of documents.values())clear(doc.uri);await service.restart();for(const doc of documents.values())open(doc);}),
      vscode.workspace.onDidChangeConfiguration(event=>{if(event.affectsConfiguration('solidityLean')){cancel();for(const doc of documents.values())clear(doc.uri);service.restart().then(()=>{for(const doc of documents.values())open(doc);}).catch(showError);}}),
      {dispose(){service.removeListener('report',receive);service.removeListener('diagnostics',receiveDiagnostics);service.removeListener('serverError',showError);}});
    for(const doc of vscode.workspace.textDocuments)open(doc);
  }
  let disposed=false;
  return { verify, cancel, controller, diagnostics, reports, service,
    async dispose(){if(disposed)return;disposed=true;cancel();for(const item of context.subscriptions)item.dispose();await service?.dispose();} };
}
let runtime;
function activate(context) {
  const vscode=require('vscode');
  const configuration=doc=>{
    if(!vscode.workspace.isTrusted)throw new Error('Language services require a trusted workspace');
    const cfg=vscode.workspace.getConfiguration('solidityLean',doc.uri),workspace=vscode.workspace.getWorkspaceFolder(doc.uri)?.uri.fsPath;
    const configured=cfg.get('backendPath','');if(!configured&&!workspace)throw new Error('Set solidityLean.backendPath to the repository directory');
    return {backendPath:resolve(workspace||'.',configured||'.'),nodePath:cfg.get('nodePath','node'),timeoutMs:cfg.get('timeoutMs',600000),workers:cfg.get('workers',1),
      automaticVerification:cfg.get('verifyOnSave',false)?'save':({onchange:'change',onsave:'save',never:'never'}[cfg.get('automaticVerification','never')]||'never'),
      counterexamples:cfg.get('counterexamples',false),auditPreconditions:cfg.get('auditPreconditions',false)};
  };
  const service=new (require('./lsp-client.cjs').LanguageServers)(configuration);
  const api=createExtension(vscode,context,args=>service.verify(args),service);
  context.subscriptions.push({dispose:()=>service.dispose()});runtime=api;return api;
}
function deactivate(){return runtime?.dispose();}
module.exports = { activate, deactivate, createExtension };
