'use strict';
const { pathToFileURL } = require('node:url');
class Collection extends Map {
  add(item) { this.set(item.id, item); }
  replace(items) { this.clear(); items.forEach(item => this.add(item)); }
}
class Range {
  constructor(sl, sc, el, ec) { this.start = { line: sl, character: sc }; this.end = { line: el, character: ec }; }
  contains(p) { return (p.line > this.start.line || p.line === this.start.line && p.character >= this.start.character) && (p.line < this.end.line || p.line === this.end.line && p.character <= this.end.character); }
}
const disposable = () => ({ dispose() {} });
function mock() {
  const commands = new Map(), events = {}, notices = [], logs = [], diagnosticMap = new Map(), runs = [];
  const doc = {
    uri: { scheme: 'file', fsPath: '/tmp/contract.sol', toString() { return pathToFileURL(this.fsPath).href; } },
    version: 1, isDirty: false, isClosed: false, text: 'contract C {}', getText() { return this.text; },
    async save() { this.isDirty = false; return true; }
  };
  const config = {};
  const controller = {
    items: new Collection(), createTestItem: (id, label, uri) => ({ id, label, uri, children: new Collection() }),
    createRunProfile(name, kind, handler) { this.run = handler; return disposable(); },
    createTestRun() {
      const calls = [];
      const run = {};
      for (const name of ['started', 'passed', 'failed', 'errored', 'skipped', 'end']) run[name] = (...args) => calls.push([name, ...args]);
      run.calls = calls; runs.push(run); return run;
    }, dispose() {}
  };
  const vscode = {
    Range, Diagnostic: class { constructor(range, message, severity) { Object.assign(this, { range, message, severity }); } },
    DiagnosticSeverity: { Error: 0, Warning: 1 }, TestRunProfileKind: { Run: 1 }, ProgressLocation: { Notification: 1 },
    TestMessage: class { constructor(message) { this.message = message; } },
    MarkdownString: class { appendText(text) { this.value = text; } }, Hover: class { constructor(contents, range) { Object.assign(this, { contents, range }); } },
    tests: { createTestController: () => controller },
    languages: {
      createDiagnosticCollection: () => ({ set: (uri, value) => diagnosticMap.set(uri.toString(), value), delete: uri => diagnosticMap.delete(uri.toString()), dispose() {} }),
      registerHoverProvider(selector, provider) { events.hover = provider; return disposable(); }
    },
    commands: { registerCommand(name, fn) { commands.set(name, fn); return disposable(); } },
    window: {
      activeTextEditor: { document: doc }, showErrorMessage: message => notices.push(message),
      createOutputChannel: () => ({ appendLine: text => logs.push(text), dispose() {} }),
      withProgress: async (options, task) => task({}, { isCancellationRequested: false, onCancellationRequested: disposable })
    },
    workspace: {
      isTrusted: true, getConfiguration: () => ({ get: (key, fallback) => config[key] ?? fallback }),
      getWorkspaceFolder: () => ({ uri: { fsPath: '/workspace/solidity-lean' } }), asRelativePath: uri => uri.fsPath,
      findFiles: async () => [doc.uri], openTextDocument: async () => doc,
      onDidSaveTextDocument(fn) { events.save = fn; return disposable(); },
      onDidChangeTextDocument(fn) { events.change = fn; return disposable(); },
      onDidCloseTextDocument(fn) { events.close = fn; return disposable(); }
    }
  };
  return { vscode, doc, config, events, commands, notices, logs, diagnosticMap, controller, runs, context: { subscriptions: [] } };
}
module.exports = { mock };
