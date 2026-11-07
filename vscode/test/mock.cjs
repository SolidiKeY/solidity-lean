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
class CancellationTokenSource {
  constructor(){this.listeners=new Set();this.cancelled=false;const self=this;this.token={get isCancellationRequested(){return self.cancelled;},onCancellationRequested(fn){self.listeners.add(fn);return{dispose(){self.listeners.delete(fn);}};}};}
  cancel(){if(this.cancelled)return;this.cancelled=true;for(const listener of [...this.listeners])listener();}
  dispose(){this.listeners.clear();}
}
const disposable = () => ({ dispose() {} });
function mock() {
  const commands = new Map(), events = {}, notices = [], logs = [], diagnosticMap = new Map(), runs = [];
  const doc = {
    uri: { scheme: 'file', fsPath: '/tmp/contract.sol', toString() { return pathToFileURL(this.fsPath).href; } },
    version: 1, isDirty: false, isClosed: false, text: 'contract C {}', getText() { return this.text; },
    async save() { this.isDirty = false; return true; }
  };
  const config = {},documentConfigs=new Map(),listeners=new Map();
  const subscribe=(name,fn)=>{const list=listeners.get(name)||[];list.push(fn);listeners.set(name,list);events[name]=(...args)=>list.slice().map(listener=>listener(...args));return{dispose(){const i=list.indexOf(fn);if(i>=0)list.splice(i,1);}};};
  const controller = {
    items: new Collection(), createTestItem: (id, label, uri) => ({ id, label, uri, children: new Collection() }),
    createRunProfile(name, kind, handler) { this.run = handler; return disposable(); },
    createTestRun() {
      const calls = [];
      const cancellation=new CancellationTokenSource(),run={token:cancellation.token,cancel:()=>cancellation.cancel()};
      for (const name of ['enqueued','started', 'passed', 'failed', 'errored', 'skipped', 'end']) run[name] = (...args) => calls.push([name, ...args]);
      run.calls = calls; runs.push(run); return run;
    }, dispose() {}
  };
  const vscode = {
    Range, CancellationTokenSource, Diagnostic: class { constructor(range, message, severity) { Object.assign(this, { range, message, severity }); } },
    DiagnosticSeverity: { Error: 0, Warning: 1 }, TestRunProfileKind: { Run: 1 }, ProgressLocation: { Notification: 1 },
    TestRunRequest: class { constructor(include){this.include=include;} },
    TestMessage: class { constructor(message) { this.message = message; } },
    MarkdownString: class { appendText(text) { this.value = text; } }, Hover: class { constructor(contents, range) { Object.assign(this, { contents, range }); } },
    tests: { createTestController: () => controller },
    languages: {
      createDiagnosticCollection: () => ({ set: (uri, value) => diagnosticMap.set(uri.toString(), value), delete: uri => diagnosticMap.delete(uri.toString()), dispose() {} }),
      registerHoverProvider(selector, provider) { events.hover = provider; return disposable(); }
    },
    commands: { registerCommand(name, fn) { commands.set(name, fn); return {dispose(){commands.delete(name);}}; },executeCommand(name,...args){return commands.get(name)?.(...args);} },
    window: {
      activeTextEditor: { document: doc }, showErrorMessage: message => notices.push(message),
      createOutputChannel: () => ({ appendLine: text => logs.push(text), show:()=>logs.push('output shown'), dispose() {} }),
      withProgress: async (options, task) => task({}, { isCancellationRequested: false, onCancellationRequested: disposable })
    },
    workspace: {
      isTrusted: true, getConfiguration: (_,uri) => ({ get: (key, fallback) => documentConfigs.get(uri?.toString())?.[key] ?? config[key] ?? fallback }),
      getWorkspaceFolder: () => ({ uri: { fsPath: require('node:path').resolve(__dirname,'../..') } }), asRelativePath: uri => uri.fsPath,
      findFiles: async () => [doc.uri], openTextDocument: async () => doc,
      onDidSaveTextDocument(fn) { return subscribe('save',fn); },
      onDidChangeTextDocument(fn) { return subscribe('change',fn); },
      onDidChangeConfiguration(fn) {return subscribe('configuration',fn);},
      onDidCloseTextDocument(fn) { return subscribe('close',fn); }
    }
  };
  return { vscode, doc, config, documentConfigs,subscribe, events, commands, notices, logs, diagnosticMap, controller, runs, context: { subscriptions: [] } };
}
const leaves=item=>[...item.children.values()].flatMap(child=>child.children.size?leaves(child):[child]);
module.exports = { mock, leaves };
