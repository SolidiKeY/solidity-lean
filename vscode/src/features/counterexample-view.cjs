'use strict';
const {resolve} = require('node:path');
const {createHash} = require('node:crypto');
const {validateCounterexample, escapedText} = require('../counterexample.cjs');
const {tokens} = require('../solidity-text.cjs');
const hash = text => createHash('sha256').update(text).digest('hex');
// Split only at the current nesting level of the backend's fmtFoldShadow text.
function split(text, delimiter, keepEmpty = false) {
  const result = []; let depth = 0, start = 0;
  for (let i = 0; i < text.length; i++) {
    if ('[{'.includes(text[i])) depth++;
    if (']}'.includes(text[i])) depth--;
    if (depth < 0) return [text];
    if (!depth && text[i] === delimiter) {result.push(text.slice(start, i).trim()); start = i + 1;}
  }
  if (depth) return [text];
  result.push(text.slice(start).trim()); return keepEmpty ? result : result.filter(Boolean);
}
const node = (label, value, children = []) => ({label: escapedText(label), value: value === undefined ? undefined : escapedText(value), children});
function valueNode(label, value) {
  const text = String(value).trim(); let children = [];
  if (text.startsWith('[') && text.endsWith(']')) {
    const parts = split(text.slice(1, -1), '|', true);
    children = split(parts[0] || '', ',').map((v, i) => valueNode(`[${i}]`, v));
    if (parts.length === 2 && parts[1].startsWith('past the end:')) children.push(node('Past the end', undefined,
      split(parts[1].slice(13), ',').map((v, i) => valueNode(`[${children.length + i}]`, v))));
  } else if (text.startsWith('{') && text.endsWith('}')) {
    children = split(text.slice(1, -1), ',').map(entry => {
      const colon = entry.indexOf(':');
      return colon < 0 ? node(entry) : valueNode(entry.slice(0, colon).trim(), entry.slice(colon + 1));
    });
  }
  return node(label, text, children);
}
function storageEntries(text) {
  return split(text, ';').flatMap(entry => {
    const match = /^([A-Za-z_$][\w$]*) = (.+)$/s.exec(entry);
    return match ? [[match[1], match[2]]] : [];
  });
}
function modelTree(row) {
  validateCounterexample(row);
  if (row.status !== 'refuted') return [];
  const m = row.counterexample, storage = storageEntries(m.initialStorage);
  return [node('Arguments', undefined, m.arguments.map(a => valueNode(a.sourceName || a.modelName, a.value))),
    node('Transaction', undefined, ['msgSender','selfAddress','msgValue','timestamp'].map(k => valueNode(k,m.transaction[k]))),
    valueNode('Initial balance', m.initialBalance),
    node('Initial ledger', undefined, m.initialLedger.map(e => valueNode(e.address, e.amount))),
    node('Initial storage', storage.length ? undefined : m.initialStorage, storage.map(([k,v]) => valueNode(k,v)))];
}
const samePoint = (a,b) => a.line === b.line && a.character === b.character;
// Tokenize only the inheritance header; declaration ownership comes from the
// compiler's existing definition service, never from matching a base's spelling.
function baseReferences(doc, symbol) {
  if (!symbol.range || !symbol.selectionRange) return null;
  const start = doc.offsetAt(symbol.range.start);
  const ts = tokens(doc.getText().slice(start, doc.offsetAt(symbol.range.end))).filter(t => t.kind !== 'comment');
  let depth = 0, end = ts.length;
  for (let i = 0; i < ts.length; i++) {
    if (ts[i].text === '{' && !depth) {end = i; break;}
    if (ts[i].text === '(') depth++; if (ts[i].text === ')') depth--;
  }
  const header = ts.slice(0,end), is = header.findIndex(t => t.text === 'is');
  if (is < 0) return [];
  const refs = []; let i = is + 1;
  while (i < header.length) {
    if (header[i].kind !== 'word') return null;
    let name = header[i++];
    while (header[i]?.text === '.' && header[i+1]?.kind === 'word') {name = header[i+1]; i += 2;}
    refs.push(doc.positionAt(start + name.start));
    if (header[i]?.text === '(') {
      let nested = 1; i++;
      while (i < header.length && nested) {if (header[i].text === '(') nested++; if (header[i].text === ')') nested--; i++;}
      if (nested) return null;
    }
    if (i === header.length || header[i]?.text === 'layout') break;
    if (header[i++]?.text !== ',') return null;
  }
  return refs;
}
// Mirror the importer's checked right-to-left C3 ordering and stateRenames.
// This is location metadata only: values always come from initialStorage.
async function storageDeclarations(doc, row, symbols, service, openDocument, isCurrent = () => true) {
  const own = symbols.find(s => s.name === row.contract);
  const direct = new Map((own?.children || []).filter(s => s.kind === 13).map(s => [s.name,s]));
  if (!own) return {roots:direct, current:isCurrent};
  const documents = new Map([[doc.uri.toString(), {doc, symbols, version:doc.version, text:doc.getText()}]]), graph = new Map();
  const current = () => isCurrent() && [...documents.values()].every(s => !s.doc.isClosed && s.doc.version === s.version && s.doc.getText() === s.text);
  async function visit(record, symbol) {
    if (!current()) throw new Error('Counterexample declaration lookup became stale');
    const key = `${record.doc.uri}:${JSON.stringify(symbol.selectionRange?.start)}`;
    if (graph.has(key)) return graph.get(key);
    const entry = {record, symbol, parents:[], complete:false}; graph.set(key,entry);
    const refs = baseReferences(record.doc,symbol); if (!refs) return entry;
    for (const position of refs) {
      const result = await service.request('textDocument/definition',record.doc,{position});
      const location = Array.isArray(result) ? result.length === 1 ? result[0] : null : result;
      if (!location?.uri || !location.range || !current()) return entry;
      let target = documents.get(location.uri);
      if (!target) {
        if (!openDocument) return entry;
        const other = await openDocument(location.uri), version = other.version, text = other.getText();
        const otherSymbols = await service.request('textDocument/documentSymbol',other,{});
        if (other.version !== version || other.getText() !== text || other.isClosed) return entry;
        target = {doc:other,symbols:otherSymbols,version,text}; documents.set(location.uri,target);
      }
      const matches = target.symbols.filter(s => s.selectionRange && samePoint(s.selectionRange.start,location.range.start) && samePoint(s.selectionRange.end,location.range.end));
      if (matches.length !== 1) return entry;
      entry.parents.push(await visit(target,matches[0]));
    }
    entry.complete = true; return entry;
  }
  const root = await visit(documents.get(doc.uri.toString()),own), cache = new Map(), visiting = new Set();
  function linearize(entry) {
    if (!entry.complete || visiting.has(entry)) return null;
    if (cache.has(entry)) return cache.get(entry);
    visiting.add(entry);
    const parents = [...entry.parents].reverse(), orders = parents.map(linearize);
    if (orders.some(o => !o)) return null;
    const queues = [...orders.map(o => [...o]), [...parents]], order = [entry];
    while (queues.some(q => q.length)) {
      const head = queues.find(q => q.length && !queues.some(other => other.slice(1).includes(q[0])))?.[0];
      if (!head) return null;
      order.push(head); for (const q of queues) if (q[0] === head) q.shift();
    }
    visiting.delete(entry); cache.set(entry,order); return order;
  }
  const lineage = linearize(root);
  if (!lineage || !current()) return {roots:direct,current};
  const fields = [...lineage].reverse().flatMap(owner => (owner.symbol.children || []).filter(s => s.kind === 13).map(symbol => ({owner,symbol}))), taken = new Set(fields.map(f => f.symbol.name)), roots = new Map();
  fields.forEach(({owner,symbol},i) => {
    let name = symbol.name;
    if (fields.slice(i+1).some(f => f.symbol.name === name)) {
      name = `${name}_${owner.symbol.name}`; while (taken.has(name)) name += '_'; taken.add(name);
    }
    if (owner.record.doc.uri.toString() === doc.uri.toString()) roots.set(name,symbol);
  });
  return {roots,current};
}
function declarationValues(doc, row, symbols, storage) {
  const foreign = row.diagnosticSource && (!doc.uri?.fsPath || resolve(row.diagnosticSource) !== resolve(doc.uri.fsPath));
  const contract = symbols.find(s => s.name === row.contract);
  if (!contract) return [];
  const functions = (foreign ? [] : symbols).flatMap(s => s.children || []).filter(s => s.name === row.function && (!row.range || samePoint(s.range.start, row.range.start)));
  const fn = functions.length === 1 ? functions[0] : undefined, text = doc.getText();
  const offset = p => doc.offsetAt(p);
  const ts = tokens(fn ? text.slice(offset(fn.range.start), offset(fn.range.end)) : '').filter(t => t.kind !== 'comment');
  const open = ts.findIndex(t => t.text === '('); let depth = 0, index = 0; const params = [[]];
  for (const t of ts.slice(open + 1)) {
    if (t.text === ')' && !depth) break;
    if (t.text === ',' && !depth) {params.push([]); index++; continue;}
    params[index].push(t);
    if (t.text === '(') depth++; if (t.text === ')') depth--;
  }
  const result = [];
  for (const a of row.counterexample.arguments) {
    if (!fn || !Number.isSafeInteger(a.paramIndex)) continue;
    const param = params[a.paramIndex], last = param?.at(-1);
    if (a.sourceName === '' && param?.length) result.push({position:doc.positionAt(offset(fn.range.start) + param[0].start), name:a.modelName, value:String(a.value)});
    else if (last?.kind === 'word' && last.text === a.sourceName) result.push({position:doc.positionAt(offset(fn.range.start) + last.start), name:a.sourceName, value:String(a.value)});
  }
  for (const [name,value] of storageEntries(row.counterexample.initialStorage)) {
    const matches = storage ? [storage.get(name)].filter(Boolean) : (contract.children || []).filter(s => s.name === name && s.kind === 13);
    if (matches.length === 1) result.push({position:matches[0].selectionRange.start, name, value});
  }
  return result;
}
function activate(context, {vscode, service, output}) {
  const changed = new vscode.EventEmitter(), snapshots = new Map(); let selected, enabled = false, generation = 0, stopped = false;
  const decoration = vscode.window.createTextEditorDecorationType({after:{margin:'0 0 0 1.5em', color:new vscode.ThemeColor('editorCodeLens.foreground')}});
  const provider = {onDidChangeTreeData:changed.event, getChildren:element => element ? element.children : selected?.tree || [],
    getTreeItem(element) {const item = new vscode.TreeItem(element.label, element.children.length ? vscode.TreeItemCollapsibleState.Collapsed : vscode.TreeItemCollapsibleState.None); item.description = element.value; return item;}};
  const view = vscode.window.createTreeView('solidityLeanCounterexample', {treeDataProvider:provider});
  function clear() {generation++; selected = undefined; changed.fire(); for (const editor of vscode.window.visibleTextEditors) editor.setDecorations(decoration, []);}
  function receive(params) {
    const doc = vscode.workspace.textDocuments.find(d => d.uri.toString() === params.uri);
    if (!doc || doc.isClosed || doc.version !== params.version || hash(doc.getText()) !== params.sourceHash) return;
    try {
      const incoming = params.report.results; incoming.forEach(validateCounterexample);
      const old = snapshots.get(params.uri);
      const preserved = params.selection?.function && old?.version === params.version && old.sourceHash === params.sourceHash
        ? old.rows.filter(previous => !incoming.some(r => r.contract === previous.contract && (r.signature || r.function) === (previous.signature || previous.function))) : [];
      const rows = [...preserved, ...incoming.filter(r => r.status === 'refuted')];
      snapshots.set(params.uri, {version:params.version, sourceHash:params.sourceHash, rows});
      if (selected?.uri === params.uri) clear();
    } catch (error) {output.appendLine(`Counterexample: ${error.message}`);}
  }
  async function show() {
    const editor = vscode.window.activeTextEditor, doc = editor?.document;
    if (!doc) return;
    const initialGeneration = generation;
    const uri = doc.uri.toString(), snapshot = snapshots.get(uri);
    if (!snapshot || snapshot.version !== doc.version || snapshot.sourceHash !== hash(doc.getText())) {clear(); return;}
    const position = editor.selection.active;
    const before = (a,b) => a.line < b.line || a.line === b.line && a.character <= b.character;
    const containing = snapshot.rows.filter(r => r.range && before(r.range.start,position) && before(position,r.range.end));
    let row = containing.length === 1 ? containing[0] : undefined;
    if (!row && snapshot.rows.length === 1) row = snapshot.rows[0];
    if (!row && snapshot.rows.length > 1) row = (await vscode.window.showQuickPick(snapshot.rows.map(r => ({label:`${r.contract}.${r.signature || r.function}`, row:r}))))?.row;
    if (!row || stopped || generation !== initialGeneration || vscode.window.activeTextEditor !== editor || snapshots.get(uri) !== snapshot || doc.version !== snapshot.version) return;
    const toggle = selected?.row === row; enabled = toggle ? !enabled : true;
    clear(); selected = {uri, row, tree:modelTree(row)}; view.title = `${row.contract}.${row.signature || row.function}`; changed.fire();
    const epoch = generation;
    await vscode.commands.executeCommand('solidityLeanCounterexample.focus');
    if (!enabled || stopped || epoch !== generation) return;
    try {
      const symbols = await service.request('textDocument/documentSymbol', doc, {});
      if (stopped || epoch !== generation || doc.version !== snapshot.version || hash(doc.getText()) !== snapshot.sourceHash) return;
      const storage = await storageDeclarations(doc,row,symbols,service,uri => vscode.workspace.openTextDocument(vscode.Uri.parse(uri)),() => !stopped && epoch === generation && doc.version === snapshot.version && hash(doc.getText()) === snapshot.sourceHash);
      if (!storage.current()) return;
      const values = declarationValues(doc, row, symbols,storage.roots), lines = new Map();
      for (const value of values) {const list = lines.get(value.position.line) || []; list.push(`${value.name} = ${escapedText(value.value)}`); lines.set(value.position.line,list);}
      const decorations = [...lines].map(([line,values]) => ({range:doc.lineAt(line).range, renderOptions:{after:{contentText:values.join('; ')}}}));
      for (const target of vscode.window.visibleTextEditors) if (target.document === doc) target.setDecorations(decoration, decorations);
    } catch (error) {if (epoch === generation) output.appendLine(`Counterexample declarations: ${error.message}`);}
  }
  service.on('report', receive);
  const invalidate = params => {snapshots.delete(params.uri); if (selected?.uri === params.uri) clear();};
  service.on('invalidated', invalidate);
  const failed = () => {snapshots.clear(); clear();}; service.on('serverError', failed);
  context.subscriptions.push(changed, decoration, view,
    vscode.commands.registerCommand('solidityLean.showCounterexample', show),
    vscode.workspace.onDidChangeTextDocument(e => invalidate({uri:e.document.uri.toString()})),
    vscode.workspace.onDidCloseTextDocument(doc => invalidate({uri:doc.uri.toString()})),
    vscode.window.onDidChangeActiveTextEditor(() => clear()),
    {dispose() {stopped = true; clear(); snapshots.clear(); service.removeListener('report',receive); service.removeListener('invalidated',invalidate); service.removeListener('serverError',failed);}});
}
module.exports = {activate, split, valueNode, storageEntries, modelTree, declarationValues, baseReferences, storageDeclarations};
