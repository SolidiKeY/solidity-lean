'use strict';
const {resolve} = require('node:path');
const {createHash} = require('node:crypto');
const {validateCounterexample, escapedText} = require('../counterexample.cjs');
const {tokens} = require('../solidity-text.cjs');
const hash = text => createHash('sha256').update(text).digest('hex');
// Split only at the current nesting level of the backend's fmtFoldShadow text.
function split(text, delimiter) {
  const result = []; let depth = 0, start = 0;
  for (let i = 0; i < text.length; i++) {
    if ('[{'.includes(text[i])) depth++;
    if (']}'.includes(text[i])) depth--;
    if (depth < 0) return [text];
    if (!depth && text[i] === delimiter) {result.push(text.slice(start, i).trim()); start = i + 1;}
  }
  if (depth) return [text];
  result.push(text.slice(start).trim()); return result.filter(Boolean);
}
const node = (label, value, children = []) => ({label: escapedText(label), value: value === undefined ? undefined : escapedText(value), children});
function valueNode(label, value) {
  const text = String(value).trim(); let children = [];
  if (text.startsWith('[') && text.endsWith(']')) {
    const parts = split(text.slice(1, -1), '|');
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
function declarationValues(doc, row, symbols) {
  if (row.diagnosticSource && (!doc.uri?.fsPath || resolve(row.diagnosticSource) !== resolve(doc.uri.fsPath))) return [];
  const contract = symbols.find(s => s.name === row.contract);
  if (!contract) return [];
  const functions = symbols.flatMap(s => s.children || []).filter(s => s.name === row.function && (!row.range || samePoint(s.range.start, row.range.start)));
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
    if (!fn || !Number.isSafeInteger(a.paramIndex) || !a.sourceName) continue;
    const param = params[a.paramIndex], last = param?.at(-1);
    if (last?.kind === 'word' && last.text === a.sourceName) result.push({position:doc.positionAt(offset(fn.range.start) + last.start), name:a.sourceName, value:String(a.value)});
  }
  for (const [name,value] of storageEntries(row.counterexample.initialStorage)) {
    const matches = (contract.children || []).filter(s => s.name === name && [7,8,13,14].includes(s.kind));
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
    const uri = doc.uri.toString(), snapshot = snapshots.get(uri);
    if (!snapshot || snapshot.version !== doc.version || snapshot.sourceHash !== hash(doc.getText())) {clear(); return;}
    let row = snapshot.rows.find(r => r.range && editor.selection.active.line >= r.range.start.line && editor.selection.active.line <= r.range.end.line);
    if (!row && snapshot.rows.length === 1) row = snapshot.rows[0];
    if (!row && snapshot.rows.length > 1) row = (await vscode.window.showQuickPick(snapshot.rows.map(r => ({label:`${r.contract}.${r.signature || r.function}`, row:r}))))?.row;
    if (!row || stopped || snapshots.get(uri) !== snapshot || doc.version !== snapshot.version) return;
    const toggle = selected?.row === row; enabled = toggle ? !enabled : true;
    clear(); selected = {uri, row, tree:modelTree(row)}; view.title = `${row.contract}.${row.signature || row.function}`; changed.fire();
    const epoch = generation;
    await vscode.commands.executeCommand('solidityLeanCounterexample.focus');
    if (!enabled || stopped || epoch !== generation) return;
    try {
      const symbols = await service.request('textDocument/documentSymbol', doc, {});
      if (stopped || epoch !== generation || doc.version !== snapshot.version || hash(doc.getText()) !== snapshot.sourceHash) return;
      const values = declarationValues(doc, row, symbols), lines = new Map();
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
module.exports = {activate, split, valueNode, storageEntries, modelTree, declarationValues};
