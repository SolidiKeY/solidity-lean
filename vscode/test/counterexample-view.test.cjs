'use strict';
const test = require('node:test'), assert = require('node:assert/strict');
const {EventEmitter} = require('node:events');
const {createHash} = require('node:crypto');
const {evidence} = require('./witness.cjs');
const {activate, modelTree, declarationValues} = require('../src/features/counterexample-view.cjs');
const point = (line,character=0) => ({line,character});
const range = (a,b) => ({start:point(a),end:point(b)});
const row = (name='f', overrides={}) => ({source:'C.sol',contract:'C',function:name,status:'refuted',range:range(1,3),counterexample:evidence(),...overrides});
function harness() {
  const service = new EventEmitter(), subscriptions = [], handlers = {}, calls = [], events = {};
  const text = 'contract C {\nfunction f(uint x) public {\n}\n}';
  const doc = {uri:{toString:()=> 'file:///C.sol'},version:1,getText:()=>text,isClosed:false};
  const editor = {document:doc,selection:{active:point(2)},setDecorations:(_,v)=>calls.push(v)};
  let provider, pick;
  const listen = name => fn => {events[name]=fn;return {dispose(){delete events[name];}};};
  const vscode = {EventEmitter:class {event=()=>({dispose(){}});fire(){}dispose(){}},ThemeColor:class{},TreeItem:class{constructor(label){this.label=label;}},TreeItemCollapsibleState:{Collapsed:1,None:0},
    workspace:{textDocuments:[doc],onDidChangeTextDocument:listen('edit'),onDidCloseTextDocument:listen('close')},
    window:{activeTextEditor:editor,visibleTextEditors:[editor],createTextEditorDecorationType:()=>({dispose(){}}),createTreeView:(_,opts)=>{provider=opts.treeDataProvider;return {dispose(){}};},onDidChangeActiveTextEditor:listen('active'),showQuickPick:async items=>items[pick??0]},
    commands:{registerCommand:(name,fn)=>{handlers[name]=fn;return {dispose(){}};},executeCommand:async()=>{}}};
  service.request=async()=>[];
  activate({subscriptions},{vscode,service,output:{appendLine(){}}});
  const report = (rows, selection) => service.emit('report',{uri:doc.uri.toString(),version:doc.version,sourceHash:createHash('sha256').update(text).digest('hex'),report:{results:rows,errors:[]},selection});
  return {service,doc,editor,vscode,calls,events,report,provider,show:()=>handlers['solidityLean.showCounterexample'](),setPick:i=>{pick=i;},dispose:()=>subscriptions.slice().reverse().forEach(s=>s.dispose())};
}
// Backend wire format from sourceWitnessJson/fmtFoldShadow, not execution traces.
test('nested storage expands one level, including mapping defaults and array shadows',()=>{
  const tree=modelTree(row('f',{counterexample:evidence({initialStorage:'items = [{amount: 5}, {amount: 9} | past the end: {amount: 7}]; owners = {1: [3, 4], _: [0]}',initialLedger:[{address:'9',amount:'-2'}]})}));
  const storage=tree.at(-1).children;
  assert.equal(storage[0].children[0].children[0].value,'5');
  assert.equal(storage[0].children[2].label,'Past the end');
  assert.equal(storage[0].children[2].children[0].children[0].value,'7');
  assert.equal(storage[1].children[1].label,'_');
  assert.equal(storage[1].children[0].children[1].value,'4');
  assert.equal(tree[3].children[0].value,'-2');
});
test('empty model stays empty and extra transaction fields are not displayed',()=>{
  const m=evidence({arguments:[],initialStorage:'',initialLedger:[]});m.transaction.fake='invented';
  const tree=modelTree(row('f',{counterexample:m}));
  assert.equal(tree[0].children.length,0);assert.equal(tree.at(-1).children.length,0);
  assert.equal(tree[1].children.length,4);
});
test('current version only; edit clears tree and decorations; disposal detaches listeners',async()=>{
  const h=harness();h.report([row()]);await h.show();assert.equal(h.provider.getChildren().length,5);
  h.doc.version++;h.events.edit({document:h.doc});assert.deepEqual(h.provider.getChildren(),[]);assert.deepEqual(h.calls.at(-1),[]);
  h.service.emit('report',{uri:h.doc.uri.toString(),version:1,sourceHash:'stale',report:{results:[row()]}});
  await h.show();assert.deepEqual(h.provider.getChildren(),[]);h.dispose();assert.equal(h.service.listenerCount('report'),0);
});
test('two failures use cursor selection and command toggles the same model',async()=>{
  const h=harness();h.report([row('f'),row('g',{range:range(5,8),counterexample:evidence({initialBalance:'19'})})]);
  h.editor.selection.active=point(6);await h.show();assert.equal(h.provider.getChildren()[2].value,'19');
  const before=h.calls.length;await h.show();assert.equal(h.calls.length,before+1);assert.deepEqual(h.calls.at(-1),[]);h.dispose();
});
test('pending symbols cannot restore decorations after edit or selection change',async()=>{
  const h=harness();let resolve;h.service.request=()=>new Promise(r=>{resolve=r;});h.report([row()]);
  const pending=h.show();await new Promise(r=>setImmediate(r));h.doc.version++;h.events.edit({document:h.doc});resolve([]);await pending;
  assert.deepEqual(h.provider.getChildren(),[]);assert.deepEqual(h.calls.at(-1),[]);h.dispose();
});
test('compiler declaration ranges anchor parameters and storage, not body references',()=>{
  const text='contract C { uint x; function f(uint x, bool ok) public { x; } }';
  const pos=n=>point(0,n), doc={getText:()=>text,offsetAt:p=>p.character,positionAt:pos};
  const fnStart=text.indexOf('function'),storage=text.indexOf('x;');
  const r=row('f',{range:{start:pos(fnStart),end:pos(text.length-2)},counterexample:evidence({arguments:[{modelName:'p0',paramIndex:0,sourceName:'x',type:'uint',value:'7'},{modelName:'p1',paramIndex:1,sourceName:'ok',type:'bool',value:true}],initialStorage:'x = 9'})});
  const symbols=[{name:'C',children:[{name:'x',kind:13,selectionRange:{start:pos(storage)}},{name:'f',range:r.range}]}];
  const values=declarationValues(doc,r,symbols);
  assert.deepEqual(values.map(v=>[v.name,v.value]),[['x','7'],['ok','true'],['x','9']]);
  assert.equal(values[0].position.character,text.indexOf('x, bool'));
  assert.equal(values[2].position.character,storage);
});

test('function-specific replies preserve another failure and remove a newly proved one', async()=>{
  const h=harness();h.report([row('f'),row('g',{range:range(5,8)})]);
  const f=row('f',{status:'proved'});delete f.counterexample;h.report([f],{function:'f'});
  await h.show();assert.equal(h.provider.getChildren().length,5);
  const g=row('g',{status:'proved'});delete g.counterexample;h.report([g],{function:'g'});
  await h.show();assert.deepEqual(h.provider.getChildren(),[]);h.dispose();
});

test('two failures on one line use character positions', async()=>{
  const h=harness();h.report([row('f',{range:{start:point(0,0),end:point(0,10)}}),row('g',{range:{start:point(0,12),end:point(0,30)},counterexample:evidence({initialBalance:'22'})})]);
  h.editor.selection.active=point(0,18);await h.show();assert.equal(h.provider.getChildren()[2].value,'22');h.dispose();
});
test('switching editors during Quick Pick cancels old document selection', async()=>{
  const h=harness();h.report([row('f',{range:range(5,6)}),row('g',{range:range(8,9)})]);
  let pick;h.vscode.window.showQuickPick=items=>new Promise(resolve=>{pick=()=>resolve(items[0]);});
  const pending=h.show();h.vscode.window.activeTextEditor=undefined;h.events.active();pick();await pending;
  assert.deepEqual(h.provider.getChildren(),[]);h.dispose();
});
