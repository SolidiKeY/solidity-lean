'use strict';
const test = require('node:test'), assert = require('node:assert/strict');
const {EventEmitter} = require('node:events');
const {createHash} = require('node:crypto');
const {evidence} = require('./witness.cjs');
const {activate, modelTree, declarationValues, storageDeclarations} = require('../src/features/counterexample-view.cjs');
const point = (line,character=0) => ({line,character});
const range = (a,b) => ({start:point(a),end:point(b)});
const row = (name='f', overrides={}) => ({source:'C.sol',contract:'C',function:name,status:'refuted',range:range(1,3),counterexample:evidence(),...overrides});
function harness(text = 'contract C {\nfunction f(uint x) public {\n}\n}') {
  const service = new EventEmitter(), subscriptions = [], handlers = {}, calls = [], events = {};
  const doc = {uri:{toString:()=> 'file:///C.sol'},version:1,getText:()=>text,isClosed:false,
    offsetAt:p=>text.split('\n').slice(0,p.line).reduce((n,line)=>n+line.length+1,0)+p.character,
    positionAt:n=>{const lines=text.slice(0,n).split('\n');return point(lines.length-1,lines.at(-1).length);},
    lineAt:line=>({range:{start:point(line),end:point(line,text.split('\n')[line].length)}})};
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

test('unnamed parameters use their returned parameter index',()=>{
  const text='function f(uint, bool ok) public {}',doc={getText:()=>text,offsetAt:p=>p.character,positionAt:n=>point(0,n)};
  const r=row('f',{range:{start:point(0),end:point(0,text.length)},counterexample:evidence({arguments:[{modelName:'p0',paramIndex:0,sourceName:'',type:'uint',value:'12'}],initialStorage:''})});
  const values=declarationValues(doc,r,[{name:'C',children:[{name:'f',range:r.range}]}]);
  assert.deepEqual(values,[{position:point(0,text.indexOf('uint')),name:'p0',value:'12'}]);
});

test('command renders the returned value after its parameter line and toggles it off',async()=>{
  const h=harness();h.service.request=async()=>[{name:'C',children:[{name:'f',range:range(1,3)}]}];
  h.report([row('f',{counterexample:evidence({arguments:[{modelName:'p0',paramIndex:0,sourceName:'x',type:'uint',value:'17'}],initialStorage:''})})]);
  await h.show();assert.deepEqual(h.calls.at(-1),[{range:h.doc.lineAt(1).range,renderOptions:{after:{contentText:'x = 17'}}}]);
  await h.show();assert.deepEqual(h.calls.at(-1),[]);h.dispose();
});
test('edit while focusing the tree prevents an obsolete declaration request',async()=>{
  const h=harness();let focus,requests=0;
  h.vscode.commands.executeCommand=()=>new Promise(resolve=>{focus=resolve;});h.service.request=async()=>{requests++;return [];};
  h.report([row()]);const pending=h.show();h.doc.version++;h.events.edit({document:h.doc});focus();await pending;
  assert.equal(requests,0);assert.deepEqual(h.provider.getChildren(),[]);assert.deepEqual(h.calls.at(-1),[]);h.dispose();
});

test('empty live arrays retain shadow slots as past-the-end values',()=>{
  const tree=modelTree(row('f',{counterexample:evidence({initialStorage:'items = [ | past the end: 7, {amount: 9}]; empty = []; nested = {_: [ | past the end: 3]}'})}));
  const storage=tree.at(-1).children,items=storage[0].children;
  assert.equal(items.length,1);assert.equal(items[0].label,'Past the end');
  assert.deepEqual(items[0].children.map(n=>n.label),['[0]','[1]']);
  assert.equal(items[0].children[0].value,'7');assert.equal(items[0].children[1].children[0].value,'9');
  assert.deepEqual(storage[1].children,[]);
  assert.equal(storage[2].children[0].children[0].label,'Past the end');
  assert.equal(storage[2].children[0].children[0].children[0].value,'3');
});

// Pinned compiler ownership/locations plus recorded wire-format model fields;
// the values are transport fixtures, not kernel/EVM or visual UI evidence.
async function compilerDocuments(sources, main, run) {
  const fs=require('node:fs'),path=require('node:path'),os=require('node:os'),{pathToFileURL}=require('node:url'),lang=require('../src/language-services.cjs');
  const directory=fs.mkdtempSync(path.join(os.tmpdir(),'counterexample-inheritance-'));
  try {
    for (const [name,text] of Object.entries(sources)) fs.writeFileSync(path.join(directory,name),text);
    const {compileFixture}=await import('../../scripts/solc-ast.mjs');
    const compiled=compileFixture({args:['--source',path.join(directory,main),'--out',path.join(directory,'out.json'),'--no-wrapper'],sourceBytes:Buffer.from(sources[main]),analysisOnly:true,quiet:true});
    const files=compiled.project?.files || Object.fromEntries(Object.keys(compiled.rawAsts).map(name=>[name,{path:path.join(directory,name),text:sources[name]}])),documents=new Map(),indices=new Map();
    for (const [name,ast] of Object.entries(compiled.rawAsts)) {
      const file=files[name],text=file.text,uri=pathToFileURL(file.path),doc={uri,version:1,isClosed:false,getText:()=>text,offsetAt:p=>lang.offset(text,p),positionAt:n=>lang.position(text,n)};
      documents.set(uri.toString(),doc);indices.set(uri.toString(),lang.index(text,ast,{asts:compiled.rawAsts,files,uri:uri.toString()}));
    }
    const doc=documents.get(pathToFileURL(path.join(directory,main)).toString()),requests=[];
    const service={async request(method,document,params) {
      requests.push({method,uri:document.uri.toString()});const index=indices.get(document.uri.toString());
      if (method==='textDocument/documentSymbol') return index.symbols;
      assert.equal(method,'textDocument/definition');const target=index.target(params.position);return target?index.location(target):null;
    }};
    await run({doc,symbols:indices.get(doc.uri.toString()).symbols,service,open:async uri=>documents.get(uri),requests,compiled,documents});
  } finally {fs.rmSync(directory,{recursive:true,force:true});}
}
test('compiler-owned same-buffer inheritance annotates B.x for C.f (land F2)',async()=>{
  await compilerDocuments({'Main.sol':'pragma solidity ^0.8.34; contract B { uint x; } contract C is B { function f() public {} }'},'Main.sol',async({doc,symbols,service,open})=>{
    const fn=symbols.find(s=>s.name==='C').children.find(s=>s.name==='f'),r=row('f',{range:fn.range,counterexample:evidence({arguments:[],initialStorage:'x = 9'})});
    const storage=await storageDeclarations(doc,r,symbols,service,open),values=declarationValues(doc,r,symbols,storage.roots);
    assert.equal(storage.current(),true);assert.deepEqual(values,[{position:symbols.find(s=>s.name==='B').children[0].selectionRange.start,name:'x',value:'9'}]);
  });
});
test('compiler-owned diamond and private root collisions follow importer ordering',async()=>{
  const text='pragma solidity ^0.8.34; contract A { uint private x; uint private x_A; } contract L is A { uint private x; } contract R is A { uint r; } contract C is L, R { uint c; function f() public {} }';
  await compilerDocuments({'Main.sol':text},'Main.sol',async({doc,symbols,service,open})=>{
    const fn=symbols.find(s=>s.name==='C').children.find(s=>s.name==='f'),r=row('f',{range:fn.range,counterexample:evidence({arguments:[],initialStorage:'x_A_ = 9; x_A = 10; x = 11; r = 12; c = 13'})});
    const storage=await storageDeclarations(doc,r,symbols,service,open),values=declarationValues(doc,r,symbols,storage.roots);
    assert.deepEqual(values.map(v=>[v.name,v.value]),[['x_A_','9'],['x_A','10'],['x','11'],['r','12'],['c','13']]);
    assert.equal(values[0].position.character,text.indexOf('x;'));assert.equal(values[1].position.character,text.indexOf('x_A;'));assert.equal(values[2].position.character,text.indexOf('x;',text.indexOf('contract L')));
  });
});
test('compiler-owned imported aliases affect root renaming but foreign fields are not decorated',async()=>{
  const sources={'Base.sol':'pragma solidity ^0.8.34; contract Imported { uint private x; uint z; }','Main.sol':'pragma solidity ^0.8.34; import {Imported as Alias} from "./Base.sol"; contract A is Alias { uint private x; uint a; } contract C is A { function f() public {} }'};
  await compilerDocuments(sources,'Main.sol',async({doc,symbols,service,open,requests,documents})=>{
    const fn=symbols.find(s=>s.name==='C').children.find(s=>s.name==='f'),r=row('f',{range:fn.range,counterexample:evidence({arguments:[],initialStorage:'x_Imported = 9; z = 12; x = 10; a = 11'})});
    const storage=await storageDeclarations(doc,r,symbols,service,open),values=declarationValues(doc,r,symbols,storage.roots);
    assert.deepEqual(values.map(v=>[v.name,v.value]),[['x','10'],['a','11']]);
    assert.ok(requests.some(r=>r.method==='textDocument/documentSymbol'&&r.uri.endsWith('/Base.sol')));
    [...documents.values()].find(d=>d.uri.toString().endsWith('/Base.sol')).version++;assert.equal(storage.current(),false);
  });
});

test('editing or closing imported ancestry immediately clears dependent inline values and tree',async()=>{
  const sources={'Base.sol':'pragma solidity ^0.8.34; contract B { uint x; }','Main.sol':'pragma solidity ^0.8.34; import "./Base.sol"; contract C is B { uint y; function f() public {} }'};
  await compilerDocuments(sources,'Main.sol',async({doc,symbols,service,open,documents})=>{
    const h=harness(sources['Main.sol']);h.doc.uri=doc.uri;h.service.request=service.request;h.vscode.Uri={parse:s=>s};h.vscode.workspace.openTextDocument=open;
    const fn=symbols.find(s=>s.name==='C').children.find(s=>s.name==='f'),r=row('f',{range:fn.range,counterexample:evidence({arguments:[],initialStorage:'x = 9; y = 17'})}),base=[...documents.values()].find(d=>d.uri.toString().endsWith('/Base.sol'));
    h.report([r]);await h.show();assert.equal(h.calls.at(-1)[0].renderOptions.after.contentText,'y = 17');
    base.version++;h.events.edit({document:base});assert.deepEqual(h.provider.getChildren(),[]);assert.deepEqual(h.calls.at(-1),[]);
    await h.show();assert.deepEqual(h.provider.getChildren(),[]);
    h.report([r]);await h.show();assert.equal(h.provider.getChildren().length,5);
    h.events.close(base);assert.deepEqual(h.provider.getChildren(),[]);assert.deepEqual(h.calls.at(-1),[]);h.dispose();
  });
});

test('an imported edit during declaration lookup cannot restore stale values',async()=>{
  const sources={'Base.sol':'pragma solidity ^0.8.34; contract B { uint x; }','Main.sol':'pragma solidity ^0.8.34; import "./Base.sol"; contract C is B { uint y; function f() public {} }'};
  await compilerDocuments(sources,'Main.sol',async({doc,symbols,service,open,documents})=>{
    const h=harness(sources['Main.sol']);h.doc.uri=doc.uri;h.vscode.Uri={parse:s=>s};h.vscode.workspace.openTextDocument=open;
    let release,entered;const started=new Promise(resolve=>{entered=resolve;});
    h.service.request=async(method,document,params)=>{
      const result=await service.request(method,document,params);
      if (method==='textDocument/documentSymbol'&&document.uri.toString().endsWith('/Base.sol')) {await new Promise(resolve=>{release=resolve;entered();});}
      return result;
    };
    const fn=symbols.find(s=>s.name==='C').children.find(s=>s.name==='f');
    h.report([row('f',{range:fn.range,counterexample:evidence({arguments:[],initialStorage:'x = 9; y = 17'})})]);
    const pending=h.show();await started;
    const base=[...documents.values()].find(d=>d.uri.toString().endsWith('/Base.sol'));base.version++;h.events.edit({document:base});release();await pending;
    assert.deepEqual(h.provider.getChildren(),[]);assert.deepEqual(h.calls.at(-1),[]);await h.show();assert.deepEqual(h.provider.getChildren(),[]);h.dispose();
  });
});
