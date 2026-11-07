// Execute exact pinned Testing UI code against an injected editor API; not rendered/reference-server evidence.
'use strict';
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),{createHash}=require('node:crypto'),{mock}=require('../test/mock.cjs');
function compare(){
 const root=path.resolve(__dirname,'../../.cache/dafny-extension'),ts=require(path.join(root,'node_modules/typescript')),cache=new Map(),sources={},e=mock(),uri=e.doc.uri.toString();
 e.vscode.Position=class{constructor(line,character){Object.assign(this,{line,character});}};e.vscode.Range=class{constructor(start,end){Object.assign(this,{start,end});}contains(range){const cmp=(a,b)=>a.line-b.line||a.character-b.character;return cmp(this.start,range.start)<=0&&cmp(this.end,range.end)>=0;}isEqual(range){return JSON.stringify(this.start)===JSON.stringify(range.start)&&JSON.stringify(this.end)===JSON.stringify(range.end);}};e.vscode.Uri={parse:value=>({toString:()=>value})};
 function load(relative){if(cache.has(relative))return cache.get(relative).exports;const file=path.join(root,relative),bytes=fs.readFileSync(file);sources[relative]=createHash('sha256').update(bytes).digest('hex');const module={exports:{}};cache.set(relative,module);
 const code=ts.transpileModule(bytes.toString(),{compilerOptions:{module:ts.ModuleKind.CommonJS,target:ts.ScriptTarget.ES2020}}).outputText;
 const requireRef=name=>name==='vscode'?e.vscode:name==='../language/dafnyLanguageClient'?{}:load(path.relative(root,path.resolve(path.dirname(file),name))+'.ts');
 vm.runInNewContext('(function(require,module,exports){'+code+'\n})',{console},{filename:file})(requireRef,module,module.exports);return module.exports;}
 const View=load('src/ui/verificationSymbolStatusView.ts').default,cancellations=[],view=new View(e.context,{OnVerificationSymbolStatus:()=>({dispose(){}}),cancelVerification:params=>cancellations.push(params)}),observations=[];
 const update=(phase,states)=>{view.updateForSpecificDocumentVersion({uri,version:1,namedVerifiables:states.map((status,index)=>({status,nameRange:{start:{line:0,character:index},end:{line:0,character:index+1}}}))},e.doc,undefined);observations.push({phase,states,runs:e.runs.map(run=>run.calls.map(call=>({method:call[0],item:call[1]?.id}))),cancellations:[...cancellations]});};
 update('queued',[1,1]);update('duplicate-queued',[1,1]);update('running',[2,1]);update('terminal',[5,4]);update('duplicate-terminal',[5,4]);update('stale',[0,0]);update('empty',[]);
 const hierarchy=[];
 const range=(start,end)=>new e.vscode.Range(new e.vscode.Position(0,start),new e.vscode.Position(0,end)),leafRange=range(3,4),functionSymbol={name:'f',kind:12,range:range(2,8),selectionRange:leafRange,children:[]},roots=[{name:'C',kind:5,range:range(0,12),selectionRange:range(0,1),children:[functionSymbol]}];
 const snapshot=collection=>{const values=[];collection.forEach(item=>values.push({id:item.id,label:item.label,range:item.range,children:snapshot(item.children)}));return values;};
 const localTree=require('../src/testing-tree.cjs');
 for(const [label,symbols]of [['matched',roots],['unmatched',[{...roots[0],children:[]}]],['missing',undefined],['historical',[{...roots[0],detail:'Outdated: previous'}]]]){
  const boundary=mock(),reference=new View(boundary.context,{OnVerificationSymbolStatus:()=>({dispose(){}}),cancelVerification(){}});
  reference.updateForSpecificDocumentVersion({uri,version:1,namedVerifiables:[{nameRange:leafRange,status:5}]},boundary.doc,symbols);
  const local=mock(),metadata=new Map(),tree=localTree.install(local.vscode,local.controller,metadata),row={contract:'C',function:'f',signature:'f()',range:leafRange,status:'proved'};
  tree.render(local.doc,{results:[row],errors:[]},localTree.currentSymbols(symbols,local.doc.text));
  hierarchy.push({label,inputSymbols:symbols??null,pinned:snapshot(boundary.controller.items),local:snapshot(local.controller.items)});
  for(const disposable of boundary.context.subscriptions)disposable.dispose();
 }
 for(const disposable of e.context.subscriptions)disposable.dispose();
 return{schemaVersion:1,scope:'Pinned upstream TypeScript algorithm, injected VS Code API/document and symbol statuses. No renderer/reference server/proof.',sources,observations,hierarchy,notes:['Pinned run grouping and end calls are retained exactly as observed; local regressions independently require end-once on every lifecycle path.','Hierarchy comparison explicitly retains unmatched/missing/historical symbol behavior differences; no rendered or proof equivalence is claimed.','Local only maps explicit per-function queued/running states; native document-wide jobs never imply those states.','Local terminal resultKind retains direct/check, audit, unknown and unsupported distinctions; pinned five-state fixtures cannot establish semantic equivalence.']};
}
module.exports={compare};
