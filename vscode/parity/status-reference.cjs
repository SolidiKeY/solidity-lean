// Execute pinned UI algorithms with an explicitly injected editor boundary; not a VS Code host run.
'use strict';
const fs=require('node:fs'),path=require('node:path'),vm=require('node:vm'),{createHash}=require('node:crypto'),{offset}=require('../src/language-services.cjs'),{summarize}=require('../src/status-summary.cjs');
async function compare(){
 const root=path.resolve(__dirname,'../../.cache/dafny-extension'),ts=require(path.join(root,'node_modules/typescript')),cache=new Map(),sources={},menus=[];
 const text='alpha beta gamma delta epsilon',uri='file:///reference.dfy',doc={uri:{toString:()=>uri},version:4,getText(range){return range?text.slice(offset(text,range.start),offset(text,range.end)):text;}};
 const vscode={Uri:{parse:value=>({toString:()=>value})},window:{activeTextEditor:{document:doc},showQuickPick:async items=>{menus.push(items);return undefined;}},workspace:{openTextDocument:async()=>doc},env:{openExternal(){throw Error('Reference actions must never navigate');}},commands:{executeCommand(){throw Error('Reference actions must never dispatch');}}};
 function load(relative){
  if(cache.has(relative))return cache.get(relative).exports;const file=path.join(root,relative),bytes=fs.readFileSync(file);sources[relative]=createHash('sha256').update(bytes).digest('hex');const module={exports:{}};cache.set(relative,module);
  const code=ts.transpileModule(bytes.toString(),{compilerOptions:{module:ts.ModuleKind.CommonJS,target:ts.ScriptTarget.ES2020}}).outputText;
  const requireRef=name=>{
   if(name==='vscode')return vscode;
   if(name==='../tools/vscode')return{getVsDocumentPath:params=>params.uri};
   if(name==='../tools/visibility')return{};
   if(name==='./verificationSymbolStatusView')return{default:{convertRange:range=>range}};
   if(name==='../language/dafnyLanguageClient')return{};
   if(name==='process')return{chdir(){throw Error('Reference must not change process directory');},cwd:()=>root};
   if(name==='fs')return{readFile(){throw Error('Unexpected reference file access');}};
   if(name==='util')return require('node:util');
   const resolved=path.relative(root,path.resolve(path.dirname(file),name))+'.ts';return load(resolved);
  };
  vm.runInNewContext('(function(require,module,exports){'+code+'\n})',{},{filename:file})(requireRef,module,module.exports);return module.exports;
 }
 const View=load('src/ui/compilationStatusView.ts').default,Action=load('src/ui/statusBarActionView.ts').default,enumeration=load('src/language/api/compilationStatus.ts').CompilationStatus;
 const names=text.split(' '),range=name=>({start:{line:0,character:text.indexOf(name)},end:{line:0,character:text.indexOf(name)+name.length}}),cases=[];
 for(const [label,values]of [['mixed',[5,4,2,1,0]],['queued',[5,1,0]],['success',[5,5]],['skipped',[5,0,0]],['one-error',[5,4,0]],['multiple-errors',[4,4,5]],['empty',[]]]){
  const bar={text:''},view=new View(bar,{},{}),namedVerifiables=values.map((status,i)=>({nameRange:range(names[i]),status}));await view.showVerifiableRangesInStatusBar({uri,version:doc.version,namedVerifiables});const mapped=values.map((status,i)=>({range:range(names[i]),status:({0:'stale',1:'queued',2:'running',4:'error',5:'proved'})[status]}));cases.push({label,input:namedVerifiables,pinned:bar.text,local:summarize({state:values.some(value=>value===1||value===2)?'running':'complete',functions:mapped},doc)});
 }
 const phases=[];for(const name of ['Parsing','Resolving','ParsingFailed','ResolutionFailed','PreparingVerification','CompilationSucceeded']){const bar={text:''},view=new View(bar,{},{});view.compilationStatusChangedAfter38({uri,version:4,status:enumeration[name]});const before=bar.text;view.compilationStatusChangedAfter38({uri,version:3,status:enumeration.Parsing});phases.push({name,pinned:before,afterOldVersion:bar.text});}
 const pkg=JSON.parse(fs.readFileSync(path.join(root,'package.json'))),context={extensionPath:'/reference/dafny-lang.ide-vscode-'+pkg.version};
 for(const current of [cases.find(row=>row.label==='mixed').pinned,cases.find(row=>row.label==='one-error').pinned,'$(sync~spin) Verifying...']){const action=new Action({getCurrentDocumentStatus:()=>current},'4.11.0.0',context);await action.openStatusBarMenu();}
 return{schemaVersion:1,scope:'Exact pinned TypeScript message/action algorithms with injected VS Code/document boundary; no reference server, renderer or external actions run.',sources,cases,phases,menus,notes:['Local Completed denotes finished outcomes including errors, never a proof count.','Local direct/unknown/unsupported/audit states are explicit; injected reference fixtures cover only its five published symbol states.','Empty symbols yield pinned success but local no-results; no row is claimed complete.','Pinned modern verifying text uses lowercase verifying; its help condition checks uppercase Verifying. Menus retain the actual observation.']};
}
module.exports={compare};
