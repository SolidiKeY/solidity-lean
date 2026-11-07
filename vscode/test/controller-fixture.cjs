// Shared injected VS Code/service boundary; not rendered or proof evidence.
'use strict';
const {EventEmitter}=require('node:events'),{createHash}=require('node:crypto'),{mock}=require('./mock.cjs'),{createExtension}=require('../src/extension.cjs');
const noop=()=>({dispose(){}});
function fixture(backend,configure){
  const e=mock();e.calls={opens:[],restarts:0,cancels:0};
  const b={...e.doc,uri:{...e.doc.uri,fsPath:'/tmp/other.sol'}};e.documents=[e.doc,b];
  e.editors=e.documents.map(document=>({document,decorations:new Map(),setDecorations(type,rows){this.decorations.set(type.kind,rows);}}));
  e.bar={visible:false,text:'',show(){this.visible=true;},hide(){this.visible=false;},dispose(){this.visible=false;}};
  e.vscode.Uri={file:fsPath=>({fsPath}),parse:value=>({toString:()=>value})};e.vscode.StatusBarAlignment={Left:1,Right:2};e.versionBar={visible:false,text:'',show(){this.visible=true;},hide(){this.visible=false;},dispose(){this.visible=false;}};e.vscode.CodeActionKind={QuickFix:{}};
  for(const name of ['registerCompletionItemProvider','registerDefinitionProvider','registerReferenceProvider','registerDocumentSymbolProvider','registerSignatureHelpProvider','registerDocumentHighlightProvider','registerRenameProvider','registerDocumentFormattingEditProvider','registerCodeActionsProvider','registerWorkspaceSymbolProvider'])e.vscode.languages[name]=noop;
  Object.assign(e.vscode.window,{activeTextEditor:e.editors[0],visibleTextEditors:e.editors,createTextEditorDecorationType:options=>({kind:require('node:path').basename(options.gutterIconPath.fsPath,'.svg'),dispose(){}}),createStatusBarItem:alignment=>alignment===2?e.versionBar:e.bar,
    onDidChangeActiveTextEditor:fn=>e.subscribe('activeEditor',fn),onDidChangeVisibleTextEditors:fn=>e.subscribe('visibleEditors',fn),showQuickPick:async()=>undefined});
  Object.assign(e.vscode.workspace,{textDocuments:e.documents,onDidOpenTextDocument:fn=>e.subscribe('open',fn),createFileSystemWatcher:()=>({dispose(){},onDidChange:noop,onDidCreate:noop,onDidDelete:noop})});
  e.service=Object.assign(new EventEmitter(),{open:async doc=>e.calls.opens.push(doc),cancel:()=>e.calls.cancels++,save(){},close(){},restart:async()=>e.calls.restarts++,dispose:async()=>{}});
  configure?.(e);
  e.api=createExtension(e.vscode,e.context,backend|| (async args=>({results:[row(args.document)],errors:[]})),e.service);
  e.status=(doc,state='complete',version=doc.version)=>e.service.emit('status',{uri:doc.uri.toString(),version,state,functions:[{range:{start:{line:0,character:0},end:{line:0,character:1}},status:state==='complete'?'proved':'running'}]});
  e.changeConfig=(name,uri)=>e.events.configuration({affectsConfiguration:(key,scope)=>key===name&&(!uri||scope?.toString()===uri.toString())});
  return e;
}
function row(doc){return{source:doc.uri.fsPath,sourceHash:createHash('sha256').update(doc.text).digest('hex'),contract:'C',function:'f',signature:'f()',status:'proved',range:{start:{line:0,character:0},end:{line:0,character:1}}};}


module.exports={fixture,row};
