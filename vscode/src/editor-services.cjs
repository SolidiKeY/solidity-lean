'use strict';
const {join,resolve,sep}=require('node:path');
const {createHash}=require('node:crypto');
const {summarize,issueURL}=require('./status-summary.cjs');
const model=require('./model.cjs');

function install(vscode,context,servers,reportError){
  const selector={scheme:'file',pattern:'**/*.sol'};
  const range=r=>new vscode.Range(r.start.line,r.start.character,r.end.line,r.end.character);
  const location=l=>new vscode.Location(vscode.Uri.parse(l.uri),range(l.range));
  const raw=async(method,doc,params,token)=>{
    const controller=new AbortController(),registration=token?.onCancellationRequested(()=>controller.abort());
    if(token?.isCancellationRequested)controller.abort();
    try{return await servers.request(method,doc,params,{signal:controller.signal});}finally{registration?.dispose();}
  };
  const query=async(method,doc,params,token)=>{
    try{return await raw(method,doc,params,token);}
    catch(error){if(![-32800,-32801].includes(error.code)&&error.code!=='CANCELLED')reportError(error);return null;}
  };
  const workspaceEdit=result=>{const edit=new vscode.WorkspaceEdit();for(const change of result?.documentChanges||[]){
    const uri=vscode.Uri.parse(change.textDocument.uri),open=vscode.workspace.textDocuments.find(d=>d.uri.toString()===uri.toString());
    if(change.textDocument.version!==null&&open?.version!==change.textDocument.version)throw new Error('Refactoring target changed; retry the operation');
    edit.set(uri,change.edits.map(row=>new vscode.TextEdit(range(row.range),row.newText)));
  }return edit;};
  const providers=[
    vscode.languages.registerDocumentFormattingEditProvider(selector,{async provideDocumentFormattingEdits(doc,options,token){return (await query('textDocument/formatting',doc,{options},token)||[]).map(e=>new vscode.TextEdit(range(e.range),e.newText));}}),
    vscode.languages.registerCodeActionsProvider(selector,{async provideCodeActions(doc,selection,options,token){
      const diagnostics=options.diagnostics.map(d=>({range:{start:d.range.start,end:d.range.end},message:d.message,code:typeof d.code==='object'?d.code.value:d.code,severity:d.severity+1}));
      const actions=await query('textDocument/codeAction',doc,{range:{start:selection.start,end:selection.end},context:{diagnostics,only:options.only?[options.only.value]:undefined}},token)||[];
      return actions.map(row=>{const action=new vscode.CodeAction(row.title,vscode.CodeActionKind.QuickFix);action.edit=workspaceEdit(row.edit);return action;});
    }},{providedCodeActionKinds:[vscode.CodeActionKind.QuickFix]}),
    vscode.languages.registerWorkspaceSymbolProvider({async provideWorkspaceSymbols(queryText,token){
      if(!servers.clients.size){const files=await vscode.workspace.findFiles('**/*.sol','**/{node_modules,.lake,.git,.cache}/**',1);if(files.length)await servers.open(await vscode.workspace.openTextDocument(files[0]));}
      const abort=new AbortController(),registration=token?.onCancellationRequested(()=>abort.abort());if(token?.isCancellationRequested)abort.abort();
      try{return (await servers.workspaceSymbols(queryText,{signal:abort.signal})).map(s=>new vscode.SymbolInformation(s.name,s.kind-1,'',location(s.location)));}
      catch(error){if(![-32800,-32801].includes(error.code))reportError(error);return [];}
      finally{registration?.dispose();}
    }}),
    vscode.languages.registerCompletionItemProvider(selector,{async provideCompletionItems(doc,position,token){
      const result=await query('textDocument/completion',doc,{position},token);
      return result?new vscode.CompletionList(result.items.map(row=>{const item=new vscode.CompletionItem(row.label,row.kind===14?vscode.CompletionItemKind.Keyword:row.kind===3?vscode.CompletionItemKind.Function:vscode.CompletionItemKind.Variable);item.detail=row.detail;return item;}),result.isIncomplete):null;
    }},'.'),
    vscode.languages.registerDefinitionProvider(selector,{async provideDefinition(doc,position,token){const result=await query('textDocument/definition',doc,{position},token);return Array.isArray(result)?result.map(location):result?location(result):null;}}),
    vscode.languages.registerReferenceProvider(selector,{async provideReferences(doc,position,options,token){return (await query('textDocument/references',doc,{position,context:options},token)||[]).map(location);}}),
    vscode.languages.registerDocumentSymbolProvider(selector,{async provideDocumentSymbols(doc,token){
      const symbol=row=>{const item=new vscode.DocumentSymbol(row.name,row.detail||'',row.kind-1,range(row.range),range(row.selectionRange));item.children=(row.children||[]).map(symbol);return item;};
      return (await query('textDocument/documentSymbol',doc,{},token)||[]).map(symbol);
    }}),
    vscode.languages.registerSignatureHelpProvider(selector,{async provideSignatureHelp(doc,position,token){
      const result=await query('textDocument/signatureHelp',doc,{position},token);if(!result)return null;
      const help=new vscode.SignatureHelp();help.activeParameter=result.activeParameter;help.activeSignature=result.activeSignature;
      help.signatures=result.signatures.map(row=>{const signature=new vscode.SignatureInformation(row.label);signature.parameters=row.parameters.map(p=>new vscode.ParameterInformation(p.label));return signature;});return help;
    }},'(',','),
    vscode.languages.registerDocumentHighlightProvider(selector,{async provideDocumentHighlights(doc,position,token){return (await query('textDocument/documentHighlight',doc,{position},token)||[]).map(r=>new vscode.DocumentHighlight(range(r.range),vscode.DocumentHighlightKind.Text));}}),
    vscode.languages.registerRenameProvider(selector,{async prepareRename(doc,position,token){const result=await raw('textDocument/prepareRename',doc,{position},token);if(!result)throw new Error('No renameable compiler declaration');return {range:range(result.range),placeholder:result.placeholder};},
      async provideRenameEdits(doc,position,newName,token){return workspaceEdit(await raw('textDocument/rename',doc,{position,newName},token));}})
  ];
  const watcher=vscode.workspace.createFileSystemWatcher('**/*.sol');
  providers.push(watcher,watcher.onDidChange(uri=>servers.changed(uri)),watcher.onDidCreate(uri=>servers.changed(uri)),watcher.onDidDelete(uri=>servers.changed(uri)));
  const icons=new Map();
  for(const state of ['proved','pending','running','error'])icons.set(state,vscode.window.createTextEditorDecorationType({
    gutterIconPath:vscode.Uri.file(join(__dirname,'../media',state+'.svg')),gutterIconSize:'contain'}));
  const states=new Map(),pickerEpochs=new Map();let activeRevision=0,lifecycleRevision=0;
  const touch=uri=>{const key=uri.toString();pickerEpochs.set(key,(pickerEpochs.get(key)||0)+1);lifecycleRevision++;};
  let disposed=false;
  const document=uri=>vscode.workspace.textDocuments.find(doc=>!doc.isClosed&&doc.uri.toString()===uri);
  const current=doc=>{const value=states.get(doc.uri.toString());return !doc.isClosed&&value?.document===doc&&value.params.version===doc.version&&value.text===doc.getText()?value.params:null;};
  const draw=editor=>{
    const state=current(editor.document);
    const enabled=vscode.workspace.getConfiguration('solidityLean',editor.document.uri).get('displayGutterStatus',true);
    for(const [kind,type]of icons){
      const ranges=!enabled||!state?[]:(state.functions||[]).filter(f=>{
        const status=f.status==='refuted'?'error':['ready','pending','unsupported','notRun','queued','stale','cancelled','skip','skipped','internal','excluded','unknown'].includes(f.status)?'pending':f.status;
        return status===kind;
      }).map(f=>({range:range(f.range),hoverMessage:model.status(f)}));
      editor.setDecorations(type,ranges);
    }
  };
  const identities=new Map(),versionBar=vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Right,10);
  const statusBar=vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left,10);
  statusBar.command='solidityLean.openStatusBarMenu';
  const render=()=>{
    if(disposed)return;
    const active=vscode.window.activeTextEditor,state=active&&current(active.document),identity=active&&identities.get(active.document.uri.toString());
    if(identity&&!active.document.isClosed&&active.document.uri.scheme==='file'&&active.document.uri.fsPath.toLowerCase().endsWith('.sol')){
      versionBar.text=identity.serverInfo.version;versionBar.tooltip=`${identity.serverInfo.name}: ${identity.serverInfo.version}\nNode.js: ${identity.runtimeInfo?.version||'unknown'}\nExtension: ${require('../package.json').version}`;versionBar.show();
    }else versionBar.hide();
    if(state){
      const summary=summarize(state,active.document);statusBar.text=summary.text;statusBar.tooltip=summary.tooltip+'\nClick for actions';statusBar.show();
    }else statusBar.hide();
    vscode.window.visibleTextEditors.forEach(draw);
  };
  const status=params=>{
    const doc=document(params.uri);
    // Closed, foreign and obsolete notifications must never replace current state.
    if(disposed||!doc||doc.version!==params.version||!Number.isInteger(params.version))return;
    if(params.sourceHash!==undefined&&params.sourceHash!==createHash('sha256').update(doc.getText()).digest('hex'))return;
    if(params.functions!==undefined&&(!Array.isArray(params.functions)||params.functions.some(row=>!row||!model.validRange(row.range)||typeof row.status!=='string')))return;
    states.set(params.uri,{params:structuredClone(params),document:doc,text:doc.getText()});render();
  };
  const clear=uri=>{touch(uri);states.delete(uri.toString());render();};
  const clearIdentity=uri=>{touch(uri);identities.delete(uri.toString());render();};
  const identity=params=>{if(disposed)return;for(const uri of params.uris||[])if(document(uri))identities.set(uri,params);render();};
  const failed=error=>{if(disposed||[-32800,-32801].includes(error.code)||error.code==='CANCELLED')return;for(const uri of error.uris||identities.keys())identities.delete(uri);render();};
  servers.on('status',status);servers.on('identity',identity);servers.on('serverError',failed);
  providers.push(statusBar,versionBar,...icons.values(),
    vscode.commands.registerCommand('solidityLean.openStatusBarMenu',async()=>{
      const owner=vscode.window.activeTextEditor?.document,version=owner?.version,text=owner?.getText(),epoch=owner?pickerEpochs.get(owner.uri.toString()):lifecycleRevision,active=activeRevision,identitySnapshot=owner&&identities.get(owner.uri.toString());
      const actions=[{label:'Restart Solidity Lean',description:'Restart the language servers',command:'solidityLean.restartServer'},
        {label:'Show verification output',description:'Open the Solidity Lean output channel',command:'solidityLean.showOutput'}];
      if(owner&&current(owner)&&summarize(current(owner),owner).help)actions.unshift({label:'Help with a proof',description:'Open project proof guide: docs/calculus.md',proofHelp:'guide'},{label:'Proof documentation index',description:'Open project documentation: docs/README.md',proofHelp:'index'});
      const link=issueURL(identitySnapshot,owner&&current(owner));if(link)actions.push({label:'Report verification issue',description:'Open an issue draft with server and extension versions; no source attached',uri:link,reportIssue:true});
      const selected=await vscode.window.showQuickPick(actions,{matchOnDescription:true,placeHolder:'Pick an action'});
      if(disposed||!actions.includes(selected)||!vscode.workspace.isTrusted)return;
      if(vscode.window.activeTextEditor?.document!==owner||activeRevision!==active)return;
      if(owner?(owner.isClosed||owner.version!==version||owner.getText()!==text||pickerEpochs.get(owner.uri.toString())!==epoch):lifecycleRevision!==epoch)return;
      if(selected.proofHelp){
        const state=owner&&current(owner);if(!state||!summarize(state,owner).help)return;
        const cfg=vscode.workspace.getConfiguration('solidityLean',owner.uri),folder=vscode.workspace.getWorkspaceFolder(owner.uri)?.uri.fsPath,configured=cfg.get('backendPath','');let destination;
        try{if(!configured&&!folder)throw Error('Missing backend configuration');const fs=require('node:fs'),root=fs.realpathSync(resolve(folder||'.',configured||'.')),index=fs.realpathSync(join(root,'docs/README.md')),guide=fs.realpathSync(join(root,'docs/calculus.md'));if(![index,guide].every(file=>file.startsWith(root+sep)&&fs.statSync(file).isFile()))throw Error('Documentation escapes configured repository');destination=selected.proofHelp==='guide'?guide:index;}
        catch(cause){reportError(new Error('Project proof documentation is unavailable. Set solidityLean.backendPath to a complete repository containing docs/README.md and docs/calculus.md.',{cause}));return;}
        await vscode.commands.executeCommand('vscode.open',vscode.Uri.file(destination));return;
      }
      const destination=selected.reportIssue?issueURL(owner&&identities.get(owner.uri.toString()),owner&&current(owner)):selected.uri;
      if(destination)await vscode.env.openExternal(vscode.Uri.parse(destination));else await vscode.commands.executeCommand(selected.command);
    }),
    vscode.window.onDidChangeVisibleTextEditors(render),vscode.window.onDidChangeActiveTextEditor(()=>{activeRevision++;render();}),
    vscode.workspace.onDidChangeConfiguration(event=>{if(event.affectsConfiguration('solidityLean.displayGutterStatus'))render();}),
    vscode.workspace.onDidChangeTextDocument(event=>{if(event.contentChanges.length)clear(event.document.uri);}),
    vscode.workspace.onDidCloseTextDocument(doc=>{clear(doc.uri);clearIdentity(doc.uri);pickerEpochs.delete(doc.uri.toString());}),
    {dispose(){disposed=true;servers.removeListener('status',status);servers.removeListener('identity',identity);servers.removeListener('serverError',failed);states.clear();identities.clear();pickerEpochs.clear();}});
  context.subscriptions.push(...providers);
  return {clear,clearIdentity};
}
module.exports={install};
