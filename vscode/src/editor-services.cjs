'use strict';
const {join}=require('node:path');

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
  const states=new Map();
  const draw=editor=>{
    const state=states.get(editor.document.uri.toString());
    const enabled=vscode.workspace.getConfiguration('solidityLean',editor.document.uri).get('displayGutterStatus',true);
    for(const [kind,type]of icons){
      const ranges=!enabled||state?.version!==editor.document.version?[]:(state.functions||[]).filter(f=>{
        const status=f.status==='refuted'?'error':['ready','pending','unsupported','notRun'].includes(f.status)?'pending':f.status;
        return status===kind;
      }).map(f=>({range:range(f.range),hoverMessage:f.status}));
      editor.setDecorations(type,ranges);
    }
  };
  const statusBar=vscode.window.createStatusBarItem(vscode.StatusBarAlignment.Left,10);
  statusBar.command='solidityLean.verify';
  const status=params=>{
    states.set(params.uri,params);
    const active=vscode.window.activeTextEditor;
    if(active?.document.uri.toString()===params.uri&&active.document.version===params.version){
      statusBar.text=['queued','compiling','running'].includes(params.state)?'$(sync~spin) Solidity Lean':`$(beaker) Solidity Lean: ${params.state}`;
      statusBar.tooltip='Solidity verification';statusBar.show();
    }
    vscode.window.visibleTextEditors.forEach(draw);
  };
  servers.on('status',status);
  providers.push(statusBar,...icons.values(),vscode.window.onDidChangeVisibleTextEditors(editors=>editors.forEach(draw)),
    vscode.window.onDidChangeActiveTextEditor(editor=>{if(editor&&states.has(editor.document.uri.toString()))status(states.get(editor.document.uri.toString()));else statusBar.hide();}),
    {dispose(){servers.removeListener('status',status);states.clear();}});
  context.subscriptions.push(...providers);
  return {clear(uri){states.delete(uri.toString());if(vscode.window.activeTextEditor?.document.uri.toString()===uri.toString())statusBar.hide();vscode.window.visibleTextEditors.filter(e=>e.document.uri.toString()===uri.toString()).forEach(draw);}};
}
module.exports={install};
