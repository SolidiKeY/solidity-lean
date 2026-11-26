'use strict';
const {randomUUID}=require('node:crypto');
const {selector,isSolidityFile}=require('../editor-document.cjs');
const {validRange}=require('../model.cjs');
const COMMAND='solidityLean.showObligation',SCHEME='solidity-lean-obligation';
function activate(context,{vscode,client,registerCommand,output}) {
  const documents=new Map(),links=new Map(),pending=new Set();let disposed=false;
  const owned=[],own=d=>(owned.push(d),d);
  const check=(doc,version,text,signal)=>{
    if(signal.aborted)throw Object.assign(new Error('Request cancelled'),{code:-32800});
    if(disposed||doc.isClosed||!isSolidityFile(doc)||doc.version!==version||doc.getText()!==text)throw Object.assign(new Error('Document content changed'),{code:-32801});
  };
  const report=error=>{if(![-32800,-32801].includes(error.code)&&error.code!=='CANCELLED'){output?.appendLine(`Obligation: ${error.message}`);vscode.window.showErrorMessage(`Could not show obligation: ${error.message}`);}};
  async function query(doc,position,token){
    if(!isSolidityFile(doc))return null;
    const version=doc.version,text=doc.getText(),abort=new AbortController();pending.add(abort);
    const subscription=token?.onCancellationRequested(()=>abort.abort());if(token?.isCancellationRequested)abort.abort();
    try{
      check(doc,version,text,abort.signal);
      const result=await client.request('solidityLean/showObligation',doc,{position},{signal:abort.signal});
      check(doc,version,text,abort.signal);
      if(!result)return null;
      if(typeof result.text!=='string'||!result.text.trim()||!validRange(result.range)||result.languageId!=='lean'||typeof result.label!=='string')throw new Error('Invalid obligation response');
      return {result,doc,version,text,position};
    }finally{pending.delete(abort);subscription?.dispose();}
  }
  function store(record){
    const key=randomUUID(),uri=vscode.Uri.parse(`${SCHEME}:/${key}.lean`);
    documents.set(uri.toString(),record.result.text);links.set(key,record);
    // Bound retained hover snapshots; open documents have their own VS Code text.
    while(links.size>32){const oldest=links.keys().next().value;links.delete(oldest);documents.delete(`${SCHEME}:/${oldest}.lean`);}
    return {key,uri};
  }
  async function show(record){
    const {doc,version,text}=record;check(doc,version,text,new AbortController().signal);
    const {uri}=store(record),virtual=await vscode.workspace.openTextDocument(uri);
    check(doc,version,text,new AbortController().signal);
    await vscode.languages.setTextDocumentLanguage(virtual,'lean');
    check(doc,version,text,new AbortController().signal);
    return vscode.window.showTextDocument(virtual,{preview:true});
  }
  own(vscode.workspace.registerTextDocumentContentProvider(SCHEME,{provideTextDocumentContent(uri){return documents.get(uri.toString())||'';}}));
  own((registerCommand||vscode.commands.registerCommand)(COMMAND,async key=>{
    try{
      if(typeof key==='string'){const record=links.get(key);if(!record)throw new Error('Obligation link expired; hover again');check(record.doc,record.version,record.text,new AbortController().signal);const fresh=await query(record.doc,record.position);if(fresh)return await show(fresh);return;}
      const editor=vscode.window.activeTextEditor;if(!editor)return;
      const record=await query(editor.document,editor.selection.active);if(record)return await show(record);
    }catch(error){report(error);}
  }));
  own(vscode.languages.registerHoverProvider(selector,{async provideHover(doc,position,token){
    try{
      const record=await query(doc,position,token);if(!record)return null;
      const {key}=store(record),{result}=record,limit=4000;
      const markdown=new vscode.MarkdownString();
      markdown.appendCodeblock(result.text.slice(0,limit)+(result.text.length>limit?'\n… (truncated)':''),'lean');
      markdown.appendMarkdown(`\n[Open full obligation](command:${COMMAND}?${encodeURIComponent(JSON.stringify([key]))})`);
      markdown.isTrusted={enabledCommands:[COMMAND]};
      return new vscode.Hover(markdown,new vscode.Range(result.range.start.line,result.range.start.character,result.range.end.line,result.range.end.character));
    }catch(error){report(error);return null;}
  }}));
  return {dispose(){disposed=true;for(const controller of pending)controller.abort();for(const item of owned.reverse())item.dispose();documents.clear();links.clear();}};
}
module.exports={activate,COMMAND,SCHEME};
