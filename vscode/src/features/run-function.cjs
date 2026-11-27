'use strict';
const {argument,supported} = require('../server-features/run-function.cjs');
function render(fn,result) {
  const lines=[`Concrete typed-model run: ${fn.contract}.${fn.signature}`,`Outcome: ${result.status}`];
  if(result.code!==null && result.code!==undefined)lines.push(`Code: ${result.code}`);
  lines.push(`Returns: ${JSON.stringify(result.returns)}`);
  lines.push(`Emitted logs: ${result.logs===null?'unavailable':JSON.stringify(result.logs)}`);
  lines.push(`Storage slots written: ${result.storageWrites===null?'unavailable':JSON.stringify(result.storageWrites)}`);
  if(result.text)lines.push(result.text);
  for(const limitation of result.limitations || [])lines.push(`Limitation: ${limitation}`);
  return lines.join('\n');
}
function activate(context,services) {
  const {vscode,output}=services,client=services.client || services.service;
  const defaults=new Map(),active=new Set(); let disposed=false;
  const registration=services.registerCommand('solidityLean.runFunction',async()=>{
    const editor=vscode.window.activeTextEditor,doc=editor?.document;
    if(!doc || doc.languageId!=='solidity' || doc.uri.scheme!=='file')return vscode.window.showInformationMessage('Open a Solidity file to run a function');
    if(!vscode.workspace.isTrusted)return vscode.window.showErrorMessage('Running functions requires a trusted workspace');
    const uri=doc.uri.toString(),version=doc.version,text=doc.getText(),abort=new AbortController(); active.add(abort);
    const current=()=>{if(abort.signal.aborted)throw Object.assign(new Error('Run cancelled'),{code:-32800});
      if(disposed||doc.isClosed||doc.version!==version||doc.getText()!==text)throw Object.assign(new Error('Buffer changed; run again'),{code:-32801});};
    try {
      const listing=await client.request('solidityLean/runFunctions',doc,{}, {signal:abort.signal}); current();
      if(!listing.functions.length)return vscode.window.showInformationMessage('No concrete functions found in this buffer');
      const picked=await vscode.window.showQuickPick(listing.functions.map(fn=>({label:`${fn.contract}.${fn.signature}`,fn})),{placeHolder:'Run a function on concrete arguments'});
      current();if(!picked)return;
      const fn=picked.fn,key=`${uri}:${fn.contract}.${fn.signature}`,previous=defaults.get(key)||[],args=[];
      for(const param of fn.parameters)if(!supported(param.type))throw new Error(`Unsupported ABI input type ${param.type}`);
      for(const [i,param] of fn.parameters.entries()) {
        const value=await vscode.window.showInputBox({title:`${fn.signature}: argument ${i+1}`,prompt:`${param.name || 'argument'} (${param.type})`,value:previous[i]??'',
          validateInput:value=>{try{argument(param.type,value);return undefined;}catch(error){return error.message;}}});
        current();if(value===undefined)return;
        argument(param.type,value);args.push(value);
      }
      const timeoutMs=vscode.workspace.getConfiguration?.('solidityLean',doc.uri).get('timeoutMs',600000) || 600000;
      const result=await vscode.window.withProgress({location:vscode.ProgressLocation.Notification,title:`Running ${fn.signature}`,cancellable:true},async(_progress,token)=>{
        const cancellation=token.onCancellationRequested(()=>abort.abort());
        try{if(token.isCancellationRequested)abort.abort();current();return await client.request('solidityLean/runFunction',doc,{sourceHash:listing.sourceHash,functionId:fn.id,args:args.map((a,i)=>argument(fn.parameters[i].type,a))},{signal:abort.signal,timeoutMs:timeoutMs+5000});}
        finally{cancellation.dispose();}
      });
      current();defaults.set(key,args);output.appendLine(render(fn,result));output.show(true);return result;
    } catch(error) {
      if(![-32800,-32801].includes(error.code)&&error.code!=='CANCELLED')await vscode.window.showErrorMessage(`Run function: ${error.message}`);
      else if(error.code===-32801)await vscode.window.showInformationMessage('Buffer changed; run again');
    } finally{active.delete(abort);}
  });
  return {dispose(){disposed=true;for(const abort of active)abort.abort();registration.dispose();defaults.clear();}};
}
module.exports={activate,render};
