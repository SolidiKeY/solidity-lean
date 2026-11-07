// Concrete typed-model execution and compiler artifacts; never verification verdicts.
'use strict';
const fs=require('node:fs'),path=require('node:path'),{spawn}=require('node:child_process'),{createHash,randomUUID}=require('node:crypto');
const {terminateTree}=require('./backend.cjs'),{trackChild,waitForClose,waitForGroup}=require('./child-lifetime.cjs'),{processState}=require('./process-state.cjs');
const digest=text=>createHash('sha256').update(text).digest('hex');
function selection(text){const parts=text.split('::');if(parts.length!==2||!/^[$A-Za-z_][$\w]*$/.test(parts[0])||!parts[1].trim())throw Error('Use Contract::function or Contract::function(type,...)');return{contract:parts[0],function:parts[1].trim()};}
function argumentsOf(values){if(!Array.isArray(values)||values.some(v=>typeof v!=='boolean'&&(typeof v!=='string'||! /^-?(?:[0-9]+|0x[0-9a-fA-F]+)$/.test(v))))throw Error('Arguments must be booleans or exact integer strings');return values.map(String);}
function buildArguments(value){
 if(!value||typeof value!=='object'||Array.isArray(value)||Object.keys(value).some(key=>!['includePaths','remappings'].includes(key)))throw Error('Custom compiler arguments accept only includePaths and remappings');
 const result={};for(const key of ['includePaths','remappings'])if(Object.hasOwn(value,key)){const items=value[key];if(!Array.isArray(items)||items.some(item=>typeof item!=='string'||!item.trim()||item.includes('\0')))throw Error('Custom compiler arguments must be arrays of nonempty strings');result[key]=[...items];}return result;
}
function processJob(config,args,signal,timeoutMs){return new Promise((resolve,reject)=>{
 if(signal?.aborted){reject(Object.assign(Error('Cancelled'),{code:'CANCELLED'}));return;}
 const child=spawn(config.nodePath||process.execPath,args,{cwd:config.backendPath,shell:false,detached:process.platform!=='win32',stdio:['ignore','pipe','pipe']});child.ownedGroup=process.platform!=='win32';child.processBirth=processState(child.pid)?.birth;const closed=trackChild(child);let stdout='',stderr='',settled=false,stopping;
 const finish=(error,value)=>{if(settled)return;settled=true;clearTimeout(timer);signal?.removeEventListener('abort',abort);error?reject(error):resolve(value);};
 const stop=error=>{if(stopping||settled)return;stopping=error;try{terminateTree(child);}catch(e){error=e;}waitForClose(child,{closed,kill:true}).then(()=>finish(error),failure=>{failure.cleanupFailed=true;finish(failure);});};
 const abort=()=>stop(Object.assign(Error('Cancelled'),{code:'CANCELLED'})),timer=setTimeout(()=>stop(Object.assign(Error('Source command timed out'),{code:'TIMEOUT'})),timeoutMs);signal?.addEventListener('abort',abort,{once:true});if(signal?.aborted)abort();
 child.stdout.setEncoding('utf8');child.stderr.setEncoding('utf8');child.on('error',error=>{if(child.pid)stop(error);else finish(error);});child.stdout.on('data',b=>{if(stopping||settled)return;if(Buffer.byteLength(stdout)+Buffer.byteLength(b)>32*1024*1024){stop(Error('Source command output exceeds32MiB'));return;}stdout+=b;});child.stderr.on('data',b=>{if(!stopping&&!settled)stderr=(stderr+b).slice(-16000);});
 child.on('close',async(code,signalCode)=>{if(stopping||settled)return;try{await waitForGroup(child);finish(null,{code,signalCode,stdout,stderr});}catch(error){error.cleanupFailed=true;finish(error);}});
 });}
async function execute(operation,config,source,input={},signal){
 const requestedOperation=operation;
 if(operation==='buildCustomArgs'){config={...config,...buildArguments(input)};operation='build';}
 if(!Number.isSafeInteger(config.timeoutMs)||config.timeoutMs<1||config.timeoutMs>3600000)throw Error('Invalid source-command timeout');
 const deadline=Date.now()+config.timeoutMs,remaining=()=>{const n=deadline-Date.now();if(n<=0)throw Object.assign(Error('Source command timed out'),{code:'TIMEOUT'});return n;};
 const text=fs.readFileSync(source,'utf8'),project=require('./project.cjs').snapshot(source,text,config,[]);
 const probe=await processJob(config,['--version'],signal,Math.min(remaining(),5000)),version=/^v(\d+)\.\d+\.\d+(?:-[0-9A-Za-z.-]+)?$/.exec(probe.stdout.trim());
 if(probe.code!==0||!version||Number(version[1])<18)throw Error('Configured runtime must satisfy the existing Node.js18+ contract; unknown version is not accepted');
 if(!require('./project.cjs').current(project,[]))throw Error('Source project changed during runtime probe');
 const root=path.resolve(config.backendPath);let directory=path.join(root,'.lake/editor-source-artifacts');
 if(operation==='build'){const output=config.compilerOutputDir??'bin';if(typeof output!=='string'||output.includes('\0'))throw Error('Compiler output directory must be a string without NUL');directory=path.resolve(config.projectRoot||path.dirname(source),output);}
 fs.mkdirSync(directory,{recursive:true});const scratch=fs.mkdtempSync(path.join(directory,operation==='build'?path.basename(source,path.extname(source))+'-':operation+'-'));
 if(operation==='build'){
  const artifact=path.join(scratch,'source.ast.json'),args=[path.join(root,'scripts/solc-ast.mjs'),'--source',source,'--out',artifact,'--no-wrapper','--project-root',config.projectRoot];for(const p of config.includePaths||[])args.push('--include-path',path.resolve(config.projectRoot||path.dirname(source),p));for(const r of config.remappings||[])args.push('--remapping',r);
  const result=await processJob(config,args,signal,remaining());if(result.code!==0)throw Error(result.stderr||result.stdout||'Compiler build failed');const fixture=JSON.parse(fs.readFileSync(artifact,'utf8'));
  const admitted=Object.entries(project.files),units=fixture.sourceUnits;
  if(admitted.length>1||units!==undefined){
   if(!Array.isArray(units)||units.length!==admitted.length||units.some(unit=>!unit||typeof unit.name!=='string')||new Set(units.map(unit=>unit.name)).size!==units.length||admitted.some(([name,file])=>!units.some(unit=>unit.name===name&&unit.sourceSha256===file.hash)))throw Error('Compiler artifact does not match admitted project');
  }
  if((fixture.header?.sourceSha256??fixture.sourceUnits?.find(unit=>unit.name===fixture.header?.mainSource)?.sourceSha256)!==digest(text)||!require('./project.cjs').current(project,[]))throw Error('Source changed during build');const report={schemaVersion:1,operation:requestedOperation,kind:'compiler-ast',outputDirectory:directory,source,sourceHash:digest(text),artifact,projectDigest:project.digest,compilerOptions:{includePaths:[...(config.includePaths||[])],remappings:[...(config.remappings||[])]},verification:'not-run'};fs.writeFileSync(path.join(scratch,'manifest.json'),JSON.stringify(report,null,2)+'\n');return report;
 }
 if(operation!=='run'&&operation!=='test')throw Error('Unknown source command');
 if(config.includePaths?.length||config.remappings?.length)throw Error('Concrete CLI currently supports its default import resolution; custom include paths/remappings are not silently ignored');
 const cases=operation==='run'?[input]:input.cases;if(!Array.isArray(cases)||!cases.length)throw Error('A nonempty concrete case list is required');const results=[];
 for(let i=0;i<cases.length;i++){
  if(signal?.aborted)throw Object.assign(Error('Cancelled'),{code:'CANCELLED'});if(!require('./project.cjs').current(project,[]))throw Error('Source project changed');const c=cases[i],target=selection(c.target),args=argumentsOf(c.args===undefined?[]:c.args),state=c.state===undefined?{}:c.state;if(!state||typeof state!=='object'||Array.isArray(state))throw Error('State must be an object');
  if(operation==='test'&&(!c.expect||!['ok','revert','panic'].includes(c.expect.status)||typeof c.expect.text!=='string'))throw Error('Each test needs exact expect.status(ok/revert/panic) and expect.text; unsupported/error cannot pass');
  const stateFile=path.join(scratch,'state-'+i+'.json');fs.writeFileSync(stateFile,JSON.stringify(state));const argv=[path.join(root,'scripts/solidity-lean.mjs'),'run','--contract',target.contract,'--function',target.function,'--state',stateFile,'--timeout',String(remaining()),'--json'];for(const a of args)argv.push('--arg',a);argv.push('--',source);
  const result=await processJob(config,argv,signal,remaining());fs.writeFileSync(path.join(scratch,'case-'+i+'.stdout.json'),result.stdout);fs.writeFileSync(path.join(scratch,'case-'+i+'.stderr.log'),result.stderr);if(![0,1].includes(result.code))throw Error(result.stderr||result.stdout||'Concrete runner setup failed');let report;try{report=JSON.parse(result.stdout);}catch{throw Error('Concrete runner returned malformed JSON');}
  if(report.command!=='run'||report.schemaVersion!==1||!Array.isArray(report.results)||report.results.length!==1||!Array.isArray(report.errors)||report.errors.length)throw Error('Concrete runner returned no unique valid result');const row=report.results[0];if(row.contract!==target.contract||row.source!==source||typeof row.text!=='string'||!['ok','revert','panic','diverge','unsupported','error'].includes(row.status))throw Error('Concrete result identity/status mismatch');
  if(target.function.includes('(')?row.signature!==target.function:row.function!==target.function)throw Error('Concrete function identity mismatch');if(!require('./project.cjs').current(project,[]))throw Error('Source project changed');if(result.code!==(row.status==='ok'?0:1))throw Error('Concrete result exit/status mismatch');if(fs.readFileSync(source,'utf8')!==text)throw Error('Source changed during concrete execution');const passed=operation==='test'?row.status===c.expect.status&&row.text===c.expect.text:row.status==='ok';results.push({name:c.name||String(i+1),target:c.target,passed,status:row.status,text:row.text,exitCode:result.code});
 }
 const report={schemaVersion:1,operation,kind:'typed-model-concrete',source,sourceHash:digest(text),results,passed:results.every(r=>r.passed),verification:'not-run'};fs.writeFileSync(path.join(scratch,'result.json'),JSON.stringify(report,null,2)+'\n');return report;
}
function install(vscode,context,{settings,output,cancelVerification}){
 const jobs=new Map(),retiring=new Map(),epochs=new Map(),documents=new Map();let generation=0;
 const touch=uri=>epochs.set(uri,++generation);let disposed=false,disposal;
 const recordFailure=error=>output.appendLine('Source command retirement failed: '+error.message);
 function stop(uri){
  if(uri===undefined)return Promise.allSettled([...new Set([...jobs.keys(),...retiring.keys()])].map(stop)).then(results=>{const errors=results.filter(r=>r.status==='rejected').map(r=>r.reason);if(errors.length)throw new AggregateError(errors,'Source child cleanup failed: '+errors.map(e=>e.message).join('; '));});
  if(retiring.has(uri))return retiring.get(uri);const job=jobs.get(uri);if(!job)return Promise.resolve();job.abort.abort();
  const promise=job.promise.then(()=>{},error=>{if(error.cleanupFailed)throw error;}).then(()=>{if(retiring.get(uri)===promise)retiring.delete(uri);});retiring.set(uri,promise);return promise;
 }
 const isCurrent=(doc,version,text,epoch)=>epochs.get(doc.uri.toString())===epoch&&!disposed&&!doc.isClosed&&doc.version===version&&doc.getText()===text&&vscode.window.activeTextEditor?.document===doc&&vscode.workspace.isTrusted;
 const command=operation=>async()=>{
  const doc=vscode.window.activeTextEditor?.document;if(disposed||!vscode.workspace.isTrusted||doc?.uri.scheme!=='file'||!doc.uri.fsPath.endsWith('.sol'))return;
  const uri=doc.uri.toString();documents.set(uri,doc);touch(uri);const epoch=epochs.get(uri),commandId=randomUUID();let version=doc.version,text=doc.getText(),job;
  const receipt=(phase,extra={})=>output.appendLine(JSON.stringify({schemaVersion:1,kind:'source-command',commandId,operation,phase,uri,version,sourceHash:digest(text),sourceSession:epoch,verification:'not-run',...extra}));
  try{
   // The new epoch already invalidates the previous result. Retire that work
   // before awaiting a prompt which may be cancelled without admitting a job.
   await stop(uri);if(!isCurrent(doc,version,text,epoch))return;
   if(doc.isUntitled||!await doc.save())return;version=doc.version;text=doc.getText();let input={};
   if(operation==='buildCustomArgs'){
    const configured=settings(doc),value=await vscode.window.showInputBox({prompt:'Compiler import options as JSON (includePaths, remappings only)',value:JSON.stringify({includePaths:configured.includePaths||[],remappings:configured.remappings||[]})});if(value===undefined)return;input=buildArguments(JSON.parse(value));
   }else if(operation==='run'){
    const target=await vscode.window.showInputBox({prompt:'Concrete typed-model call: Contract::function(signature)'});if(target===undefined)return;selection(target);
    const args=await vscode.window.showInputBox({prompt:'Arguments as JSON booleans/integer strings',value:'[]'});if(args===undefined)return;input={target,args:JSON.parse(args)};argumentsOf(input.args);
   }else if(operation==='test'){
    const chosen=await vscode.window.showOpenDialog({canSelectMany:false,filters:{'Concrete Solidity tests':['json']},openLabel:'Run typed-model tests'});if(!chosen?.length)return;
    if(fs.statSync(chosen[0].fsPath).size>32*1024*1024)throw Error('Concrete tests exceed32MiB');input=JSON.parse(fs.readFileSync(chosen[0].fsPath,'utf8'));if(input.schemaVersion!==1)throw Error('Concrete test schemaVersion must be1');
   }
   if(!isCurrent(doc,version,text,epoch))return;if(fs.readFileSync(doc.uri.fsPath,'utf8')!==text)throw Error('Save the source before running commands');
   await stop(uri);if(!isCurrent(doc,version,text,epoch))return;cancelVerification?.(doc.uri);
   const abort=new AbortController();job={abort,document:doc,version,text};output.show(true);output.appendLine(operation+': '+doc.uri.fsPath);receipt('started');
   job.promise=execute(operation,settings(doc),doc.uri.fsPath,input,abort.signal);jobs.set(uri,job);
   job.promise.catch(error=>{if(error.cleanupFailed&&!retiring.has(uri)){const poison=Promise.reject(error);poison.catch(recordFailure);retiring.set(uri,poison);}});
   try{
    const report=await job.promise;if(!isCurrent(doc,version,text,epoch)||abort.signal.aborted||jobs.get(uri)!==job)return;
    if(report.sourceHash!==digest(text))throw Error('Source changed before command admission');output.appendLine(JSON.stringify(report,null,2));receipt('completed',{artifact:report.artifact});if(report.passed===false)vscode.window.showErrorMessage('Concrete '+operation+' failed; see output. No verification verdict was produced.');return report;
   }finally{if(jobs.get(uri)===job)jobs.delete(uri);}
  }catch(error){
   if(error.cleanupFailed)recordFailure(error);
   if(error.code!=='CANCELLED'&&isCurrent(doc,version,text,epoch)&&!job?.abort.signal.aborted){receipt('failed',{admitted:!!job,message:error.message,code:error.code||'SOURCE_COMMAND_FAILED'});vscode.window.showErrorMessage(error.message);}
  }
 };
 function dispose(){if(disposal)return disposal;disposed=true;disposal=stop();return disposal;}
 const subscriptions=['build','run','test','buildCustomArgs'].map(operation=>vscode.commands.registerCommand('solidityLean.'+operation,command(operation)));
 if(vscode.workspace.onDidChangeTextDocument)subscriptions.push(vscode.workspace.onDidChangeTextDocument(event=>{if(event.contentChanges.length){touch(event.document.uri.toString());stop(event.document.uri.toString()).catch(recordFailure);}}));
 if(vscode.workspace.onDidCloseTextDocument)subscriptions.push(vscode.workspace.onDidCloseTextDocument(doc=>{const uri=doc.uri.toString();touch(uri);documents.delete(uri);epochs.delete(uri);stop(uri).catch(recordFailure);}));
 if(vscode.workspace.onDidChangeConfiguration)subscriptions.push(vscode.workspace.onDidChangeConfiguration(event=>{for(const [uri,doc]of documents)if(['backendPath','nodePath','timeoutMs','includePaths','remappings','compilerOutputDir'].some(key=>event.affectsConfiguration('solidityLean.'+key,doc.uri))){touch(uri);stop(uri).catch(recordFailure);}}));
 subscriptions.push({dispose:()=>{dispose().catch(recordFailure);}});context.subscriptions.push(...subscriptions);return{cancel:uri=>{if(uri===undefined)for(const key of epochs.keys())touch(key);else touch(uri);const result=stop(uri);result.catch(recordFailure);return result;},dispose};
}
module.exports={execute,install,selection,argumentsOf,buildArguments,processJob};
