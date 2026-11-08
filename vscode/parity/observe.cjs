'use strict';
const Module = require('node:module');
const {performance} = require('node:perf_hooks');
const childProcess=require('node:child_process');
const {appendFileSync}=require('node:fs');
const {LspFrames}=require('./core.cjs');
const {sep}=require('node:path');
const {createHash,randomUUID}=require('node:crypto');

/** Observe calls on real VS Code objects. No mocked renderer or verifier. */
function observe(vscode, record, extensionPath, tracePath,workspacePath,options={}) {
  const controllers = [], profiles = [], decorations = [], outputs=[], finalizers=[];
  function instrument(object, handlers) {
    return new Proxy(object, {get(target,key) {
      if (handlers[key]) return handlers[key];
      const value = Reflect.get(target,key);
      return typeof value === 'function' ? value.bind(target) : value;
    }});
  }
  const sessions=new WeakMap();let commandSequence=0,outputSequence=0;
  const diagnostic=value=>{try{return value instanceof Error?value.message:String(value);}catch{return 'Unprintable observation error';}};
  const commandSource=()=>{try{const doc=vscode.window.activeTextEditor?.document;if(!doc)return null;if(!sessions.has(doc))sessions.set(doc,randomUUID());return{uri:doc.uri.toString(),version:doc.version,session:sessions.get(doc),textHash:createHash('sha256').update(doc.getText()).digest('hex'),dirty:doc.isDirty,closed:doc.isClosed,trusted:vscode.workspace.isTrusted};}catch(error){return{unavailable:true,reason:diagnostic(error)};}};
  const api = {...vscode,
    env:vscode.env&&instrument(vscode.env,{clipboard:instrument(vscode.env.clipboard,{writeText(text){record('clipboard.write',{sha256:createHash('sha256').update(text).digest('hex'),source:commandSource()});return vscode.env.clipboard.writeText(text);}})}),
    commands:vscode.commands&&instrument(vscode.commands,{registerCommand(id,handler,thisArg){
      return vscode.commands.registerCommand(id,function(...args){
        if(restored)return handler.apply(this,args);
        const invocationId=++commandSequence;record('command.start',{id,invocationId,source:commandSource()});
        const end=value=>{if(!restored)record('command.end',{id,invocationId,source:commandSource(),result:typeof value==='boolean'?value:null});return value;};
        const error=error=>{if(!restored)record('command.error',{id,invocationId,source:commandSource(),message:diagnostic(error)});throw error;};
        let result;try{result=handler.apply(this,args);}catch(e){return error(e);}
        return result&&typeof result.then==='function'?result.then(end,error):end(result);
      },thisArg);
    }}),
    tests:instrument(vscode.tests, {createTestController(...args) {
      const controller = vscode.tests.createTestController(...args); controllers.push(controller);
      return instrument(controller, {
        createRunProfile(name,kind,handler,...rest) {
          profiles.push({controller,name,handler});
          return controller.createRunProfile(name,kind,handler,...rest);
        },
        createTestRun(...params) {
          const run = controller.createTestRun(...params);
          const handlers = {};
          for (const name of ['enqueued','started','passed','failed','errored','skipped','end']) handlers[name] = (...values) => {
            record('test.'+name,{id:values[0]?.id,label:values[0]?.label});
            return run[name](...values);
          };
          return instrument(run,handlers);
        }
      });
    }}),
    window:instrument(vscode.window, {
      createTextEditorDecorationType(options) {
        const type = vscode.window.createTextEditorDecorationType(options);
        decorations.push({key:type.key,options}); record('decoration.register',{key:type.key,options}); return type;
      },
      createOutputChannel(...args) {
        const channel = vscode.window.createOutputChannel(...args),channelId=++outputSequence;
        record('output.create',{channel:args[0],channelId});
        const observed=instrument(channel, {appendLine(text) {record('output',{channel:args[0],channelId,text}); return channel.appendLine(text);},show(...values){record('output.show',{channel:args[0],channelId});return channel.show(...values);},dispose(){record('output.dispose',{channel:args[0],channelId});return channel.dispose();}});outputs.push({name:args[0],channelId,channel:observed});return observed;
      },
      showInformationMessage(...args){record('information',{message:args[0],source:commandSource()});return vscode.window.showInformationMessage(...args);},
      showErrorMessage(...args) {record('error',{message:args[0]}); return vscode.window.showErrorMessage(...args);}
    })
  };
  let restored=false;const executions=new WeakMap();let sequence=0;const identity=execution=>{if(!executions.has(execution))executions.set(execution,++sequence);return executions.get(execution);};
  const terminalSupported=!!vscode.window.onDidStartTerminalShellExecution&&!!vscode.window.onDidEndTerminalShellExecution;
  const ownedTerminals=new Set(),relevant=(execution,terminal)=>ownedTerminals.has(terminal)||workspacePath&&execution.commandLine.value.includes(workspacePath);
  const terminalSubscriptions=[];
  if(terminalSupported){
    terminalSubscriptions.push(vscode.window.onDidStartTerminalShellExecution(event=>{if(!relevant(event.execution,event.terminal))return;if(restored)return;const commandLine=event.execution.commandLine.value,executionId=identity(event.execution);record('terminal.start',{commandLine,executionId});(async()=>{try{let bytes=0;for await(const data of event.execution.read()){if(restored)break;bytes+=Buffer.byteLength(data);if(bytes>32*1024*1024){record('terminal.output.error',{commandLine,executionId,message:'Terminal observation exceeds existing32MiB output bound'});return;}record('terminal.output',{commandLine,executionId,data});}if(!restored)record('terminal.output.end',{commandLine,executionId});}catch(error){if(!restored)record('terminal.output.error',{commandLine,executionId,message:diagnostic(error)});}})();}));
    terminalSubscriptions.push(vscode.window.onDidEndTerminalShellExecution(event=>{if(!restored&&relevant(event.execution,event.terminal))record('terminal.end',{commandLine:event.execution.commandLine.value,executionId:identity(event.execution),exitCode:event.exitCode});}));
  }
  const original = Module._load;
  let processSequence=0;
  const spawnObserved=(...args)=>{
    if(restored)return childProcess.spawn(...args);
    const child=childProcess.spawn(...args);
    const owner={processSession:randomUUID(),processSequence:++processSequence,pid:child.pid,birth:require('../src/process-state.cjs').processState(child.pid)?.birth};
    record('process.spawn',{...owner,executable:args[0],args:args[1]||[],cwd:args[2]?.cwd});
    if(options.captureServerArtifacts&&args[1]?.some(a=>a==='server'||typeof a==='string'&&a.endsWith('lsp-server.cjs'))){
      const fs=require('node:fs'),path=require('node:path'),describe=file=>({file:fs.realpathSync(file),bytes:fs.statSync(file).size,sha256:createHash('sha256').update(fs.readFileSync(file)).digest('hex')});
      try{const directory=path.dirname(args[0]),files=[args[0],...(args[1]||[]).filter(a=>typeof a==='string'&&path.isAbsolute(a)&&fs.existsSync(a)&&fs.statSync(a).isFile()),...fs.readdirSync(directory).filter(name=>/^Dafny.*\.dll$/.test(name)||name.endsWith('.runtimeconfig.json')).map(name=>path.join(directory,name))];
        record('process.artifacts',{...owner,files:[...new Set(files)].map(file=>{const actual=describe(file),reference=options.artifactReferenceDirectory&&path.join(options.artifactReferenceDirectory,path.basename(file));return{...actual,...(reference&&fs.existsSync(reference)?{reference:describe(reference)}:{})};})});
      }catch(error){record('process.artifacts.error',{...owner,message:diagnostic(error)});}
    }
    child.once('error',error=>!restored&&record('process.error',{...owner,message:diagnostic(error)}));
    child.once('exit',(code,signal)=>!restored&&record('process.exit',{...owner,code,signal}));
    child.once('close',(code,signal)=>!restored&&record('process.close',{...owner,code,signal}));
    if(tracePath&&(args[1]?.includes('server')||args[1]?.some(a=>typeof a==='string'&&a.endsWith('lsp-server.cjs')))&&child.stdin&&child.stdout) {
      const parser=direction=>{
        const frames=new LspFrames();
        let finalized=false;
        frames.on('message',message=>appendFileSync(tracePath,JSON.stringify({time:Date.now(),...owner,direction,message})+'\n'));
        const finish=()=>{
          if(finalized)return;finalized=true;
          try{frames.end();appendFileSync(tracePath,JSON.stringify({...owner,direction,framingFinalized:true})+'\n');}
          catch(error){appendFileSync(tracePath,JSON.stringify({...owner,direction,error:error.message})+'\n');}
        };
        finalizers.push(finish);
        (direction==='server'?child.stdout:child.stdin).once(direction==='server'?'end':'finish',finish);
        return chunk=>{if(finalized)return;try{frames.push(Buffer.isBuffer(chunk)?chunk:Buffer.from(chunk));}catch(error){appendFileSync(tracePath,JSON.stringify({...owner,direction,error:error.message})+'\n');}};
      };
      child.stdout.on('data',parser('server'));
      const outgoing=parser('client'),write=child.stdin.write.bind(child.stdin);
      child.stdin.write=function(chunk,...rest){outgoing(chunk);return write(chunk,...rest);};
    }
    return child;
  };
  // Preserve identities/custom promisify implementations on execFile and exec.
  const processes=new Proxy(childProcess,{get(target,key){return key==='spawn'?spawnObserved:Reflect.get(target,key);}});
  Module._load = function(request,parent,isMain) {
    if (request === 'vscode' && parent?.filename.startsWith(extensionPath+sep)) return api;
    if (['child_process','node:child_process'].includes(request)&&parent?.filename.startsWith(extensionPath+sep)) return processes;
    return original.call(this,request,parent,isMain);
  };
  const registration = vscode.languages.onDidChangeDiagnostics(event => {
    for (const uri of event.uris) record('diagnostics',{uri:uri.toString(),diagnostics:vscode.languages.getDiagnostics(uri)});
  });
  return {controllers,profiles,decorations,outputs,terminalSupported,ownTerminal:terminal=>ownedTerminals.add(terminal),restore() { restored=true;for(const subscription of terminalSubscriptions)subscription.dispose(); finalizers.forEach(f=>f());Module._load = original; registration.dispose(); }};
}
module.exports = {observe};
