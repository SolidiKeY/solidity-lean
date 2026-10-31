'use strict';
const Module = require('node:module');
const {performance} = require('node:perf_hooks');
const childProcess=require('node:child_process');
const {appendFileSync}=require('node:fs');
const {LspFrames}=require('./core.cjs');
const {sep}=require('node:path');

/** Observe calls on real VS Code objects. No mocked renderer or verifier. */
function observe(vscode, record, extensionPath, tracePath) {
  const controllers = [], profiles = [], decorations = [];
  function instrument(object, handlers) {
    return new Proxy(object, {get(target,key) {
      if (handlers[key]) return handlers[key];
      const value = Reflect.get(target,key);
      return typeof value === 'function' ? value.bind(target) : value;
    }});
  }
  const api = {...vscode,
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
        const channel = vscode.window.createOutputChannel(...args);
        return instrument(channel, {appendLine(text) {record('output',{channel:args[0],text}); return channel.appendLine(text);}});
      },
      showErrorMessage(...args) {record('error',{message:args[0]}); return vscode.window.showErrorMessage(...args);}
    })
  };
  const original = Module._load;
  const spawnObserved=(...args)=>{
    const child=childProcess.spawn(...args);
    if(tracePath&&(args[1]?.includes('server')||args[1]?.some(a=>typeof a==='string'&&a.endsWith('lsp-server.cjs')))&&child.stdin&&child.stdout) {
      const parser=direction=>{
        const frames=new LspFrames();
        frames.on('message',message=>appendFileSync(tracePath,JSON.stringify({time:Date.now(),direction,message})+'\n'));
        return chunk=>{try{frames.push(Buffer.isBuffer(chunk)?chunk:Buffer.from(chunk));}catch(error){appendFileSync(tracePath,JSON.stringify({direction,error:error.message})+'\n');}};
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
  return {controllers,profiles,decorations,restore() { Module._load = original; registration.dispose(); }};
}
module.exports = {observe};
