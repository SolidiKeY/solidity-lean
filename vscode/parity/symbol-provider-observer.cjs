'use strict';
const {createHash}=require('node:crypto');
const {performance}=require('node:perf_hooks');
const {argumentSnapshot}=require('./code-action-lifecycle.cjs');

// Diagnostic provider calls, not attestation that executeDocumentSymbolProvider
// consumed a particular result or that any returned symbol was rendered.
function observeSymbolProviders(vscode,record,sessionFor){
  let stopped=false,registrationId=0,invocationId=0;
  const epochs=new WeakMap(),failures=[];
  const reason=e=>{try{return String(e?.message??e);}catch{return 'unprintable';}};
  const capture=fn=>{try{fn();}catch(e){failures.push(reason(e));}};
  const emit=(kind,data)=>{try{record(kind,{monotonicMs:performance.now(),...data});}catch(e){failures.push(reason(e));}};
  const close=vscode.workspace.onDidCloseTextDocument(doc=>epochs.set(doc,(epochs.get(doc)||0)+1));
  const source=doc=>{try{
    const state={uri:doc.uri.toString(),version:doc.version,languageId:doc.languageId,closed:doc.isClosed,session:sessionFor(doc),publicCloseEvents:epochs.get(doc)||0};
    return state.closed?state:{...state,textHash:createHash('sha256').update(doc.getText()).digest('hex')};
  }catch(e){const failure=reason(e);failures.push(failure);return {unavailable:true,reason:failure};}};
  // Neutral targets cannot expose frozen source descriptors as nonconfigurable.
  // Enumeration/capability checks still reflect the actual public members.
  const reflection=object=>({has:(_target,key)=>Reflect.has(object,key),ownKeys:()=>Reflect.ownKeys(object),getPrototypeOf:()=>Reflect.getPrototypeOf(object),getOwnPropertyDescriptor(_target,key){const descriptor=Reflect.getOwnPropertyDescriptor(object,key);return descriptor?{...descriptor,configurable:true}:undefined;}});
  const languages=new Proxy(Object.create(null),{...reflection(vscode.languages),get(_target,key){
    const target=vscode.languages;
    if(key!=='registerDocumentSymbolProvider'){const value=Reflect.get(target,key);return typeof value==='function'?value.bind(target):value;}
    return function(selector,provider,...rest){
      if(stopped)return target.registerDocumentSymbolProvider(selector,provider,...rest);
      const id=++registrationId;
      emit('symbolProvider.register',{registrationId:id,selector:argumentSnapshot(selector),metadata:argumentSnapshot(rest)});
      // Forward all properties/method receivers to the actual provider, including
      // classes with private fields. Return its original disposable and promise.
      const wrapped=new Proxy(Object.create(null),{...reflection(provider),get(_object,property){
        const object=provider;
        const value=Reflect.get(object,property,object);
        if(property!=='provideDocumentSymbols')return typeof value==='function'?value.bind(object):value;
        if(typeof value!=='function')return value;
        return function(doc,token){
          if(stopped)return value.call(object,doc,token);
          const call=++invocationId;
          capture(()=>emit('symbolProvider.start',{registrationId:id,invocationId:call,source:source(doc),cancelled:token?.isCancellationRequested===true}));
          const finish=(outcome,result)=>capture(()=>{if(!stopped)emit('symbolProvider.end',{registrationId:id,invocationId:call,outcome,source:source(doc),cancelled:token?.isCancellationRequested===true,result:argumentSnapshot(result)});});
          let result;
          try{result=value.call(object,doc,token);}catch(error){finish('throw',reason(error));throw error;}
          // Native promises can be observed without replacing the returned value.
          // Never assimilate arbitrary thenables or execute a then accessor.
          capture(()=>{if(result instanceof Promise){Promise.prototype.then.call(result,v=>finish('fulfilled',v),e=>finish('rejected',reason(e)));}
          else if(result===null||typeof result!=='object')finish('returned',result);
          else if(Array.isArray(result))finish('returned',result);
          else finish('unobserved-object',{$diagnostic:'unsupported-return-object'});});
          return result;
        };
      }});
      return target.registerDocumentSymbolProvider(selector,wrapped,...rest);
    };
  }});
  return {languages,failures,dispose(){if(stopped)return;stopped=true;capture(()=>close.dispose());}};
}
function recordingErrors(failures){
 if(!Array.isArray(failures)||!Array.from(failures).every(error=>typeof error==='string'&&error.length))return['Missing or malformed symbol provider recording health'];
 return failures.map(error=>'Symbol provider recording failed: '+error);
}
function finalizeRecording(result,failures){
 result.observations??={};result.observations.symbolProviderRecordingFailures=Array.isArray(failures)?failures.slice():failures;
 const errors=recordingErrors(failures);if(errors.length){if(!['broken','timeout'].includes(result.status))result.status='broken';if(result.error===undefined)result.error=errors.join('\n');}return errors;
}
module.exports={observeSymbolProviders,recordingErrors,finalizeRecording};
