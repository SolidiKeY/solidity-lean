'use strict';
const test=require('node:test'),assert=require('node:assert/strict');
const {observeSymbolProviders}=require('../parity/symbol-provider-observer.cjs');
function fixture(record){
 const events=[],registrations=[];let listener,disposed=0;
 const disposable={dispose(){}};
 const vscode={workspace:{onDidCloseTextDocument(fn){listener=fn;return{dispose(){disposed++;}};}},languages:{registerDocumentSymbolProvider(...args){registrations.push(args);return disposable;}}};
 const observation=observeSymbolProviders(vscode,record||((kind,data)=>events.push({kind,data})),()=> 'owned-session');
 const doc={uri:{toString:()=> 'file:///source.sol'},version:1,languageId:'solidity',isClosed:false,getText:()=> 'contract C {}'};
 return{observation,events,registrations,doc,disposable,close:()=>listener(doc),disposed:()=>disposed};
}
test('symbol observer preserves registration arguments, private receiver and synchronous result identity',()=>{
 const f=fixture(),selector={language:'solidity'},metadata={label:'actual'},result=[];
 class Provider{#value=result;provideDocumentSymbols(){return this.#value;}}
 assert.equal(f.observation.languages.registerDocumentSymbolProvider(selector,new Provider(),metadata),f.disposable);
 const [actual,provider,meta]=f.registrations[0];assert.equal(actual,selector);assert.equal(meta,metadata);
 assert.equal(provider.provideDocumentSymbols(f.doc,{}),result);
 assert.deepEqual(f.events.map(e=>e.kind),['symbolProvider.register','symbolProvider.start','symbolProvider.end']);
 assert.equal(f.events.at(-1).data.outcome,'returned');f.observation.dispose();
});
test('symbol observer preserves actual promise and rejection identity',async()=>{
 const f=fixture(),error=new Error('actual failure'),promise=Promise.reject(error);
 f.observation.languages.registerDocumentSymbolProvider({}, {provideDocumentSymbols:()=>promise});
 assert.equal(f.registrations[0][1].provideDocumentSymbols(f.doc,{}),promise);
 await assert.rejects(promise,e=>e===error);await Promise.resolve();
 assert.equal(f.events.at(-1).data.outcome,'rejected');f.observation.dispose();
});
test('recording failures and throwing cancellation getters do not replace product return or throw',()=>{
 const f=fixture(()=>{throw Error('disk failure');}),expected=new Error('provider failure');let calls=0;
 f.observation.languages.registerDocumentSymbolProvider({}, {provideDocumentSymbols(){calls++;throw expected;}});
 const token={get isCancellationRequested(){throw Error('token diagnostic failure');}};
 assert.throws(()=>f.registrations[0][1].provideDocumentSymbols(f.doc,token),e=>e===expected);
 assert.equal(calls,1);assert.ok(f.observation.failures.length>=2);f.observation.dispose();
});
test('same document public close events change diagnostic epoch without inventing a new session',()=>{
 const f=fixture();f.observation.languages.registerDocumentSymbolProvider({}, {provideDocumentSymbols:()=>undefined});
 const provider=f.registrations[0][1];provider.provideDocumentSymbols(f.doc,{});f.close();
 f.doc.languageId='plaintext';provider.provideDocumentSymbols(f.doc,{});
 const starts=f.events.filter(e=>e.kind==='symbolProvider.start').map(e=>e.data.source);
 assert.deepEqual(starts.map(s=>s.publicCloseEvents),[0,1]);assert.equal(starts[0].session,starts[1].session);
 f.doc.isClosed=true;f.doc.getText=()=>{throw Error('closed content read');};provider.provideDocumentSymbols(f.doc,{});
 assert.equal(f.events.at(-1).data.source.closed,true);assert.equal(f.events.at(-1).data.source.unavailable,undefined);
 f.observation.dispose();f.observation.dispose();assert.equal(f.disposed(),1);
});
test('unsupported thenable is not assimilated and late completions after disposal are not recorded',async()=>{
 const f=fixture();let thenReads=0,resolve;
 const thenable={get then(){thenReads++;throw Error('must not read');}};
 f.observation.languages.registerDocumentSymbolProvider({}, {provideDocumentSymbols:()=>thenable});
 assert.equal(f.registrations[0][1].provideDocumentSymbols(f.doc,{}),thenable);assert.equal(thenReads,0);
 assert.equal(f.events.at(-1).data.outcome,'unobserved-object');
 const promise=new Promise(r=>resolve=r);f.observation.languages.registerDocumentSymbolProvider({}, {provideDocumentSymbols:()=>promise});
 assert.equal(f.registrations[1][1].provideDocumentSymbols(f.doc,{}),promise);f.observation.dispose();const count=f.events.length;
 resolve([]);await promise;await Promise.resolve();assert.equal(f.events.length,count);
});

test('frozen provider and frozen API methods preserve forwarding and actual receiver',()=>{
 const f=fixture(),result=[];
 // Rebuild around a frozen API, whose own method descriptors cannot be replaced
 // by a proxy directly targeting that API.
 let registered;const languages=Object.freeze({registerDocumentSymbolProvider(...args){assert.equal(this,languages);registered=args;return f.disposable;}});
 const observation=observeSymbolProviders({languages,workspace:{onDidCloseTextDocument(){return{dispose(){}};}}},()=>{},()=> 'session');
 const provider=Object.freeze({provideDocumentSymbols(){assert.equal(this,provider);return result;}});
 assert.equal(observation.languages.registerDocumentSymbolProvider({},provider),f.disposable);
 assert.equal('registerDocumentSymbolProvider' in observation.languages,true);
 assert.deepEqual(Object.keys(observation.languages),Object.keys(languages));
 assert.equal('provideDocumentSymbols' in registered[1],true);
 assert.deepEqual(Object.keys(registered[1]),Object.keys(provider));
 assert.equal(Object.getPrototypeOf(registered[1]),Object.getPrototypeOf(provider));
 assert.equal(registered[1].provideDocumentSymbols(f.doc,{}),result);
 observation.dispose();f.observation.dispose();
});

test('observer cleanup failure is retained without aborting caller cleanup',()=>{
 let attempted=0;const observed=observeSymbolProviders({languages:{},workspace:{onDidCloseTextDocument(){return{dispose(){attempted++;throw Error('close disposal failed');}};}}},()=>{},()=> 'session');
 assert.doesNotThrow(()=>observed.dispose());observed.dispose();assert.equal(attempted,1);
 assert.deepEqual(observed.failures,['close disposal failed']);
});

test('source snapshot failures are recorded without replacing provider return identity',()=>{
 const f=fixture(),value=[];f.observation.languages.registerDocumentSymbolProvider({}, {provideDocumentSymbols:()=>value});f.doc.getText=()=>{throw Error('actual source getter failed');};
 assert.equal(f.registrations[0][1].provideDocumentSymbols(f.doc,{}),value);assert.ok(f.observation.failures.some(error=>error==='actual source getter failed'));assert.equal(f.events.at(-1).data.source.unavailable,true);f.observation.dispose();
});

test('recording finalization keeps original failure/status and snapshots observer cleanup errors',()=>{
 const {finalizeRecording,recordingErrors}=require('../parity/symbol-provider-observer.cjs');
 for(const status of ['passed','passed-with-gaps','broken','timeout']){const scenarios=[{id:'original',status:'broken'}],failures=['actual cleanup failure'],result={status,error:'original request failure',scenarios};
 assert.equal(finalizeRecording(result,failures).length,1);assert.equal(result.status,status==='timeout'?'timeout':'broken');assert.equal(result.error,'original request failure');assert.equal(result.scenarios,scenarios);failures.push('later');assert.deepEqual(result.observations.symbolProviderRecordingFailures,['actual cleanup failure']);}
 const result={status:'passed-with-gaps'};assert.deepEqual(finalizeRecording(result,[]),[]);assert.equal(result.status,'passed-with-gaps');assert.equal(result.error,undefined);
 const missing={status:'passed'};assert.ok(finalizeRecording(missing,undefined).length);assert.equal(missing.status,'broken');
 for(const value of [{},[null],[''],Array(1)])assert.match(recordingErrors(value)[0],/malformed/);
});
