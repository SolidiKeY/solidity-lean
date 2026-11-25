// Regression: delayed editor provider results cannot survive source/language epochs.
// Injected VS Code/service boundary, not native rendering or kernel evidence.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),{fixture}=require('./controller-fixture.cjs');
function setup(){let provider,release,signal;const e=fixture(undefined,env=>{
 env.vscode.DocumentSymbol=class{constructor(name,detail,kind,range,selectionRange){Object.assign(this,{name,detail,kind,range,selectionRange});}};
 env.vscode.languages.registerDocumentSymbolProvider=(_selector,p)=>{provider=p;return{dispose(){}};};
 env.service.request=(_method,_doc,_params,options)=>{signal=options.signal;return new Promise(resolve=>release=resolve);};
 });
 const row={name:'f',kind:12,range:{start:{line:0,character:0},end:{line:0,character:1}},selectionRange:{start:{line:0,character:0},end:{line:0,character:1}}};
 return{e,provider,row,finish:()=>release([row]),signal:()=>signal};
}
test('current document symbol response retains compiler name and range',async()=>{const f=setup();try{const pending=f.provider.provideDocumentSymbols(f.e.doc);f.finish();const rows=await pending;assert.equal(rows.length,1);assert.equal(rows[0].name,'f');assert.equal(rows[0].kind,11);}finally{await f.e.api.dispose();}});
test('delayed symbol response is refused across reused-object language lifecycle',async()=>{const f=setup();try{const doc=f.e.doc,pending=f.provider.provideDocumentSymbols(doc);doc.languageId='plaintext';f.e.events.close(doc);f.e.events.open(doc);doc.languageId='solidity';f.e.events.close(doc);f.e.events.open(doc);assert.equal(f.e.doc,doc);f.finish();assert.deepEqual(await pending,[]);}finally{await f.e.api.dispose();}});
test('ignored cancellation source/version close/reopen restart and disposal cannot publish stale symbols',async()=>{
 for(const mode of ['cancel','text','version','closed','replaced','restart','dispose']){const f=setup(),token=new f.e.vscode.CancellationTokenSource();try{const pending=f.provider.provideDocumentSymbols(f.e.doc,token.token);
 if(mode==='cancel')token.cancel();else if(mode==='text')f.e.doc.text+=' ';else if(mode==='version')f.e.doc.version++;else if(mode==='closed')f.e.doc.isClosed=true;else if(mode==='replaced')f.e.vscode.workspace.textDocuments=[{...f.e.doc}];else if(mode==='restart')await f.e.vscode.commands.executeCommand('solidityLean.restartServer');else await f.e.api.dispose();
 if(mode==='cancel')assert.equal(f.signal().aborted,true);f.finish();assert.deepEqual(await pending,[],mode);
 }finally{token.dispose();await f.e.api.dispose();}}
});
test('unrelated document edits do not invalidate the owned symbol response',async()=>{const f=setup();try{const pending=f.provider.provideDocumentSymbols(f.e.doc);f.e.documents[1].text+=' ';f.e.events.change({document:f.e.documents[1],contentChanges:[{}]});f.finish();assert.equal((await pending).length,1);}finally{await f.e.api.dispose();}});

test('already cancelled provider request never reaches the service',async()=>{const f=setup(),token=new f.e.vscode.CancellationTokenSource();let calls=0;f.e.service.request=async()=>{calls++;return[f.row];};try{token.cancel();assert.deepEqual(await f.provider.provideDocumentSymbols(f.e.doc,token.token),[]);assert.equal(calls,0);}finally{token.dispose();await f.e.api.dispose();}});
test('raw rename preparation rejects a delayed result from the old language epoch',async()=>{
 let provider,release;const e=fixture(undefined,env=>{env.vscode.languages.registerRenameProvider=(_s,p)=>{provider=p;return{dispose(){}};};env.service.request=()=>new Promise(r=>release=r);});
 try{const pending=provider.prepareRename(e.doc,{line:0,character:0});e.events.close(e.doc);e.events.open(e.doc);release({placeholder:'f',range:{start:{line:0,character:0},end:{line:0,character:1}}});await assert.rejects(pending,error=>error.code===-32801);}finally{await e.api.dispose();}
});
