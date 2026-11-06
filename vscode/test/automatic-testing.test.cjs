// Injected editor/service boundary; terminal outcomes below are fixtures, not proof evidence.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),{EventEmitter}=require('node:events'),{createHash}=require('node:crypto');
const {mock,leaves}=require('./mock.cjs'),{createExtension}=require('../src/extension.cjs');
const tick=()=>new Promise(r=>setImmediate(r)),noop=()=>({dispose(){}});
const {fixture,row}=require('./controller-fixture.cjs');
const packet=(doc,rows=[row(doc)])=>({uri:doc.uri.toString(),version:doc.version,sourceHash:createHash('sha256').update(doc.text).digest('hex'),report:{results:rows,errors:[]}});
const calls=run=>run.calls.map(c=>c[0]);
test('automatic terminal report creates one run without user action; duplicates do not create another',async()=>{
 const e=fixture();try{const p=packet(e.doc);e.service.emit('report',p);assert.equal(e.runs.length,1);assert.deepEqual(calls(e.runs[0]),['passed','end']);e.service.emit('report',structuredClone(p));assert.equal(e.runs.length,1);}finally{await e.api.dispose();}
});
test('automatic direct, unknown, audit and unsupported outcomes retain existing model classifications',async()=>{
 const e=fixture();try{const rows=[{...row(e.doc),function:'direct',verification:'direct'},{...row(e.doc),function:'audit',preconditions:'unknown'},{...row(e.doc),function:'unknown',status:'pending',verification:'direct'},{...row(e.doc),function:'unsupported',status:'unsupported'}];rows.forEach(row=>row.signature=row.function+'()');e.service.emit('report',packet(e.doc,rows));assert.equal(e.runs.length,1);assert.deepEqual(calls(e.runs[0]),['passed','errored','skipped','errored','end']);assert.match(leaves([...e.controller.items.values()][0])[0].description,/correct/);}finally{await e.api.dispose();}
});

function progress(e,doc,status='running',overrides={}){const r=row(doc);e.service.emit('status',{uri:doc.uri.toString(),version:doc.version,sourceHash:r.sourceHash,state:status==='queued'?'queued':'running',progressScope:'functions',functions:[{name:'C.f()',range:r.range,status}],...overrides});}
async function listed(e,doc=e.doc){await e.api.verify(doc,{listing:true});assert.equal(e.runs.length,0);}
test('genuine per-function queued/running states share a run through report terminal; duplicates are idempotent',async()=>{
 const e=fixture();try{await listed(e);progress(e,e.doc,'queued');progress(e,e.doc,'queued');progress(e,e.doc);progress(e,e.doc);e.service.emit('report',packet(e.doc));e.service.emit('report',packet(e.doc));assert.equal(e.runs.length,1);assert.deepEqual(calls(e.runs[0]),['enqueued','started','passed','end']);}finally{await e.api.dispose();}
});
test('document-wide work never fabricates per-function start; ready/listing/empty reports never pass',async()=>{
 const e=fixture();try{await listed(e);progress(e,e.doc,'running',{progressScope:'document'});assert.equal(e.runs.length,0);e.service.emit('report',packet(e.doc,[{...row(e.doc),status:'ready'}]));e.service.emit('report',packet(e.doc,[]));assert.equal(e.runs.length,0);}finally{await e.api.dispose();}
});
test('multi-file automatic ownership survives unrelated file close; ended runs never feedback cancellation',async()=>{
 const e=fixture();try{await listed(e);await listed(e,e.documents[1]);progress(e,e.doc);progress(e,e.documents[1]);assert.equal(e.runs.length,2);e.doc.isClosed=true;e.events.close(e.doc);assert.deepEqual(calls(e.runs[0]),['started','skipped','end']);assert.deepEqual(calls(e.runs[1]),['started']);const cancels=e.calls.cancels;e.runs[0].cancel();assert.equal(e.calls.cancels,cancels);e.service.emit('report',packet(e.documents[1]));assert.deepEqual(calls(e.runs[1]),['started','passed','end']);}finally{await e.api.dispose();}
});
for(const cause of ['edit','invalidated','compiler-error','cancel','crash','restart','visibility','dispose'])test(`automatic ${cause} ends once and rejects late successful revival`,async()=>{
 const e=fixture();try{await listed(e);progress(e,e.doc);const old=packet(e.doc);
 if(cause==='edit'){e.doc.version++;e.doc.text+=' ';e.events.change({document:e.doc,contentChanges:[{}]});}
 else if(cause==='invalidated')e.service.emit('invalidated',{uri:e.doc.uri.toString(),version:e.doc.version});
 else if(cause==='compiler-error')progress(e,e.doc,'running',{state:'error',phase:'compilation',message:'compiler rejected source'});
 else if(cause==='cancel')e.commands.get('solidityLean.cancel')();
 else if(cause==='crash')e.service.emit('serverError',Object.assign(Error('crash'),{uris:[e.doc.uri.toString()]}));
 else if(cause==='restart')await e.commands.get('solidityLean.restartServer')();
 else if(cause==='visibility'){e.config.displayVerificationAsTests=false;e.changeConfig('solidityLean.displayVerificationAsTests');}
 else await e.api.dispose();
 // Terminal packets for retired generations are filtered by the production client; at this injected
 // service boundary only edit/hash/hidden/disposed guards can be exercised authentically.
 if(['edit','visibility','dispose','compiler-error','cancel'].includes(cause))e.service.emit('report',old);
 assert.equal(e.runs[0].calls.filter(c=>c[0]==='end').length,1);assert.equal(e.runs[0].calls.filter(c=>c[0]==='passed').length,0);
 assert.equal(e.runs.length,1);
 }finally{await e.api.dispose();}
});
test('automatic native cancellation stops work once, blocks late terminal and permits a new queued attempt',async()=>{
 const e=fixture();try{await listed(e);progress(e,e.doc);const before=e.calls.cancels;e.runs[0].cancel();assert.equal(e.calls.cancels,before+1);e.service.emit('report',packet(e.doc));assert.equal(e.runs.length,1);assert.deepEqual(calls(e.runs[0]),['started','skipped','end']);progress(e,e.doc,'queued');e.service.emit('report',packet(e.doc));assert.equal(e.runs.length,2);assert.deepEqual(calls(e.runs[1]),['enqueued','passed','end']);}finally{await e.api.dispose();}
});
test('manual run owns status/report projection without creating a second automatic run',async()=>{
 const e=fixture(async args=>{progress(e,args.document);e.service.emit('report',packet(args.document));return packet(args.document).report;});try{
 // Listing backend is separate from verification so fixtures do not emit terminal proof claims on list.
 e.config.displayVerificationAsTests=true;e.service.emit('report',packet(e.doc,[{...row(e.doc),status:'ready'}]));
 const leaf=leaves([...e.controller.items.values()][0])[0];
 await e.controller.run({include:[leaf]},null);assert.equal(e.runs.length,1);assert.deepEqual(calls(e.runs[0]),['enqueued','started','passed','end']);e.service.emit('report',packet(e.doc));assert.equal(e.runs.length,1);
 }finally{await e.api.dispose();}
});
test('visibility off/on preserves duplicate terminal fingerprint and does not run verification',async()=>{
 const e=fixture();try{e.service.emit('report',packet(e.doc));assert.equal(e.runs.length,1);e.config.displayVerificationAsTests=false;e.changeConfig('solidityLean.displayVerificationAsTests');e.config.displayVerificationAsTests=true;e.changeConfig('solidityLean.displayVerificationAsTests');e.service.emit('report',packet(e.doc));assert.equal(e.runs.length,1);assert.equal(e.calls.restarts,0);}finally{await e.api.dispose();}
});
test('current source identity gates progress and terminal delivery',async()=>{
 const e=fixture();try{await listed(e);progress(e,e.doc,'running',{sourceHash:'wrong'});e.service.emit('report',{...packet(e.doc),sourceHash:'wrong'});progress(e,e.doc,'running',{version:e.doc.version-1});assert.equal(e.runs.length,0);}finally{await e.api.dispose();}
});

for(const status of ['skip','skipped','internal'])test(`terminal ${status} report and companion complete status do not double-run`,async()=>{
 const e=fixture();try{const p=packet(e.doc,[{...row(e.doc),status}]);e.service.emit('report',p);progress(e,e.doc,status,{state:'complete'});e.service.emit('report',p);assert.equal(e.runs.length,1);assert.deepEqual(calls(e.runs[0]),['skipped','end']);}finally{await e.api.dispose();}
});
test('cancel/hide/show retains stop ownership until a new verification attempt',async()=>{
 const e=fixture();try{await listed(e);progress(e,e.doc);e.runs[0].cancel();e.config.displayVerificationAsTests=false;e.changeConfig('solidityLean.displayVerificationAsTests');e.config.displayVerificationAsTests=true;e.changeConfig('solidityLean.displayVerificationAsTests');e.service.emit('report',packet(e.doc));assert.equal(e.runs.length,1);}finally{await e.api.dispose();}
});
for(const state of ['cancelled','error'])test(`queued ${state} can recover through a legitimate queued retry`,async()=>{
 const e=fixture();try{await listed(e);progress(e,e.doc,'queued');progress(e,e.doc,'queued',{state});progress(e,e.doc,'queued');e.service.emit('report',packet(e.doc));assert.equal(e.runs.length,2);assert.deepEqual(calls(e.runs[1]),['enqueued','passed','end']);}finally{await e.api.dispose();}
});

const fs=require('node:fs'),path=require('node:path'),os=require('node:os');
test('same URI/version/text reopen rejects delayed report from the previous synchronization',async()=>{
 const {LanguageClient}=require('../src/lsp-client.cjs'),directory=fs.mkdtempSync(path.join(os.tmpdir(),'status-session-')),nodePath=path.join(directory,'fixture'),root=path.resolve(__dirname,'../..');
 fs.writeFileSync(nodePath,'#!'+process.execPath+'\n'+`if(process.argv.includes('--version')){console.log(process.version);process.exit(0);}const {RpcPeer}=require(${JSON.stringify(require.resolve('../src/rpc.cjs'))});const peer=new RpcPeer(process.stdin,process.stdout);let first,uri,sourceHash;peer.onRequest('initialize',()=>({capabilities:{},serverInfo:{name:'Status fixture',version:'1.0.0'}}));peer.onNotification('initialized',()=>peer.notify('solidityLean/serverVersion',{name:'Status fixture',version:'1.0.0'}));peer.onNotification('textDocument/didOpen',params=>{const d=params.textDocument,old=first;first??=d.synchronizationId;uri=d.uri;sourceHash=require('node:crypto').createHash('sha256').update(d.text).digest('hex');peer.notify('solidityLean/report',{uri,version:1,sourceHash,report:{results:[],errors:[]},synchronizationId:d.synchronizationId,state:'ready',functions:[]});if(old)peer.notify('solidityLean/report',{uri,version:1,sourceHash,report:{results:[],errors:[]},synchronizationId:old,state:'error',functions:[]});});peer.onNotification('textDocument/didClose',()=>peer.notify('solidityLean/report',{uri,version:1,sourceHash,report:{results:[],errors:[]},synchronizationId:first,state:'cancelled',functions:[]}));peer.onRequest('fixture/barrier',()=>true);peer.onRequest('shutdown',()=>null);peer.onNotification('exit',()=>process.exit(0));`,{mode:0o700});
 const client=new LanguageClient({backendPath:root,nodePath,automaticVerification:'never'}),doc={uri:new URL('file:///same.sol'),version:1,isClosed:false,getText:()=> 'contract C {}'},accepted=[],raw=[];client.on('report',packet=>accepted.push(packet));
 try{await client.ready;client.peer.frames.on('message',message=>{if(message.method==='solidityLean/report')raw.push(message.params);});await client.sync(doc);await client.peer.request('fixture/barrier',{});const first=client.documents.get(doc.uri.href).synchronizationId;client.closeDocument(doc.uri.href);await client.sync({...doc});await client.peer.request('fixture/barrier',{});const second=client.documents.get(doc.uri.href).synchronizationId;assert.notEqual(first,second);assert.deepEqual(raw.map(packet=>packet.state),['ready','cancelled','ready','error']);assert.deepEqual(accepted.map(packet=>packet.state),['ready','ready']);assert.equal(accepted.at(-1).synchronizationId,second);}finally{await client.dispose();fs.rmSync(directory,{recursive:true,force:true});}
});


test('report errors prevent an automatic pass even when a row claims success',async()=>{
 const e=fixture();try{const p=packet(e.doc);p.report.errors.push({source:e.doc.uri.fsPath,reason:'injected report error'});e.service.emit('report',p);assert.deepEqual(calls(e.runs[0]),['errored','end']);assert.match(e.runs[0].calls[0][2].message,/injected report error/);}finally{await e.api.dispose();}
});

test('context subscription disposal ends automatic runs even before deactivate; obsolete cancellation never cancels newer text',async()=>{
 const e=fixture();try{await listed(e);progress(e,e.doc);e.doc.version++;e.doc.text+=' newer';const count=e.calls.cancels;e.runs[0].cancel();assert.equal(e.calls.cancels,count);assert.deepEqual(calls(e.runs[0]),['started','skipped','end']);for(const disposable of e.context.subscriptions)disposable.dispose();assert.equal(e.service.listenerCount('report'),0);}finally{await e.api.dispose();}
});
test('malformed function status cannot mutate test lifecycle',async()=>{
 const e=fixture();try{await listed(e);for(const functions of [null,{},[null],[{status:'running',name:'C.f()',range:{}}]])assert.doesNotThrow(()=>progress(e,e.doc,'running',{functions}));assert.equal(e.runs.length,0);}finally{await e.api.dispose();}
});

test('automatic duration uses authentic row time, then only explicit per-function running observation',async()=>{
 const e=fixture();try{await listed(e);progress(e,e.doc);e.service.emit('report',packet(e.doc));const elapsed=e.runs[0].calls.find(call=>call[0]==='passed')[2];assert.equal(typeof elapsed,'number');assert.ok(elapsed>=0);progress(e,e.doc,'queued');progress(e,e.doc);e.service.emit('report',packet(e.doc,[{...row(e.doc),elapsedMs:123}]));assert.equal(e.runs[1].calls.find(call=>call[0]==='passed')[2],123);}finally{await e.api.dispose();}
});
