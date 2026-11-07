// Production status producer with injected AST/verification boundaries; no kernel proof is claimed.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),os=require('node:os'),{pathToFileURL}=require('node:url'),{createHash}=require('node:crypto');
const {SolidityService}=require('../src/lsp-server.cjs');
test('document scheduling does not fabricate per-function running states',()=>{
 const root=fs.mkdtempSync(path.join(os.tmpdir(),'status-producer-')),events=[],service=new SolidityService({notify:(method,params)=>events.push({method,params})},root,{automaticVerification:'never'},{fingerprint:()=> 'fixed'}),text='contract C { function real() external {} }',uri=pathToFileURL(path.join(root,'C.sol')).href,doc=service.open({uri,version:1,text});clearTimeout(doc.timer);
 try{const node={nodeType:'FunctionDefinition',name:'real'},at=text.indexOf('real');doc.index={nodes:[node],nameRange:()=>({start:{line:0,character:at},end:{line:0,character:at+4}}),parents:new Map([[node,{nodeType:'ContractDefinition',name:'C'}]])};service.status(doc,'queued');const packet=events.at(-1).params;assert.equal(packet.progressScope,'document');assert.equal(packet.functions[0].status,'ready');assert.equal(packet.functions[0].name,'C.real');assert.equal(packet.sourceHash,createHash('sha256').update(text).digest('hex'));}finally{service.dispose();fs.rmSync(root,{recursive:true,force:true});}
});

const {summarize}=require('../src/status-summary.cjs'),plainDoc={getText:()=> 'x'};
test('internal counter names cannot become successful native outcomes',()=>{
 for(const status of ['direct','failed','unverified']){const result=summarize({state:'complete',functions:[{name:'C.f',status}]},plainDoc);assert.equal(result.counts.direct,0);assert.equal(result.counts.proved,0);assert.equal(result.counts.unknown,1);}
});
test('reported proof completion preserves existing entry audit qualifications visibly',()=>{
 for(const preconditions of ['unknown','notRun','impossible']){const result=summarize({state:'complete',functions:[{name:'C.f',status:'proved',preconditions}]},plainDoc);assert.equal(result.counts.proved,1);assert.doesNotMatch(result.text,/thumbsup/);assert.match(result.text,/audit|vacuous/);}
});
test('invalid synchronization metadata cannot cancel an existing document',()=>{
 const root=fs.mkdtempSync(path.join(os.tmpdir(),'status-validation-')),events=[],service=new SolidityService({notify:(method,params)=>events.push({method,params})},root,{automaticVerification:'never'},{fingerprint:()=> 'fixed'}),uri=pathToFileURL(path.join(root,'C.sol')).href,doc=service.open({uri,version:1,text:'contract C {}',synchronizationId:'1'});clearTimeout(doc.timer);doc.analysisAbort=new AbortController();events.length=0;
 try{assert.throws(()=>service.open({uri,version:2,text:'contract C {}',synchronizationId:42}),error=>error.code===-32602);assert.equal(doc.analysisAbort.signal.aborted,false);assert.equal(events.length,0);assert.equal(service.docs.get(uri),doc);}finally{service.dispose();fs.rmSync(root,{recursive:true,force:true});}
});

test('summary distinguishes empty, skipped, unknown and direct outcomes without false success',()=>{
 const empty=summarize({state:'complete',functions:[]},plainDoc);assert.match(empty.text,/no verification results/);assert.doesNotMatch(empty.text,/thumbsup/);
 const rows=['stale','unsupported','pending','cancelled','skipped','ready'].map(status=>({name:'C.'+status,status})),mixed=summarize({state:'complete',functions:rows},plainDoc);assert.equal(mixed.completed,0);for(const word of ['stale','unsupported','unknown','cancelled','skipped','unverified'])assert.match(mixed.text,new RegExp(word));assert.doesNotMatch(mixed.text,/thumbsup/);
 const direct=summarize({state:'complete',functions:[{name:'C.direct',status:'proved',verification:'direct'}]},plainDoc);assert.match(direct.text,/1 direct correct/);assert.match(direct.tooltip,/not a kernel certificate/);assert.doesNotMatch(direct.text,/1 proved/);
});
test('queued and failure messages preserve exact names/counts and source range fallback',()=>{
 const doc={getText:()=> 'alpha beta'},range={start:{line:0,character:0},end:{line:0,character:5}};
 assert.match(summarize({state:'running',functions:[{status:'queued',range}]},doc).text,/Completed 0\/1, preparing verification/);
 assert.match(summarize({state:'complete',functions:[{status:'error',range}]},doc).text,/Could not prove alpha/);
 assert.match(summarize({state:'complete',functions:[{status:'error',range},{name:'beta',status:'refuted'}]},doc).text,/Could not prove 2 declarations/);
 assert.match(summarize({state:'compiling',functions:[]},doc).text,/Compiling Solidity/);assert.match(summarize({state:'ready',functions:[]},doc).text,/not verified/);assert.match(summarize({state:'cancelled',functions:[]},doc).text,/cancelled/);
});
test('completed producer retains backend names, direct mode, audit metadata and error count',()=>{
 const root=fs.mkdtempSync(path.join(os.tmpdir(),'status-results-')),events=[],service=new SolidityService({notify:(method,params)=>events.push({method,params})},root,{automaticVerification:'never'},{fingerprint:()=> 'fixed'}),text='contract C {}',uri=pathToFileURL(path.join(root,'C.sol')).href,doc=service.open({uri,version:1,text,synchronizationId:'current'});clearTimeout(doc.timer);
 try{service.publish(doc,{results:[{source:doc.path,sourceHash:createHash('sha256').update(text).digest('hex'),contract:'C',function:'f',signature:'f()',status:'proved',verification:'direct',preconditions:'notApplicable'}],errors:[{source:doc.path,stage:'injected',reason:'injected boundary failure'}]});const packet=events.filter(event=>event.method==='solidityLean/status').at(-1).params;assert.equal(packet.progressScope,'functions');assert.equal(packet.errors,1);assert.equal(packet.synchronizationId,'current');assert.equal(packet.functions[0].name,'C.f()');assert.equal(packet.functions[0].verification,'direct');assert.equal(packet.functions[0].preconditions,'notApplicable');}finally{service.dispose();fs.rmSync(root,{recursive:true,force:true});}
});

test('same URI/version/text reopen rejects delayed status from the previous synchronization',async()=>{
 const {LanguageClient}=require('../src/lsp-client.cjs'),directory=fs.mkdtempSync(path.join(os.tmpdir(),'status-session-')),nodePath=path.join(directory,'fixture'),root=path.resolve(__dirname,'../..');
 fs.writeFileSync(nodePath,'#!'+process.execPath+'\n'+`if(process.argv.includes('--version')){console.log(process.version);process.exit(0);}const {RpcPeer}=require(${JSON.stringify(require.resolve('../src/rpc.cjs'))});const peer=new RpcPeer(process.stdin,process.stdout);let first,uri,sourceHash;peer.onRequest('initialize',()=>({capabilities:{},serverInfo:{name:'Status fixture',version:'1.0.0'}}));peer.onNotification('initialized',()=>peer.notify('solidityLean/serverVersion',{name:'Status fixture',version:'1.0.0'}));peer.onNotification('textDocument/didOpen',params=>{const d=params.textDocument,old=first;first??=d.synchronizationId;uri=d.uri;sourceHash=require('node:crypto').createHash('sha256').update(d.text).digest('hex');peer.notify('solidityLean/status',{uri,version:1,sourceHash,synchronizationId:d.synchronizationId,state:'ready',functions:[]});if(old)peer.notify('solidityLean/status',{uri,version:1,sourceHash,synchronizationId:old,state:'error',functions:[]});});peer.onNotification('textDocument/didClose',()=>peer.notify('solidityLean/status',{uri,version:1,sourceHash,synchronizationId:first,state:'cancelled',functions:[]}));peer.onRequest('fixture/barrier',()=>true);peer.onRequest('shutdown',()=>null);peer.onNotification('exit',()=>process.exit(0));`,{mode:0o700});
 const client=new LanguageClient({backendPath:root,nodePath,automaticVerification:'never'}),doc={uri:new URL('file:///same.sol'),version:1,isClosed:false,getText:()=> 'contract C {}'},accepted=[],raw=[];client.on('status',packet=>accepted.push(packet));
 try{await client.ready;client.peer.frames.on('message',message=>{if(message.method==='solidityLean/status')raw.push(message.params);});await client.sync(doc);await client.peer.request('fixture/barrier',{});const first=client.documents.get(doc.uri.href).synchronizationId;client.closeDocument(doc.uri.href);await client.sync({...doc});await client.peer.request('fixture/barrier',{});const second=client.documents.get(doc.uri.href).synchronizationId;assert.notEqual(first,second);assert.deepEqual(raw.map(packet=>packet.state),['ready','cancelled','ready','error']);assert.deepEqual(accepted.map(packet=>packet.state),['ready','ready']);assert.equal(accepted.at(-1).synchronizationId,second);}finally{await client.dispose();fs.rmSync(directory,{recursive:true,force:true});}
});

test('compiler rejection terminates document compilation status instead of leaving it spinning',async()=>{
 const root=fs.mkdtempSync(path.join(os.tmpdir(),'status-compiler-')),events=[],service=new SolidityService({notify:(method,params)=>events.push({method,params})},root,{automaticVerification:'never'},{fingerprint:()=> 'fixed',analyze:async()=>{throw Error('injected compiler rejection');}}),uri=pathToFileURL(path.join(root,'C.sol')).href,doc=service.open({uri,version:1,text:'contract C {}'});clearTimeout(doc.timer);
 try{await assert.rejects(service.analyze(doc),/compiler rejection/);const packet=events.filter(event=>event.method==='solidityLean/status').at(-1).params;assert.equal(packet.state,'error');assert.equal(packet.phase,'compilation');assert.match(packet.message,/compiler rejection/);}finally{service.dispose();fs.rmSync(root,{recursive:true,force:true});}
});

test('an aborted replaced compiler attempt cannot publish a late ordinary error',async()=>{
 const root=fs.mkdtempSync(path.join(os.tmpdir(),'status-stale-analysis-')),events=[];let fail,started;const gate=new Promise((resolve,reject)=>{fail=reject;}),begun=new Promise(resolve=>{started=resolve;});
 const service=new SolidityService({notify:(method,params)=>events.push({method,params})},root,{automaticVerification:'never'},{fingerprint:()=> 'fixed',analyze:async()=>{started();return gate;}}),uri=pathToFileURL(path.join(root,'C.sol')).href,doc=service.open({uri,version:1,text:'contract C {}'});clearTimeout(doc.timer);
 const result=assert.rejects(service.analyze(doc),/late compiler failure/);try{await begun;service.cancel(doc);events.length=0;fail(Error('late compiler failure'));await result;assert.equal(events.length,0);}finally{service.dispose();fs.rmSync(root,{recursive:true,force:true});}
});

test('H80 offers both project proof-help destinations while retaining ordinary status output',async()=>{const e=require('./controller-fixture.cjs').fixture();let actions;e.vscode.window.showQuickPick=async rows=>{actions=rows;};try{e.status(e.doc,'error');await e.commands.get('solidityLean.openStatusBarMenu')();assert.ok(actions.some(row=>row.label==='Show verification output'));assert.deepEqual(actions.filter(row=>row.proofHelp).map(row=>row.proofHelp),['guide','index']);assert.ok(actions.some(row=>row.description.includes('docs/calculus.md')));assert.ok(actions.some(row=>row.description.includes('docs/README.md')));}finally{await e.api.dispose();}});
