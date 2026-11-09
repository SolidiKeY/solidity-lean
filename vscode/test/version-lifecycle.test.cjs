// Native producer assertions and labeled injected version transport cases. No proof/UI parity claim.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),path=require('node:path'),fs=require('node:fs'),os=require('node:os');
const {performance}=require('node:perf_hooks');
const {LanguageClient}=require('../src/lsp-client.cjs'),{RpcPeer}=require('../src/rpc.cjs');
const root=path.resolve(__dirname,'../..'),configuration={backendPath:root,nodePath:process.execPath,automaticVerification:'never'};
const method='solidityLean/serverVersion';
test('native server produces actual version after initialized and identity follows the notification',async()=>{
 const observations=[],receive=RpcPeer.prototype.receive,write=RpcPeer.prototype.write;RpcPeer.prototype.write=function(message){observations.push({direction:'client',message});return write.call(this,message);};RpcPeer.prototype.receive=function(message){observations.push({direction:'server',message});return receive.call(this,message);};
 const client=new LanguageClient(configuration);client.on('identity',value=>observations.push({identity:value}));
 try{await client.ready;const version=observations.findIndex(row=>row.message?.method===method);assert.ok(version>=0,'native version producer notification missing');const initialized=observations.findIndex(row=>row.direction==='client'&&row.message?.method==='initialized'),reply=observations.findIndex(row=>row.direction==='server'&&row.message?.result?.capabilities);assert.ok(reply>=0&&initialized>reply&&version>initialized);assert.deepEqual(observations[version].message.params,{name:'Solidity Lean Language Server',version:require('../package.json').version});assert.ok(observations.findIndex(row=>row.identity)>version);}
 finally{await client.dispose();RpcPeer.prototype.receive=receive;RpcPeer.prototype.write=write;}
});
function fixture(body){const directory=fs.mkdtempSync(path.join(os.tmpdir(),'version-notification-')),nodePath=path.join(directory,'runtime');fs.writeFileSync(nodePath,'#!'+process.execPath+'\n'+`if(process.argv.includes('--version')){console.log(process.version);process.exit(0);}const {RpcPeer}=require(${JSON.stringify(require.resolve('../src/rpc.cjs'))});const peer=new RpcPeer(process.stdin,process.stdout);peer.onRequest('initialize',()=>({capabilities:{},serverInfo:{name:'Notification fixture',version:'9.9.9'}}));peer.onRequest('shutdown',()=>null);peer.onNotification('exit',()=>process.exit(0));`+body,{mode:0o700});return{directory,nodePath};}
test('injected delayed version is awaited instead of publishing initialize header as final identity',async()=>{
 const f=fixture(`peer.onNotification('initialized',()=>setTimeout(()=>peer.notify('${method}',{name:'Notification fixture',version:'1.2.3'}),100));`),client=new LanguageClient({...configuration,nodePath:f.nodePath});
 try{await client.ready;assert.equal(client.serverInfo.version,'1.2.3');assert.equal(client.peer.notifications.has(method),false);}finally{await client.dispose();fs.rmSync(f.directory,{recursive:true,force:true});}
});

test('early and malformed/duplicate injected notifications resolve only once after initialize',async()=>{
 for(const early of [true,false]){
  const send=`peer.notify('${method}',{name:'Notification fixture',version:42});peer.notify('${method}',{name:'Notification fixture',version:'1.2.3'});peer.notify('${method}',{name:'Notification fixture',version:'2.3.4'});`;
  const body=early?`peer.onRequest('initialize',()=>{${send}return new Promise(resolve=>setTimeout(()=>resolve({capabilities:{},serverInfo:{name:'Notification fixture',version:'9.9.9'}}),50));});`:`peer.onNotification('initialized',()=>{${send}});`;
  const f=fixture(body),client=new LanguageClient({...configuration,nodePath:f.nodePath}),identities=[];client.on('identity',i=>identities.push(i));
  try{await client.ready;assert.equal(client.serverInfo.version,'1.2.3');assert.equal(identities.length,1);assert.equal(client.versionSource,'notification');assert.equal(client.versionWait.pending,false);assert.equal(client.peer.notifications.has(method),false);assert.equal(require('node:events').getEventListeners(client.startupAbort.signal,'abort').length,0);}finally{await client.dispose();fs.rmSync(f.directory,{recursive:true,force:true});}
 }
});
test('missing, malformed and late injected versions use the separate 5000ms unknown fallback',async()=>{
 assert.equal(require('../src/startup.cjs').versionTimeoutMs,5000);
 const cases=[['missing',''],['malformed',`peer.notify('${method}',{name:'Notification fixture',version:42});`],['late',`setTimeout(()=>peer.notify('${method}',{name:'Notification fixture',version:'1.2.3'}),5200);`]],resources=[];
 try{
  await Promise.all(cases.map(async([name,send])=>{
   const f=fixture(`peer.onNotification('initialized',()=>{peer.notify('window/logMessage',{message:'started'});${send}});`),client=new LanguageClient({...configuration,nodePath:f.nodePath}),identities=[];const events=[];resources.push({name,f,client,events});client.once('log',()=>{const child=client.child;events.push({event:'started',at:performance.now(),pid:child.pid,birth:child.processBirth});for(const event of ['exit','close'])child.once(event,(code,signal)=>events.push({event,at:performance.now(),code,signal}));});client.on('identity',i=>identities.push(i));let started;
   client.on('log',()=>{started=performance.now();});await client.ready;
   assert.ok(performance.now()-started>=4900,name+' must wait for version fallback after startup');assert.equal(client.serverInfo.version,'unknown');assert.equal(client.versionSource,'timeout');assert.equal(client.peer.notifications.has(method),false);
   await new Promise(resolve=>setTimeout(resolve,350));assert.equal(identities.length,1);assert.equal(client.serverInfo.version,'unknown');
  }));
 }finally{await require('./fixture-cleanup.cjs').settleFixtures(resources,{record:rows=>{if(process.env.DAFNY_CHILD_CLOSURE_EVIDENCE)fs.writeFileSync(process.env.DAFNY_CHILD_CLOSURE_EVIDENCE,JSON.stringify({scope:'Actual Node/RPC transport with injected version producer; no solver/kernel/rendered evidence.',rows},null,2));}});}
});
test('transport failure and disposal while awaiting version cannot publish identity',async()=>{
 for(const fail of [true,false]){
  const f=fixture(`peer.onNotification('initialized',()=>{peer.notify('window/logMessage',{message:'waiting'});${fail?'setTimeout(()=>process.exit(2),50);':''}});`),client=new LanguageClient({...configuration,nodePath:f.nodePath}),identities=[];
  client.on('identity',i=>identities.push(i));const rejected=assert.rejects(client.ready);
  try{if(!fail){await new Promise(resolve=>client.once('log',resolve));await client.dispose();}await rejected;await client.dispose();assert.equal(identities.length,0);assert.equal(client.versionWait.pending,false);assert.equal(client.peer.notifications.has(method),false);assert.ok(client.child.exitCode!==null||client.child.signalCode!==null);}finally{await client.dispose();fs.rmSync(f.directory,{recursive:true,force:true});}
 }
});
test('cancelling one readiness waiter does not cancel shared version discovery',async()=>{
 const f=fixture(`peer.onNotification('initialized',()=>setTimeout(()=>peer.notify('${method}',{name:'Notification fixture',version:'1.2.3'}),150));`),client=new LanguageClient({...configuration,nodePath:f.nodePath}),abort=new AbortController();
 const doc={uri:new URL('file:///cancel.sol'),version:1,isClosed:false,getText:()=> 'contract C {}'};
 try{const request=client.request('textDocument/hover',doc,{}, {signal:abort.signal}),rejected=assert.rejects(request,e=>e.code===-32800);abort.abort();await rejected;assert.equal(client.documents.size,0);await client.ready;assert.equal(client.serverInfo.version,'1.2.3');assert.equal(client.disposed,false);}finally{await client.dispose();fs.rmSync(f.directory,{recursive:true,force:true});}
});

test('matching early metadata is not hidden by another producer name',async()=>{
 const {PassThrough}=require('node:stream'),input=new PassThrough(),output=new PassThrough(),peer=new RpcPeer(input,output),wait=require('../src/startup.cjs').waitForServerVersion(peer);
 try{for(const [name,version]of [['Wrong server','1.0.0'],['Actual server','2.0.0']])peer.receive({jsonrpc:'2.0',method,params:{name,version}});const result=wait.start({name:'Actual server',version:'9.9.9'});assert.equal(wait.pending,false);assert.equal((await result).serverInfo.version,'2.0.0');}
 finally{wait.dispose();peer.close();input.destroy();output.destroy();}
});
test('workspace search cancellation during version discovery rejects without cancelling shared readiness',async()=>{
 const {LanguageServers}=require('../src/lsp-client.cjs'),servers=new LanguageServers(()=>({})),abort=new AbortController();let release,completed=false,outcome;
 const ready=new Promise(resolve=>{release=resolve;});servers.clients.set('pending',{ready,peer:{request:async()=>[]},dispose:async()=>{}});
 const request=servers.workspaceSymbols('x',{signal:abort.signal}).then(result=>{completed=true;outcome=result;},error=>{completed=true;outcome=error;});
 try{await new Promise(setImmediate);abort.abort();await new Promise(setImmediate);assert.equal(completed,true);assert.equal(outcome.code,-32800);assert.equal(servers.clients.size,1);}
 finally{release();await servers.dispose();await request;}
});

test('notification registration disposal preserves replacements and transport close releases handlers',()=>{
 const {PassThrough}=require('node:stream'),input=new PassThrough(),output=new PassThrough(),peer=new RpcPeer(input,output);let called=0;
 const first=peer.onNotification('example',()=>{called+=100;}),second=peer.onNotification('example',()=>{called++;});first.dispose();peer.receive({jsonrpc:'2.0',method:'example',params:{}});assert.equal(called,1);second.dispose();assert.equal(peer.notifications.size,0);
 peer.onNotification('retained',()=>{});peer.onRequest('retained',()=>null);peer.close();assert.equal(peer.notifications.size,0);assert.equal(peer.requests.size,0);input.destroy();output.destroy();
});

test('early version metadata overflow fails explicitly instead of retaining unlimited candidates',async()=>{
 const {PassThrough}=require('node:stream'),input=new PassThrough(),output=new PassThrough(),peer=new RpcPeer(input,output),wait=require('../src/startup.cjs').waitForServerVersion(peer);
 try{for(let i=0;i<129;i++)peer.receive({jsonrpc:'2.0',method,params:{name:'Producer-'+i,version:'1.0.0'}});assert.equal(wait.pending,false);await assert.rejects(wait.promise,error=>error.code==='STARTUP'&&/metadata/.test(error.message));assert.equal(peer.notifications.has(method),false);}
 finally{wait.dispose();peer.close();input.destroy();output.destroy();}
});

test('early candidates copy metadata only and oversized metadata fails closed',async()=>{
 const {PassThrough}=require('node:stream');
 for(const oversized of [false,true]){
  const input=new PassThrough(),output=new PassThrough(),peer=new RpcPeer(input,output),wait=require('../src/startup.cjs').waitForServerVersion(peer),value={name:'Actual server',version:oversized?'1.2.3-'+ 'a'.repeat(65536):'2.0.0',extra:'discarded'.repeat(10000)};
  try{peer.receive({jsonrpc:'2.0',method,params:value});if(oversized)await assert.rejects(wait.promise,error=>error.code==='STARTUP');else{value.version='3.0.0';assert.equal((await wait.start({name:'Actual server'})).serverInfo.version,'2.0.0');}}
  finally{wait.dispose();peer.close();input.destroy();output.destroy();}
 }
});
test('matrix cleanup attempts every client after an earlier cleanup failure',async()=>{
 const {cleanup}=require('../parity/version-lifecycle.cjs'),attempts=[];const entry=(label,fail)=>({label,client:{versionWait:{pending:false,dispose(){}},async dispose(){attempts.push(label);if(fail)throw Error('injected cleanup failure');}}});
 const errors=await cleanup([entry('first',true),entry('second',false),entry('third',false)],[{async dispose(){throw Error('injected manager cleanup failure');}}]);assert.deepEqual(attempts,['first','second','third']);assert.equal(errors.length,2);
});

test('matrix cleanup also stops an owned live child when disposal falsely resolves',async()=>{
 const {spawn}=require('node:child_process'),{terminateTree}=require('../src/backend.cjs'),{cleanup}=require('../parity/version-lifecycle.cjs'),child=spawn(process.execPath,['-e','setInterval(()=>{},1000)'],{detached:process.platform!=='win32',stdio:'ignore'}),closed=new Promise(resolve=>child.once('close',resolve));
 const entry={label:'injected-false-disposal',client:{child,closed,versionWait:{pending:false,dispose(){}},async dispose(){}}};
 try{const errors=await cleanup([entry],[]);assert.ok(errors.length>=1);assert.ok(child.exitCode!==null||child.signalCode!==null);assert.throws(()=>process.kill(child.pid,0),error=>error.code==='ESRCH');}
 finally{if(child.exitCode===null&&child.signalCode===null)terminateTree(child);await closed;}
});

test('request, verification and workspace cancellation cross a restart barrier without spawning clients',async()=>{
 const {LanguageServers}=require('../src/lsp-client.cjs');let release,calls=0;const gate=new Promise(resolve=>{release=resolve;}),servers=new LanguageServers(()=>{calls++;return{};}),abort=new AbortController(),doc={uri:new URL('file:///barrier.sol'),version:1,isClosed:false,getText:()=>''};
 servers.clients.set('retiring',{dispose:()=>gate});const restart=servers.restart();
 const requests=[servers.request('textDocument/hover',doc,{}, {signal:abort.signal}),servers.verify({document:doc,signal:abort.signal}),servers.workspaceSymbols('x',{signal:abort.signal})];const rejected=requests.map(request=>assert.rejects(request,error=>error.code===-32800));
 try{abort.abort();await Promise.all(rejected);assert.equal(calls,0);}finally{release();await restart;await servers.dispose();}
});
