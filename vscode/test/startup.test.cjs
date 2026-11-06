// Production LanguageClient startup boundary. No proof/backend-readiness claim.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),os=require('node:os'),path=require('node:path');
const {LanguageClient,LanguageServers}=require('../src/lsp-client.cjs');
const root=path.resolve(__dirname,'../..'),configuration={backendPath:root,nodePath:process.execPath,automaticVerification:'never'};
test('a directory without the declared backend is rejected before server initialization',async()=>{
 const empty=fs.mkdtempSync(path.join(os.tmpdir(),'startup-empty-')),client=new LanguageClient({...configuration,backendPath:empty});
 try{await assert.rejects(client.ready,e=>e.code==='STARTUP'&&e.setting==='backendPath');assert.equal(client.child,undefined);}finally{await client.dispose();fs.rmSync(empty,{recursive:true,force:true});}
});
test('missing configured runtime failure identifies the setting and preserves its concrete cause',async()=>{
 const client=new LanguageClient({...configuration,nodePath:path.join(root,'nonexistent-runtime')});
 try{await assert.rejects(client.ready,e=>e.code==='STARTUP'&&e.setting==='nodePath'&&e.cause?.code==='ENOENT');}finally{await client.dispose();}
});
test('native initialized identity is the running server manifest, not a stale literal or proof readiness',async()=>{
 const client=new LanguageClient(configuration);
 try{const result=await client.ready;assert.equal(result.serverInfo.version,require('../package.json').version);assert.equal(client.serverInfo.version,result.serverInfo.version);assert.equal(client.runtimeInfo.version,process.version.slice(1));}finally{await client.dispose();}
});

test('closed or retired startup failures never publish ownerless errors',async()=>{
 for(const action of ['close','restart']){
  const servers=new LanguageServers(()=>({...configuration,backendPath:path.join(root,'nonexistent-backend')})),errors=[],doc={uri:{toString:()=> 'file:///startup.sol'},isClosed:false};servers.on('serverError',error=>errors.push(error));
  const client=servers.client(doc);let restarting;
  if(action==='close'){doc.isClosed=true;servers.close(doc.uri);}else{restarting=servers.restart();client.emit('serverError',Error('old-generation transport failure'));}
  try{await assert.rejects(client.ready);await restarting;assert.equal(errors.length,0);}finally{await servers.dispose();}
 }
});

test('workspace symbols from a retired startup generation are rejected',async()=>{
 const servers=new LanguageServers(()=>({}));let release,started;const ready=new Promise(r=>{started=r;}),gate=new Promise(r=>{release=r;});
 servers.clients.set('old',{ready:Promise.resolve(),peer:{request:()=>{started();return gate;}},dispose:async()=>{}});
 const pending=servers.workspaceSymbols('x'),rejected=assert.rejects(pending,e=>e.code===-32801);await ready;await servers.restart();release([{name:'old-generation-symbol',location:{uri:'file:///old.sol'}}]);
 try{await rejected;}finally{await servers.dispose();}
});

function executable(directory,name,body,mode=0o700){const file=path.join(directory,name);fs.writeFileSync(file,'#!'+process.execPath+'\n'+body,{mode});return file;}
test('unexecutable runtime and unknown/unsupported claimed versions stop before server spawn',async()=>{
 const temp=fs.mkdtempSync(path.join(os.tmpdir(),'startup-runtime-'));
 try{
  for(const [name,body,mode,version]of [['denied','',0o600,null],['unknown',"console.log('not a version');",0o700,'unknown'],['unsupported',"console.log('v17.9.0');",0o700,'17.9.0']]){
   const nodePath=executable(temp,name,body,mode),client=new LanguageClient({...configuration,nodePath});
   try{await assert.rejects(client.ready,e=>e.code==='STARTUP'&&e.setting==='nodePath'&&(version?e.runtimeInfo?.version===version:e.cause?.code==='EACCES'));assert.equal(client.child,undefined);}finally{await client.dispose();}
  }
 }finally{fs.rmSync(temp,{recursive:true,force:true});}
});
test('missing or malformed server version remains unknown after a valid bounded initialize response',async()=>{
 const temp=fs.mkdtempSync(path.join(os.tmpdir(),'startup-identity-'));
 try{
  for(const info of [undefined,{name:'Protocol fixture',version:42},{name:'Protocol fixture',version:'malformed'}]){
   const nodePath=executable(temp,'protocol',`if(process.argv.includes('--version')){console.log(process.version);process.exit(0);}const {RpcPeer}=require(${JSON.stringify(require.resolve('../src/rpc.cjs'))});const peer=new RpcPeer(process.stdin,process.stdout);peer.onRequest('initialize',()=>(${JSON.stringify({capabilities:{},serverInfo:info})}));peer.onRequest('shutdown',()=>null);peer.onNotification('exit',()=>process.exit(0));`),client=new LanguageClient({...configuration,nodePath});
   try{await client.ready;assert.equal(client.serverInfo.version,'unknown');assert.equal(client.initialized,true);}finally{await client.dispose();}
  }
 }finally{fs.rmSync(temp,{recursive:true,force:true});}
});
test('disposal cancels a live executable version probe without starting a server',async()=>{
 const temp=fs.mkdtempSync(path.join(os.tmpdir(),'startup-cancel-')),marker=path.join(temp,'started');
 const nodePath=executable(temp,'slow',`require('node:fs').writeFileSync(${JSON.stringify(marker)},String(process.pid));setInterval(()=>{},1000);`),client=new LanguageClient({...configuration,nodePath});
 try{
  const deadline=Date.now()+2000;while(!fs.existsSync(marker)){assert.ok(Date.now()<deadline);await new Promise(r=>setTimeout(r,5));}
  const rejected=assert.rejects(client.ready,e=>e.code==='CANCELLED');await client.dispose();await rejected;assert.equal(client.child,undefined);
 }finally{await client.dispose();fs.rmSync(temp,{recursive:true,force:true});}
});

test('an unresponsive runtime probe is bounded by the documented 5000 ms startup check',async()=>{
 const temp=fs.mkdtempSync(path.join(os.tmpdir(),'startup-timeout-')),nodePath=executable(temp,'hung','setInterval(()=>{},1000);'),client=new LanguageClient({...configuration,nodePath});
 try{await assert.rejects(client.ready,e=>e.code==='STARTUP'&&/5000 ms/.test(e.message));assert.equal(client.child,undefined);}finally{await client.dispose();fs.rmSync(temp,{recursive:true,force:true});}
});

test('shared-client scoped restart rejects an old request even when the same client is reused',async()=>{
 const config={...configuration},servers=new LanguageServers(()=>config),a={uri:new URL('file:///a.sol'),version:1,isClosed:false,getText:()=> 'contract C {}'},b={...a,uri:new URL('file:///b.sol')};let release,started;
 const gate=new Promise(r=>{release=r;}),ready=new Promise(r=>{started=r;});
 const shared=Object.assign(Object.create(LanguageClient.prototype),{ready:Promise.resolve(),documents:new Map(),disposed:false,serverInfo:{name:'fixture',version:'unknown'},peer:{closed:false,notify(){},request(){started();return gate;}},dispose:async function(){this.disposed=true;}});
 servers.clients.set(JSON.stringify(config),shared);servers.owners.set(a.uri.href,shared);servers.owners.set(b.uri.href,shared);
 const request=servers.request('textDocument/hover',a,{}),rejected=assert.rejects(request,e=>e.code===-32801);await ready;await servers.restart([a.uri]);await servers.open(a);assert.equal(servers.owners.get(b.uri.href),shared);assert.equal(shared.disposed,false);release({contents:'old generation'});
 try{await rejected;}finally{await servers.dispose();}
});
