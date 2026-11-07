#!/usr/bin/env node
// Production startup/recovery observations. No Lean execution or renderer is involved.
'use strict';
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict'),{pathToFileURL}=require('node:url'),{performance}=require('node:perf_hooks');
const {LanguageServers}=require('../src/lsp-client.cjs'),{RpcPeer}=require('../src/rpc.cjs'),{statistics}=require('./core.cjs');
async function run(output){
 fs.mkdirSync(output);const observations=[],traffic=[],samples={cold:[],warm:[]},begin=performance.now();let phase='setup',sequence=0;
 const record=(event,data)=>observations.push({sequence:++sequence,phase,event,elapsedMs:performance.now()-begin,...data});
 const peerIds=new WeakMap();let nextPeer=0;const peerId=peer=>{if(!peerIds.has(peer))peerIds.set(peer,++nextPeer);return peerIds.get(peer);};
 const write=RpcPeer.prototype.write,receive=RpcPeer.prototype.receive;
 RpcPeer.prototype.write=function(message){traffic.push({sequence:++sequence,phase,peerId:peerId(this),direction:'client',message});return write.call(this,message);};
 RpcPeer.prototype.receive=function(message){traffic.push({sequence:++sequence,phase,peerId:peerId(this),direction:'server',message});return receive.call(this,message);};
 const root=path.resolve(__dirname,'../..'),empty=path.join(output,'empty-backend');fs.mkdirSync(empty);
 const denied=path.join(output,'unexecutable-runtime');fs.writeFileSync(denied,'not executable',{mode:0o600});
 for(const name of ['folder-a','folder-b'])fs.mkdirSync(path.join(output,name));
 const doc=name=>({uri:pathToFileURL(path.join(output,'folder-'+name,name+'.sol')),version:1,isClosed:false,getText:()=> 'contract C {}'}),a=doc('a'),b=doc('b');
 let config={backendPath:root,nodePath:path.join(output,'missing-runtime'),workers:1};
 const servers=new LanguageServers(document=>({... (document===a?config:{backendPath:root,nodePath:process.execPath,workers:1}),projectRoot:path.join(output,document===a?'folder-a':'folder-b'),automaticVerification:'never'}));
 const clients=new Set();servers.on('identity',identity=>record('identity',{identity}));servers.on('serverError',error=>record('failure',{error:{message:error.message,code:error.code,setting:error.setting,uris:error.uris,cause:error.cause&&{code:error.cause.code,message:error.cause.message}}}));
 const initialize=async document=>{const start=performance.now(),client=servers.client(document);clients.add(client);await servers.open(document);const result=await client.ready;const id=peerId(client.peer),events=traffic.filter(row=>row.peerId===id),reply=events.findIndex(row=>row.direction==='server'&&row.message.result?.capabilities),initialized=events.findIndex(row=>row.direction==='client'&&row.message.method==='initialized'),version=events.findIndex(row=>row.direction==='server'&&row.message.method==='solidityLean/serverVersion');assert.ok(reply>=0&&initialized>reply&&version>initialized);assert.equal(client.versionSource,'notification');assert.equal(client.peer.notifications.has('solidityLean/serverVersion'),false);assert.deepEqual(events[version].message.params,{name:'Solidity Lean Language Server',version:require('../package.json').version});record('initialized',{uri:document.uri.href,peerId:id,pid:client.child.pid,versionSource:client.versionSource,runtimeInfo:client.runtimeInfo,result});return{client,elapsedMs:performance.now()-start};};
 let status='failed';
 try{
  phase='healthy-folder';const healthy=(await initialize(b)).client,healthyPid=healthy.child.pid;
  for(const [name,patch,setting,cause]of [['missing-runtime',{nodePath:path.join(output,'missing-runtime')},'nodePath','ENOENT'],['unexecutable-runtime',{nodePath:denied},'nodePath','EACCES'],['missing-backend',{backendPath:empty,nodePath:process.execPath},'backendPath','ENOENT']]){
   phase=name;config={backendPath:root,nodePath:process.execPath,workers:1,...patch};
   await assert.rejects(initialize(a),e=>e.code==='STARTUP'&&e.setting===setting&&e.cause?.code===cause);
   assert.equal(servers.owners.get(b.uri.href),healthy);assert.equal(healthy.child.pid,healthyPid);assert.equal(healthy.disposed,false);await servers.restart([a.uri]);
  }
  phase='configuration-corrected';config={backendPath:root,nodePath:process.execPath,workers:1};let current=await initialize(a);samples.cold.push(current.elapsedMs);assert.equal(current.client.serverInfo.version,require('../package.json').version);
  phase='initialize-failure';await servers.restart([a.uri]);config={...config,workers:5};await assert.rejects(initialize(a),e=>e.code==='STARTUP'&&e.cause?.code===-32602);
  phase='configuration-recovered';await servers.restart([a.uri]);config={...config,workers:1};current=await initialize(a);samples.cold.push(current.elapsedMs);
  for(let trial=0;trial<3;trial++){phase='restart-'+trial;const old=current.client;await servers.restart([a.uri]);current=await initialize(a);samples.cold.push(current.elapsedMs);assert.notEqual(current.client.child.pid,old.child.pid);assert.equal(healthy.child.pid,healthyPid);assert.equal(healthy.disposed,false);}
  for(let trial=0;trial<5;trial++){phase='warm-reuse-'+trial;const start=performance.now(),same=await servers.open(a);samples.warm.push(performance.now()-start);assert.equal(same,current.client);record('reused',{pid:same.child.pid});}
  phase='disposal';await servers.dispose();assert.equal(servers.clients.size,0);assert.equal(servers.owners.size,0);assert.ok([...clients].every(client=>client.disposed));const children=[...clients].filter(client=>client.child).map(client=>({pid:client.child.pid,exitCode:client.child.exitCode,signalCode:client.child.signalCode}));for(const child of children){assert.ok(child.exitCode!==null||child.signalCode!==null);assert.throws(()=>process.kill(child.pid,0),error=>error.code==='ESRCH');}record('disposed',{clients:clients.size,children});status='passed-with-gaps';
 }finally{
  await servers.dispose();RpcPeer.prototype.write=write;RpcPeer.prototype.receive=receive;
  fs.writeFileSync(path.join(output,'traffic.jsonl'),traffic.map(x=>JSON.stringify(x)).join('\n')+'\n');
  fs.writeFileSync(path.join(output,'report.json'),JSON.stringify({schemaVersion:1,status,scope:'Native production Node/backend validation, actual LSP initialize, scoped configuration failure/recovery, restart/disposal. No Lean/proof/compiler readiness or rendered UI/Dafny equivalence.',observations,samples,statistics:{cold:statistics(samples.cold),warm:statistics(samples.warm)},boundaries:'Process-cold includes runtime probe and initialize, retains OS caches; warm reuses server. Serial startup only, not proof worker scaling.'},null,2)+'\n');
 }
 return status;
}
if(require.main===module){const args=process.argv.slice(2);if(![2,3].includes(args.length)||args[0]!=='--output'||args.length===3&&!['--versions','--status','--testing','--hierarchy','--retention','--large-file','--hover'].includes(args[2])){process.stderr.write('Use --output NEW_DIRECTORY [--versions|--status|--testing|--hierarchy|--retention|--large-file|--hover]\n');process.exitCode=1;}else (args[2]==='--hover'?require('./hover-lifecycle.cjs').run:args[2]==='--large-file'?require('./large-file-lifecycle.cjs').run:args[2]==='--retention'?require('./retention-lifecycle.cjs').run:args[2]==='--hierarchy'?require('./hierarchy-lifecycle.cjs').run:args[2]==='--testing'?require('./testing-lifecycle.cjs').run:args[2]==='--status'?require('./status-lifecycle.cjs').run:args[2]?require('./version-lifecycle.cjs').run:run)(path.resolve(args[1])).then(status=>process.stdout.write(status+'\n')).catch(error=>{process.stderr.write(error.stack+'\n');process.exitCode=1;});}
module.exports={run};
