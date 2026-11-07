// Opt-in ordered version scenarios in the existing startup harness. Fixtures are labeled, never proof producers.
'use strict';
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict'),{performance}=require('node:perf_hooks');
const {LanguageClient,LanguageServers}=require('../src/lsp-client.cjs'),{RpcPeer}=require('../src/rpc.cjs'),{versionNotification:method,versionTimeoutMs}=require('../src/startup.cjs');
async function cleanup(entries,managers,record=()=>{}){
 const errors=[];
 const stop=async entry=>{
  for(const action of [()=>entry.client.startupAbort?.abort(),()=>entry.client.versionWait?.dispose()])try{action();}catch(error){errors.push(error);}
  const child=entry.client.child;if(child?.pid&&child.exitCode===null&&child.signalCode===null){try{require('../src/backend.cjs').terminateTree(child);}catch(error){errors.push(error);}let timer;try{await Promise.race([entry.client.closed,new Promise(resolve=>{timer=setTimeout(resolve,1000);})]);}catch(error){errors.push(error);}finally{clearTimeout(timer);}}
 };
 for(const manager of managers)try{await manager.dispose();}catch(error){errors.push(error);}
 for(const entry of entries){
  try{await entry.client.dispose();}catch(error){errors.push(error);await stop(entry);}
  try{if(entry.client.versionWait)assert.equal(entry.client.versionWait.pending,false);const child=entry.client.child;if(child?.pid){assert.ok(child.exitCode!==null||child.signalCode!==null);assert.throws(()=>process.kill(child.pid,0),error=>error.code==='ESRCH');record(entry.label,'child-exited',{pid:child.pid,exitCode:child.exitCode,signalCode:child.signalCode});}}catch(error){errors.push(error);await stop(entry);}
 }
 return errors;
}
async function run(output){
 fs.mkdirSync(output);const root=path.resolve(__dirname,'../..'),configuration={backendPath:root,nodePath:process.execPath,automaticVerification:'never'},entries=[],observations=[],traffic=[],managers=[];let sequence=0,failure,cleanupErrors=[];const begin=performance.now();
 const record=(label,event,data={})=>observations.push({sequence:++sequence,label,event,elapsedMs:performance.now()-begin,...data});
 const write=RpcPeer.prototype.write,receive=RpcPeer.prototype.receive;
 const trace=(peer,direction,message)=>{const entry=entries.find(row=>row.client.peer===peer);if(entry&&direction==='client'&&message.method==='initialized'){entry.startedAt=performance.now();entry.resolveStarted();}traffic.push({sequence:++sequence,label:entry?.label||'unassigned',source:entry?.source||'unknown',elapsedMs:performance.now()-begin,direction,message});};
 RpcPeer.prototype.write=function(message){trace(this,'client',message);return write.call(this,message);};RpcPeer.prototype.receive=function(message){trace(this,'server',message);return receive.call(this,message);};
 const observe=(label,client,source)=>{const entry={label,client,source,identities:[]};entries.push(entry);entry.started=new Promise((resolve,reject)=>{entry.resolveStarted=resolve;entry.rejectStarted=reject;});entry.started.catch(()=>{});client.on('identity',identity=>{entry.identities.push(identity);record(label,'identity',{source,initialized:client.initialized,identity});});entry.outcome=client.ready.then(result=>{record(label,'ready',{source,result,serverInfo:client.serverInfo,versionSource:client.versionSource,versionWaitMs:performance.now()-entry.startedAt});return{ok:true,result};},error=>{entry.rejectStarted(error);record(label,'rejected',{source,error:{code:error.code,message:error.message}});return{ok:false,error};});return entry;};
 const header={capabilities:{},serverInfo:{name:'Notification fixture',version:'9.9.9'}};
 const fixture=(label,body)=>{const nodePath=path.join(output,label+'-runtime');fs.writeFileSync(nodePath,'#!'+process.execPath+'\n'+`if(process.argv.includes('--version')){console.log(process.version);process.exit(0);}const {RpcPeer}=require(${JSON.stringify(require.resolve('../src/rpc.cjs'))});const peer=new RpcPeer(process.stdin,process.stdout);peer.onRequest('initialize',()=>(${JSON.stringify(header)}));peer.onRequest('shutdown',()=>null);peer.onNotification('exit',()=>process.exit(0));`+body,{mode:0o700});return nodePath;};
 const notify=(version='1.2.3',name='Notification fixture')=>`peer.notify('${method}',${JSON.stringify({name,version})});`;
 const make=(label,body)=>observe(label,new LanguageClient({...configuration,nodePath:fixture(label,body)}),'injected-transport');
 try{
  const native=observe('native-producer',new LanguageClient(configuration),'native-producer');await native.outcome;assert.equal(native.client.serverInfo.version,require('../package.json').version);assert.equal(native.client.versionSource,'notification');
  native.client.peer.notify('initialized',{});await native.client.peer.request('solidityLean/stats',{});
  const events=traffic.filter(row=>row.label===native.label),reply=events.findIndex(row=>row.direction==='server'&&row.message.result?.capabilities),initialized=events.findIndex(row=>row.direction==='client'&&row.message.method==='initialized'),version=events.findIndex(row=>row.direction==='server'&&row.message.method===method);assert.ok(reply>=0&&initialized>reply&&version>initialized);assert.equal(events.filter(row=>row.direction==='server'&&row.message.method===method).length,1);
  const early=make('early',`peer.onRequest('initialize',()=>{${notify('8.0.0','Wrong server')+notify()+notify('2.3.4')}return new Promise(resolve=>setTimeout(()=>resolve(${JSON.stringify(header)}),50));});peer.onNotification('initialized',()=>peer.notify('window/logMessage',{message:'started'}));`);
  const known=make('known-malformed-duplicate',`peer.onNotification('initialized',()=>{peer.notify('window/logMessage',{message:'started'});${notify(42)+notify('8.0.0','Wrong server')}setTimeout(()=>{${notify()+notify('2.3.4')}},100);});`);
  const missing=make('missing',`peer.onNotification('initialized',()=>peer.notify('window/logMessage',{message:'started'}));`);
  const malformed=make('malformed',`peer.onNotification('initialized',()=>{peer.notify('window/logMessage',{message:'started'});${notify(42)}peer.notify('${method}',null);});`);
  const late=make('late',`peer.onNotification('initialized',()=>{peer.notify('window/logMessage',{message:'started'});setTimeout(()=>{${notify()}},5200);});`);
  const failed=make('transport-failure',`peer.onNotification('initialized',()=>setTimeout(()=>process.exit(2),50));`);
  const disposed=make('disposed',`peer.onNotification('initialized',()=>peer.notify('window/logMessage',{message:'started'}));`);
  const cancelled=make('cancelled-request',`peer.onNotification('initialized',()=>{peer.notify('window/logMessage',{message:'started'});setTimeout(()=>{${notify()}},300);});`);
  const cancelTask=(async()=>{await cancelled.started;const abort=new AbortController(),doc={uri:new URL('file:///cancel.sol'),version:1,isClosed:false,getText:()=> 'contract C {}'};const request=cancelled.client.request('textDocument/hover',doc,{}, {signal:abort.signal}),rejected=assert.rejects(request,error=>error.code===-32800);abort.abort();await rejected;record(cancelled.label,'request-cancelled');assert.equal(cancelled.client.documents.size,0);assert.equal(cancelled.client.disposed,false);})();
  await disposed.started;await disposed.client.dispose();record(disposed.label,'disposed-during-wait');await cancelTask;
  await Promise.all([early,known,missing,malformed,late,failed,disposed,cancelled].map(entry=>entry.outcome));
  for(const entry of [early,known,cancelled]){assert.equal(entry.client.serverInfo.version,'1.2.3');assert.equal(entry.client.versionSource,'notification');assert.equal(entry.identities.length,1);}
  for(const entry of [missing,malformed,late]){assert.equal(entry.client.serverInfo.version,'unknown');assert.equal(entry.client.versionSource,'timeout');const decision=observations.find(row=>row.label===entry.label&&row.event==='ready');assert.ok(decision.versionWaitMs>=4900);}
  assert.equal(failed.identities.length,0);assert.equal(disposed.identities.length,0);assert.equal((await failed.outcome).ok,false);assert.equal((await disposed.outcome).ok,false);
  await new Promise(resolve=>setTimeout(resolve,400));assert.equal(late.identities.length,1);assert.equal(late.client.serverInfo.version,'unknown');assert.equal(traffic.filter(row=>row.label===late.label&&row.message.method===method).length,1);
  for(const entry of entries){assert.equal(entry.client.versionWait.pending,false);assert.equal(entry.client.peer.notifications.has(method),false);assert.equal(require('node:events').getEventListeners(entry.client.startupAbort.signal,'abort').length,0);}
  // Real native healthy folder plus a pending injected old generation; recovery uses the actual producer.
  let nativeA=false;const pendingPath=fixture('scoped-pending',`peer.onNotification('initialized',()=>peer.notify('window/logMessage',{message:'started'}));`),a={uri:new URL('file://'+path.join(output,'a.sol')),version:1,isClosed:false,getText:()=> 'contract C {}'},b={...a,uri:new URL('file://'+path.join(output,'b.sol'))};
  const servers=new LanguageServers(doc=>({...configuration,nodePath:doc.uri.href===a.uri.href&&!nativeA?pendingPath:process.execPath,projectRoot:output+(doc.uri.href===a.uri.href?'/a':'/b')}));managers.push(servers);servers.on('identity',identity=>record('scoped-manager','identity',{identity}));
  const healthy=observe('scoped-native-B',servers.client(b),'native-producer');await servers.open(b);const healthyPid=healthy.client.child.pid;
  const old=observe('scoped-old-A',servers.client(a),'injected-transport'),oldOpen=servers.open(a).then(()=>true,error=>error);await old.started;servers.close(a.uri);a.isClosed=true;record('scoped-manager','closed-old-A');const reopened={...a,isClosed:false};const reopenedOpen=servers.open(reopened).then(()=>true,error=>error);await new Promise(setImmediate);nativeA=true;await servers.restart([a.uri]);
  const recovered=observe('scoped-new-A',servers.client(reopened),'native-producer');await servers.open(reopened);assert.equal(recovered.client.versionSource,'notification');assert.equal(old.identities.length,0);assert.equal(old.client.versionWait.pending,false);assert.notEqual(await oldOpen,true);assert.notEqual(await reopenedOpen,true);assert.equal(healthy.client.child.pid,healthyPid);assert.equal(healthy.client.disposed,false);record('scoped-manager','recovered',{healthyPid,newPid:recovered.client.child.pid});
 }catch(error){failure=error;}
 finally{
  cleanupErrors=await cleanup(entries,managers,record);failure??=cleanupErrors[0];
  RpcPeer.prototype.write=write;RpcPeer.prototype.receive=receive;
  fs.writeFileSync(path.join(output,'traffic.jsonl'),traffic.map(row=>JSON.stringify(row)).join('\n')+'\n');fs.writeFileSync(path.join(output,'report.json'),JSON.stringify({schemaVersion:1,status:failure?'failed':'passed-with-gaps',versionTimeoutMs,scope:'Native manifest producer and explicitly labeled injected transport scenarios. No proof/backend readiness, renderer or full Dafny correspondence.',observations,cleanupErrors:cleanupErrors.map(error=>error.stack),error:failure?.stack},null,2)+'\n');
 }
 if(failure)throw failure;return 'passed-with-gaps';
}
module.exports={run,cleanup};
