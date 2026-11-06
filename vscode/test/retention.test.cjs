// Real compiler-worker processes unless explicitly labeled as injected lifecycle boundaries. No Lean/proof jobs.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),{once}=require('node:events');
const {WorkerPool}=require('../src/worker-pool.cjs'),{SolidityService}=require('../src/lsp-server.cjs');
const root=path.resolve(__dirname,'../..'),text='contract C {}';
fs.mkdirSync(path.join(root,'.lake'),{recursive:true});
function observe(pool){const entries=[],spawn=pool.spawn.bind(pool);pool.spawn=()=>{const worker=spawn();const entry={worker,closed:false};entry.close=new Promise(resolve=>worker.child.once('close',()=>{entry.closed=true;resolve();}));entries.push(entry);return worker;};return entries;}
const task=directory=>({action:'analyze',source:path.join(directory,'C.sol'),text});
test('compiler worker disposal settles child close before returning success',async()=>{
 const directory=fs.mkdtempSync(path.join(root,'.lake/retention-test-')),pool=new WorkerPool(root,path.join(directory,'workers'),1),entries=observe(pool);let pending;
 try{pending=pool.run(task(directory)).catch(error=>error);await once(entries[0].worker.child,'spawn');await pool.dispose();assert.equal(entries[0].closed,true);assert.throws(()=>process.kill(entries[0].worker.child.pid,0),error=>error.code==='ESRCH');}
 finally{await pool.dispose();await Promise.all(entries.map(entry=>entry.close));await pending;fs.rmSync(directory,{recursive:true,force:true});}
});
test('cancelled worker closes before a queued replacement can spawn',async()=>{
 const directory=fs.mkdtempSync(path.join(root,'.lake/retention-test-')),pool=new WorkerPool(root,path.join(directory,'workers'),1),entries=observe(pool),abort=new AbortController();let first,second;
 try{first=pool.run(task(directory),{signal:abort.signal}).catch(error=>error);await once(entries[0].worker.child,'spawn');let oldClosedAtReplacement;const spawn=pool.spawn.bind(pool);pool.spawn=()=>{oldClosedAtReplacement=entries[0].closed;return spawn();};second=pool.run(task(directory)).catch(error=>error);abort.abort();const result=await second;assert.ok(!(result instanceof Error),result?.message);assert.equal(oldClosedAtReplacement,true,'replacement started before old worker close');assert.equal((await first).code,-32800);}
 finally{await pool.dispose();await Promise.all(entries.map(entry=>entry.close));await first;await second;fs.rmSync(directory,{recursive:true,force:true});}
});
test('service disposal keeps its directory until live compiler workers have closed',async()=>{
 const service=new SolidityService({notify(){}},root,{automaticVerification:'never'},{fingerprint:()=> 'injected-fingerprint-only'}),entries=observe(service.analysisPool);let pending;
 try{pending=service.analysisPool.run(task(service.directory)).catch(error=>error);await once(entries[0].worker.child,'spawn');const disposal=service.dispose();if(!entries[0].closed)assert.equal(fs.existsSync(service.directory),true,'removed live-worker directory before close');await disposal;assert.equal(entries[0].closed,true);assert.equal(fs.existsSync(service.directory),false);}
 finally{await service.dispose();await Promise.all(entries.map(entry=>entry.close));await pending;fs.rmSync(service.directory,{recursive:true,force:true});}
});

const proc=pid=>{try{const stat=fs.readFileSync('/proc/'+pid+'/stat','utf8'),parts=stat.slice(stat.lastIndexOf(')')+2).split(' ');return{pid,state:parts[0],ppid:Number(parts[1]),group:Number(parts[2]),session:Number(parts[3]),birth:parts[19]};}catch(error){if(error.code==='ENOENT')return null;throw error;}};
const alive=record=>!!record&&!['Z','X'].includes(record.state);
test('abrupt server crash cannot orphan an owned compiler worker that cannot run disconnect handlers',async()=>{
 const {LanguageClient}=require('../src/lsp-client.cjs'),directory=fs.mkdtempSync(path.join(root,'.lake/retention-crash-')),client=new LanguageClient({backendPath:root,nodePath:process.execPath,projectRoot:directory,automaticVerification:'never'}),doc={uri:new URL('file://'+path.join(directory,'C.sol')),version:1,isClosed:false,getText:()=>text};let worker;
 try{await client.request('textDocument/documentSymbol',doc);const children=fs.readdirSync('/proc').filter(name=>/^\d+$/.test(name)).map(Number).map(proc).filter(record=>record?.ppid===client.child.pid);assert.equal(children.length,1);worker=children[0];process.kill(worker.pid,'SIGSTOP');client.child.kill('SIGKILL');await client.closed;await client.dispose();assert.equal(alive(proc(worker.pid)),false,'stopped compiler worker survived crashed server disposal');}
 finally{if(worker&&proc(worker.pid)?.birth===worker.birth&&alive(proc(worker.pid)))process.kill(worker.pid,'SIGKILL');await client.dispose();fs.rmSync(directory,{recursive:true,force:true});}
});

const tick=()=>new Promise(resolve=>setImmediate(resolve));
test('queued work keeps its original deadline and cannot spawn after barrier disposal',async()=>{
 const directory=fs.mkdtempSync(path.join(root,'.lake/retention-barrier-'));let release;const pool=new WorkerPool(root,directory,1,{startAfter:new Promise(resolve=>{release=resolve;})});
 try{await assert.rejects(pool.run(task(directory),{timeoutMs:20}),error=>error.code===-32800);await pool.dispose();release();await tick();assert.equal(pool.workers.length,0);}finally{await pool.dispose();fs.rmSync(directory,{recursive:true,force:true});}
});
test('invalid reset does not cancel resources and rapid reset generations never share paths',async()=>{
 const service=new SolidityService({notify(){}},root,{automaticVerification:'never'},{fingerprint:()=> 'injected-fingerprint-only'}),pool=service.pool;try{const abort=new AbortController(),doc=service.open({uri:new URL('file://'+path.join(service.directory,'C.sol')).href,version:1,text});clearTimeout(doc.timer);doc.analysisAbort=abort;assert.throws(()=>service.reset({workers:5}),/workers/);assert.equal(abort.signal.aborted,false);assert.equal(service.pool,pool);const paths=[];for(let i=0;i<3;i++){service.reset();paths.push(service.analysisPool.directory);}assert.equal(new Set(paths).size,3);await service.dispose();assert.equal(fs.existsSync(service.directory),false);}finally{await service.dispose();}
});
test('manager waits per configuration for physical retirement and retains cleanup failures',async()=>{
 const {LanguageServers}=require('../src/lsp-client.cjs'),configuration={backendPath:root},servers=new LanguageServers(()=>configuration),doc={uri:new URL('file:///retiring.sol'),version:1,isClosed:false,getText:()=>text};let close;
 const fake={child:{pid:-1},closed:new Promise(resolve=>{close=resolve;}),dispose:async()=>{}};const retirement=servers.retire(JSON.stringify(configuration),fake);await tick();assert.throws(()=>servers.client(doc),/retiring/);const abort=new AbortController(),pending=servers.request('textDocument/documentSymbol',doc,{}, {signal:abort.signal});abort.abort();await assert.rejects(pending,error=>error.code===-32800);assert.equal(servers.clients.size,0);close();await retirement;await servers.dispose();
 const failed=new LanguageServers(()=>configuration),error=Error('injected cleanup failure');await assert.rejects(failed.retire(JSON.stringify(configuration),{dispose:async()=>{throw error;}}),e=>e===error);await assert.rejects(failed.request('textDocument/documentSymbol',doc),e=>e===error);assert.equal(failed.clients.size,0);await assert.rejects(failed.dispose(),/cleanup failed/);
});

test('RPC cancel write failure still settles once and clears request timers/listeners',async()=>{
 const {PassThrough}=require('node:stream'),{RpcPeer}=require('../src/rpc.cjs'),input=new PassThrough(),output=new PassThrough(),peer=new RpcPeer(input,output);let listener;const signal={aborted:false,addEventListener(name,fn){listener=fn;},removeEventListener(){listener=null;}};
 const pending=peer.request('injected-never-replies',{}, {signal}).catch(error=>error);peer.notify=()=>{throw Error('injected cancel write failure');};
 try{assert.doesNotThrow(()=>listener());const error=await pending;assert.equal(error.code,-32800);assert.equal(peer.pending.size,0);assert.equal(listener,null);assert.equal(peer.closed,true);}finally{peer.close();await pending;input.destroy();output.destroy();}
});

test('uncooperative transport shutdown rejects at the existing deadline rather than reporting unconfirmed success',async()=>{
 const {LanguageClient}=require('../src/lsp-client.cjs'),directory=fs.mkdtempSync(path.join(root,'.lake/retention-client-')),executable=path.join(directory,'runtime');
 fs.writeFileSync(executable,'#!'+process.execPath+'\n'+`if(process.argv.includes('--version')){console.log(process.version);process.exit(0);}const{RpcPeer}=require(${JSON.stringify(require.resolve('../src/rpc.cjs'))});const p=new RpcPeer(process.stdin,process.stdout);p.onRequest('initialize',()=>({capabilities:{},serverInfo:{name:'Retention fixture',version:'1.0.0'}}));p.onNotification('initialized',()=>p.notify('solidityLean/serverVersion',{name:'Retention fixture',version:'1.0.0'}));p.onRequest('shutdown',()=>null);p.onNotification('exit',()=>{});setInterval(()=>{},1000);`,{mode:0o700});
 const client=new LanguageClient({backendPath:root,nodePath:executable,automaticVerification:'never'});
 try{await client.ready;await assert.rejects(client.dispose(),/closure.*deadline/);await client.closed;assert.equal(alive(proc(client.child.pid)),false);}finally{await client.dispose().catch(()=>{});await client.closed;fs.rmSync(directory,{recursive:true,force:true});}
});

test('worker-only crash retires its real owned descendant before replacement (injected compiler fixture)',async()=>{
 const directory=fs.mkdtempSync(path.join(root,'.lake/retention-descendant-'));fs.mkdirSync(path.join(directory,'scripts'));fs.writeFileSync(path.join(directory,'scripts/source-locations.mjs'),'export const unused=true;');fs.writeFileSync(path.join(directory,'scripts/solc-ast.mjs'),`import{spawn}from'node:child_process';import{writeFileSync}from'node:fs';export function compileFixture(options){const text=options.sourceBytes.toString();if(text==='spawn-descendant'){const child=spawn(process.execPath,['-e','setInterval(()=>{},1000)'],{stdio:'ignore'});writeFileSync(${JSON.stringify(path.join(directory,'child.pid'))},String(child.pid));}if(text==='crash')process.exit(9);return{fixture:text};}`);
 const pool=new WorkerPool(directory,path.join(directory,'workers'),1);let descendant;
 try{await pool.run({...task(directory),text:'spawn-descendant'});descendant=proc(Number(fs.readFileSync(path.join(directory,'child.pid'),'utf8')));assert.ok(descendant);await assert.rejects(pool.run({...task(directory),text:'crash'}),/exited/);await pool.run({...task(directory),text:'recovered'});assert.equal(alive(proc(descendant.pid)),false,'worker descendant survived replacement');}
 finally{if(descendant&&proc(descendant.pid)?.birth===descendant.birth&&alive(proc(descendant.pid)))process.kill(descendant.pid,'SIGKILL');await pool.dispose();fs.rmSync(directory,{recursive:true,force:true});}
});
test('actual build child identity is transferred to its owner (fake executable, no Lean)',async()=>{
 const directory=fs.mkdtempSync(path.join(root,'.lake/retention-build-')),events=[];fs.mkdirSync(path.join(directory,'scripts'));const executable=path.join(directory,'fake-lake');fs.writeFileSync(executable,'#!'+process.execPath+'\nsetInterval(()=>{},1000);\n',{mode:0o700});fs.writeFileSync(path.join(directory,'scripts/lake-command.mjs'),'export const lakeCommand=()=>'+JSON.stringify(executable)+';');const service=new SolidityService({ownedProcessRegistration:true,request:async(method,params)=>{events.push({method,params});return true;},notify:(method,params)=>events.push({method,params})},directory,{}, {fingerprint:()=> 'injected-build-fingerprint'});const pending=service.build().catch(error=>error);
 try{const deadline=Date.now()+2000;while(!service.buildChild){assert.ok(Date.now()<deadline);await tick();}assert.ok(events.some(event=>event.method==='solidityLean/registerOwnedProcess'&&event.params.kind==='build'&&event.params.pid===service.buildChild.pid));}
 finally{await service.dispose();await pending;fs.rmSync(directory,{recursive:true,force:true});}
});

test('failed retirement rejects promptly and keeps an unconfirmed physical-close key poisoned (injected owner)',async()=>{
 const {LanguageServers}=require('../src/lsp-client.cjs'),configuration={backendPath:root},manager=new LanguageServers(()=>configuration),failure=Error('injected already-exceeded closure deadline'),doc={uri:new URL('file:///poisoned.sol'),version:1,isClosed:false,getText:()=>text};
 const fake={child:{pid:-1},closed:new Promise(()=>{}),dispose:async()=>{throw failure;}};await assert.rejects(manager.retire(JSON.stringify(configuration),fake),error=>error===failure);assert.equal(manager.retirementFailures[0],failure);await assert.rejects(manager.request('textDocument/documentSymbol',doc),error=>error===failure);assert.equal(manager.clients.size,0);await assert.rejects(manager.dispose(),/cleanup failed/);
});

test('ownership ACK refuses nonexistent or non-private process identities',async()=>{
 const {ownedProcess}=require('../src/process-state.cjs');assert.throws(()=>ownedProcess({pid:2147483647,birth:'1',kind:'analysis'},{pid:process.pid}),/owned|registration/);
});
test('fast build cannot succeed before delayed ownership refusal (fake true executable, no Lean)',async()=>{
 const directory=fs.mkdtempSync(path.join(root,'.lake/retention-build-refusal-'));fs.mkdirSync(path.join(directory,'scripts'));fs.writeFileSync(path.join(directory,'scripts/lake-command.mjs'),`export const lakeCommand=()=>'/bin/true';`);let service;
 const peer={ownedProcessRegistration:true,notify(){},request:()=>new Promise(resolve=>service.buildChild.once('close',()=>setImmediate(()=>resolve(false))))};service=new SolidityService(peer,directory,{timeoutMs:100},{fingerprint:()=> 'injected-fast-build-fingerprint'});
 try{const result=await service.build().then(()=>null,error=>error);assert.ok(result instanceof Error,'build succeeded without accepted ownership');assert.equal(service.legacyBuilt,false);}finally{await service.dispose();fs.rmSync(directory,{recursive:true,force:true});}
});

test('build launcher waits for actual acknowledgement before executing the unchanged command (fake executable)',async()=>{
 const directory=fs.mkdtempSync(path.join(root,'.lake/retention-build-ack-')),marker=path.join(directory,'command-started');fs.mkdirSync(path.join(directory,'scripts'));const executable=path.join(directory,'fake-lake');fs.writeFileSync(executable,'#!'+process.execPath+'\nrequire("node:fs").writeFileSync('+JSON.stringify(marker)+',"started");\n',{mode:0o700});fs.writeFileSync(path.join(directory,'scripts/lake-command.mjs'),'export const lakeCommand=()=>'+JSON.stringify(executable)+';');let service,release,ready;
 const peer={ownedProcessRegistration:true,notify(){},request:()=>new Promise(resolve=>{ready=once(service.buildChild,'message');release=()=>resolve(true);})};service=new SolidityService(peer,directory,{}, {fingerprint:()=> 'injected-ack-build-fingerprint'});const pending=service.build();
 try{const deadline=Date.now()+2000;while(!ready){assert.ok(Date.now()<deadline);await tick();}assert.deepEqual((await ready)[0],{ready:true});assert.equal(fs.existsSync(marker),false);release();await pending;assert.equal(fs.readFileSync(marker,'utf8'),'started');assert.equal(service.legacyBuilt,true);}finally{release?.();await service.dispose();await pending.catch(()=>{});fs.rmSync(directory,{recursive:true,force:true});}
});

test('RPC timeout write failure settles and closes without retaining request state',async()=>{
 const{PassThrough}=require('node:stream'),{RpcPeer}=require('../src/rpc.cjs'),input=new PassThrough(),output=new PassThrough(),peer=new RpcPeer(input,output);const pending=peer.request('injected-timeout',{}, {timeoutMs:20}).catch(error=>error);peer.notify=()=>{throw Error('injected timeout write failure');};try{assert.equal((await pending).code,-32800);assert.equal(peer.pending.size,0);assert.equal(peer.closed,true);}finally{peer.close();input.destroy();output.destroy();}
});
