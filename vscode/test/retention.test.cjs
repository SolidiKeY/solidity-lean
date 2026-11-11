// Real compiler-worker processes unless labeled injected; actual Lean lifecycle is opt-in below.
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

// Regression: normal real Lean-session retirement must reap its exact owned descendant births.
// This opt-in is a real pinned Lean lifecycle observation, not injected solver/proof equivalence.
test('actual Lean normal disposal reaps owned descendant process entries', {skip:!process.env.SOLIDITY_LEAN_REAL_BACKEND,timeout:180000},async()=>{
 const backend=path.resolve(process.env.SOLIDITY_LEAN_REAL_BACKEND),directory=fs.mkdtempSync(path.join(backend,'.lake/retention-actual-')),session=new (require('../src/lean-session.cjs').LeanSession)(backend,directory),{processState}=require('../src/process-state.cjs'),{trackChild,waitForClose}=require('../src/child-lifetime.cjs');
 const evidence=process.env.DAFNY_RETENTION_EVIDENCE,observations={directory,input:'import Solidity.Frontend.Testing\n/-! Regression: normal Lean-session descendant retirement. -/\n#check Nat\n',scope:'Actual Lean only, no source/EVM/solver or complete retention parity claim.'};let child,owned=[];
 const readback=()=>owned.map(p=>{const now=processState(p.pid);return{...p,present:now?.birth===p.birth,state:now?.birth===p.birth?now.state:null,parent:now?.birth===p.birth?now.ppid:null};});
 try{
  const diagnostics=await session.check(observations.input,60000);observations.diagnostics=diagnostics;assert.equal(diagnostics.filter(d=>d.severity===1).length,0);child=session.child;const closed=trackChild(child);
  const table=fs.readdirSync('/proc').filter(name=>/^\d+$/.test(name)).map(Number).map(processState).filter(Boolean),ids=new Set([child.pid]);let changed=true;while(changed){changed=false;for(const row of table)if(ids.has(row.ppid)&&!ids.has(row.pid)){ids.add(row.pid);changed=true;}}
  owned=table.filter(row=>ids.has(row.pid)).map(row=>({pid:row.pid,birth:row.birth}));assert.ok(owned.length>=2,'actual descendant processes observed before retirement');observations.before=readback();const start=Date.now(),deadline=start+1000;
  if(typeof session.finishDispose==='function')await session.finishDispose({deadline});else session.dispose();
  await waitForClose(child,{closed,deadline});while(readback().some(p=>p.present)&&Date.now()<deadline)await new Promise(resolve=>setTimeout(resolve,10));observations.elapsedRetirementMs=Date.now()-start;observations.after=readback();assert.deepEqual(observations.after.filter(p=>p.present),[],'normal disposal must reap owned entries, including zombies');
 }finally{
  if(session.child)session.dispose();observations.final=readback();if(evidence){fs.mkdirSync(evidence,{recursive:true});fs.writeFileSync(path.join(evidence,'observation.json'),JSON.stringify(observations,null,2)+'\n');fs.copyFileSync(path.join(directory,'Worker.lean'),path.join(evidence,'Worker.lean'));}
 }
});

// Regression: idle retirement uses lifecycle IPC independently of success/backend metadata.
for(const exit of [0,1,'timeout'])test('idle worker cooperative retirement '+exit+' (injected worker, no proof)',async()=>{
 const directory=fs.mkdtempSync(path.join(root,'.lake/retention-cooperative-')),fixture=path.join(directory,'worker.cjs'),marker=path.join(directory,'shutdown.json');
 fs.writeFileSync(fixture,`process.on('message',message=>{require('node:fs').writeFileSync(${JSON.stringify(marker)},JSON.stringify(message));${exit==='timeout'?'':`process.exit(${exit});`}});setInterval(()=>{},1000);`);
 const {fork}=require('node:child_process'),{trackChild}=require('../src/child-lifetime.cjs'),child=fork(fixture,[],{stdio:['ignore','ignore','ignore','ipc'],detached:true}),pool=new WorkerPool(root,directory,1),worker={child,closed:trackChild(child),busy:null};pool.workers.push(worker);
 try{await once(child,'spawn');const reads=[],clock=Date.now;let retirement;try{Date.now=()=>{const now=clock();reads.push(now);return now;};retirement=pool.dispose();}finally{Date.now=clock;}if(exit===0)await retirement;else await assert.rejects(retirement,/retirement|closure|deadline/);assert.equal(JSON.parse(fs.readFileSync(marker,'utf8')).action,'shutdown');assert.equal(JSON.parse(fs.readFileSync(marker,'utf8')).deadline,reads[0]+1000,'original1000ms deadline measured at actual admission clock read');if(exit!==0)assert.ok(pool.failure,'failed retirement poisons replacement');}
 finally{require('../src/backend.cjs').terminateTree(child);await worker.closed;fs.rmSync(directory,{recursive:true,force:true});}
});

// Regression: a terminal retirement during asynchronous startup cannot spawn afterward.
test('Lean startup cannot resume after terminal retirement (injected delayed launcher)',async()=>{
 const directory=fs.mkdtempSync(path.join(root,'.lake/retention-startup-')),entered=path.join(directory,'entered'),release=path.join(directory,'release'),spawned=path.join(directory,'spawned');fs.mkdirSync(path.join(directory,'scripts'));
 fs.writeFileSync(path.join(directory,'scripts/lake-command.mjs'),`import fs from 'node:fs';fs.writeFileSync(${JSON.stringify(entered)},'entered');while(!fs.existsSync(${JSON.stringify(release)}))await new Promise(r=>setTimeout(r,1));export const lakeCommand=()=>${JSON.stringify(path.join(directory,'fake-lake'))};`);
 fs.writeFileSync(path.join(directory,'fake-lake'),'#!'+process.execPath+'\nrequire("node:fs").writeFileSync('+JSON.stringify(spawned)+',"spawned");',{mode:0o700});
 const session=new (require('../src/lean-session.cjs').LeanSession)(directory,path.join(directory,'worker')),pending=session.start().catch(error=>error);
 try{const deadline=Date.now()+1000;while(!fs.existsSync(entered)){assert.ok(Date.now()<deadline);await tick();}await session.finishDispose();fs.writeFileSync(release,'release');assert.match((await pending).message,/retiring/);assert.equal(fs.existsSync(spawned),false);assert.ok(!session.child);}
 finally{fs.writeFileSync(release,'release');session.dispose();await pending;fs.rmSync(directory,{recursive:true,force:true});}
});

// Regression: actual compiler + certified Lean pool retirement reaps sampled descendant births.
test('actual Lean pool idle disposal after a failed subsequent task', {skip:!process.env.SOLIDITY_LEAN_REAL_BACKEND,timeout:180000},async()=>{
 const backend=path.resolve(process.env.SOLIDITY_LEAN_REAL_BACKEND),directory=fs.mkdtempSync(path.join(backend,'.lake/retention-pool-')),pool=new WorkerPool(backend,directory,1),source=path.join(backend,'tests/editor-parity/constant.sol'),text=fs.readFileSync(source,'utf8'),{processState}=require('../src/process-state.cjs');let owned=[];const observations={scope:'Actual compiler/kernel-certified f0 then deliberately mismatched compiler hash rejection. No EVM or full retention parity.'};
 const readback=()=>owned.map(p=>{const now=processState(p.pid);return{...p,present:now?.birth===p.birth,state:now?.birth===p.birth?now.state:null};});
 try{const compiled=await pool.run({action:'analyze',source,text});const result=await pool.run({action:'verify',source,text,compiled,options:{certify:true,function:'f0()'}});assert.equal(result.results.find(r=>r.function==='f0').status,'proved');assert.ok(result.backend.leanServerPid);observations.report=result;
 await assert.rejects(pool.run({action:'verify',source,text,compiled:{...compiled,sourceHash:'injected-wrong-source-hash'},options:{certify:true,function:'f0()'}}),/snapshot hash mismatch/);
 const worker=pool.workers[0],table=fs.readdirSync('/proc').filter(n=>/^\d+$/.test(n)).map(Number).map(processState).filter(Boolean),ids=new Set([worker.child.pid]);let changed=true;while(changed){changed=false;for(const p of table)if(ids.has(p.ppid)&&!ids.has(p.pid)){ids.add(p.pid);changed=true;}}owned=table.filter(p=>ids.has(p.pid)).map(p=>({pid:p.pid,birth:p.birth}));assert.ok(owned.length>=3);observations.before=readback();await pool.dispose();observations.after=readback();assert.deepEqual(observations.after.filter(p=>p.present),[]);
 }finally{await pool.dispose();observations.final=readback();if(process.env.DAFNY_RETENTION_EVIDENCE){fs.mkdirSync(process.env.DAFNY_RETENTION_EVIDENCE,{recursive:true});fs.writeFileSync(path.join(process.env.DAFNY_RETENTION_EVIDENCE,'pool-observation.json'),JSON.stringify(observations,null,2)+'\n');}}
});

// Regression: terminal disposal closes an already-admitted native version probe.
test('Lean native version probe is reaped on retirement (injected plugin identity)',async()=>{
 const directory=fs.mkdtempSync(path.join(root,'.lake/retention-probe-')),launcher=path.join(directory,'fake-lake');fs.mkdirSync(path.join(directory,'scripts'));fs.writeFileSync(launcher,'#!'+process.execPath+'\nsetInterval(()=>{},1000);',{mode:0o700});fs.writeFileSync(path.join(directory,'scripts/lake-command.mjs'),'export const lakeCommand=()=>'+JSON.stringify(launcher)+';');
 const native=require('../src/native-plugin.cjs'),file=require.resolve('../src/lean-session.cjs'),original=require.cache[file],inspect=native.inspectNative;let session,pending;
 try{native.inspectNative=()=>({path:'injected-not-real-plugin',leanCommit:'injected'});delete require.cache[file];const {LeanSession}=require(file);native.inspectNative=inspect;session=new LeanSession(directory,path.join(directory,'worker'));pending=session.start().catch(error=>error);const deadline=Date.now()+1000;while(!session.startupProbe){assert.ok(Date.now()<deadline);await tick();}const child=session.startupProbe.child,birth=require('../src/process-state.cjs').processState(child.pid)?.birth;assert.ok(birth);await session.finishDispose();assert.match((await pending).message,/retiring/);assert.notEqual(require('../src/process-state.cjs').processState(child.pid)?.birth,birth);assert.ok(!session.child);}
 finally{native.inspectNative=inspect;if(original)require.cache[file]=original;else delete require.cache[file];session?.dispose();await pending;fs.rmSync(directory,{recursive:true,force:true});}
});

// Regression: an idle native-protocol child must be reaped before its pool owner exits.
// The compiler is real; the executable is explicitly injected and returns pending only.
test('idle native protocol child retires before worker success (injected pending-only executable)',{skip:process.platform!=='linux'},async()=>{
 const directory=fs.mkdtempSync(path.join(root,'.lake/retention-direct-')),runtime=path.join(directory,'runtime'),marker=path.join(directory,'native.pid'),pool=new WorkerPool(root,path.join(directory,'workers'),1),source=path.join(root,'tests/editor-parity/constant.sol'),text=fs.readFileSync(source,'utf8'),previous=process.env.SOLIDITY_LEAN_DIRECT_DIR,enabled=process.env.SOLIDITY_LEAN_DIRECT,{processState}=require('../src/process-state.cjs'),sha=bytes=>require('node:crypto').createHash('sha256').update(bytes).digest('hex');fs.mkdirSync(runtime);let owned;
 const observations={scope:'Actual compiler; injected native-protocol executable returns pending only. No C runtime, solver, kernel or EVM equivalence.'};
 try{process.env.SOLIDITY_LEAN_DIRECT_DIR=runtime;process.env.SOLIDITY_LEAN_DIRECT='1';const compiled=await pool.run({action:'analyze',source,text}),ast=compiled.primaryAst??compiled.fixture.ast,declaration=ast.nodes.find(n=>n.nodeType==='ContractDefinition'&&n.name==='Parity').nodes.find(n=>n.nodeType==='FunctionDefinition'&&n.name==='f0');
 const executable=path.join(runtime,'direct-check'),program='#!'+process.execPath+'\n'+`require('node:fs').writeFileSync(${JSON.stringify(marker)},String(process.pid));console.log(JSON.stringify({ready:true}));require('node:readline').createInterface({input:process.stdin}).on('line',()=>console.log(JSON.stringify({results:[{sourceId:${declaration.id},function:'f0',status:'pending',verification:'direct',reason:'Injected pending-only lifecycle fixture'}]})));setInterval(()=>{},1000);`;
 fs.writeFileSync(executable,program,{mode:0o700});fs.writeFileSync(path.join(runtime,'build.json'),JSON.stringify({version:1,platform:process.platform,arch:require('node:os').machine(),toolchain:fs.readFileSync(path.join(root,'lean-toolchain'),'utf8').trim(),leanCommit:'797c613eb9b6d4ec95db23e3e00af9ac6657f24b',executable:sha(program),sourceFiles:[{module:'Solidity.Tools.DirectRuntime',sourceSha256:sha(fs.readFileSync(path.join(root,'Solidity/Tools/DirectRuntime.lean')))}]}));
 const report=await pool.run({action:'verify',source,text,compiled,options:{certify:false,function:'f0()'}});assert.equal(report.backend.kind,'generated-c-native');assert.ok(report.results.every(r=>r.status==='pending'));owned=processState(Number(fs.readFileSync(marker,'utf8')));assert.ok(owned);assert.equal(owned.ppid,pool.workers[0].child.pid);observations.before=owned;observations.report=report;await pool.dispose();const after=processState(owned.pid);observations.after=after;assert.notEqual(after?.birth,owned.birth,'successful normal retirement left an owned process entry');
 }finally{await pool.dispose();if(owned){const current=processState(owned.pid);if(current?.birth===owned.birth&&!['Z','X'].includes(current.state))require('../src/backend.cjs').terminateTree({pid:owned.pid,processBirth:owned.birth});}if(previous===undefined)delete process.env.SOLIDITY_LEAN_DIRECT_DIR;else process.env.SOLIDITY_LEAN_DIRECT_DIR=previous;if(enabled===undefined)delete process.env.SOLIDITY_LEAN_DIRECT;else process.env.SOLIDITY_LEAN_DIRECT=enabled;if(process.env.DAFNY_NATIVE_RETENTION_EVIDENCE){fs.mkdirSync(process.env.DAFNY_NATIVE_RETENTION_EVIDENCE,{recursive:true});fs.writeFileSync(path.join(process.env.DAFNY_NATIVE_RETENTION_EVIDENCE,'observation.json'),JSON.stringify(observations,null,2)+'\n');}fs.rmSync(directory,{recursive:true,force:true});}
});

// Regression (H550): a Lean server busy at retirement cannot spend the whole
// window on graceful LSP shutdown. The graceful phase gets at most half of the
// original deadline; termination and close confirmation fit in the rest.
// The child is an injected LSP fixture, not Lean.
for(const mode of ['busy','graceful'])test(`Lean session retirement within its deadline: ${mode} server (injected LSP child)`,{skip:process.platform==='win32'},async()=>{
 const directory=fs.mkdtempSync(path.join(root,'.lake/retention-split-')),fixture=path.join(directory,'lean.cjs');
 fs.writeFileSync(fixture,`const {RpcPeer}=require(${JSON.stringify(path.join(root,'vscode/src/rpc.cjs'))});const peer=new RpcPeer(process.stdin,process.stdout);peer.onRequest('shutdown',()=>${mode==='busy'?'new Promise(()=>{})':'null'});peer.onNotification('exit',()=>process.exit(0));process.stderr.write('ready\\n');setInterval(()=>{},1000);`);
 const {spawn}=require('node:child_process'),{RpcPeer}=require('../src/rpc.cjs'),{trackChild}=require('../src/child-lifetime.cjs'),{LeanSession}=require('../src/lean-session.cjs');
 const child=spawn(process.execPath,[fixture],{stdio:['pipe','pipe','pipe']}),closed=trackChild(child),session=new LeanSession(directory,path.join(directory,'worker'));
 let signal=null;child.once('exit',(code,sig)=>{signal=sig;});
 Object.assign(session,{child,peer:new RpcPeer(child.stdout,child.stdin),closed});
 try{
  await once(child,'spawn');await new Promise(resolve=>{let seen='';child.stderr.on('data',chunk=>{seen+=chunk;if(seen.includes('ready'))resolve();});});const start=Date.now(),deadline=start+1000;
  await session.finishDispose({deadline});
  const elapsed=Date.now()-start;
  assert.ok(elapsed<1000,`retirement finished inside the original deadline (${elapsed} ms)`);
  await closed;assert.notEqual(child.exitCode===null&&child.signalCode===null,true,'the child is closed');
  if(mode==='busy')assert.ok(signal,'a busy server is terminated after the graceful half');else assert.equal(child.exitCode,0,'a responsive server takes the graceful path');
 }finally{try{child.kill('SIGKILL');}catch{}fs.rmSync(directory,{recursive:true,force:true});}
});
