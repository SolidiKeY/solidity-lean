'use strict';
const {test}=require('node:test');
const assert=require('node:assert/strict');
const {mkdtempSync,mkdirSync,rmSync,writeFileSync}=require('node:fs');
const {tmpdir}=require('node:os');
const {join}=require('node:path');
const {pathToFileURL}=require('node:url');
const {PassThrough}=require('node:stream');
const {createHash}=require('node:crypto');
const {SolidityService}=require('../src/lsp-server.cjs');
const {RpcPeer,LspFrames}=require('../src/rpc.cjs');
const lang=require('../src/language-services.cjs');
const {checkpointRows,importDiagnostic}=require('../src/lsp-worker.cjs');
const {WorkerPool,fingerprint}=require('../src/worker-pool.cjs');
const hash=text=>createHash('sha256').update(text).digest('hex');
const tick=()=>new Promise(resolve=>setImmediate(resolve));
const deferred=()=>{let resolve;const promise=new Promise(r=>{resolve=r;});return {promise,resolve};};
const text='contract C { function f() public pure returns(uint) { return 1; } }';
function compiled(source){return {fixture:{header:{sourceSha256:hash(source)},ast:{nodes:[]}},rawAst:{nodeType:'SourceUnit',nodes:[]},diagnostics:[],text:'{}',hash:'0x0'};}
function setup(overrides={}){
  const root=mkdtempSync(join(tmpdir(),'solidity-lsp-unit-')),events=[];
  const state={generation:'generation-1',calls:0};
  const service=new SolidityService({notify:(method,params)=>events.push({method,params:structuredClone(params)})},root,{automaticVerification:'never'},
    {fingerprint:()=>state.generation,analyze:async doc=>compiled(doc.text),verify:async task=>{
      state.calls++;return {results:[{source:task.source,sourceHash:hash(task.text),contract:'C',function:'f',signature:'f()',sourceId:1,status:'proved'}],errors:[]};
    },...overrides});
  const uri=pathToFileURL(join(root,'C.sol')).href;
  service.open({uri,version:1,text});clearTimeout(service.docs.get(uri).timer);
  return {service,uri,root,state,events,dispose(){service.dispose();rmSync(root,{recursive:true,force:true});}};
}
test('LSP transport preserves UTF-8 framing and document/request ordering',async()=>{
  const incoming=new PassThrough(),outgoing=new PassThrough();const server=new RpcPeer(incoming,outgoing),client=new RpcPeer(outgoing,incoming);
  let version=0;server.onNotification('change',p=>{version=p.version;});server.onRequest('read',()=>version);
  try{client.notify('change',{version:2});assert.equal(await client.request('read',{}),2);client.notify('change',{version:3});assert.equal(await client.request('read',{}),3);
    const frames=new LspFrames(),messages=[];frames.on('message',m=>messages.push(m));const body=Buffer.from(JSON.stringify({text:'😀é'})),bytes=Buffer.concat([Buffer.from(`Content-Length: ${body.length}\r\n\r\n`),body]);
    for(const byte of bytes)frames.push(Buffer.from([byte]));frames.end();assert.equal(messages[0].text,'😀é');
  }finally{client.close();server.close();incoming.destroy();outgoing.destroy();}
});
test('incremental edits use sequential UTF-16 ranges and reject invalid changes atomically',()=>{
  assert.equal(lang.applyChanges('a😀b\r\nc', [{range:{start:{line:0,character:1},end:{line:0,character:3}},text:'X'},
    {range:{start:{line:1,character:1},end:{line:1,character:1}},text:'d'}]),'aXb\r\ncd');
  const s=setup();try{assert.throws(()=>s.service.change({textDocument:{uri:s.uri,version:2},contentChanges:[{range:{start:{line:99,character:0},end:{line:99,character:0}},text:'bad'}]}));assert.equal(s.service.docs.get(s.uri).text,text);}
  finally{s.dispose();}
});
test('proof cache requires exact source, selection, proof options and backend generation',async()=>{
  const s=setup();try{
    await s.service.verify(s.uri);await s.service.verify(s.uri);assert.equal(s.state.calls,1);assert.equal(s.service.hits,1);
    await s.service.verify(s.uri,{auditPreconditions:false,function:'f()'});assert.equal(s.state.calls,2);
    s.service.change({textDocument:{uri:s.uri,version:2},contentChanges:[{text:text+'\n// changed'}]});
    await s.service.verify(s.uri);assert.equal(s.state.calls,3);
    s.state.generation='generation-2';await s.service.verify(s.uri);assert.equal(s.state.calls,4);
  }finally{s.dispose();}
});
test('backend changes during proof construction prevent publication and caching',async()=>{
  const gate=deferred(),started=deferred();
  const s=setup({verify:async task=>{started.resolve();await gate.promise;return {results:[{source:task.source,sourceHash:hash(task.text),contract:'C',function:'f',status:'proved'}],errors:[]};}});
  try{const pending=s.service.verify(s.uri);await started.promise;s.state.generation='new-backend';gate.resolve();await assert.rejects(pending,e=>e.code===-32801);
    assert.equal(s.service.cache.size,0);assert.equal(s.events.filter(e=>e.method==='solidityLean/report').length,0);
  }finally{s.dispose();}
});
test('late analyses and proofs cannot overwrite a newer document version',async()=>{
  const gate=deferred(),started=deferred();
  const s=setup({analyze:async doc=>{const value=compiled(doc.text);started.resolve();await gate.promise;return value;}});
  try{const pending=s.service.analyze(s.service.docs.get(s.uri));await started.promise;
    s.service.change({textDocument:{uri:s.uri,version:2},contentChanges:[{text:text+'\n// newest'}]});gate.resolve();await assert.rejects(pending,e=>e.code===-32801);
    assert.equal(s.service.docs.get(s.uri).compiled,null);assert.equal(s.events.some(e=>e.method==='solidityLean/report'),false);
  }finally{s.dispose();}
});
test('cancel followed by immediate same-version retry starts a live request',async()=>{
  const first=deferred(),started=deferred();let calls=0;
  const s=setup({verify:async task=>{if(++calls===1){started.resolve();await first.promise;}return {results:[{source:task.source,sourceHash:hash(task.text),contract:'C',function:'f',status:'proved'}],errors:[]};}});
  try{const old=s.service.verify(s.uri);await started.promise;s.service.cancel(s.service.docs.get(s.uri));
    const latest=await s.service.verify(s.uri);assert.equal(latest.results[0].status,'proved');first.resolve();await assert.rejects(old,e=>e.code===-32801);
    const states=s.events.filter(e=>e.method==='solidityLean/status').map(e=>e.params.state);assert.equal(states.at(-1),'complete');assert.equal(calls,2);
  }finally{first.resolve();s.dispose();}
});
test('verification restarts compiler analysis cancelled during symbol discovery',async()=>{
  const started=deferred();let calls=0;
  const s=setup({analyze:async(doc,signal)=>{
    if(++calls===1){started.resolve();await new Promise(resolve=>signal.addEventListener('abort',resolve,{once:true}));throw Object.assign(new Error('cancelled'),{code:-32800});}
    return compiled(doc.text);
  }});
  try{const discovery=s.service.analyze(s.service.docs.get(s.uri));const rejected=assert.rejects(discovery,e=>e.code===-32800);
    await started.promise;s.service.cancel(s.service.docs.get(s.uri));
    assert.equal((await s.service.verify(s.uri)).results[0].status,'proved');await rejected;assert.equal(calls,2);
  }finally{s.dispose();}
});
test('selected verification preserves sibling failures and cached proofs restore compiler diagnostics',async()=>{
  const warning={severity:'warning',message:'compiler warning'};
  const s=setup({analyze:async doc=>({...compiled(doc.text),diagnostics:[warning]}),verify:async task=>({results:(task.options.function?['f']:['f','g']).map(name=>({source:task.source,sourceHash:hash(task.text),contract:'C',function:name,status:name==='g'?'pending':'proved'})),errors:[]})});
  try{
    await s.service.verify(s.uri);s.service.cancel(s.service.docs.get(s.uri));await s.service.verify(s.uri,{function:'f()'});
    assert.ok(s.service.docs.get(s.uri).report.results.some(r=>r.function==='g'&&r.status==='pending'));
    const last=s.events.filter(e=>e.method==='textDocument/publishDiagnostics').at(-1);assert.ok(last.params.diagnostics.some(d=>d.message.includes('g')));
    s.service.close(s.uri);s.service.open({uri:s.uri,version:2,text});await s.service.verify(s.uri);
    assert.ok(s.events.filter(e=>e.method==='textDocument/publishDiagnostics').at(-1).params.diagnostics.some(d=>d.message==='compiler warning'));
    assert.equal(s.service.hits,1);
  }finally{s.dispose();}
});
test('a backend change during cached analysis restoration blocks publication',async()=>{
  const gate=deferred(),started=deferred();let calls=0;
  const s=setup({analyze:async doc=>{if(++calls>1){started.resolve();await gate.promise;}return compiled(doc.text);}});
  try{await s.service.verify(s.uri);s.service.close(s.uri);s.service.open({uri:s.uri,version:2,text});
    const pending=s.service.verify(s.uri);await started.promise;s.state.generation='changed-during-analysis';gate.resolve();await assert.rejects(pending,e=>e.code===-32801);
    assert.equal(s.events.filter(e=>e.method==='solidityLean/report'&&e.params.version===2).length,0);
  }finally{gate.resolve();s.dispose();}
});
test('a document closed during initialization is never opened on the server',async()=>{
  const ready=deferred(),notifications=[];
  const client=Object.create(require('../src/lsp-client.cjs').LanguageClient.prototype);
  Object.assign(client,{ready:ready.promise,documents:new Map(),peer:{notify:(...args)=>notifications.push(args)}});
  const doc={uri:{toString:()=> 'file:///closed.sol'},version:1,isClosed:false,getText:()=>text};
  const pending=client.sync(doc);doc.isClosed=true;ready.resolve();await assert.rejects(pending,e=>e.code===-32801);assert.deepEqual(notifications,[]);
});
test('language requests reject edits that arrive while compiler analysis is pending',async()=>{
  const gate=deferred(),started=deferred();const s=setup({analyze:async doc=>{const c=compiled(doc.text);started.resolve();await gate.promise;return c;}});
  try{const pending=s.service.language('textDocument/rename',{textDocument:{uri:s.uri},position:{line:0,character:22},newName:'renamed'});await started.promise;
    s.service.change({textDocument:{uri:s.uri,version:2},contentChanges:[{text:text+' // new'}]});gate.resolve();await assert.rejects(pending,e=>e.code===-32801);
  }finally{s.dispose();}
});
test('an imported buffer edit cancels and reschedules an importer during its first analysis',async()=>{
  const started=deferred();let calls=0;
  const s=setup({analyze:async(doc,signal)=>{
    if(++calls===1){doc.projectSnapshot={files:{dependency:{path:join(doc.path,'../Dependency.sol')}}};started.resolve();await new Promise(resolve=>signal.addEventListener('abort',resolve,{once:true}));throw Object.assign(new Error('cancelled'),{code:-32800});}
    return compiled(doc.text);
  }});
  try{const doc=s.service.docs.get(s.uri),pending=s.service.analyze(doc),rejected=assert.rejects(pending,e=>e.code===-32800);await started.promise;
    s.service.open({uri:pathToFileURL(join(s.root,'Dependency.sol')).href,version:1,text:'contract Dependency {}'});await rejected;
    assert.ok(doc.timer);assert.ok(s.events.some(e=>e.method==='solidityLean/invalidated'&&e.params.uri===s.uri));
    clearTimeout(doc.timer);await s.service.analyze(doc);assert.equal(calls,2);
  }finally{s.dispose();}
});
test('a redundant filesystem notification preserves a current proof and a real dependency change invalidates it',async()=>{
  const s=setup();
  try{
    const dependency=join(s.root,'Dependency.sol');writeFileSync(dependency,'contract Dependency {}');
    const source='import "./Dependency.sol"; '+text;s.service.change({textDocument:{uri:s.uri,version:2},contentChanges:[{text:source}]});
    await s.service.verify(s.uri);const doc=s.service.docs.get(s.uri),compiled=doc.compiled;
    compiled.project=require('../src/project.cjs').snapshot(doc.path,doc.text,{projectRoot:s.root},s.service.projectDocuments());doc.projectSnapshot=compiled.project;
    s.service.invalidatePath(dependency);assert.equal(doc.compiled,compiled);assert.ok(doc.report);assert.equal(doc.verifyAbort.signal.aborted,false);
    writeFileSync(dependency,'contract Dependency { uint changed; }');s.service.invalidatePath(dependency);assert.equal(doc.compiled,null);assert.equal(doc.report,null);
    assert.ok(s.events.some(e=>e.method==='solidityLean/invalidated'));
  }finally{s.dispose();}
});
test('contract checkpoint identities and native import warnings remain visible',()=>{
  const root=mkdtempSync(join(tmpdir(),'lsp-checkpoint-'));
  try{const path=join(root,'result.json');writeFileSync(path,JSON.stringify([{function:'f',sourceId:10,status:'proved'}]));
    assert.throws(()=>checkpointRows(path,{nodes:[{nodeType:'FunctionDefinition',id:20,name:'f'}]}),/selected contract/);
    assert.equal(checkpointRows(join(root,'missing.json'),{nodes:[]}),null);
    assert.equal(importDiagnostic({severity:2,message:'solc_import: the initializers are left out'}),true);
    assert.equal(importDiagnostic({severity:2,message:'unused variable'}),false);
  }finally{rmSync(root,{recursive:true,force:true});}
});
test('rename rejects Solidity keywords and qualified references preserve their qualifier',()=>{
  for(const name of ['if','uint256','while','this','true','fixed128x18','import','pragma','as','from'])assert.equal(lang.validIdentifier(name),false);
  assert.equal(lang.validIdentifier('$renamed'),true);
  const source='struct S {} C.S value;';
  const ast={nodeType:'SourceUnit',nodes:[{nodeType:'StructDefinition',id:1,name:'S',src:'0:11:0',nameLocation:'7:1:0'},
    {nodeType:'UserDefinedTypeName',src:'12:3:0',referencedDeclaration:1,pathNode:{nodeType:'IdentifierPath',name:'C.S',src:'12:3:0',nameLocations:['12:1:0','14:1:0'],referencedDeclaration:1}}]};
  const index=lang.index(source,ast),occurrence=index.occurrence({line:0,character:14});
  assert.deepEqual(occurrence.range,{start:{line:0,character:14},end:{line:0,character:15}});
  assert.equal(index.references(occurrence.declaration,false)[0].start.character,14);assert.equal(index.references(occurrence.declaration,false).length,1);
});
test('the default sibling compiler path participates in cache invalidation',()=>{
  const base=mkdtempSync(join(tmpdir(),'lsp-fingerprint-')),root=join(base,'repo'),solkey=join(base,'solkey');
  const previous=process.env.SOLKEY_ROOT;delete process.env.SOLKEY_ROOT;
  try{
    mkdirSync(root,{recursive:true});for(const file of ['lean-toolchain','lakefile.toml','lake-manifest.json'])writeFileSync(join(root,file),'fixture');
    const compilerDir=join(solkey,'keyext.solidity.core/build/soljson');mkdirSync(compilerDir,{recursive:true});
    writeFileSync(join(solkey,'keyext.solidity.core/build.gradle'),'ext.soljsonFile = "stub.cjs"');writeFileSync(join(compilerDir,'stub.cjs'),'first');
    const before=fingerprint(root);writeFileSync(join(compilerDir,'stub.cjs'),'changed binary');assert.notEqual(fingerprint(root),before);
  }finally{if(previous===undefined)delete process.env.SOLKEY_ROOT;else process.env.SOLKEY_ROOT=previous;rmSync(base,{recursive:true,force:true});}
});
test('queued work cancels before execution and crashed workers can be replaced',async()=>{
  const root=mkdtempSync(join(tmpdir(),'lsp-pool-'));mkdirSync(join(root,'scripts'));
  writeFileSync(join(root,'scripts/source-locations.mjs'),'export const unused = true;');
  writeFileSync(join(root,'scripts/solc-ast.mjs'),`export function compileFixture(options){const text=options.sourceBytes.toString();if(text==='crash')process.exit(9);return new Promise(resolve=>setTimeout(()=>resolve({text}),150));}`);
  const pool=new WorkerPool(root,join(root,'workers'),1);
  try{
    const first=pool.run({action:'analyze',source:join(root,'A.sol'),text:'first'}),controller=new AbortController();
    const queued=pool.run({action:'analyze',source:join(root,'B.sol'),text:'queued'},{signal:controller.signal});controller.abort();
    await assert.rejects(queued,e=>e.code===-32800);assert.equal((await first).text,'first');
    const old=pool.workers[0].child.pid;
    await assert.rejects(pool.run({action:'analyze',source:join(root,'C.sol'),text:'crash'}),/exited/);
    assert.equal((await pool.run({action:'analyze',source:join(root,'D.sol'),text:'recovered'})).text,'recovered');
    assert.notEqual(pool.workers[0].child.pid,old);
  }finally{pool.dispose();rmSync(root,{recursive:true,force:true});}
});
test('reset stops an in-flight build and cannot clear a replacement build handle',async()=>{
  const s=setup({verify:undefined});mkdirSync(join(s.root,'scripts'));
  const lake=join(s.root,'fake-lake');writeFileSync(lake,`#!${process.execPath}\nsetInterval(()=>{},1000);\n`,{mode:0o700});
  writeFileSync(join(s.root,'scripts/lake-command.mjs'),`export const lakeCommand=()=>${JSON.stringify(lake)};`);
  try{
    const old=s.service.build().catch(error=>error);
    const until=async fn=>{const deadline=Date.now()+2000;while(!fn()){assert.ok(Date.now()<deadline);await tick();}};
    await until(()=>s.service.buildChild);const previous=s.service.buildChild;
    s.service.reset();const replacement=s.service.build().catch(error=>error);
    await until(()=>s.service.buildChild&&s.service.buildChild!==previous);const current=s.service.buildChild;
    await old;assert.equal(s.service.buildChild,current);
    s.service.dispose();await replacement;
  }finally{s.dispose();}
});

test('direct and certificate requests never share a result cache entry',async()=>{
  const s=setup({verify:async task=>({results:[{source:task.source,sourceHash:hash(task.text),contract:'C',function:'f',status:'proved',...(task.options.certify?{}:{verification:'direct'})}],errors:[]})});
  try{
    const first=await s.service.verify(s.uri);assert.equal(first.results[0].verification,'direct');
    const certified=await s.service.verify(s.uri,{certify:true});assert.equal(certified.results[0].verification,undefined);
    assert.equal((await s.service.verify(s.uri)).results[0].verification,'direct');
  }finally{s.dispose();}
});

test('analysis during an owned build ignores intermediate artifacts but detects changed inputs',async()=>{
  const s=setup({verify:undefined});mkdirSync(join(s.root,'scripts'));
  const lake=join(s.root,'fake-lake');writeFileSync(lake,`#!${process.execPath}\nprocess.on('SIGUSR1',()=>process.exit(0));setInterval(()=>{},1000);\n`,{mode:0o700});
  writeFileSync(join(s.root,'scripts/lake-command.mjs'),`export const lakeCommand=()=>${JSON.stringify(lake)};`);
  let input='source-1';s.service.buildInputs=()=>input;
  try{
    const pending=s.service.build().catch(e=>e);
    while(!s.service.buildChild)await tick();const child=s.service.buildChild;
    s.state.generation='artifact-half-written';await s.service.analyze(s.service.docs.get(s.uri));
    assert.equal(s.service.buildChild,child);assert.equal(s.service.generation,'generation-1');
    input='source-2';s.service.refresh();assert.equal(s.service.buildChild,null);
    await pending;
  }finally{s.dispose();}
});
test('a short verification deadline also bounds a shared lazy build wait',async()=>{
  const s=setup(),build=deferred();s.service.build=()=>build.promise;
  s.service.pool.run=async()=>({needsLegacyBuild:true});
  try{
    const start=Date.now();await assert.rejects(s.service.prove({options:{timeoutMs:25}},undefined),e=>e.code===-32800);
    assert.ok(Date.now()-start<1000);build.resolve();
  }finally{s.dispose();}
});

test('frontend dependency fingerprints track imported models and keep owned build inputs stable',()=>{
  const base=mkdtempSync(join(tmpdir(),'lsp-closure-')),root=join(base,'repo'),solkey=join(base,'solkey'),previous=process.env.SOLKEY_ROOT;
  process.env.SOLKEY_ROOT=solkey;
  try{
    mkdirSync(root,{recursive:true});for(const file of ['lean-toolchain','lakefile.toml','lake-manifest.json'])writeFileSync(join(root,file),'fixture');
    mkdirSync(join(solkey,'keyext.solidity.core/build/soljson'),{recursive:true});writeFileSync(join(solkey,'keyext.solidity.core/build.gradle'),'ext.soljsonFile = "stub.cjs"');writeFileSync(join(solkey,'keyext.solidity.core/build/soljson/stub.cjs'),'compiler');
    for(const d of ['Solidity/Frontend','Solidity/Tools','.lake/build/ir/Solidity/Frontend','.lake/build/lib/lean/Solidity'])mkdirSync(join(root,d),{recursive:true});
    for(const name of ['Frontend/Testing','Tools/DirectRuntime','Dependency','Unrelated'])writeFileSync(join(root,'Solidity',name+'.lean'),'-- '+name);
    const setupFile=join(root,'.lake/build/ir/Solidity/Frontend/Testing.setup.json');
    writeFileSync(setupFile,JSON.stringify({importArts:{'Solidity.Dependency':{}}}));
    const artifact=join(root,'.lake/build/lib/lean/Solidity/Dependency.olean');writeFileSync(artifact,'built');
    const first=fingerprint(root),inputs=fingerprint(root,{buildInputs:true});
    writeFileSync(join(root,'Solidity/Unrelated.lean'),'-- changed outside verifier closure');
    assert.equal(fingerprint(root),first);assert.notEqual(fingerprint(root,{buildInputs:true}),inputs);
    const stableInputs=fingerprint(root,{buildInputs:true});writeFileSync(artifact,'rebuilt');
    assert.notEqual(fingerprint(root),first);assert.equal(fingerprint(root,{buildInputs:true}),stableInputs);
    const before=fingerprint(root);writeFileSync(join(root,'Solidity/Dependency.lean'),'import Solidity.NewDependency');assert.notEqual(fingerprint(root),before);
    writeFileSync(join(root,'Solidity/NewDependency.lean'),'-- new');writeFileSync(setupFile,JSON.stringify({importArts:{'Solidity.Dependency':{},'Solidity.NewDependency':{}}}));
    const updated=fingerprint(root);writeFileSync(join(root,'Solidity/NewDependency.lean'),'-- new model changed');assert.notEqual(fingerprint(root),updated);
  }finally{if(previous===undefined)delete process.env.SOLKEY_ROOT;else process.env.SOLKEY_ROOT=previous;rmSync(base,{recursive:true,force:true});}
});

// Regression (landing review): a certified recheck must end before the pool's
// request deadline, or the pool retires the worker and its kept direct answers
// are lost. The budget keeps a reply margin of 20% of the time left (at most 1 s).
test('certified recheck budget ends before the request deadline',()=>{
  const {recheckBudget}=require('../src/lsp-worker.cjs'),now=1_000_000;
  assert.equal(recheckBudget(60000,now+10000,now),9000,"margin capped at 1 s");
  assert.equal(recheckBudget(60000,now+500,now),400);
  assert.equal(recheckBudget(5000,now+60000,now),5000,'a shorter request timeout is kept');
  assert.equal(recheckBudget(60000,undefined,now),60000,'no deadline: unchanged');
  assert.equal(recheckBudget(60000,now-5,now),1,'an expired deadline leaves a minimal budget');
  for(const left of [2,50,999,5000,120000])assert.ok(recheckBudget(1e9,now+left,now)<left||left<=1,`budget below ${left} ms`);
});
test('the worker pool sends each task its request deadline',async()=>{
  const fs=require('node:fs'),path=require('node:path'),{WorkerPool}=require('../src/worker-pool.cjs'),root=path.resolve(__dirname,'../..');
  const directory=fs.mkdtempSync(path.join(root,'.lake/pool-deadline-')),pool=new WorkerPool(root,directory,1),sent=[],spawn=pool.spawn.bind(pool);
  pool.spawn=()=>{const worker=spawn(),send=worker.child.send.bind(worker.child);worker.child.send=(message,...rest)=>{sent.push(message);return send(message,...rest);};return worker;};
  try{
    const before=Date.now(),source=path.join(root,'tests/editor-parity/constant.sol');
    await pool.run({action:'analyze',source,text:fs.readFileSync(source,'utf8')},{timeoutMs:120000});
    const task=sent.find(message=>message.action==='analyze');assert.ok(task);
    assert.ok(task.requestDeadline>=before+120000&&task.requestDeadline<=Date.now()+120000,'deadline = admission time + timeout');
  }finally{await pool.dispose();fs.rmSync(directory,{recursive:true,force:true});}
});

// Regression (landing review on f244f336): a Lean fallback after a compiled-
// verifier gap must end before the pool's request deadline and return what it
// holds, instead of outliving the deadline and losing the whole report. The
// Lean server is an injected stand-in that never finishes a check.
test('a stalled Lean fallback returns before the request deadline',{skip:process.platform==='win32',timeout:60000},async()=>{
  const fs=require('node:fs'),path=require('node:path'),{WorkerPool}=require('../src/worker-pool.cjs'),root=path.resolve(__dirname,'../..');
  const directory=fs.mkdtempSync(path.join(root,'.lake/pool-stall-')),bin=path.join(directory,'bin'),runtime=path.join(directory,'no-runtime');fs.mkdirSync(bin);fs.mkdirSync(runtime);
  fs.writeFileSync(path.join(bin,'lake'),`#!${process.execPath}\nconst args=process.argv.slice(2);if(args[0]==='env'){console.log('injected-not-a-lean-commit');process.exit(0);}\nconst {RpcPeer}=require(${JSON.stringify(path.join(root,'vscode/src/rpc.cjs'))});const peer=new RpcPeer(process.stdin,process.stdout);peer.onRequest('initialize',()=>({capabilities:{}}));peer.onRequest('textDocument/waitForDiagnostics',()=>new Promise(()=>{}));peer.onRequest('shutdown',()=>null);peer.onNotification('exit',()=>process.exit(0));setInterval(()=>{},1000);\n`,{mode:0o700});
  const saved={PATH:process.env.PATH,DIR:process.env.SOLIDITY_LEAN_DIRECT_DIR,DIRECT:process.env.SOLIDITY_LEAN_DIRECT};
  process.env.PATH=bin+path.delimiter+process.env.PATH;process.env.SOLIDITY_LEAN_DIRECT_DIR=runtime;process.env.SOLIDITY_LEAN_DIRECT='1';
  const pool=new WorkerPool(root,path.join(directory,'workers'),1),source=path.join(root,'tests/editor-parity/constant.sol'),text=fs.readFileSync(source,'utf8');
  try{
    const compiled=await pool.run({action:'analyze',source,text},{timeoutMs:60000});
    const start=Date.now();
    const report=await pool.run({action:'verify',source,text,compiled,options:{certify:false,timeoutMs:60000}},{timeoutMs:6000});
    assert.ok(Date.now()-start<6000,'returned before the pool deadline');
    assert.ok(report.errors.some(e=>e.stage==='lean'&&/request deadline/.test(e.reason)),JSON.stringify(report.errors));
    assert.ok(report.results.length>0&&report.results.every(r=>r.status==='unsupported'),'open rows are reported unknown, not dropped');
  }finally{await pool.dispose().catch(()=>{});process.env.PATH=saved.PATH;for(const [k,v] of [['SOLIDITY_LEAN_DIRECT_DIR',saved.DIR],['SOLIDITY_LEAN_DIRECT',saved.DIRECT]])if(v===undefined)delete process.env[k];else process.env[k]=v;fs.rmSync(directory,{recursive:true,force:true});}
});
