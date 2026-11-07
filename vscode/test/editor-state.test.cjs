/* Injected VS Code boundary regressions. These do not establish visual/editor-host parity. */
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),{EventEmitter}=require('node:events'),{createHash}=require('node:crypto');
const {mock}=require('./mock.cjs'),{createExtension}=require('../src/extension.cjs');
const tick=()=>new Promise(r=>setImmediate(r)),noop=()=>({dispose(){}});
function fixture(backend){
  const e=mock();e.calls={opens:[],restarts:0,cancels:0};
  const b={...e.doc,uri:{...e.doc.uri,fsPath:'/tmp/other.sol'}};e.documents=[e.doc,b];
  e.editors=e.documents.map(document=>({document,decorations:new Map(),setDecorations(type,rows){this.decorations.set(type.kind,rows);}}));
  e.bar={visible:false,text:'',show(){this.visible=true;},hide(){this.visible=false;},dispose(){this.visible=false;}};
  e.vscode.Uri={file:fsPath=>({fsPath}),parse:value=>({toString:()=>value})};e.vscode.StatusBarAlignment={Left:1,Right:2};e.versionBar={visible:false,text:'',show(){this.visible=true;},hide(){this.visible=false;},dispose(){this.visible=false;}};e.vscode.CodeActionKind={QuickFix:{}};
  for(const name of ['registerCompletionItemProvider','registerDefinitionProvider','registerReferenceProvider','registerDocumentSymbolProvider','registerSignatureHelpProvider','registerDocumentHighlightProvider','registerRenameProvider','registerDocumentFormattingEditProvider','registerCodeActionsProvider','registerWorkspaceSymbolProvider'])e.vscode.languages[name]=noop;
  Object.assign(e.vscode.window,{activeTextEditor:e.editors[0],visibleTextEditors:e.editors,createTextEditorDecorationType:options=>({kind:require('node:path').basename(options.gutterIconPath.fsPath,'.svg'),dispose(){}}),createStatusBarItem:alignment=>alignment===2?e.versionBar:e.bar,
    onDidChangeActiveTextEditor:fn=>e.subscribe('activeEditor',fn),onDidChangeVisibleTextEditors:fn=>e.subscribe('visibleEditors',fn),showQuickPick:async()=>undefined});
  Object.assign(e.vscode.workspace,{textDocuments:e.documents,onDidOpenTextDocument:fn=>e.subscribe('open',fn),createFileSystemWatcher:()=>({dispose(){},onDidChange:noop,onDidCreate:noop,onDidDelete:noop})});
  e.service=Object.assign(new EventEmitter(),{open:async doc=>e.calls.opens.push(doc),cancel:()=>e.calls.cancels++,save(){},close(){},restart:async()=>e.calls.restarts++,dispose:async()=>{}});
  e.api=createExtension(e.vscode,e.context,backend|| (async args=>({results:[row(args.document)],errors:[]})),e.service);
  e.status=(doc,state='complete',version=doc.version)=>e.service.emit('status',{uri:doc.uri.toString(),version,state,functions:[{range:{start:{line:0,character:0},end:{line:0,character:1}},status:state==='complete'?'proved':'running'}]});
  e.changeConfig=(name,uri)=>e.events.configuration({affectsConfiguration:(key,scope)=>key===name&&(!uri||scope?.toString()===uri.toString())});
  return e;
}
function row(doc){return{source:doc.uri.fsPath,sourceHash:createHash('sha256').update(doc.text).digest('hex'),contract:'C',function:'f',signature:'f()',status:'proved',range:{start:{line:0,character:0},end:{line:0,character:1}}};}
test('status stays with each open document and stale background events cannot overwrite it',async()=>{
  const e=fixture();try{
    const [a,b]=e.documents;e.status(a);e.status(b,'running');assert.match(e.bar.text,/complete/);
    e.vscode.window.activeTextEditor=e.editors[1];e.events.activeEditor(e.editors[1]);assert.match(e.bar.text,/sync/);
    a.version++;e.events.change({document:a,contentChanges:[{}]});e.status(a,'complete');e.status(a,'error',a.version-1);
    e.vscode.window.activeTextEditor=e.editors[0];e.events.activeEditor(e.editors[0]);assert.match(e.bar.text,/complete/);assert.equal(e.editors[0].decorations.get('proved').length,1);
    a.version++;e.events.activeEditor(e.editors[0]);assert.equal(e.bar.visible,false);assert.equal(e.editors[0].decorations.get('proved').length,0);
  }finally{await e.api.dispose();}
});
test('gutter resource toggles redraw immediately without losing other-file state or restarting proofs',async()=>{
  const e=fixture();try{
    e.documents.forEach(d=>e.status(d));e.documentConfigs.set(e.doc.uri.toString(),{displayGutterStatus:false});e.changeConfig('solidityLean.displayGutterStatus');
    assert.equal(e.editors[0].decorations.get('proved').length,0);assert.equal(e.editors[1].decorations.get('proved').length,1);assert.equal(e.calls.restarts,0);
    e.documentConfigs.clear();e.changeConfig('solidityLean.displayGutterStatus');assert.equal(e.editors[0].decorations.get('proved').length,1);
  }finally{await e.api.dispose();}
});
test('test visibility toggles preserve reports and other-file tests without backend work',async()=>{
  const e=fixture();try{
    for(const doc of e.documents)await e.api.verify(doc);
    e.documentConfigs.set(e.doc.uri.toString(),{displayVerificationAsTests:false});e.changeConfig('solidityLean.displayVerificationAsTests',e.doc.uri);
    assert.equal(e.controller.items.has(e.doc.uri.toString()),false);assert.equal(e.controller.items.has(e.documents[1].uri.toString()),true);assert.equal(e.api.reports.size,2);assert.equal(e.calls.restarts,0);
    await e.api.verify(e.doc);assert.equal(e.controller.items.has(e.doc.uri.toString()),false);
    e.documentConfigs.clear();e.changeConfig('solidityLean.displayVerificationAsTests');assert.equal(e.controller.items.size,2);
    e.doc.version++;e.events.change({document:e.doc,contentChanges:[{}]});e.changeConfig('solidityLean.displayVerificationAsTests');assert.equal(e.controller.items.has(e.doc.uri.toString()),false);
  }finally{await e.api.dispose();}
});
test('rapid server configuration changes reopen only the newest generation and disposal suppresses delayed opens',async()=>{
  const e=fixture(),finish=[];try{
    e.service.restart=()=>{e.calls.restarts++;return new Promise(resolve=>finish.push(resolve));};e.calls.opens=[];
    e.changeConfig('solidityLean.workers');e.changeConfig('solidityLean.automaticVerification');assert.equal(finish.length,2);
    finish[0]();await tick();assert.equal(e.calls.opens.length,0);finish[1]();await tick();assert.equal(e.calls.opens.length,2);
    e.changeConfig('solidityLean.workers');await e.api.dispose();finish[2]();await tick();assert.equal(e.calls.opens.length,2);
  }finally{await e.api.dispose();}
});
test('close and crash discard tests, diagnostics, gutter and status; late notifications cannot revive a closed file',async()=>{
  const e=fixture();try{
    await e.api.verify(e.doc);e.status(e.doc);e.doc.isClosed=true;e.events.close(e.doc);e.status(e.doc);
    assert.equal(e.bar.visible,false);assert.equal(e.controller.items.size,0);assert.equal(e.editors[0].decorations.get('proved').length,0);
    const b=e.documents[1];e.vscode.window.activeTextEditor=e.editors[1];await e.api.verify(b);e.status(b);e.service.emit('serverError',Error('server crashed'));
    assert.equal(e.api.reports.size,0);assert.equal(e.controller.items.size,0);assert.equal(e.bar.visible,false);assert.equal(e.editors[1].decorations.get('proved').length,0);
  }finally{await e.api.dispose();}
});
test('status action selection dispatches local commands; cancellation and disposed pickers do nothing',async()=>{
  const e=fixture();try{
    assert.equal(e.bar.command,'solidityLean.openStatusBarMenu');
    e.vscode.window.showQuickPick=async actions=>actions[1];await e.commands.get(e.bar.command)();assert(e.logs.includes('output shown'));
    e.vscode.window.showQuickPick=async()=>undefined;await e.commands.get(e.bar.command)();assert.equal(e.calls.restarts,0);
    let release;e.vscode.window.showQuickPick=actions=>new Promise(r=>{release=()=>r(actions[0]);});const pending=e.commands.get(e.bar.command)();await e.api.dispose();release();await pending;assert.equal(e.calls.restarts,0);assert.equal(e.service.listenerCount('status'),0);assert.equal(e.service.listenerCount('log'),0);
  }finally{await e.api.dispose();}
});

test('one client crash preserves healthy-client UI',async()=>{
  const e=fixture();try{
    for(const doc of e.documents){await e.api.verify(doc);e.status(doc);}
    e.api.reports.delete(e.doc.uri.toString());
    // Source-bound automatic reports from healthy documents stay visible after a scoped crash.
    e.service.emit('serverError',Object.assign(Error('one workspace crashed'),{uris:[e.doc.uri.toString()]}));
    const b=e.documents[1];assert.equal(e.api.reports.has(b.uri.toString()),true);assert.equal(e.controller.items.has(b.uri.toString()),true);assert.equal(e.editors[1].decorations.get('proved').length,1);assert.equal(e.controller.items.has(e.doc.uri.toString()),false);
  }finally{await e.api.dispose();}
});
test('late restart failures after disposal or a newer restart cannot append errors',async()=>{
  const e=fixture(),pending=[];try{
    e.service.restart=()=>new Promise((resolve,reject)=>pending.push({resolve,reject}));
    e.changeConfig('solidityLean.workers');e.changeConfig('solidityLean.workers');pending[1].resolve();await tick();pending[0].reject(Error('obsolete failure'));await tick();assert.equal(e.notices.length,0);
    e.changeConfig('solidityLean.workers');await e.api.dispose();pending[2].reject(Error('disposed failure'));await tick();assert.equal(e.notices.length,0);
  }finally{await e.api.dispose();}
});

test('LanguageServers scopes failures to owners and retires the failed client without touching its replacement',async()=>{
  const {LanguageServers}=require('../src/lsp-client.cjs'),root=require('node:path').resolve(__dirname,'../..');
  const fs=require('node:fs'),path=require('node:path'),temporary=fs.mkdtempSync(path.join(require('node:os').tmpdir(),'client-ownership-'));
  const executable=path.join(temporary,'protocol-fixture');
  fs.writeFileSync(executable,`#!${process.execPath}
if(process.argv.includes('--version')){console.log(process.version);process.exit(0);}
const {RpcPeer}=require(${JSON.stringify(require.resolve('../src/rpc.cjs'))});const peer=new RpcPeer(process.stdin,process.stdout);peer.onRequest('initialize',()=>({capabilities:{}}));peer.onRequest('shutdown',()=>null);peer.onNotification('exit',()=>process.exit(0));
`,{mode:0o700});
  const e=mock(),b={...e.doc,uri:{...e.doc.uri,fsPath:'/tmp/second-resource.sol'}};
  const servers=new LanguageServers(doc=>({backendPath:root,nodePath:executable,projectRoot:root,workers:doc===b?2:1,automaticVerification:'never'}));
  let c1,c2;try{
    c1=servers.client(e.doc);c2=servers.client(b);await Promise.all([c1.ready,c2.ready]);
    const errors=[];servers.on('serverError',error=>errors.push(error));
    c1.emit('serverError',Error('simulated transport failure'));
    assert.deepEqual(errors[0].uris,[e.doc.uri.toString()]);assert.equal(c1.disposed,true);assert.equal(servers.owners.get(b.uri.toString()),c2);assert.equal(servers.clients.size,1);
    c1.emit('status',{uri:e.doc.uri.toString(),version:1,state:'complete'});assert.equal(servers.owners.has(e.doc.uri.toString()),false);
  }finally{await Promise.all([servers.dispose(),c1?.dispose(),c2?.dispose()]);fs.rmSync(temporary,{recursive:true,force:true});}
});

test('a failed client cannot publish an in-flight result after scoped cleanup, even if backend ignores abort',async()=>{
  let finish,signal;const e=fixture(args=>{signal=args.signal;return new Promise(resolve=>{finish=()=>resolve({results:[row(args.document)],errors:[]});});});
  try{
    const pending=e.api.verify(e.doc);await tick();e.service.emit('serverError',Object.assign(Error('transport lost'),{uris:[e.doc.uri.toString()]}));
    assert.equal(signal.aborted,true);finish();assert.equal(await pending,null);assert.equal(e.api.reports.size,0);assert.equal(e.controller.items.size,0);
  }finally{await e.api.dispose();}
});

test('stale saves and cancelled operations cannot clear healthy verification state',async()=>{
  const e=fixture();try{
    await e.api.verify(e.doc);e.status(e.doc);
    for(const code of [-32800,-32801,'CANCELLED'])e.service.emit('serverError',Object.assign(Error('stale save'),{code}));
    assert.equal(e.api.reports.size,1);assert.equal(e.controller.items.size,1);assert.equal(e.bar.visible,true);assert.equal(e.notices.length,0);
    const {LanguageServers}=require('../src/lsp-client.cjs'),servers=new LanguageServers(()=>({})),errors=[];servers.on('serverError',error=>errors.push(error));
    servers.save({...e.doc,isClosed:true});await tick();assert.equal(errors.length,0);await servers.dispose();
  }finally{await e.api.dispose();}
});
test('service disposal waits for clients already removed from the active registry',async()=>{
  const {LanguageServers}=require('../src/lsp-client.cjs'),servers=new LanguageServers(()=>({}));let complete;
  const retired=new Promise(resolve=>{complete=resolve;});servers.retiring.add(retired);retired.then(()=>servers.retiring.delete(retired));
  let finished=false;const disposal=servers.dispose().then(()=>{finished=true;});await tick();assert.equal(finished,false);complete();await disposal;assert.equal(finished,true);
});

test('native diagnostic related information preserves foreign URI/range and rejects stale or closed-document batches',async()=>{
  const e=fixture();try{
    e.vscode.Location=class{constructor(uri,range){Object.assign(this,{uri,range});}};
    e.vscode.DiagnosticRelatedInformation=class{constructor(location,message){Object.assign(this,{location,message});}};
    const primary={start:{line:0,character:0},end:{line:0,character:1}},related={start:{line:2,character:3},end:{line:2,character:8}};
    const batch=version=>({uri:e.doc.uri.toString(),version,diagnostics:[{range:primary,severity:1,message:'duplicate',code:1686,relatedInformation:[{location:{uri:e.documents[1].uri.toString(),range:related},message:'other declaration'}]}]});
    e.service.emit('diagnostics',batch(1));const actual=e.diagnosticMap.get(e.doc.uri.toString())[0].relatedInformation[0];assert.equal(actual.location.uri.toString(),e.documents[1].uri.toString());assert.deepEqual(actual.location.range.start,related.start);assert.equal(actual.message,'other declaration');
    e.doc.version++;e.events.change({document:e.doc,contentChanges:[{}]});e.service.emit('diagnostics',batch(1));assert.equal(e.diagnosticMap.size,0);
    e.service.emit('diagnostics',batch(2));assert.equal(e.diagnosticMap.size,1);e.doc.isClosed=true;e.events.close(e.doc);e.service.emit('diagnostics',batch(2));assert.equal(e.diagnosticMap.size,0);
  }finally{await e.api.dispose();}
});
test('an ignored cancellation or configuration restart cannot produce a stale hover widget',async()=>{
  for(const change of ['cancel','edit','restart','dispose']){
    const e=fixture();let finish,abort;const token=new e.vscode.CancellationTokenSource();try{
      e.service.request=(_,doc,params,options)=>{abort=options.signal;return new Promise(resolve=>{finish=()=>resolve({contents:{value:'obsolete hover'},range:{start:{line:0,character:0},end:{line:0,character:1}}});});};
      const hover=e.events.hover.provideHover(e.doc,{line:0,character:0},token.token);
      if(change==='cancel')token.cancel();else if(change==='edit'){e.doc.version++;e.doc.text+=' newer';e.events.change({document:e.doc,contentChanges:[{}]});}else if(change==='restart')e.changeConfig('solidityLean.workers');else await e.api.dispose();
      finish();assert.equal(await hover,null);if(change==='cancel')assert.equal(abort.aborted,true);
    }finally{token.dispose();await e.api.dispose();}
  }
});

test('startup actions are explicit, scoped to declared settings and suppressed after restart/disposal',async()=>{
 for(const action of ['Change configuration','Node.js downloads','stale','disposed','closed','reopened']){
  const e=fixture();let choose;const actions=[],commands=[],links=[];
  e.vscode.window.showErrorMessage=(message,...items)=>{actions.push({message,items});return new Promise(r=>{choose=r;});};
  e.vscode.commands.executeCommand=async(...args)=>commands.push(args);e.vscode.env={openExternal:async uri=>links.push(uri.toString())};
  try{
   const error=Object.assign(Error('configured runtime cannot start'),{code:'STARTUP',setting:'nodePath',uris:[e.doc.uri.toString()]});
   e.service.emit('serverError',error);e.service.emit('serverError',error);assert.equal(actions.length,1);assert.deepEqual(actions[0].items,['Change configuration','Node.js downloads']);
   if(action==='stale')await e.commands.get('solidityLean.restartServer')();if(action==='disposed')await e.api.dispose();if(action==='closed'||action==='reopened'){e.doc.isClosed=true;e.events.close(e.doc);if(action==='reopened')e.events.open({...e.doc,isClosed:false});}
   choose(action==='stale'||action==='disposed'||action==='closed'||action==='reopened'?'Node.js downloads':action);await tick();
   const contextCommands=commands.filter(c=>c[0]==='setContext'),actionCommands=commands.filter(c=>c[0]!=='setContext');
   for(const call of contextCommands){assert.equal(call.length,3);assert.match(call[1],/^solidityLean\.verificationTrace\.(CanShow|CanHide|CanCopy)$/);assert.equal(typeof call[2],'boolean');}
   assert.equal(actionCommands.length,action==='Change configuration'?1:0);assert.equal(links.length,action==='Node.js downloads'?1:0);
   if(actionCommands.length)assert.match(actionCommands[0][1],/solidityLean.nodePath/);if(links.length)assert.equal(links[0],'https://nodejs.org/en/download');
  }finally{await e.api.dispose();}
 }
});
test('actual server identity status is per document, unknown stays unknown and subscriptions dispose',async()=>{
 const e=fixture();try{
  const identity=(doc,version)=>e.service.emit('identity',{uris:[doc.uri.toString()],serverInfo:{name:'Actual server',version},runtimeInfo:{version:'24.19.0'}});
  identity(e.doc,'0.5.5');identity(e.documents[1],'unknown');e.service.emit('serverError',Object.assign(Error('cancelled operation'),{code:'CANCELLED'}));assert.equal(e.versionBar.text,'0.5.5');assert.equal(e.versionBar.visible,true);
  e.vscode.window.activeTextEditor=e.editors[1];e.events.activeEditor();assert.equal(e.versionBar.text,'unknown');assert.match(e.versionBar.tooltip,/Actual server: unknown/);
  e.service.emit('serverError',Object.assign(Error('folder failure'),{uris:[e.doc.uri.toString()]}));assert.equal(e.versionBar.visible,true);
  e.documents[1].isClosed=true;e.events.close(e.documents[1]);assert.equal(e.versionBar.visible,false);
  await e.api.dispose();assert.equal(e.service.listenerCount('identity'),0);assert.equal(e.versionBar.visible,false);
 }finally{await e.api.dispose();}
});

test('configuration recovery targets affected folders and concurrent independent recoveries both reopen',async()=>{
 const e=fixture(),pending=[];try{
  e.calls.opens.length=0;e.service.restart=uris=>new Promise(resolve=>pending.push({uris,resolve}));
  for(const doc of e.documents)e.events.configuration({affectsConfiguration:(setting,uri)=>setting==='solidityLean.nodePath'&&uri.toString()===doc.uri.toString()});
  assert.deepEqual(pending.map(p=>p.uris.map(uri=>uri.toString())),e.documents.map(doc=>[doc.uri.toString()]));
  pending[1].resolve();await tick();pending[0].resolve();await tick();assert.deepEqual(new Set(e.calls.opens.map(doc=>doc.uri.toString())),new Set(e.documents.map(doc=>doc.uri.toString())));
 }finally{pending.forEach(p=>p.resolve());await e.api.dispose();}
});
test('production activation in an untrusted workspace creates no executable clients',async()=>{
 const e=fixture(),Module=require('node:module'),load=Module._load,context={subscriptions:[]};let api;
 try{
  e.vscode.workspace.isTrusted=false;Module._load=function(name,...args){return name==='vscode'?e.vscode:load.call(this,name,...args);};
  try{api=require('../src/extension.cjs').activate(context);}finally{Module._load=load;}
  await tick();assert.equal(api.service.clients.size,0);assert.equal(api.service.owners.size,0);assert.ok(e.notices.some(message=>/trusted workspace/.test(message)));
 }finally{Module._load=load;await api?.dispose();await e.api.dispose();}
});

test('an unrelated folder configuration change preserves a live startup action',async()=>{
 const e=fixture();let choose;const links=[];e.vscode.window.showErrorMessage=()=>new Promise(r=>{choose=r;});e.vscode.env={openExternal:async uri=>links.push(uri.toString())};
 try{
  e.service.emit('serverError',Object.assign(Error('folder B runtime missing'),{code:'STARTUP',setting:'nodePath',uris:[e.documents[1].uri.toString()]}));
  e.events.configuration({affectsConfiguration:(setting,uri)=>setting==='solidityLean.nodePath'&&uri.toString()===e.doc.uri.toString()});await tick();choose('Node.js downloads');await tick();assert.deepEqual(links,['https://nodejs.org/en/download']);
 }finally{await e.api.dispose();}
});

function mixedStatus(e){
 const names=['good','direct','failed','active','queue','old','unsupported','unknown','unverified','cancelled','skipped'];e.doc.text='contract C {\n'+names.map(name=>'  function '+name+'() external {}').join('\n')+'\n}';
 const statuses=['proved','proved','error','running','queued','stale','unsupported','pending','ready','cancelled','skipped'];
 return {uri:e.doc.uri.toString(),version:e.doc.version,sourceHash:createHash('sha256').update(e.doc.text).digest('hex'),state:'running',functions:names.map((name,i)=>({name:'C.'+name+'()',range:{start:{line:i+1,character:11},end:{line:i+1,character:11+name.length}},status:statuses[i],...(name==='direct'?{verification:'direct'}:{})}))};
}
test('mixed status summarizes actual completion, active names and all incomplete categories',async()=>{
 const e=fixture();try{e.service.emit('status',mixedStatus(e));assert.match(e.bar.text,/Completed 3\/11/);assert.match(e.bar.text,/verifying C.active/);for(const word of ['unknown','unsupported','stale','cancelled','unverified','direct'])assert.match(e.bar.tooltip,new RegExp(word));}finally{await e.api.dispose();}
});
test('a status source hash mismatch cannot overwrite legitimate current state',async()=>{
 const e=fixture();try{e.status(e.doc);const before=e.bar.text;e.service.emit('status',{uri:e.doc.uri.toString(),version:e.doc.version,sourceHash:'0'.repeat(64),state:'error',functions:[]});assert.equal(e.bar.text,before);}finally{await e.api.dispose();}
});
test('a picker owned by another active document cannot restart the current servers',async()=>{
 const e=fixture();let release;try{e.status(e.doc);e.vscode.window.showQuickPick=actions=>new Promise(resolve=>{release=()=>resolve(actions[0]);});const pick=e.commands.get(e.bar.command)();e.vscode.window.activeTextEditor=e.editors[1];e.events.activeEditor();release();await pick;assert.equal(e.calls.restarts,0);}finally{await e.api.dispose();}
});

test('an ownerless picker cannot act on a newly active document',async()=>{
 const e=fixture();let release;try{e.vscode.window.activeTextEditor=undefined;e.vscode.window.showQuickPick=actions=>new Promise(resolve=>{release=()=>resolve(actions[0]);});const pending=e.commands.get(e.bar.command)();e.vscode.window.activeTextEditor=e.editors[0];e.events.activeEditor();release();await pending;assert.equal(e.calls.restarts,0);}finally{await e.api.dispose();}
});

test('pending picker rejects edits, close/reopen, config, active ABA and disposal but accepts current status delivery',async()=>{
 for(const action of ['edit','close-reopen','config','active-ABA','dispose','status']){
  const e=fixture();let release;try{e.status(e.doc);e.vscode.window.showQuickPick=items=>new Promise(resolve=>{release=()=>resolve(items[1]);});const pending=e.commands.get(e.bar.command)();
   if(action==='edit'){e.doc.version++;e.doc.text+=' ';e.events.change({document:e.doc,contentChanges:[{}]});}
   if(action==='close-reopen'){e.doc.isClosed=true;e.events.close(e.doc);const reopened={...e.doc,isClosed:false};e.documents[0]=reopened;e.editors[0].document=reopened;e.events.open(reopened);e.status(reopened);}
   if(action==='config')e.changeConfig('solidityLean.workers',e.doc.uri);
   if(action==='active-ABA'){e.vscode.window.activeTextEditor=e.editors[1];e.events.activeEditor();e.vscode.window.activeTextEditor=e.editors[0];e.events.activeEditor();}
   if(action==='dispose')await e.api.dispose();if(action==='status')e.status(e.doc,'running');release();await pending;assert.equal(e.logs.includes('output shown'),action==='status');
  }finally{await e.api.dispose();}
 }
});
test('issue draft uses current real identity metadata and never attaches source automatically',async()=>{
 const e=fixture();let release;const links=[];e.vscode.env={openExternal:async uri=>links.push(uri.toString())};
 try{e.doc.text='contract PrivateSourceNeverAttach {}';e.status(e.doc);e.vscode.window.showQuickPick=items=>new Promise(resolve=>{release=()=>resolve(items.find(item=>item.reportIssue));});const pending=e.commands.get(e.bar.command)();
  e.service.emit('identity',{uris:[e.doc.uri.toString()],serverInfo:{name:'Actual server',version:'0.5.5'},runtimeInfo:{version:'24.19.0'}});release();await pending;assert.equal(links.length,1);const url=new URL(links[0]);assert.equal(url.origin,'https://github.com');assert.equal(url.pathname,'/SolidiKeY/solidity-lean/issues/new');const body=url.searchParams.get('body');assert.match(body,/Actual server 0.5.5/);assert.match(body,/Node.js: 24.19.0/);assert.doesNotMatch(body,/PrivateSourceNeverAttach|contract.sol/);
 }finally{await e.api.dispose();}
});
test('ordinary output preserves unrelated-folder picker ownership',async()=>{
 const e=fixture();let release,seen;try{e.status(e.doc,'running');e.vscode.window.showQuickPick=items=>{seen=items;return new Promise(resolve=>{release=()=>resolve(items.find(item=>item.label==='Show verification output'));});};const pending=e.commands.get(e.bar.command)();assert.ok(seen.some(item=>item.label==='Show verification output'));e.changeConfig('solidityLean.workers',e.documents[1].uri);release();await pending;assert.ok(e.logs.includes('output shown'));}finally{await e.api.dispose();}
});

for(const phase of ['running','error','complete'])test('H80 proof-help uses project documentation only for a qualified current '+phase+' state (injected editor)',async()=>{
 const e=fixture(),opened=[];const original=e.vscode.commands.executeCommand;e.vscode.commands.executeCommand=async(command,...args)=>{if(command==='vscode.open'){opened.push(args[0].fsPath);return;}return original(command,...args);};try{e.status(e.doc,phase);let offered;e.vscode.window.showQuickPick=async actions=>(offered=actions,actions.find(item=>item.proofHelp==='index'));await e.commands.get('solidityLean.openStatusBarMenu')();assert.equal(offered.some(item=>item.proofHelp),phase!=='complete');assert.deepEqual(opened,phase==='complete'?[]:[require('node:fs').realpathSync(require('node:path').resolve(__dirname,'../../docs/README.md'))]);assert.equal(e.calls.restarts,0);}finally{await e.api.dispose();}
});
for(const barrier of ['edit','close','switch','configuration','dispose','trust'])test('proof-help selection rejects '+barrier+' owner changes (injected editor)',async()=>{
 const e=fixture(),opened=[];let release;const original=e.vscode.commands.executeCommand;e.vscode.commands.executeCommand=async(command,...args)=>{if(command==='vscode.open'){opened.push(args[0]);return;}return original(command,...args);};try{e.status(e.doc,'running');e.vscode.window.showQuickPick=actions=>new Promise(resolve=>{release=()=>resolve(actions.find(item=>item.proofHelp));});const pending=e.commands.get('solidityLean.openStatusBarMenu')();if(barrier==='edit'){e.doc.version++;e.doc.text+=' ';e.events.change({document:e.doc,contentChanges:[{}]});}if(barrier==='close'){e.doc.isClosed=true;e.events.close(e.doc);}if(barrier==='switch'){e.vscode.window.activeTextEditor=e.editors[1];e.events.activeEditor(e.editors[1]);}if(barrier==='configuration')e.changeConfig('solidityLean.backendPath',e.doc.uri);if(barrier==='dispose')await e.api.dispose();if(barrier==='trust')e.vscode.workspace.isTrusted=false;release();await pending;assert.deepEqual(opened,[]);}finally{await e.api.dispose();}
});

test('proof guide and documentation index are both selectable destinations (injected editor)',async()=>{
 const e=fixture(),opened=[];const original=e.vscode.commands.executeCommand;e.vscode.commands.executeCommand=async(command,...args)=>{if(command==='vscode.open'){opened.push(args[0].fsPath);return;}return original(command,...args);};try{e.status(e.doc,'running');for(const target of ['guide','index']){e.vscode.window.showQuickPick=async actions=>actions.find(item=>item.proofHelp===target);await e.commands.get('solidityLean.openStatusBarMenu')();}assert.deepEqual(opened,['calculus.md','README.md'].map(file=>require('node:fs').realpathSync(require('node:path').resolve(__dirname,'../../docs',file))));}finally{await e.api.dispose();}
});
test('missing project documentation reports a useful configuration error instead of raw ENOENT (injected editor)',async()=>{
 const e=fixture(),fs=require('node:fs'),directory=fs.mkdtempSync(require('node:path').join(require('node:os').tmpdir(),'proof-docs-')),opened=[];const original=e.vscode.commands.executeCommand;e.vscode.commands.executeCommand=async(command,...args)=>{if(command==='vscode.open'){opened.push(args);return;}return original(command,...args);};try{e.config.backendPath=directory;e.status(e.doc,'running');e.vscode.window.showQuickPick=async actions=>actions.find(item=>item.proofHelp==='guide');await e.commands.get('solidityLean.openStatusBarMenu')();assert.deepEqual(opened,[]);assert.match(e.notices.join('\n'),/Set solidityLean.backendPath.*docs\/README.md.*docs\/calculus.md/);assert.doesNotMatch(e.notices.join('\n'),/ENOENT|realpath/);}finally{await e.api.dispose();fs.rmSync(directory,{recursive:true,force:true});}
});
