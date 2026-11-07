/* Display migration and provider scheduling tests, with injected compilation/verification boundaries. No kernel proofs. */
'use strict';
const {test}=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),os=require('node:os'),{pathToFileURL}=require('node:url'),{createHash}=require('node:crypto');
const {migrateRange,migrateDiagnostics,incrementalChange}=require('../src/diagnostic-state.cjs'),language=require('../src/language-services.cjs'),{SolidityService}=require('../src/lsp-server.cjs');
const hash=s=>createHash('sha256').update(s).digest('hex'),deferred=()=>{let resolve;const promise=new Promise(r=>{resolve=r;});return{promise,resolve};};
const range=(a,b,c,d)=>({start:{line:a,character:b},end:{line:c,character:d}});
const text='contract C { function f() public pure returns(uint) { return 1; } }';
function compiled(source){const start=source.indexOf('function'),name=source.indexOf('f()');return{fixture:{header:{sourceSha256:hash(source)}},rawAst:{nodeType:'SourceUnit',id:0,src:`0:${Buffer.byteLength(source)}:0`,nodes:[{nodeType:'FunctionDefinition',id:1,name:'f',src:`${start}:${source.length-start-2}:0`,nameLocation:`${name}:1:0`,typeDescriptions:{typeString:'function () returns (uint256)'}}]},diagnostics:[]};}
function setup(overrides={}){
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'diagnostic-state-')),events=[];
  const service=new SolidityService({notify:(method,params)=>events.push({method,params:structuredClone(params)})},root,{automaticVerification:'never'},
    {fingerprint:()=> 'fixed-generation',analyze:async doc=>compiled(doc.text),verify:async task=>({results:[{source:task.source,sourceHash:hash(task.text),contract:'C',function:'f',signature:'f()',status:'pending',range:range(0,13,0,60)}],errors:[]}),...overrides});
  const uri=pathToFileURL(path.join(root,'C.sol')).href;const doc=service.open({uri,version:1,text});clearTimeout(doc.timer);
  return{root,events,service,uri,doc,dispose(){service.dispose();fs.rmSync(root,{recursive:true,force:true});}};
}
test('incremental sync roundtrips edits without splitting CRLF or surrogate boundaries',()=>{
  for(const [before,after] of [['a😀b\r\nc','a😃b\r\nc'],['a\r\nb','a\nb'],['a\r\nb','a\r\nxb'],['😀','😀x'],['abc',''],['','😀\r\nx'],['same','same']]){
    const change=incrementalChange(before,after);assert.equal(language.applyChanges(before,[change]),after);
    for(const p of [change.range.start,change.range.end]){const n=language.offset(before,p);assert(!(before[n-1]==='\r'&&before[n]==='\n'));}
  }
});
test('diagnostics and same-document related ranges move through UTF16/CRLF edits; foreign ranges stay fixed',()=>{
  const old='😀\r\nabc\r\ndef',uri='file:///C.sol',other='file:///Other.sol';
  const item={range:range(2,0,2,3),message:'failed',severity:1,relatedInformation:[{location:{uri,range:range(1,0,1,3)},message:'same'},{location:{uri:other,range:range(1,0,1,3)},message:'foreign'}]};
  const rows=migrateDiagnostics([item],uri,uri,old,[{range:range(0,0,0,0),text:'\r\n'},{range:range(3,0,3,0),text:'xx'}]);
  assert.deepEqual(rows[0].range,range(3,2,3,5));assert.deepEqual(rows[0].relatedInformation[0].location.range,range(2,0,2,3));assert.deepEqual(rows[0].relatedInformation[1].location.range,range(1,0,1,3));assert.equal(rows[0].message,'Outdated: failed');assert.equal(rows[0].severity,2);assert.equal(item.message,'failed');
});
test('deleted/crossed ranges disappear, contained edits resize, and full replacements cannot retain old locations',()=>{
  assert.equal(migrateRange(range(0,2,0,5),'01234567',{range:range(0,2,0,5),text:''}),null);
  assert.equal(migrateRange(range(0,2,0,5),'01234567',{range:range(0,4,0,7),text:'x'}),null);
  assert.deepEqual(migrateRange(range(0,1,0,7),'01234567',{range:range(0,3,0,4),text:'xx'}),range(0,1,0,8));
  assert.deepEqual(migrateDiagnostics([{range:range(0,1,0,3),message:'old',severity:2}],'u','u','0123',[{text:'new'}]),[]);
});
test('server preserves only outdated display diagnostics on incremental edits, then replaces them on fresh proof',async()=>{
  const s=setup();try{
    await s.service.verify(s.uri);assert.equal(s.doc.report.results[0].status,'pending');
    s.service.change({textDocument:{uri:s.uri,version:2},contentChanges:[{range:range(0,0,0,0),text:'\n'}]});clearTimeout(s.doc.timer);
    assert.equal(s.doc.report,null);let last=s.events.filter(e=>e.method==='textDocument/publishDiagnostics').at(-1).params;
    assert.equal(last.version,2);assert.match(last.diagnostics[0].message,/^Outdated: /);assert.equal(last.diagnostics[0].range.start.line,1);
    await s.service.analyze(s.doc);last=s.events.filter(e=>e.method==='textDocument/publishDiagnostics').at(-1).params;assert.match(last.diagnostics[0].message,/^Outdated: /);
    s.service.publish(s.doc,{results:[],errors:[]});last=s.events.filter(e=>e.method==='textDocument/publishDiagnostics').at(-1).params;assert.deepEqual(last.diagnostics,[]);
  }finally{s.dispose();}
});
test('reset and close/reopen never restore migrated display state',async()=>{
  const s=setup();try{await s.service.verify(s.uri);s.service.change({textDocument:{uri:s.uri,version:2},contentChanges:[{range:range(0,0,0,0),text:'\n'}]});clearTimeout(s.doc.timer);
    s.service.reset();assert.deepEqual(s.doc.verificationDiagnostics,[]);assert.deepEqual(s.events.filter(e=>e.method==='textDocument/publishDiagnostics').at(-1).params.diagnostics,[]);
    s.service.close(s.uri);const reopened=s.service.open({uri:s.uri,version:1,text});clearTimeout(reopened.timer);assert.equal(reopened.report,undefined);assert.equal(reopened.verificationDiagnostics,undefined);
  }finally{s.dispose();}
});
test('compiler secondary locations retain individual file text, UTF8 offsets, messages and order',()=>{
  const s=setup();try{
    const foreign=path.join(s.root,'Lib.sol');s.doc.projectSnapshot={files:{'C.sol':{path:s.doc.path,text:s.doc.text},'Lib.sol':{path:foreign,text:'// 😀\nxyz'}}};
    const rows=s.service.compilerDiagnostics(s.doc,[{severity:'error',message:'duplicate',errorCode:1686,sourceLocation:{file:'C.sol',start:13,end:20},secondarySourceLocations:[{file:'Lib.sol',start:8,end:11,message:'other declaration'},{file:'C.sol',start:0,end:8,message:'same file'},{file:'unknown',start:0,end:1,message:'unmapped'}]}]);
    assert.equal(rows[0].relatedInformation.length,2);assert.deepEqual(rows[0].relatedInformation[0],{location:{uri:pathToFileURL(foreign).href,range:range(1,0,1,3)},message:'other declaration'});assert.equal(rows[0].relatedInformation[1].location.uri,s.uri);
  }finally{s.dispose();}
});
test('hover returns a declaration while verification remains pending',async()=>{
  const gate=deferred(),started=deferred();let done=false;
  const s=setup({verify:async()=>{started.resolve();await gate.promise;return{results:[],errors:[]};}});
  try{
    const proof=s.service.verify(s.uri).then(v=>{done=true;return v;});await started.promise;
    let timer;const hover=await Promise.race([s.service.language('textDocument/hover',{textDocument:{uri:s.uri,version:1},position:{line:0,character:text.indexOf('f()')}}),new Promise((_,reject)=>{timer=setTimeout(()=>reject(Error('hover waited for verifier')),500);})]).finally(()=>clearTimeout(timer));
    assert.match(hover.contents.value,/function/);assert.equal(done,false);assert.equal(s.doc.report,undefined);gate.resolve();await proof;
  }finally{gate.resolve();s.dispose();}
});
test('cancelled hover detaches from shared analysis while a sibling request still succeeds',async()=>{
  const gate=deferred(),started=deferred();const s=setup({analyze:async doc=>{const value=compiled(doc.text);started.resolve();await gate.promise;return value;}});
  const abort=new AbortController();try{
    const params={textDocument:{uri:s.uri,version:1},position:{line:0,character:text.indexOf('f()')}};
    const first=s.service.language('textDocument/hover',params,abort.signal),rejected=assert.rejects(first,e=>e.code===-32800);await started.promise;
    const other=s.service.language('textDocument/hover',params);abort.abort();await rejected;assert.equal(s.doc.analysisAbort.signal.aborted,false);
    gate.resolve();assert.match((await other).contents.value,/function/);
  }finally{gate.resolve();s.dispose();}
});
test('a close/reopen with the same version cannot revive a pending old hover',async()=>{
  const gate=deferred(),started=deferred();const s=setup({analyze:async doc=>{const value=compiled(doc.text);started.resolve();await gate.promise;return value;}});
  try{const hover=s.service.language('textDocument/hover',{textDocument:{uri:s.uri,version:1},position:{line:0,character:text.indexOf('f()')}}),rejected=assert.rejects(hover,e=>[-32800,-32801].includes(e.code));await started.promise;s.service.close(s.uri);const next=s.service.open({uri:s.uri,version:1,text});clearTimeout(next.timer);gate.resolve();await rejected;assert.equal(next.index,undefined);
  }finally{gate.resolve();s.dispose();}
});

test('selected verification replaces its own migrated diagnostics without discarding unverified siblings',async()=>{
  const s=setup();try{
    const result=name=>({source:s.doc.path,sourceHash:hash(s.doc.text),contract:'C',function:name,signature:name+'()',status:'pending',range:range(0,name==='f'?13:40,0,name==='f'?20:50)});
    s.service.publish(s.doc,{results:[result('f'),result('g')],errors:[]});
    s.service.change({textDocument:{uri:s.uri,version:2},contentChanges:[{range:range(0,0,0,0),text:'\n'}]});clearTimeout(s.doc.timer);
    s.service.publish(s.doc,{results:[{...result('f'),status:'proved'}],errors:[]},false,{contract:'C',function:'f()'});
    assert.equal(s.doc.verificationDiagnostics.length,1);assert.equal(s.doc.verificationDiagnostics[0].data.solidityLean.function,'g()');assert.match(s.doc.verificationDiagnostics[0].message,/^Outdated: /);
  }finally{s.dispose();}
});
test('dependency changes discovered during analysis discard proof display even without a file-watcher notification',async()=>{
  const s=setup();try{
    await s.service.verify(s.uri);const dependency=path.join(s.root,'Dependency.sol');fs.writeFileSync(dependency,'new dependency');
    s.doc.compiled.project={files:{dependency:{path:dependency,text:'old dependency',hash:hash('old dependency')}}};
    s.service.testing.analyze=async()=>{throw Error('current compiler failure');};await assert.rejects(s.service.analyze(s.doc,{refresh:false}),/compiler failure/);
    assert.equal(s.doc.report,null);assert.deepEqual(s.doc.verificationDiagnostics,[]);
    const latest=s.events.filter(e=>e.method==='textDocument/publishDiagnostics').at(-1).params.diagnostics;assert.equal(latest.length,1);assert.equal(latest[0].message,'current compiler failure');
  }finally{s.dispose();}
});

test('a provider response from a retired or reassigned language client cannot be returned as current',async()=>{
  const {LanguageClient,LanguageServers}=require('../src/lsp-client.cjs'),gate=deferred();
  const client=Object.create(LanguageClient.prototype),doc={uri:{toString:()=> 'file:///C.sol'},version:1,isClosed:false,getText:()=>text};
  Object.assign(client,{disposed:false,sync:async()=>{},peer:{request:()=>gate.promise}});
  const pending=client.request('textDocument/hover',doc),rejected=assert.rejects(pending,e=>e.code===-32801);await Promise.resolve();client.disposed=true;gate.resolve({contents:{value:'old'}});await rejected;
  const gate2=deferred(),servers=new LanguageServers(()=>({})),owner={request:()=>gate2.promise};servers.client=()=>owner;servers.owners.set(doc.uri.toString(),owner);
  const request=servers.request('textDocument/hover',doc),obsolete=assert.rejects(request,e=>e.code===-32801);await Promise.resolve();servers.owners.set(doc.uri.toString(),{});gate2.resolve({contents:{value:'old owner'}});await obsolete;
});

test('failed reference startup cannot leave a stale passed migration artifact',()=>{
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'reference-migration-life-'));
  try{
    const out=path.join(root,'out');fs.mkdirSync(out);fs.writeFileSync(path.join(out,'migration.json'),JSON.stringify({status:'passed',run:'old'}));
    const executable=path.join(root,'exits-before-init');fs.writeFileSync(executable,'#!'+process.execPath+String.fromCharCode(10)+'process.exit(9);'+String.fromCharCode(10),{mode:0o700});
    const result=require('node:child_process').spawnSync(process.execPath,[path.resolve(__dirname,'../parity/lifecycle-trace.cjs'),executable,out,'--migration'],{encoding:'utf8',timeout:5000});
    assert.equal(result.status,1);assert.equal(result.error,undefined);assert.equal(fs.existsSync(path.join(out,'migration.json')),false);
  }finally{fs.rmSync(root,{recursive:true,force:true});}
});

test('an invalid old display range cannot desynchronize an otherwise valid edit',()=>{
  const s=setup();try{
    s.doc.verificationDiagnostics=[{range:range(99,0,100,0),severity:1,message:'invalid old location'}];
    s.service.change({textDocument:{uri:s.uri,version:2},contentChanges:[{range:range(0,0,0,0),text:'\n'}]});clearTimeout(s.doc.timer);
    assert.equal(s.doc.version,2);assert.equal(s.doc.text,'\n'+text);assert.deepEqual(s.doc.verificationDiagnostics,[]);
    assert.throws(()=>s.service.change({textDocument:{uri:s.uri,version:3},contentChanges:[{range:range(999,0,999,0),text:'invalid new edit'}]}));assert.equal(s.doc.version,2);
  }finally{s.dispose();}
});
