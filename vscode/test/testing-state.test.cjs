/* VS Code Testing boundary regressions; injected backend results are not kernel proof evidence. */
'use strict';
const {test}=require('node:test'),assert=require('node:assert/strict'),{createHash}=require('node:crypto'),{createExtension}=require('../src/extension.cjs'),{mock,leaves}=require('./mock.cjs');
const tick=()=>new Promise(r=>setImmediate(r)),idle={isCancellationRequested:false,onCancellationRequested:()=>({dispose(){}})};
const row=(doc,name='f')=>({source:doc.uri.fsPath,sourceHash:createHash('sha256').update(doc.text).digest('hex'),contract:'C',function:name,signature:name+'()',status:'proved'});
function setup(){
  const e=mock();e.calls=[];e.backend=async(args,doc)=>({results:args.function?[row(doc,args.function.split('(')[0])]:[row(doc,'f'),row(doc,'g')],errors:[]});
  e.docs=new Map([[e.doc.uri.toString(),e.doc]]);e.vscode.workspace.openTextDocument=async uri=>e.docs.get(uri.toString());
  e.api=createExtension(e.vscode,e.context,args=>{e.calls.push(args);return e.backend(args,e.docs.get(require('node:url').pathToFileURL(args.source).href));});
  e.items=()=>{const file=e.controller.items.get(e.doc.uri.toString());return{file,leaves:leaves(file)};};return e;
}
test('overlapping includes queue and execute each exact leaf once; file exclusions also block directly included leaves',async()=>{
  const e=setup();try{
    await e.api.verify(e.doc,{listing:true});e.calls=[];const {file,leaves}=e.items();
    await e.controller.run({include:[file,leaves[0],file,leaves[0]]},idle);
    assert.deepEqual(e.calls.map(c=>c.function),['f()','g()']);assert.deepEqual(e.runs[0].calls.map(c=>c[0]),['enqueued','enqueued','started','passed','started','passed','end']);
    e.calls=[];await e.controller.run({include:[leaves[0]],exclude:[file]},idle);assert.equal(e.calls.length,0);assert.deepEqual(e.runs[1].calls.map(c=>c[0]),['end']);
  }finally{await e.api.dispose();}
});
test('native TestRun cancellation aborts current work and skips queued siblings even when backend ignores abort',async()=>{
  const e=setup();let finish,signal;try{
    await e.api.verify(e.doc,{listing:true});e.calls=[];e.backend=(args,doc)=>{signal=args.signal;return new Promise(resolve=>{finish=()=>resolve({results:[row(doc,'f')],errors:[]});});};
    const pending=e.controller.run({include:[e.items().file]},idle);await tick();e.runs[0].cancel();assert.equal(signal.aborted,true);finish();await pending;
    assert.equal(e.calls.length,1);assert.deepEqual(e.runs[0].calls.map(c=>c[0]),['enqueued','enqueued','started','skipped','skipped','end']);
  }finally{await e.api.dispose();}
});
for(const cause of ['profile','run','command','dispose'])test(`${cause} cancellation during opening cannot start a backend or queued sibling`,async()=>{
  const e=setup(),profile=new e.vscode.CancellationTokenSource();let open;try{
    await e.api.verify(e.doc,{listing:true});e.calls=[];e.vscode.workspace.openTextDocument=()=>new Promise(resolve=>{open=()=>resolve(e.doc);});
    const pending=e.controller.run({include:[e.items().file]},profile.token);await tick();
    if(cause==='profile')profile.cancel();else if(cause==='run')e.runs[0].cancel();else if(cause==='command')e.commands.get('solidityLean.cancel')();else await e.api.dispose();
    open();await pending;assert.equal(e.calls.length,0);assert.deepEqual(e.runs[0].calls.map(c=>c[0]),['enqueued','enqueued','skipped','skipped','end']);
  }finally{profile.dispose();await e.api.dispose();}
});
test('edits and visibility toggles invalidate queued test identity without manufacturing a pass',async()=>{
  for(const change of ['edit','visibility']){
    const e=setup();let open;try{
      await e.api.verify(e.doc,{listing:true});e.calls=[];e.vscode.workspace.openTextDocument=()=>new Promise(resolve=>{open=()=>resolve(e.doc);});
      const pending=e.controller.run({include:[e.items().file]},idle);await tick();
      if(change==='edit'){e.doc.version++;e.doc.text+=' // newer';e.events.change({document:e.doc,contentChanges:[{}]});}
      else{e.config.displayVerificationAsTests=false;e.events.configuration({affectsConfiguration:k=>k==='solidityLean.displayVerificationAsTests'});}
      open();await pending;assert.equal(e.calls.length,0);assert.equal(e.runs[0].calls.filter(c=>c[0]==='passed').length,0);assert.equal(e.runs[0].calls.at(-1)[0],'end');
    }finally{await e.api.dispose();}
  }
});
test('multi-file exclusions preserve the included file and reject a wrongly opened document with identical contents',async()=>{
  const e=setup();try{
    const b={...e.doc,uri:{...e.doc.uri,fsPath:'/tmp/second.sol'}};e.docs.set(b.uri.toString(),b);await e.api.verify(e.doc,{listing:true});await e.api.verify(b,{listing:true});
    const a=e.items(),fileB=e.controller.items.get(b.uri.toString());e.calls=[];
    await e.controller.run({include:[a.file,fileB,...a.leaves],exclude:[a.file]},idle);assert.deepEqual(e.calls.map(c=>c.source),[b.uri.fsPath,b.uri.fsPath]);
    e.vscode.workspace.openTextDocument=async()=>e.doc;e.calls=[];await e.controller.run({include:[fileB]},idle);assert.equal(e.calls.length,0);assert.equal(e.runs[1].calls.filter(c=>c[0]==='passed').length,0);
  }finally{await e.api.dispose();}
});
test('outdated/cancelled backend responses end the run as skipped, never errored or passed',async()=>{
  for(const code of [-32800,-32801,'CANCELLED']){
    const e=setup();try{await e.api.verify(e.doc,{listing:true});e.backend=async()=>{throw Object.assign(Error('obsolete'),{code});};await e.controller.run({include:[e.items().leaves[0]]},idle);assert.deepEqual(e.runs[0].calls.map(c=>c[0]),['enqueued','started','skipped','end']);}finally{await e.api.dispose();}
  }
});
test('overlapping runs cannot turn a superseded same-function result into a pass',async()=>{
  const e=setup(),jobs=[];try{
    await e.api.verify(e.doc,{listing:true});const leaf=e.items().leaves[0];e.backend=(args,doc)=>new Promise(resolve=>jobs.push({args,finish:()=>resolve({results:[row(doc)],errors:[]})}));
    const first=e.controller.run({include:[leaf]},idle);await tick();const second=e.controller.run({include:[leaf]},idle);await tick();assert.equal(jobs[0].args.signal.aborted,true);
    jobs[1].finish();await second;jobs[0].finish();await first;assert.equal(e.runs[0].calls.filter(c=>c[0]==='passed').length,0);assert.equal(e.runs[1].calls.filter(c=>c[0]==='passed').length,1);for(const run of e.runs)assert.equal(run.calls.filter(c=>c[0]==='end').length,1);
  }finally{await e.api.dispose();}
});
