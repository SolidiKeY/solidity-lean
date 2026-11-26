'use strict';
const {test}=require('node:test');
const assert=require('node:assert/strict');
const {mkdtempSync,writeFileSync,rmSync}=require('node:fs');
const {tmpdir}=require('node:os');
const {join}=require('node:path');
const {createHandler,inspect,register}=require('../src/server-features/show-obligation.cjs');
const {activate,COMMAND}=require('../src/features/show-obligation.cjs');
const range={start:{line:0,character:9},end:{line:0,character:10}},position=range.start;
function backendFixture(t){
  const dir=mkdtempSync(join(tmpdir(),'obligation-test-')),path=join(dir,'C.sol'),text='function f() {}';writeFileSync(path,text);t.after(()=>rmSync(dir,{recursive:true,force:true}));
  const node={nodeType:'FunctionDefinition',name:'f',id:7},parent={nodeType:'ContractDefinition',name:'C'};
  const doc={uri:'file://'+path,path,text,version:1,index:{nodes:[node],nameRange:()=>range,parents:new Map([[node,parent]])}};
  const service={root:dir,docs:new Map([[doc.uri,doc]]),requests:new Map(),generation:1,settings:{},current:(d,v,g)=>d===doc&&d.version===v&&g===1,analyze:async()=>{},verify:async()=>({results:[{sourceId:7,contract:'C',signature:'f()'}]})};
  return {service,doc,params:{textDocument:{uri:doc.uri,version:1},position}};
}
test('server uses exact declaration ID and contract, returning printer output',async t=>{
  const {service,params}=backendFixture(t);let request;
  const result=await createHandler(service,async r=>(request=r,'dl{ ⊢ true }'))(params,1);
  assert.equal(result.text,'dl{ ⊢ true }');assert.equal(request.declarationId,7);assert.equal(request.contract,'C');assert.equal(service.requests.size,0);
});
test('server ignores function bodies and rejects stale versions',async t=>{
  const {service,params}=backendFixture(t);const handler=createHandler(service,()=>assert.fail('backend called'));
  assert.equal(await handler({...params,position:{line:0,character:13}},1),null);
  await assert.rejects(handler({...params,textDocument:{...params.textDocument,version:0}},2),{code:-32801});
});
test('server cancellation reaches injected backend and cannot publish',async t=>{
  const {service,params}=backendFixture(t);
  await assert.rejects(createHandler(service,async r=>{service.requests.get(5).abort();assert.equal(r.signal.aborted,true);return 'dl{ true }';})(params,5),{code:-32800});assert.equal(service.requests.size,0);
});
test('server rejects edits while backend runs and refuses unsaved source',async t=>{
  const {service,doc,params}=backendFixture(t);
  await assert.rejects(createHandler(service,async()=>{doc.text+=' ';return 'dl{ true }';})(params,1),{code:-32801});
  await assert.rejects(createHandler(service,()=>assert.fail('unsaved backend called'))(params,2),{code:-32010});
});
test('server backend errors propagate and release request',async t=>{
  const {service,params}=backendFixture(t);
  await assert.rejects(createHandler(service,async()=>{throw new Error('printer failed');})(params,1),/printer failed/);assert.equal(service.requests.size,0);
});
function clientFixture(t,request=async()=>({text:'dl{ true }',range,languageId:'lean',label:'C.f()'})){
  let hover,provider,command,shown,language;const errors=[];
  const disposable=()=>({dispose(){}}),uri={scheme:'file',fsPath:'/C.sol',toString:()=> 'file:///C.sol'};
  const doc={uri,version:1,languageId:'solidity',getText:()=> 'function f() {}',isClosed:false};
  class MarkdownString{constructor(){this.value='';}appendCodeblock(text,lang){this.code=text;this.language=lang;}appendMarkdown(text){this.value+=text;}}
  const vscode={Uri:{parse:s=>({toString:()=>s})},MarkdownString,Range:class{constructor(...args){this.args=args;}},Hover:class{constructor(contents,range){this.contents=contents;this.range=range;}},
    workspace:{registerTextDocumentContentProvider(s,p){provider=p;return disposable();},async openTextDocument(uri){return {uri,getText:()=>provider.provideTextDocumentContent(uri)};}},
    languages:{registerHoverProvider(s,p){hover=p;return disposable();},async setTextDocumentLanguage(d,l){language=l;return d;}},
    window:{activeTextEditor:{document:doc,selection:{active:position}},async showTextDocument(d){shown=d;},showErrorMessage:e=>errors.push(e)}};
  const feature=activate({}, {vscode,client:{request},registerCommand(name,handler){assert.equal(name,COMMAND);command=handler;return disposable();}});t.after(()=>feature.dispose());
  return {doc,errors,get hover(){return hover;},get command(){return command;},get shown(){return shown;},get language(){return language;}};
}
test('hover truncates safely and links to complete read-only Lean document',async t=>{
  const text='dl{ '+ 'x'.repeat(6000)+' }',f=clientFixture(t,async()=>({text,range,languageId:'lean',label:'C.f()'}));
  const hover=await f.hover.provideHover(f.doc,position);assert.match(hover.contents.code,/truncated/);assert.equal(hover.contents.language,'lean');assert.deepEqual(hover.contents.isTrusted,{enabledCommands:[COMMAND]});
  const args=JSON.parse(decodeURIComponent(hover.contents.value.match(/\?([^)]*)/)[1]));await f.command(...args);assert.equal(f.shown.getText(),text);assert.equal(f.language,'lean');
});
test('command requests the active function',async t=>{const f=clientFixture(t);await f.command();assert.equal(f.shown.getText(),'dl{ true }');assert.equal(f.language,'lean');});
test('client cancellation discards late output',async t=>{
  let cancel;const token={onCancellationRequested(fn){cancel=fn;return {dispose(){}};}};
  const f=clientFixture(t,async(m,d,p,o)=>{cancel();assert.equal(o.signal.aborted,true);return {text:'dl{ true }',range,languageId:'lean',label:'f'};});
  assert.equal(await f.hover.provideHover(f.doc,position,token),null);assert.deepEqual(f.errors,[]);
});
test('client stale buffer and stale hover link cannot open output',async t=>{
  const f=clientFixture(t);const hover=await f.hover.provideHover(f.doc,position);const args=JSON.parse(decodeURIComponent(hover.contents.value.match(/\?([^)]*)/)[1]));f.doc.version++;await f.command(...args);assert.equal(f.shown,undefined);
  const g=clientFixture(t,async()=>{g.doc.version++;return {text:'dl{ true }',range,languageId:'lean',label:'f'};});assert.equal(await g.hover.provideHover(g.doc,position),null);
});
test('client backend errors are visible',async t=>{const f=clientFixture(t,async()=>{throw new Error('backend unavailable');});await f.command();assert.match(f.errors[0],/backend unavailable/);});

test('production reports the missing exact sequent printer honestly',async()=>{
  await assert.rejects(inspect(),{code:-32004,message:/no entry point.*spec!.*dl/});
});
test('full-document links requery after dependency or backend changes',async t=>{
  for(const change of ['dependency','configuration']){
    let text='dl{ old }',calls=0;
    const f=clientFixture(t,async()=>{calls++;return {text,range,languageId:'lean',label:'C.f'};});
    const hover=await f.hover.provideHover(f.doc,position);
    const args=JSON.parse(decodeURIComponent(hover.contents.value.match(/\?([^)]*)/)[1]));
    text='dl{ '+change+' }';await f.command(...args);
    assert.equal(calls,2);assert.equal(f.shown.getText(),text);
  }
});
test('server rejects configuration replacement during printing',async t=>{
  const {service,params}=backendFixture(t);
  await assert.rejects(createHandler(service,async()=>{service.settings={};return 'dl{ true }';})(params,1),{code:-32801});
});
test('hover inspection leaves verification state alone',async t=>{
  const {service,params,doc}=backendFixture(t);service.verify=()=>assert.fail('inspection must not publish a listing over verification');
  doc.report={results:['proved']};const report=doc.report;const abort=new AbortController();doc.verifyAbort=abort;
  await createHandler(service,async()=> 'dl{ true }')(params,1);
  assert.equal(doc.report,report);assert.equal(abort.signal.aborted,false);
});

test('registry uses the documented injected printer',async t=>{
  const {service,params}=backendFixture(t);let handler;
  service.testing={printObligation:async()=> 'dl{ ⊢ true }'};
  register({service,onRequest(method,h){assert.equal(method,'solidityLean/showObligation');handler=h;}});
  assert.equal((await handler(params,1)).text,'dl{ ⊢ true }');
});
test('server cancellation settles without waiting for an uncooperative injected printer',async t=>{
  const {service,params}=backendFixture(t);let started;
  const ready=new Promise(resolve=>{started=resolve;});
  const pending=createHandler(service,()=>{started();return new Promise(()=>{});})(params,1);
  await ready;service.requests.get(1).abort();
  await assert.rejects(pending,{code:-32800});assert.equal(service.requests.size,0);
});
test('real project snapshot rejects imported buffer changes during printing',async t=>{
  const {service,params,doc}=backendFixture(t),projects=require('../src/project.cjs');
  const imported={path:join(service.root,'D.sol'),text:'contract D {}',version:1};writeFileSync(imported.path,imported.text);
  const project=projects.snapshot(doc.path,doc.text,{},[doc]);
  project.files['D.sol']={...imported,hash:projects.hash(imported.text)};
  doc.compiled={project};service.projectDocuments=()=>[doc,imported];
  await assert.rejects(createHandler(service,async()=>{imported.text+=' ';return 'dl{ true }';})(params,1),{code:-32801});
});
