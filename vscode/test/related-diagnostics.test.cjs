'use strict';
const {test}=require('node:test'),assert=require('node:assert/strict'),{createHash}=require('node:crypto'),path=require('node:path'),{pathToFileURL}=require('node:url');
const {source,textFor,phases,diagnosticSnapshot,wireSnapshot,errors,textForInput,phaseEdit}=require('../parity/related-diagnostics.cjs');
const digest=s=>createHash('sha256').update(s).digest('hex');
const {fixture,config}=require('./related-diagnostics-fixture.cjs');
test('diagnostic getters survive JSON and later API mutation without using toJSON',()=>{
 let line=1,text='other';const point={get line(){return line;},get character(){return 2;},toJSON(){throw Error('must not invoke');}},value={get severity(){return 0;},get message(){return'duplicate';},get range(){return{start:point,end:point};},get code(){return{value:1686,target:{toString:()=> 'https://example.invalid/code'}};},get relatedInformation(){return[{get message(){return text;},location:{uri:{toString:()=> 'file:///owned.sol'},range:{start:point,end:point}}}];}};
 const snapshot=diagnosticSnapshot([value]);line=7;text='mutated';const roundtrip=JSON.parse(JSON.stringify(snapshot));assert.equal(roundtrip[0].relatedInformation[0].message,'other');assert.deepEqual(roundtrip[0].range.start,{line:1,character:2});assert.equal(roundtrip[0].code.target,'https://example.invalid/code');
});
test('invalid getter positions, severity and oversized data refuse rather than disappear',()=>{
 const base={severity:0,message:'m',range:{start:{line:0,character:0},end:{line:0,character:1}}};for(const changed of [{...base,severity:9},{...base,message:'x'.repeat(65537)},{...base,range:{start:{line:-1,character:0},end:{line:0,character:1}}},{...base,relatedInformation:new Array(257).fill({})}])assert.throws(()=>diagnosticSnapshot([changed]));
 assert.throws(()=>diagnosticSnapshot([{...base,get relatedInformation(){throw Error('getter failed');}}]),/getter failed/);
});
test('injected complete API/wire fixture survives JSON only as partial evidence',()=>assert.deepEqual(errors(JSON.parse(JSON.stringify(fixture())),config),[]));
const mutations={
 'same-byte/version reopened lifetime':o=>{const b=o.steps[0].before,owner=o.steps[0].process;o.protocol.splice(2,0,{...owner,direction:'client',message:{method:'textDocument/didClose',params:{textDocument:{uri:b.uri}}}},{...owner,direction:'client',message:{method:'textDocument/didOpen',params:{textDocument:{uri:b.uri,version:b.version,text:source,synchronizationId:'new-sync'}}}});for(const row of o.steps){if(row.publicationIndex>=2)row.publicationIndex+=2;row.wireEnd+=2;}for(let n=4;n<o.protocol.length;n++){const m=o.protocol[n].message;if(m.method==='textDocument/publishDiagnostics')m.params.synchronizationId='new-sync';}},
 'future process birth':o=>o.events.unshift({kind:'unrelated',data:{}}),
 'exact deadline':o=>o.steps[1].elapsedMs=60000,
 'wrong target':o=>o.target='dafny',
 'wrong head':o=>o.sourceHead='b'.repeat(40),
 'wrong URI':o=>o.steps[1].before.uri='file:///foreign.sol',
 'wrong version':o=>o.steps[1].before.version=1,
 'wrong source hash':o=>o.steps[1].before.sourceHash='c'.repeat(64),
 'changed session':o=>o.steps[1].before.session='new',
 'owner changed during capture':o=>o.steps[0].after.closed=true,
 'late capture':o=>o.steps[1].elapsedMs=60001,
 'missing phase':o=>o.steps.splice(1,1),
 'missing related API location':o=>o.steps[0].diagnostics[0].relatedInformation=[],
 'foreign related wire and API':o=>{o.steps[0].diagnostics[0].relatedInformation[0].location.uri='file:///foreign.sol';o.protocol[1].message.params.diagnostics[0].relatedInformation[0].location.uri='file:///foreign.sol';},
 'missing diagnostic publication':o=>o.protocol[1].message.method='unrelated',
 'foreign server birth':o=>o.events[0].data.birth='999',
 'foreign wire document owner':o=>o.protocol[0].processSession='foreign',
 'late wire document change':o=>{o.protocol.push({...o.steps[2].process,direction:'client',message:{method:'textDocument/didChange',params:{textDocument:{uri:o.steps[2].before.uri,version:4},contentChanges:[{text:'changed'}]}}});o.steps[2].wireEnd=o.protocol.length;},
 'retired server':o=>{o.events.push({kind:'process.close',data:{...o.steps[0].process}});o.steps[0].eventEnd=2;},
 'wrong executable script':o=>o.events[0].data.args=['/other/lsp-server.cjs'],
 'missing synchronization':o=>delete o.protocol[0].message.params.textDocument.synchronizationId,
 'wrong synchronization':o=>o.protocol[1].message.params.synchronizationId='other',
 'missing ready barrier':o=>o.protocol.at(-1).message.method='unrelated',
 'unrelated ready barrier':o=>o.protocol.at(-1).message.params.uri='file:///foreign.sol',
 'proof side effect':o=>o.protocol.push({direction:'client',message:{method:'solidityLean/verify'}}),
 'failed capture':o=>o.status='failed',
 'reporting failure':o=>o.reportingError='disk',
 'missing API field':o=>delete o.steps[0].diagnostics[0].range
};
for(const [name,change]of Object.entries(mutations))test('injected receipt refuses '+name,()=>{const o=fixture();change(o);assert.ok(errors(o,config).length);});
test('aggregate target binding and rejection retain the failed observation',()=>{
 const {validateHostResult}=require('../parity/core.cjs'),observation=fixture(),outer={schemaVersion:1,runId:config.runId,target:'local',status:'passed-with-gaps',scenarios:[{id:'native-related-diagnostics',status:'partial',observation}],checks:[]};
 assert.ok(!validateHostResult(outer,config).error);observation.steps[0].diagnostics=[];const rejected=validateHostResult(outer,config);assert.ok(rejected.error);assert.equal(rejected.rejectedResult,outer);assert.equal(rejected.rejectedResult.scenarios[0].observation.steps.length,3);
});
test('existing launcher requires bounded serial local recording',()=>{
 const {parse}=require('../parity/run.cjs'),args=['--suite','related-diagnostics','--targets','local','--workers','1','--cache','none','--trials','1','--warmups','0','--obligations','1'];assert.equal(parse(args).suite,'related-diagnostics');for(const extra of [['--targets','dafny'],['--trace','off'],['--operation-timeout-ms','60001'],['--workers','1,2'],['--memory-max-mib','8192'],['--memory-reserve-mib','12000']])assert.throws(()=>parse([...args,...extra]));
});

test('phase deadline refuses synchronous late reads and late promise completion without timer race',async()=>{
 const {withinDeadline,elapsedBeforeDeadline}=require('../parity/related-diagnostics.cjs');let clock=0,called=false,cleared=0;
 const options={now:()=>clock,setTimer:()=>1,clearTimer:()=>cleared++};
 await assert.rejects(withinDeadline(()=>{called=true;clock=10;return 'late';},10,options),e=>e.code==='TIMEOUT');assert.equal(called,true);assert.equal(cleared,1);
 called=false;await assert.rejects(withinDeadline(()=>{called=true;},10,options),e=>e.code==='TIMEOUT');assert.equal(called,false);
 assert.throws(()=>elapsedBeforeDeadline(0,10,()=>10),e=>e.code==='TIMEOUT');assert.equal(elapsedBeforeDeadline(0,10,()=>9),9);
});

test('public EOL companion is separate: exact CRLF bytes and trusted input identity required',()=>{
 const c={...config,diagnosticInput:'public-eol-v1'},value=fixture(c.diagnosticInput);
 assert.deepEqual(errors(value,c),[]);assert.ok(errors(value,config).length);assert.ok(errors(fixture(),c).length);
 assert.equal(textFor('shifted'),'// 😀 shift\r\n'+source);assert.ok(textForInput('shifted','public-eol-v1').split('\r\n').length>3);
});
test('public EOL edit uses the actual dedicated API; default path keeps the original replace operation',()=>{
 const doc={uri:'uri',getText:()=>source,positionAt:n=>n},edits=[];
 class Edit{set(...args){edits.push(['set',...args]);}replace(...args){edits.push(['replace',...args]);}}
 const api={WorkspaceEdit:Edit,Range:class{constructor(a,b){this.start=a;this.end=b;}},EndOfLine:{LF:1,CRLF:2},TextEdit:{replace:(range,text)=>({range,text}),setEndOfLine:eol=>({eol})}};
 phaseEdit(api,doc,textForInput('shifted','public-eol-v1'),'shifted','public-eol-v1');assert.equal(edits[0][0],'set');assert.equal(edits[0][2][1].eol,2);
 phaseEdit(api,doc,textFor('shifted'),'shifted');assert.equal(edits[1][0],'replace');
});

// Controlled transport schedule, not native execution or proof evidence.
function reopenedPublications(){
 const value=fixture('public-eol-v1'),before={...value.steps.at(-1).before,session:'fresh-document'},owner=value.steps.at(-1).process,protocol=structuredClone(value.protocol),text=textForInput('fixed','public-eol-v1');
 protocol.push({...owner,direction:'client',message:{method:'textDocument/didClose',params:{textDocument:{uri:before.uri}}}});
 const openIndex=protocol.length;protocol.push({...owner,direction:'client',message:{method:'textDocument/didOpen',params:{textDocument:{...before,text,synchronizationId:'fresh-sync'}}}});
 const staleIndex=protocol.length;protocol.push({...owner,direction:'server',message:{method:'textDocument/publishDiagnostics',params:{uri:before.uri,version:before.version,sourceHash:before.sourceHash,synchronizationId:'sync-epoch',diagnostics:[]}}});
 protocol.push({...owner,direction:'server',message:{method:'solidityLean/status',params:{uri:before.uri,version:before.version,sourceHash:before.sourceHash,synchronizationId:'sync-epoch',state:'ready'}}});
 const stale=structuredClone(protocol);protocol.push({...owner,direction:'server',message:{method:'solidityLean/status',params:{uri:before.uri,version:before.version,sourceHash:before.sourceHash,synchronizationId:'fresh-sync',state:'ready'}}});const freshIndex=protocol.length;protocol.push({...owner,direction:'server',message:{method:'textDocument/publishDiagnostics',params:{uri:before.uri,version:before.version,sourceHash:before.sourceHash,synchronizationId:'fresh-sync',diagnostics:[]}}});
 return{value,before,owner,text,openIndex,staleIndex,freshIndex,stale,fresh:protocol};
}
test('collector defers stale same-byte/version publication until actual fresh synchronization appears',async()=>{
 const {captureDiagnosticStep,assertDiagnosticStep}=require('../parity/related-diagnostics.cjs'),{performance}=require('node:perf_hooks'),f=reopenedPublications(),row={phase:'reopened-fixed',status:'started'},start=performance.now();let reads=0;
 await captureDiagnosticStep({vscode:{languages:{getDiagnostics:()=>[]}},doc:{uri:{}},binding:()=>({...f.before}),wire:()=>++reads===1?f.stale:f.fresh,events:f.value.events,deadline:start+1000,start,row,kind:'fixed'});
 assert.equal(row.publicationIndex,f.freshIndex);assert.ok(reads>=2);assert.equal(row.publicationAttempts[0].publicationIndex,f.staleIndex);assert.equal(row.publicationAttempts[0].reason,'synchronization-mismatch');assert.equal(row.publicationAttempts[0].currentSynchronizationId,'fresh-sync');assert.equal(row.publicationAttempts[0].publicationSynchronizationId,'sync-epoch');assert.equal(row.status,'observed');assertDiagnosticStep(row,config,f.fresh,f.value.events,{uri:f.before.uri,session:f.before.session,text:f.text,kind:'fixed',process:f.owner});
});
test('stale-only transport exhausts original deadline and retains failed candidates without an observed row',async()=>{
 const {captureDiagnosticStep}=require('../parity/related-diagnostics.cjs'),{performance}=require('node:perf_hooks'),f=reopenedPublications(),row={phase:'reopened-fixed',status:'started'},start=performance.now();
 await assert.rejects(captureDiagnosticStep({vscode:{languages:{getDiagnostics:()=>[]}},doc:{uri:{}},binding:()=>({...f.before}),wire:()=>f.stale,events:f.value.events,deadline:start+35,start,row,kind:'fixed'}),e=>e.code==='TIMEOUT');assert.notEqual(row.status,'observed');assert.ok(row.publicationAttempts.length);assert.ok(row.publicationAttempts.every(a=>a.reason==='synchronization-mismatch'));
});
test('polling does not fall back to older success when latest candidate has foreign ownership',()=>{
 const {currentPublication}=require('../parity/related-diagnostics.cjs'),f=reopenedPublications();f.fresh.push({...f.fresh.at(-1),processSession:'foreign',pid:999,birth:'999'});assert.equal(currentPublication(f.fresh,f.before).reason,'no-current-owned-open');
});
for(const [name,change,reason]of [
 ['missing synchronization',f=>delete f.fresh[f.openIndex].message.params.textDocument.synchronizationId,'synchronization-mismatch'],
 ['wrong source',f=>f.fresh[f.openIndex].message.params.textDocument.text+='x','wire-source-version-mismatch'],
 ['wrong version',f=>f.fresh[f.openIndex].message.params.textDocument.version++,'wire-source-version-mismatch'],
 ['current document closed',f=>f.fresh.push({...f.owner,direction:'client',message:{method:'textDocument/didClose',params:{textDocument:{uri:f.before.uri}}}}),'no-current-owned-open'],
 ['publication predates reopened document',f=>f.fresh.push({...f.owner,direction:'client',message:{method:'textDocument/didOpen',params:{textDocument:{...f.before,text:f.text,synchronizationId:'fresh-sync'}}}}),'publication-before-current-open']
])test('polling refuses '+name,()=>{const f=reopenedPublications();change(f);assert.equal(require('../parity/related-diagnostics.cjs').currentPublication(f.fresh,f.before).reason,reason);});

test('fixed receipt refuses old ready from before current open or another synchronization',()=>{
 const {captureDiagnosticStep,assertDiagnosticStep,currentPublication,currentReadyIndex}=require('../parity/related-diagnostics.cjs'),f=reopenedPublications(),selection=currentPublication(f.fresh,f.before),ready=f.fresh.findIndex(r=>r.message?.params?.state==='ready'&&r.message.params.synchronizationId==='fresh-sync');assert.ok(ready>f.openIndex);assert.equal(currentReadyIndex(f.fresh,f.before,f.owner,f.openIndex,'fresh-sync'),ready);
 const row={phase:'reopened-fixed',status:'observed',before:f.before,after:{...f.before},diagnostics:[],process:f.owner,publicationIndex:f.freshIndex,wireEnd:f.fresh.length,eventEnd:f.value.events.length,elapsedMs:1};assert.doesNotThrow(()=>assertDiagnosticStep(row,config,f.fresh,f.value.events,{uri:f.before.uri,session:f.before.session,text:f.text,kind:'fixed',process:f.owner}));
 f.fresh[ready].message.params.synchronizationId='sync-epoch';assert.equal(currentReadyIndex(f.fresh,f.before,f.owner,f.openIndex,'fresh-sync'),-1);assert.throws(()=>assertDiagnosticStep(row,config,f.fresh,f.value.events,{uri:f.before.uri,session:f.before.session,text:f.text,kind:'fixed',process:f.owner}),/current compiler-ready/);
});
test('latest current cancelled status cannot reuse an earlier ready barrier',()=>{const {currentReadyIndex}=require('../parity/related-diagnostics.cjs'),f=reopenedPublications();f.fresh.push({...f.owner,direction:'server',message:{method:'solidityLean/status',params:{uri:f.before.uri,version:f.before.version,sourceHash:f.before.sourceHash,synchronizationId:'fresh-sync',state:'cancelled'}}});assert.equal(currentReadyIndex(f.fresh,f.before,f.owner,f.openIndex,'fresh-sync'),-1);});
test('collector waits within same deadline for current ready, not old ready',async()=>{
 const {captureDiagnosticStep}=require('../parity/related-diagnostics.cjs'),{performance}=require('node:perf_hooks'),f=reopenedPublications(),row={phase:'reopened-fixed',status:'started'},start=performance.now(),old=structuredClone(f.fresh);for(const r of old)if(r.message?.method==='solidityLean/status')r.message.params.synchronizationId='sync-epoch';let reads=0;
 await captureDiagnosticStep({vscode:{languages:{getDiagnostics:()=>[]}},doc:{uri:{}},binding:()=>({...f.before}),wire:()=>++reads===1?old:f.fresh,events:f.value.events,deadline:start+1000,start,row,kind:'fixed'});assert.ok(reads>=2);assert.equal(row.status,'observed');assert.equal(row.publicationAttempts[0].reason,'no-current-ready');
});
