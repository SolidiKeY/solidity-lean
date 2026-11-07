// Guards proof-help synchronization, focus-before-Enter, source ownership and PID-birth retirement.
// Injected protocol/renderer/resource boundaries; these fixtures certify no proof or image.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),os=require('node:os'),vm=require('node:vm'),{createHash}=require('node:crypto');
const {sourceBinding,sameSource,assertCertifiedFailureObservation,menuObservation}=require('../parity/proof-help.cjs'),{resourceState,resourcesAllowed}=require('../parity/resource-state.cjs');
const text='contract Parity { function f0() external {} }',hash=createHash('sha256').update(text).digest('hex'),doc={uri:{toString:()=> 'file:///tmp/Parity.sol'},version:1,isClosed:false,getText:()=>text},wire={version:1,textHash:hash,openIndex:4,synchronizationId:'injected-sync-1'};
const binding=()=>sourceBinding(doc,'injected-session',wire);
function report(){return {errors:[],backend:{kind:'lean',leanServerPid:1234},results:[{contract:'Parity',function:'f0',signature:'f0()',source:'/tmp/Parity.sol',sourceHash:hash,status:'refuted',sourceId:2,range:{start:{line:0,character:18},end:{line:0,character:43}},counterexample:{certified:true,goalKind:'fmlValid',certificateDeclaration:'SolTests.Parity.f0.refuted',axioms:['propext']}}]};}
test('proof-help observation rejects direct, unsupported, wrong-source and unaudited claimed results (injected)',()=>{
 assertCertifiedFailureObservation(report(),binding(),'/tmp/Parity.sol');
 for(const mutate of [r=>r.results[0].verification='direct',r=>r.results[0].status='unsupported',r=>r.results[0].sourceHash='0'.repeat(64),r=>r.results[0].counterexample.certified=false,r=>r.results[0].counterexample.axioms.push('sorryAx'),r=>r.backend.leanServerPid=undefined,r=>r.backend.kind='generated-c-wasm']){const row=report();mutate(row);assert.throws(()=>assertCertifiedFailureObservation(row,binding(),'/tmp/Parity.sol'));}
});
test('native source observation is tied to URI/version/text/session and protocol open lifetime (injected)',()=>{
 const owner=binding();for(const change of [{session:'reopened'},{version:2},{uri:'file:///other.sol'},{textHash:'0'.repeat(64)},{protocolOpenIndex:5},{synchronizationId:'reopened'}])assert.throws(()=>sameSource(owner,{...owner,...change}));
 assert.throws(()=>sourceBinding({...doc,isClosed:true},'session',wire));assert.throws(()=>sourceBinding({...doc,version:'1'},'session',{...wire,version:'1'}));assert.throws(()=>sourceBinding(doc,'session',{...wire,textHash:'0'.repeat(64)}));
});
test('proof-help menu requires both exact actions on the current focused source (injected)',()=>{
 const value={activeUri:doc.uri.toString(),inputFocused:true,items:[{label:'Help with a proof'},{label:'Proof documentation index'}]};menuObservation(value,binding(),'Help with a proof');
 for(const change of [{activeUri:'file:///other.sol'},{inputFocused:false},{items:[value.items[0]]},{items:[...value.items,value.items[0]]}])assert.throws(()=>menuObservation({...value,...change},binding(),'Help with a proof'));
});
test('native admission rejects swap, missing resource fields, exceeded RSS and insufficient OS reserve (injected)',()=>{
 const state=resourceState('MemAvailable: 12582912 kB\nSwapTotal: 0 kB\n'.replaceAll('\\n','\n'));
 assert.equal(resourcesAllowed(state),true);assert.equal(resourcesAllowed({...state,availableBytes:state.availableBytes-1024}),false);assert.equal(resourcesAllowed({...state,swapTotalBytes:1024}),false);assert.equal(resourcesAllowed(state,{},4096*1024**2+1),false);assert.throws(()=>resourceState('MemAvailable: 12582912 kB\n'));assert.equal(resourcesAllowed({}),false);
});
test('proof-help suite cannot admit parallel workers, multiple obligations or missing wire recording',()=>{
 const {parse}=require('../parity/run.cjs'),base=['--suite','proof-help','--targets','local','--workers','1','--obligations','1'];assert.equal(parse(base).suite,'proof-help');for(const extra of [['--workers','2'],['--obligations','2'],['--trace','off'],['--targets','dafny']])assert.throws(()=>parse([...base,...extra]));
});
test('native picker dispatches Enter only after one exact focused action, with preserved inspection (injected CDP)',async()=>{
 const directory=fs.mkdtempSync(path.join(os.tmpdir(),'proof-help-renderer-')),calls=[];let filtered=false;
 const observed=()=>({activeUri:doc.uri.toString(),inputFocused:true,items:(filtered?['Help with a proof']:['Help with a proof','Proof documentation index']).map(label=>({label}))});
 const client={async request(method,params){calls.push({method,params});if(method==='Runtime.evaluate'){new vm.Script(params.expression);return {result:{value:params.expression.startsWith('JSON.stringify')?JSON.stringify({title:'Injected',editorCount:1,notifications:[],visibleHovers:[],bodyText:'Injected UI'}):observed()}};}if(method==='Input.insertText'){filtered=true;return{};}if(method==='Accessibility.getFullAXTree')return {nodes:[{}]};if(method==='DOMSnapshot.captureSnapshot')return {documents:[{}]};if(method==='Page.captureScreenshot')return {data:Buffer.from([137,80,78,71,13,10,26,10,0]).toString('base64')};return{};}};
 try{const value=await require('../parity/renderer.cjs').captureProofHelp(client,directory,{action:'menu',binding:binding(),label:'Help with a proof'});assert.equal(value.captured,true);assert.equal(calls.filter(row=>row.method==='Input.dispatchKeyEvent').length,2);assert.equal(JSON.parse(fs.readFileSync(path.join(directory,'proof-help-rendered.json'))).items.length,2);}finally{fs.rmSync(directory,{recursive:true,force:true});}
});

test('sampled survivor termination cannot lose birth ownership across the final recheck (injected stale identity, real owned child)',{skip:process.platform!=='linux',timeout:5000},async()=>{
 const {spawn}=require('node:child_process'),{once}=require('node:events'),{processState}=require('../src/process-state.cjs'),{terminateTree}=require('../src/backend.cjs');
 const child=spawn(process.execPath,['-e','setInterval(()=>{},1000)'],{stdio:'ignore'}),closed=once(child,'close');await once(child,'spawn');const actual=processState(child.pid),stale={pid:child.pid,start:'0'};
 try{const result=require('../parity/run.cjs').retireSampledSurvivors({survivors:()=>[stale]});assert.deepEqual(result.terminated,[]);assert.equal(result.refused.length,1,'termination itself must reject the stale birth, not rely on a prior sampler check');assert.match(result.refused[0].error,/identity changed/);assert.equal(processState(child.pid)?.birth,actual.birth);assert.notEqual(processState(child.pid)?.state,'Z');}
 finally{if(processState(child.pid)?.birth===actual.birth)terminateTree({pid:child.pid,processBirth:actual.birth});await closed;}
});

test('actual producer shape without invented phase field establishes only current exact failed-function status (injected)',()=>{
 const {currentFailureStatus}=require('../parity/proof-help.cjs'),owner=binding(),row=report().results[0],status={uri:owner.uri,version:owner.version,sourceHash:owner.textHash,synchronizationId:owner.synchronizationId,state:'complete',progressScope:'functions',functions:[{name:'Parity.f0()',range:row.range,status:'refuted'}]};
 assert.equal(Object.hasOwn(status,'phase'),false);assert.equal(currentFailureStatus(status,owner,row),true);
 for(const change of [{version:2},{synchronizationId:'retired'},{sourceHash:'0'.repeat(64)},{state:'queued'},{progressScope:'document'},{functions:[{...status.functions[0],status:'unsupported'}]},{functions:[{...status.functions[0],name:'Other.f0()'}]}])assert.equal(currentFailureStatus({...status,...change},owner,row),false);
});

test('wire binding waits for real document synchronization and rejects edit/close during startup (injected)',async()=>{
 const {synchronizedBinding}=require('../parity/proof-help.cjs');for(const change of ['none','edit','close']){const current={...doc},begun={};let release,read=false;const opened=new Promise(resolve=>{release=resolve;}),pending=synchronizedBinding({open:()=>opened},current,()=>{read=true;return binding();});const rejected=change==='none'?null:assert.rejects(pending,/source changed/);await new Promise(setImmediate);assert.equal(read,false);if(change==='edit')current.version++;if(change==='close')current.isClosed=true;release();if(rejected){await rejected;assert.equal(read,false);}else{await pending;assert.equal(read,true);}}
});

test('next native trial is not admitted after cleanup identity refusal even when the reused PID is no longer a survivor (injected)',()=>{
 const {assertRetirementComplete}=require('../parity/run.cjs');let admitted=false;const previous={error:'identity changed',resources:{cleanup:{remaining:[],identityRefusals:[{pid:1234,birth:'old',error:'identity changed'}]}}};assert.throws(()=>{assertRetirementComplete(previous);admitted=true;},/identity/);assert.equal(admitted,false);
 assert.doesNotThrow(()=>assertRetirementComplete({resources:{cleanup:{remaining:[],identityRefusals:[]}}}));assert.throws(()=>assertRetirementComplete({resources:{cleanup:{remaining:[]}}}),/ownership evidence/);
});

// Original hover-before-verification obligation: actual ordering, never fake proof authority.
function injectedHoverWire(){
 const {workload}=require('../parity/workloads.cjs'),source=workload('local',1,true),expected=require('../parity/proof-help.cjs').proofHoverExpected(source),owner={...binding(),textHash:createHash('sha256').update(source).digest('hex'),protocolOpenIndex:0},value={contents:{kind:'markdown',value:expected.text},range:expected.range},proof=report();proof.results[0].sourceHash=owner.textHash;
 const client=message=>({direction:'client',message}),server=message=>({direction:'server',message});
 const rows=[client({method:'textDocument/didOpen',params:{textDocument:{uri:owner.uri,version:owner.version,text:source,synchronizationId:owner.synchronizationId}}}),client({id:1,method:'solidityLean/verify',params:{textDocument:{uri:owner.uri,version:owner.version},options:{certify:true,counterexamples:true}}}),client({id:2,method:'textDocument/hover',params:{textDocument:{uri:owner.uri,version:owner.version},position:expected.position}}),server({id:2,result:value}),server({method:'solidityLean/status',params:{...owner,sourceHash:owner.textHash,state:'complete'}}),server({id:1,result:proof})];return{rows,owner,expected,value,proof};
}
test('hover expectation binds exact shared source documentation/signature/UTF16 token range (injected)',()=>{
 const a=injectedHoverWire(),check=require('../parity/workloads.cjs').assertHoverObservation;check(a.value,a.expected);
 assert.match(a.expected.text,/function f0\(\) public pure returns \(uint256 result\)/);for(const change of [{contents:{kind:'markdown',value:'nonempty wrong hover'}},{range:{start:a.expected.range.start,end:{...a.expected.range.end,character:a.expected.range.end.character+1}}}])assert.throws(()=>check({...a.value,...change},a.expected));
});
test('hover wire observation requires exact source lifetime, order and actual provider/report payload (injected)',()=>{
 const {verificationHoverOrder}=require('../parity/proof-help.cjs'),accept=a=>verificationHoverOrder(a.rows,1,a.owner,a.expected.position,a.value,a.proof);accept(injectedHoverWire());
 for(const mutate of [a=>a.rows[2].message.params.textDocument.version++,a=>a.rows[0].message.params.textDocument.synchronizationId='other',a=>a.rows.splice(3,0,a.rows.splice(4,1)[0]),a=>a.rows[3].message={id:2,error:{code:-32800}},a=>a.rows[3].message.result={...a.value,contents:{kind:'markdown',value:'wrong wire'}},a=>a.rows[5].message.result={...a.proof,errors:['wrong']},a=>a.rows.splice(2,0,{direction:'client',message:{method:'textDocument/didChange',params:{textDocument:{uri:a.owner.uri,version:2},contentChanges:[{text:'changed'}]}}}),a=>a.rows.push(a.rows[2])]){const a=injectedHoverWire();mutate(a);assert.throws(()=>accept(a));}
});

function injectedPopup(){
 const a=injectedHoverWire(),metadata={binding:a.owner,expectedHover:a.expected,status:{uri:a.owner.uri,version:a.owner.version,sourceHash:a.owner.textHash,synchronizationId:a.owner.synchronizationId,state:'running',functions:[{range:a.expected.range,status:'ready'}]}};
 return {a,metadata,shown:{at:10,activeUri:a.owner.uri,widgets:[{fullyVisible:true,rows:require('../parity/proof-help.cjs').popupExpected(metadata)}]}};
}
test('popup checks exact documentation, code and authentic compiler-ready decoration, never nonempty text (injected)',()=>{
 const {popupObservation,popupExpected}=require('../parity/proof-help.cjs');let f=injectedPopup();popupObservation(f.shown,f.metadata);popupObservation({...f.shown,widgets:[]},f.metadata,true);
 for(const mutate of [f=>f.shown.activeUri='file:///other',f=>f.shown.widgets[0].fullyVisible=false,f=>f.shown.widgets[0].rows[0][0].text='wrong but nonempty',f=>f.shown.widgets[0].rows[0][1].text='function other()',f=>f.shown.widgets[0].rows[1][0].text='proved',f=>f.shown.widgets.push(f.shown.widgets[0]),f=>f.shown.widgets[0].rows.reverse(),f=>f.metadata.status.version++,f=>f.metadata.status.synchronizationId='reopened',f=>f.metadata.status.state='complete']){f=injectedPopup();mutate(f);assert.throws(()=>popupObservation(f.shown,f.metadata));}
 assert.throws(()=>popupObservation(injectedPopup().shown,injectedPopup().metadata,true));assert.equal(popupExpected(injectedPopup().metadata)[1][0].text,'ready');
});
function injectedPopupWire(){const a=injectedHoverWire();a.rows.splice(4,0,{direction:'client',message:{...structuredClone(a.rows[2].message),id:3}},{direction:'server',message:{id:3,result:structuredClone(a.value)}});return a;}
test('native popup second request preserves the original one-hover check and all source/terminal guards (injected)',()=>{
 const checks=require('../parity/proof-help.cjs'),accept=a=>checks.verificationPopupOrder(a.rows,1,a.owner,a.expected.position,a.value,a.proof);accept(injectedPopupWire());assert.throws(()=>checks.verificationHoverOrder(injectedPopupWire().rows,1,injectedPopupWire().owner,injectedPopupWire().expected.position,injectedPopupWire().value,injectedPopupWire().proof));
 for(const mutate of [a=>a.rows[4].message.id=2,a=>a.rows[4].message.params.textDocument.version++,a=>a.rows[5].message.result.contents.value='nonempty wrong',a=>a.rows[5].message={id:3,error:{code:-32800}},a=>a.rows.push(structuredClone(a.rows[4])),a=>a.rows.push(structuredClone(a.rows[5])),a=>a.rows.push(structuredClone(a.rows[3])),a=>a.rows.splice(5,0,a.rows.splice(6,1)[0]),a=>a.rows.splice(4,0,{direction:'client',message:{method:'textDocument/didClose',params:{textDocument:{uri:a.owner.uri}}}})]){const a=injectedPopupWire();mutate(a);assert.throws(()=>accept(a));}
});
test('proof-hover preserves narrow native profile and rejects a scenario ID without actual observations',()=>{
 const {parse}=require('../parity/run.cjs'),base=['--suite','proof-hover','--targets','local','--workers','1','--obligations','1'];assert.equal(parse(base).suite,'proof-hover');for(const extra of [['--workers','2'],['--obligations','2'],['--trace','off'],['--targets','dafny']])assert.throws(()=>parse([...base,...extra]));
 const result={schemaVersion:1,runId:'r',target:'local',scenarios:[{id:'native-certified-proof-help',status:'partial'}],checks:[],status:'passed-with-gaps'};assert.ok(require('../parity/core.cjs').hostEvidenceErrors(result,{runId:'r',target:'local',suite:'proof-hover'}).some(e=>e.includes('popup')));
});
test('native popup renderer must dispatch Escape and observe disappearance, retaining failed attempts (injected CDP)',async()=>{
 const {metadata,shown}=injectedPopup(),directory=fs.mkdtempSync(path.join(os.tmpdir(),'popup-renderer-')),calls=[];let hidden=false;
 const client={async request(method,params){calls.push({method,params});if(method==='Input.dispatchKeyEvent'){assert.equal(params.key,'Escape');if(params.type==='keyUp')hidden=true;return{};}if(method==='Runtime.evaluate'){new vm.Script(params.expression);return{result:{value:params.expression.startsWith('JSON.stringify')?JSON.stringify({title:'Injected',editorCount:1,visibleHovers:hidden?[]:['Injected'],bodyText:''}):{...shown,at:hidden?11:10,widgets:hidden?[]:shown.widgets}}};}if(method==='Accessibility.getFullAXTree')return{nodes:[{}]};if(method==='DOMSnapshot.captureSnapshot')return{documents:[{}]};if(method==='Page.captureScreenshot')return{data:Buffer.from([137,80,78,71,13,10,26,10,0]).toString('base64')};throw Error(method);}};
 try{const result=await require('../parity/renderer.cjs').captureProofHover(client,directory,metadata);assert.equal(result.hoverPopup.hidden.widgets.length,0);assert.equal(calls.filter(c=>c.method==='Input.dispatchKeyEvent').length,2);assert.ok(fs.existsSync(path.join(directory,'dismissed/screenshot.png')));
 hidden=false;shown.widgets[0].rows[0][0].text='wrong';await assert.rejects(require('../parity/renderer.cjs').captureProofHover(client,directory,metadata));assert.ok(fs.existsSync(path.join(directory,'hover-attempt.json')));
 }finally{fs.rmSync(directory,{recursive:true,force:true});}
});

test('popup disappearance during screenshot capture is rejected before Escape (injected CDP)',async()=>{
 const {metadata,shown}=injectedPopup(),directory=fs.mkdtempSync(path.join(os.tmpdir(),'popup-race-'));let captured=false,escape=0;
 const client={async request(method,params){if(method==='Input.dispatchKeyEvent'){escape++;return{};}if(method==='Runtime.evaluate')return{result:{value:params.expression.startsWith('JSON.stringify')?JSON.stringify({editorCount:1,visibleHovers:[],notifications:[]}):{...shown,widgets:captured?[]:shown.widgets}}};if(method==='Accessibility.getFullAXTree')return{nodes:[{}]};if(method==='DOMSnapshot.captureSnapshot')return{documents:[{}]};if(method==='Page.captureScreenshot'){captured=true;return{data:Buffer.from([137,80,78,71,13,10,26,10,0]).toString('base64')};}throw Error(method);}};
 try{await assert.rejects(require('../parity/renderer.cjs').captureProofHover(client,directory,metadata),/one visible/);assert.equal(escape,0);assert.ok(fs.existsSync(path.join(directory,'hover-attempt.json')));}finally{fs.rmSync(directory,{recursive:true,force:true});}
});

test('proof-hover envelope validates actual scenario nesting and independently rejects each omitted observation (injected)',()=>{
 const {hostEvidenceErrors}=require('../parity/core.cjs'),capture={status:'captured',capture:{screenshot:true}},observations={hoverPopup:{...capture,capture:{screenshot:true,hoverPopup:{shown:{},shownAfterCapture:{},hidden:{}}}},hoverDuringVerification:{wire:{popupRequestIndex:4}},actions:['guide','index'].map(choice=>({choice,menu:structuredClone(capture),document:structuredClone(capture)}))},make=()=>({schemaVersion:1,runId:'r',target:'local',status:'passed-with-gaps',checks:[],scenarios:[{id:'native-certified-proof-help',status:'partial',observation:{observations:structuredClone(observations)}}]}),config={runId:'r',target:'local',suite:'proof-hover'};
 assert.deepEqual(hostEvidenceErrors(make(),config),[]);
 for(const remove of [o=>delete o.hoverPopup,o=>delete o.hoverPopup.capture.hoverPopup.shown,o=>delete o.hoverPopup.capture.hoverPopup.shownAfterCapture,o=>delete o.hoverPopup.capture.hoverPopup.hidden,o=>delete o.hoverDuringVerification.wire.popupRequestIndex,o=>delete o.actions[0].menu,o=>delete o.actions[1].document,o=>o.actions.pop()]){const r=make();remove(r.scenarios[0].observation.observations);assert.ok(hostEvidenceErrors(r,config).length);}
});
