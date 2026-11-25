// Injected endpoint/phase scheduling controls; no native rendering or parity evidence.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),os=require('node:os');
const {connect,withPhaseRenderer}=require('../parity/renderer.cjs');
const {requestPhase,servePhases}=require('../parity/phase-capture.cjs');
const page={id:'renderer-a',url:'vscode-file://vscode-app/window',title:'owned',type:'page',webSocketDebuggerUrl:'ws://owned'};
function transport(){let now=0,created=0;const events=[],listeners=new Map(),timers=new Map();return{events,advance:n=>{now=n;},created:()=>created,options:{now:()=>now,diagnostic:e=>events.push(e),socketFactory:()=>{created++;return{addEventListener:(name,fn)=>listeners.set(name,fn),close(){listeners.get('close')?.({code:1000});}};},setTimer:(fn,ms)=>{assert.equal(ms,5000);timers.set(1,fn);return 1;},clearTimer:id=>timers.delete(id)},open:()=>listeners.get('open')(),timers};}
test('lookup journals headers/body/target and retains its original single1500ms signal',async()=>{
 const f=transport();let signal;
 const client=await connect(42,{...f.options,fetchImpl:async(url,options)=>{assert.equal(url,'http://127.0.0.1:42/json/list');signal=options.signal;return{ok:true,status:200,json:async()=>[page]};}});
 f.open();await client.ready;assert.ok(signal instanceof AbortSignal);assert.equal(signal.aborted,false);
 assert.deepEqual(f.events.slice(0,4).map(e=>e.event),['target.lookup.start','target.lookup.headers','target.lookup.body','target.lookup.finish']);
 assert.ok(f.events.slice(0,4).every(e=>e.deadlineMs===1500&&e.lookupUrl.endsWith(':42/json/list')));assert.equal(client.identity.targetId,page.id);client.close();assert.equal(f.timers.size,0);
});
for(const stage of ['headers','body'])test('late '+stage+' cannot bypass endpoint deadline before overdue timer delivery',async()=>{
 const f=transport();await assert.rejects(connect(42,{...f.options,fetchImpl:async()=>{if(stage==='headers')f.advance(1500);return{ok:true,status:200,json:async()=>{f.advance(1501);return[page];}};}}),/target lookup timeout/);
 assert.equal(f.created(),0);assert.equal(f.events.at(-1).event,'target.lookup.failed');assert.ok(f.events.at(-1).elapsedMs>=1500);
});
for(const variant of ['http','malformed','foreign','aborted'])test('lookup '+variant+' stays a failure and creates no socket',async()=>{
 const f=transport();await assert.rejects(connect(42,{...f.options,fetchImpl:async()=>{if(variant==='aborted')throw Error('The operation was aborted due to timeout');return{ok:variant!=='http',status:variant==='http'?503:200,json:async()=>variant==='malformed'?{}:variant==='foreign'?[{...page,url:'https://foreign'}]:[page]};}}));
 assert.equal(f.created(),0);assert.equal(f.events.at(-1).event,'target.lookup.failed');if(variant==='aborted')assert.equal(f.events.at(-1).error,'The operation was aborted due to timeout');
});
function phase(t){const dir=fs.mkdtempSync(path.join(os.tmpdir(),'phase-renderer-'));t.after(()=>fs.rmSync(dir,{recursive:true,force:true}));return{dir,request:{phase:'diagnostics-problems-duplicate',requestId:'request-a',metadata:{binding:{uri:'file:///owned.sol',version:7,sourceHash:'hash',session:'session-a'}}},config:{runId:'run-a',target:'local',sourceHead:'head-a'},rows:()=>fs.readFileSync(path.join(dir,'cdp-timing.jsonl'),'utf8').trim().split('\n').map(JSON.parse)};}
test('Problems connection failure is journaled with immutable source/run/request identity before any capture',async t=>{
 const f=phase(t);let captures=0;await assert.rejects(withPhaseRenderer(42,f.dir,f.request,f.config,async()=>{captures++;},{connectRenderer:async(port,{diagnostic})=>{diagnostic({event:'target.lookup.start',runId:'foreign'});throw Error('lookup aborted');}}),/lookup aborted/);
 assert.equal(captures,0);assert.deepEqual(f.rows().map(r=>r.event),['phase.start','target.lookup.start','phase.failed']);
 assert.ok(f.rows().every(r=>r.runId==='run-a'&&r.sourceHead==='head-a'&&r.phaseRequestId==='request-a'&&r.source.session==='session-a'));assert.equal(fs.existsSync(path.join(f.dir,'screenshot.png')),false);
});
test('primary phase error survives a disconnect/cleanup error; successful-looking capture cannot mask cleanup failure',async t=>{
 const f=phase(t),client={close(){throw Error('disconnect cleanup');}};
 const original=Error('capture failed');await assert.rejects(withPhaseRenderer(42,f.dir,f.request,f.config,async()=>{throw original;},{connectRenderer:async()=>client}),e=>e===original&&e.cleanupErrors[0]==='disconnect cleanup');
 await assert.rejects(withPhaseRenderer(42,f.dir,f.request,f.config,async()=>({captured:true}),{connectRenderer:async()=>client}),/disconnect cleanup/);
 assert.equal(f.rows().filter(r=>r.event==='phase.complete').length,0);
});
test('menus retain strict finish while Problems retains close, each exactly once',async t=>{
 for(const menu of [false,true]){const f=phase(t);if(menu)f.request.phase='menus-source';let closed=0,finished=0;const result={captured:false};
 assert.equal(await withPhaseRenderer(42,f.dir,f.request,f.config,async()=>result,{connectRenderer:async()=>({close(){closed++;},finish(){finished++;}})}),result);
 assert.equal(closed,menu?0:1);assert.equal(finished,menu?1:0);assert.equal(f.rows().at(-1).event,'phase.complete');}
});
test('real phase request/serve retains failed lookup and cannot synthesize screenshot success',async t=>{
 const f=phase(t),pending=requestPhase(f.dir,'run-a',f.request.phase,f.request.metadata,1000),rejected=assert.rejects(pending,/lookup aborted/);
 await servePhases(f.dir,'run-a',(dir,request)=>withPhaseRenderer(42,dir,request,f.config,async()=>{throw Error('must not capture');},{connectRenderer:async()=>{throw Error('lookup aborted');}}),new Set());await rejected;
 const reply=JSON.parse(fs.readFileSync(path.join(f.dir,'phases',f.request.phase,'reply.json')));assert.equal(reply.status,'failed');assert.equal(reply.error,'lookup aborted');assert.equal(reply.capture,undefined);
});

test('final lookup journaling cannot spend the deadline and then admit a new socket',async()=>{
 const f=transport();await assert.rejects(connect(42,{...f.options,diagnostic:event=>{f.events.push(event);if(event.event==='target.lookup.finish')f.advance(1500);},fetchImpl:async()=>({ok:true,status:200,json:async()=>[page]})}),/target lookup timeout/);
 assert.equal(f.created(),0);assert.equal(f.events.at(-1).event,'target.lookup.failed');
});
test('failed lookup journal cannot replace original fetch or JSON failure',async()=>{
 for(const stage of ['fetch','json']){const f=transport(),original=Error(stage+' original');
 await assert.rejects(connect(42,{...f.options,diagnostic:event=>{if(event.event==='target.lookup.failed')throw Error('journal write failed');},fetchImpl:async()=>{if(stage==='fetch')throw original;return{ok:true,status:200,json:async()=>{throw original;}};}}),e=>e===original&&e.reportingErrors[0]==='journal write failed');assert.equal(f.created(),0);}
});

const phaseReasons=[undefined,null,false,0,'','renderer rejected',{message:'object rejection'},{get message(){throw Error('unavailable');}},Symbol('phase'),1n];
for(const menu of [false,true])for(const stage of ['lookup','capture','cleanup'])for(const [index,reason] of phaseReasons.entries())test('non-Error phase refusal '+[menu,stage,index].join('/'),async t=>{
 const f=phase(t);if(menu)f.request.phase='menus-source';let captured=0,closed=0;
 const close=()=>{closed++;if(stage==='cleanup')throw reason;},client={close,finish:close};
 await assert.rejects(withPhaseRenderer(42,f.dir,f.request,f.config,async()=>{captured++;if(stage==='capture')throw reason;return{captured:true,screenshot:true};},{connectRenderer:async()=>{if(stage==='lookup')throw reason;return client;}}),error=>{assert.ok(error instanceof Error);assert.equal(error.cause,reason);assert.ok(error.message.length);return true;});
 assert.equal(captured,stage==='lookup'?0:1);assert.equal(closed,stage==='lookup'?0:1);const rows=f.rows();assert.equal(rows.at(-1).event,'phase.failed');assert.equal(typeof rows.at(-1).error,'string');assert.ok(rows.at(-1).error.length);assert.equal(rows.filter(r=>r.event==='phase.complete').length,0);
});
test('falsy primary cause survives a second falsy cleanup failure',async t=>{const f=phase(t);await assert.rejects(withPhaseRenderer(42,f.dir,f.request,f.config,async()=>{throw null;},{connectRenderer:async()=>({close(){throw false;}})}),e=>e instanceof Error&&e.cause===null&&e.cleanupErrors.length===1&&e.cleanupErrors[0].includes('false'));assert.equal(f.rows().at(-1).event,'phase.failed');assert.equal(f.rows().filter(r=>r.event==='phase.complete').length,0);});

for(const stage of ['fetch','json'])for(const [index,reason] of phaseReasons.entries())test('default connect retains non-Error '+stage+' cause '+index,async()=>{
 const f=transport();await assert.rejects(connect(42,{...f.options,fetchImpl:async()=>{if(stage==='fetch')throw reason;return{ok:true,status:200,json:async()=>{throw reason;}};}}),e=>e instanceof Error&&e.cause===reason&&e.message.length>0);
 assert.equal(f.created(),0);assert.equal(f.events.at(-1).event,'target.lookup.failed');assert.ok(f.events.at(-1).error.length);
});
test('falsy lookup reporting failure cannot replace original fetch cause',async()=>{const f=transport();await assert.rejects(connect(42,{...f.options,diagnostic:event=>{if(event.event==='target.lookup.failed')throw null;f.events.push(event);},fetchImpl:async()=>{throw false;}}),e=>e instanceof Error&&e.cause===false&&e.reportingErrors.length===1&&e.reportingErrors[0].includes('null'));assert.equal(f.created(),0);});
