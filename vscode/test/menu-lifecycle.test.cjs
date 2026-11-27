// Injected capture envelopes test refusal logic; no native/raster evidence.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),{createHash}=require('node:crypto'),{validate,phases}=require('../parity/menu-lifecycle.cjs');
const {fixture}=require('./menu-fixture.cjs');
test('menu envelopes retain distinct upstream untitled predicate and ordered source lifetime (injected)',()=>{for(const target of ['local','dafny'])assert.deepEqual(validate(fixture(target),'run',target,'/'),[]);});
test('menu envelopes refuse wrong target, source, lifetime, phase, menu, capture changes and side effects (injected)',()=>{
 const changes=[v=>v.target='dafny',v=>v.phases.reverse(),v=>v.phases.pop(),v=>v.phases[0].binding.sourceHash='a'.repeat(64),v=>v.phases[0].binding.session='foreign',v=>v.phases[0].binding.uri='file:///foreign.sol',v=>v.phases[0].after.version++,v=>v.phases[0].capture.runId='foreign',v=>v.phases[0].capture.metadataHash='x',v=>v.phases[0].capture.capture.screenshot=false,v=>v.phases[0].capture.capture.contributionMenu.before.activeUri='foreign',v=>v.phases[0].capture.capture.contributionMenu.after.items.pop(),v=>v.phases[0].capture.capture.contributionMenu.submenuVisible=false,v=>v.forbiddenActions.push({kind:'command.start'}),v=>v.phases[0].capture.status='failed',v=>v.phases[0].capture.error='failed',v=>v.phases[0].error='failed',v=>v.phases[0].events.push({kind:'command.start',data:{id:'solidityLean.build'}}),v=>v.events.push({kind:'terminal.start'}),v=>delete v.events,v=>delete v.phases[0].capture.capture.contributionMenu.before.items[0].ariaDisabled,v=>v.phases[0].capture.capture.contributionMenu.before.items[0].withinViewport=false];
 for(const change of changes){const value=fixture();change(value);assert.ok(validate(value,'run','local','/').length);}
});
module.exports={fixture};

test('menu readiness rejects late completion and unresolved RPC without increasing original deadline (injected clock)',async()=>{const {preparation}=require('../parity/menu-lifecycle.cjs');let now=0;await assert.rejects(preparation(async()=>{now=3001;return true;},3000,()=>now),/Late/);await assert.rejects(preparation(()=>new Promise(()=>{}),Date.now()+5),/exhausted/);assert.equal(await preparation(async()=>true,Date.now()+1000),true);});

test('failed native phase retains exact event interval and original failure (injected editor/capture)',async()=>{
 const fs=require('node:fs'),os=require('node:os'),path=require('node:path'),dir=fs.mkdtempSync(path.join(os.tmpdir(),'menu-failure-')),events=[],vscode={workspace:{isTrusted:true,async openTextDocument(file){return{uri:{toString:()=>require('node:url').pathToFileURL(file).href,scheme:'file'},version:1,languageId:'solidity',getText:()=>fs.readFileSync(file,'utf8')};}},window:{async showTextDocument(document){this.activeTextEditor={document};}},commands:{async executeCommand(){}}};
 try{await assert.rejects(require('../parity/menu-lifecycle.cjs').run({vscode,config:{target:'local',workspace:dir,dir,runId:'failed-run',operationTimeoutMs:1000},events,sessionFor:()=> 'owned',requestPhase:async()=>{events.push({kind:'clipboard.write',data:{sha256:'fake'}});throw Error('actual capture failed');}}),/actual capture failed/);const value=JSON.parse(fs.readFileSync(path.join(dir,'menu-observations.json')));assert.equal(value.phases.length,1);assert.equal(value.phases[0].error,'actual capture failed');assert.equal(value.phases[0].eventEnd,1);assert.deepEqual(value.phases[0].events,events);assert.deepEqual(value.events,events);assert.deepEqual(value.forbiddenActions,events);assert.ok(validate(value,'failed-run','local',dir).length);}finally{fs.rmSync(dir,{recursive:true,force:true});}
});

test('native menu runner refuses implicit multi-worker/multi-trial dimensions',()=>{const{parse}=require('../parity/run.cjs');assert.throws(()=>parse(['--suite','contribution-menus']),/single serial/);assert.equal(parse(['--suite','contribution-menus','--workers','1','--obligations','1','--trials','1','--warmups','0']).suite,'contribution-menus');});

test('malformed menu structures return rejection records rather than losing the host result',()=>{for(const change of [v=>v.phases=null,v=>v.phases[0]=null,v=>v.phases[0].capture.capture.contributionMenu.before.items={},v=>v.phases[0].events={}]){const v=fixture();change(v);let errors;assert.doesNotThrow(()=>{errors=validate(v,'run','local','/');});assert.ok(errors.length);}});

function trustedFixture(target='local'){
 const v=fixture(target),base=v.phases[0].binding;v.trust={mode:'native-workspace-trust',settings:{enabled:true,startupPrompt:'never',enabledUserValue:true},steps:[]};
 for(const phase of ['initial','grant','deny','lost','restore','restored']){
  const menu=['initial','lost','restored'].includes(phase),desired=['grant','restore','restored'].includes(phase),binding={...base,trusted:menu?desired:!desired};
  let metadata,captured;
  if(menu){metadata={binding,target,kind:'editor',trustObservation:true};const item=structuredClone(v.phases[0].capture.capture.contributionMenu),visible=binding.trusted;item.binding=binding;item.submenuVisible=visible;if(!visible)item.before.items=[{...item.before.items[0],label:'Copy'}];item.after=structuredClone(item.before);captured={captured:true,screenshot:true,contributionMenu:item};}
  else{metadata={binding,desired};const before={visible:true,buttons:[{label:desired?'Trust':"Don't Trust",disabled:null}]},after={visible:true,buttons:[{label:desired?"Don't Trust":'Trust',disabled:null}]};captured={captured:true,screenshot:true,trustControl:{binding,desired,before,after,beforeCaptured:structuredClone(before),afterCaptured:structuredClone(after),nativeMouse:true}};}
  v.trust.steps.push({phase,binding,after:{...binding,trusted:menu?binding.trusted:desired},events:[],eventStart:0,eventEnd:0,capture:{runId:'run',status:'captured',phase:menu?'menus-trust-'+phase:'menus-trust-control-'+phase,metadataHash:createHash('sha256').update(JSON.stringify(metadata)).digest('hex'),capture:captured}});
 }for(const row of v.phases){for(const k of ['before','after'])row.capture.capture.contributionMenu[k].rendererLifetime={timeOrigin:1,url:'vscode-file://owned'};}for(const row of v.trust.steps){const c=row.capture.capture;for(const k of ['before','after'])if(c.contributionMenu)c.contributionMenu[k].rendererLifetime={timeOrigin:1,url:'vscode-file://owned'};for(const k of ['before','after','beforeCaptured','afterCaptured'])if(c.trustControl)c.trustControl[k].rendererLifetime={timeOrigin:1,url:'vscode-file://owned'};}return v;
}
test('native trust envelopes require real UI/publicAPI/source bindings and unchanged legacy phases (injected)',()=>{for(const target of ['local','dafny'])assert.deepEqual(validate(trustedFixture(target),'run',target,'/','transitions'),[]);});
test('native trust envelopes refuse missing, stale, mutated and false-restoration evidence (injected)',()=>{
 const changes=[v=>delete v.trust,v=>v.trust.steps.reverse(),v=>v.trust.settings.enabledUserValue=false,v=>v.trust.steps[1].after.trusted=false,v=>v.trust.steps[0].binding.session='foreign',v=>v.trust.steps[0].capture.runId='foreign',v=>v.trust.steps[1].capture.capture.trustControl.nativeMouse=false,v=>v.trust.steps[1].capture.capture.trustControl.beforeCaptured.visible=false,v=>v.trust.steps[1].capture.capture.trustControl.afterCaptured.buttons=[],v=>v.trust.steps[0].events.push({kind:'clipboard.write'}),v=>{const m=v.trust.steps[5].capture.capture.contributionMenu;m.submenuVisible=false;m.before.items=[{...m.before.items[0],label:'Copy'}];m.after=structuredClone(m.before);},v=>{const m=v.trust.steps[5].capture.capture.contributionMenu;m.before.items.pop();m.after=structuredClone(m.before);},v=>v.trust.steps[0].capture.capture.contributionMenu.before.items[0].withinViewport=false,v=>v.trust.steps[2].capture.status='failed'];
 for(const change of changes){const v=trustedFixture();change(v);assert.ok(validate(v,'run','local','/','transitions').length);}
});
test('trust renderer rejects UI replacement inside either capture bracket (injected CDP)',async()=>{
 const fs=require('node:fs'),os=require('node:os'),path=require('node:path'),{captureTrustControl}=require('../parity/renderer.cjs');
 for(const mutate of [1,2]){const dir=fs.mkdtempSync(path.join(os.tmpdir(),'trust-bracket-'));let granted=false,captures=0,changed=false;const client={async request(method,params){if(method==='Input.dispatchMouseEvent'){if(params.type==='mouseReleased')granted=true;return{};}return{result:{value:{visible:!changed,buttons:[{label:granted?"Don't Trust":'Trust',disabled:null,bounds:{left:1,top:1,right:10,bottom:10}}]}}};}};
  try{await assert.rejects(captureTrustControl(client,dir,{desired:true,binding:{trusted:false}},async()=>{if(++captures===mutate)changed=true;return{captured:true,screenshot:true};}),/Trust UI changed/);assert.ok(fs.existsSync(path.join(dir,'trust-attempt.json')));}finally{fs.rmSync(dir,{recursive:true,force:true});}
 }
});
test('trust runner accepts only explicit opt-in on bounded contribution suite',()=>{const{parse}=require('../parity/run.cjs');assert.throws(()=>parse(['--menu-trust','transitions']),/require contribution/);assert.throws(()=>parse(['--suite','contribution-menus','--menu-trust','fake']),/require contribution/);assert.equal(parse(['--suite','contribution-menus','--menu-trust','transitions','--workers','1','--obligations','1','--trials','1','--warmups','0']).menuTrust,'transitions');});


test('missing host report retains complete failed partial menu record without promotion (injected file boundary)',()=>{
 const fs=require('node:fs'),os=require('node:os'),path=require('node:path'),{partialEvidence}=require('../parity/menu-lifecycle.cjs'),dir=fs.mkdtempSync(path.join(os.tmpdir(),'menu-partial-'));
 try{const original=trustedFixture();original.trust.steps=original.trust.steps.slice(0,3);original.trust.steps[2].error='CDP timeout DOMSnapshot.captureSnapshot';fs.writeFileSync(path.join(dir,'menu-observations.json'),JSON.stringify(original));const report=JSON.parse(JSON.stringify({status:'broken',error:'No fresh extension-host report',partialMenuEvidence:partialEvidence(dir,'run','local')}));assert.equal(report.status,'broken');assert.equal(report.result,undefined);assert.deepEqual(report.partialMenuEvidence.observation,original);assert.equal(report.partialMenuEvidence.status,'failed-partial');assert.equal(report.partialMenuEvidence.observation.trust.steps[2].error,'CDP timeout DOMSnapshot.captureSnapshot');assert.ok(validate(original,'run','local','/','transitions').length);assert.equal(partialEvidence(dir,'run','dafny').status,'unavailable');assert.equal(partialEvidence(dir,'foreign','local').observation,undefined);}finally{fs.rmSync(dir,{recursive:true,force:true});}
});

test('trust envelopes reject a renderer restart even with unchanged source bytes (injected)',()=>{const v=trustedFixture();v.trust.steps[5].capture.capture.contributionMenu.before.rendererLifetime.timeOrigin++;v.trust.steps[5].capture.capture.contributionMenu.after.rendererLifetime.timeOrigin++;assert.ok(validate(v,'run','local','/','transitions').includes('renderer restarted or missing lifetime evidence'));});

function recoveryFixture(target='local'){
 const v=trustedFixture(target),old=v.phases[0].binding,prior={status:'retained-failed-same-session',target,runId:'old-run',binding:{...old,session:'old-document'},host:{hostSession:'old-host'},exit:{wallTime:1},receipts:[]},value={mode:'separate-new-session-recovery',runId:'run',target,predecessor:prior,settings:{enabled:true,startupPrompt:'never',enabledUserValue:true},host:{hostSession:'new-host',runId:'run',target,pid:123,birth:'123',wallTime:2,trusted:false,previousHostRecorded:false},events:[],forbiddenActions:[],steps:[v.trust.steps[0],v.trust.steps[4],v.trust.steps[5]]};
 value.steps[0].phase='initial';value.steps[1].phase='restore';value.steps[2].phase='restored';for(const row of value.steps)row.capture.phase=row.phase==='restore'?'menus-trust-control-recovery':'menus-trust-recovery-'+row.phase;return value;
}
test('new-session recovery is separately bound and never satisfies original same-session validation (injected)',()=>{
 const {recoveryErrors}=require('../parity/menu-lifecycle.cjs');for(const target of ['local','dafny']){const v=recoveryFixture(target);assert.deepEqual(recoveryErrors(v,'run',target,v.predecessor),[]);assert.ok(validate(v,'run',target,'/','transitions').length);}
});
test('new-session recovery refuses stale source, old session, missing native transition and renderer replacement (injected)',()=>{
 const {recoveryErrors}=require('../parity/menu-lifecycle.cjs');for(const mutate of [v=>v.settings.enabled=false,v=>v.host.hostSession='old-host',v=>v.host.runId='foreign',v=>v.host.birth='',v=>v.host.wallTime=0,v=>v.steps[0].binding.session='old-document',v=>v.steps[0].binding.uri='file:///foreign',v=>v.steps[2].binding.version++,v=>v.steps[1].after.trusted=false,v=>v.steps[1].capture.capture.trustControl.nativeMouse=false,v=>v.steps[1].capture.error='failed capture',v=>v.steps[1].capture.status='failed',v=>v.steps[0].capture.capture.contributionMenu.before.items[0].withinViewport=false,v=>v.steps[2].capture.capture.contributionMenu.after.rendererLifetime.timeOrigin++,v=>v.events.push({kind:'terminal.start'}),v=>v.steps.reverse(),v=>v.steps[0].capture.metadataHash='foreign']){const v=recoveryFixture(),expected=structuredClone(v.predecessor);mutate(v);assert.ok(recoveryErrors(v,'run','local',expected).length);}const v=recoveryFixture(),other=structuredClone(v.predecessor);other.runId='different';assert.ok(recoveryErrors(v,'run','local',other).length);
});
test('recovery option requires explicit predecessor and original bounded menu dimensions',()=>{const {parse}=require('../parity/run.cjs'),base=['--suite','contribution-menus','--workers','1','--obligations','1','--trials','1','--warmups','0'];assert.throws(()=>parse([...base,'--menu-trust','recovery']),/predecessor/);assert.throws(()=>parse([...base,'--menu-recovery-from','/receipt']),/predecessor/);assert.equal(parse([...base,'--menu-trust','recovery','--menu-recovery-from','/receipt']).menuTrust,'recovery');});
test('recovery predecessor immutable receipt and source guard rejects changed bytes (injected files)',()=>{const fs=require('fs'),os=require('os'),path=require('path'),{pathToFileURL}=require('url'),{verifyRecoveryReceipts}=require('../parity/menu-lifecycle.cjs'),dir=fs.mkdtempSync(path.join(os.tmpdir(),'recovery-receipts-'));try{const source=path.join(dir,'source'),receipt=path.join(dir,'receipt');fs.writeFileSync(source,'unchanged source');fs.writeFileSync(receipt,'original failure');const hash=p=>createHash('sha256').update(fs.readFileSync(p)).digest('hex'),prior={receipts:[{file:receipt,sha256:hash(receipt)}],binding:{uri:pathToFileURL(source).href,sourceHash:hash(source)}};verifyRecoveryReceipts(prior);fs.writeFileSync(receipt,'changed failure');assert.throws(()=>verifyRecoveryReceipts(prior),/receipt mutated/);fs.writeFileSync(receipt,'original failure');fs.writeFileSync(source,'different source');assert.throws(()=>verifyRecoveryReceipts(prior),/source mutated/);}finally{fs.rmSync(dir,{recursive:true,force:true});}});

test('recovery admission validates original five endpoints and native grant, retaining only unfinished deny (injected)',()=>{const {recoveryPrefixErrors}=require('../parity/menu-lifecycle.cjs'),make=()=>{const v=trustedFixture();v.trust.steps=v.trust.steps.slice(0,3);const deny=v.trust.steps[2];delete deny.capture;delete deny.after;return v;},events=[{kind:'scenario.start',data:{id:'native-contribution-menus'}}];assert.deepEqual(recoveryPrefixErrors(make(),events,'run','local','/'),[]);for(const mutate of [v=>v.phases[0].capture.metadataHash='foreign',v=>delete v.phases[0].capture.capture.screenshot,v=>v.phases[0].error='actual error',v=>v.phases[1].capture.capture.contributionMenu.after.items=[],v=>v.trust.steps[1].capture.capture.trustControl.nativeMouse=false,v=>v.trust.steps[1].after.trusted=false,v=>v.trust.steps[1].capture.runId='foreign',v=>v.trust.steps[2].after=v.trust.steps[2].binding]){const v=make();mutate(v);assert.ok(recoveryPrefixErrors(v,events,'run','local','/').length);}assert.ok(recoveryPrefixErrors(make(),[...events,{kind:'clipboard.write'}],'run','local','/').length);});

// Exercise the real file request/server transport; bytes are synthetic, not native evidence.
test('recovery phases complete through request and capture server transport (synthetic PNG)', async()=>{
 const fs=require('node:fs'),os=require('node:os'),path=require('node:path');
 const {requestPhase,servePhases}=require('../parity/phase-capture.cjs');
 const dir=fs.mkdtempSync(path.join(os.tmpdir(),'recovery-phase-transport-')),seen=new Set();
 try{
  for(const phase of ['menus-trust-recovery-initial','menus-trust-control-recovery','menus-trust-recovery-restored']){
   const pending=requestPhase(dir,'recovery-run',phase,{source:'unchanged'},1000);
   const observed=[];
   await servePhases(dir,'recovery-run',async(destination,request)=>{
    observed.push(request.phase);
    fs.writeFileSync(path.join(destination,'screenshot.png'),Buffer.from('iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAYAAAAfFcSJAAAADUlEQVR4nGNgYGD4DwABBAEAX+XDSwAAAABJRU5ErkJggg==','base64'));
    return {captured:true,screenshot:true};
   },seen);
   const reply=await pending;
   assert.equal(reply.status,'captured');
   assert.equal(reply.phase,phase);
   assert.deepEqual(observed,[phase]);
  }
 }finally{fs.rmSync(dir,{recursive:true,force:true});}
});

// Injected CDP geometry controls; these do not establish native menu/raster parity.
test('native menu collector refuses unowned or unusable anchors before any input',async()=>{
 const {captureContributionMenu}=require('../parity/renderer.cjs'),fs=require('node:fs'),os=require('node:os'),path=require('node:path');
 const good={activeUri:'file:///owned.sol',rect:{left:10,top:20,right:210,bottom:120,width:200,height:100},viewport:{width:1000,height:800}};
 for(const change of [v=>v.activeUri='file:///foreign.sol',v=>v.rect.width=0,v=>v.rect.left=-1,v=>v.rect.right=1001,v=>v.rect.top=NaN,v=>v.viewport.height=0,v=>v.rect=null]){
  const sample=structuredClone(good);change(sample);const calls=[],dir=fs.mkdtempSync(path.join(os.tmpdir(),'menu-anchor-'));
  try{await assert.rejects(captureContributionMenu({async request(method){calls.push(method);return{result:{value:sample}};}},dir,{target:'local',kind:'editor',binding:{uri:'file:///owned.sol'}}),/Owned menu anchor/);assert.equal(calls.filter(x=>x.startsWith('Input.')).length,0);}finally{fs.rmSync(dir,{recursive:true,force:true});}
 }
});

test('owned visible menu anchor preserves original mouse offsets and rejects inconsistent point',()=>{
 const {menuAnchorPoint}=require('../parity/menu-lifecycle.cjs'),sample={activeUri:'file:///owned',rect:{left:10,top:20,right:210,bottom:120,width:200,height:100},viewport:{width:1000,height:800}};
 assert.deepEqual(menuAnchorPoint(sample,'file:///owned'),{x:70,y:32});sample.rect.right=20;assert.throws(()=>menuAnchorPoint(sample,'file:///owned'),/point/);
});

test('anchor DOM cannot borrow URI from a different Monaco subtree',async()=>{
 const {captureContributionMenu}=require('../parity/renderer.cjs'),vm=require('node:vm'),fs=require('node:fs'),os=require('node:os'),path=require('node:path'),calls=[],dir=fs.mkdtempSync(path.join(os.tmpdir(),'menu-dom-owner-')),rect={left:10,top:20,right:210,bottom:120,width:200,height:100};
 const owned={getAttribute:()=> 'file:///owned.sol',getBoundingClientRect:()=>rect},foreign={getAttribute:()=> 'file:///foreign.sol',getBoundingClientRect:()=>rect},group={querySelectorAll:selector=>selector.includes('monaco-editor')?[owned]:[]},anchor={getBoundingClientRect:()=>rect,closest:selector=>selector.includes('editor-group')?group:foreign};
 const document={querySelector:selector=>selector.includes('view-lines')?anchor:owned};
 // A filtered closest() must not skip a nested Monaco lacking data-uri.
 const nearest=anchor.closest;anchor.closest=selector=>selector.includes('[data-uri]')?owned:nearest(selector);
 try{await assert.rejects(captureContributionMenu({async request(method,params){calls.push(method);return{result:{value:vm.runInNewContext(params.expression,{document,innerWidth:1000,innerHeight:800})}};}},dir,{target:'local',kind:'editor',binding:{uri:'file:///owned.sol'}}),/Owned menu anchor/);assert.equal(calls.filter(x=>x.startsWith('Input.')).length,0);assert.equal(JSON.parse(fs.readFileSync(path.join(dir,'menu-anchor.json'))).anchor.activeUri,null);}finally{fs.rmSync(dir,{recursive:true,force:true});}
});

test('raw presentation-role diagnostics cannot waive strict trust menu attributes',()=>{
 const {trustErrors}=require('../parity/menu-lifecycle.cjs'),v=trustedFixture(),m=v.trust.steps[0].capture.capture.contributionMenu;
 m.before.items.push({label:'',ariaDisabled:null,className:null,withinViewport:true,bounds:{left:1,top:1,right:100,bottom:20}});m.after=structuredClone(m.before);
 v.menuRoles={version:1,reads:[{roles:[{label:{role:'presentation',className:'separator disabled',ariaDisabled:'true'},menuItem:null}]}]};
 assert.ok(trustErrors(v,'run','local').includes('incomplete trust menu attributes'));
});


test('menu mouse passes original absolute deadline and clock without changing ownership guard',async()=>{
 const {menuMouse}=require('../parity/menu-lifecycle.cjs');let wall=100,checks=0;const now=()=>wall,calls=[],client={request:async(...args)=>{calls.push(args);return{};}};
 for(const type of ['mousePressed','mouseReleased'])await menuMouse(client,{type},()=>{checks++;},200,now);
 assert.equal(checks,2);assert.equal(calls.length,2);for(const [method,,options] of calls){assert.equal(method,'Input.dispatchMouseEvent');assert.equal(options.deadlineWall,200);assert.equal(options.wallNow,now);}
 wall=200;await assert.rejects(menuMouse(client,{},()=>{checks++;},200,now),/Original3s/);assert.equal(checks,2);assert.equal(calls.length,2);
 await assert.rejects(menuMouse(client,{},()=>{throw Error('foreign ownership');},300,now),/foreign ownership/);assert.equal(calls.length,2);
});
