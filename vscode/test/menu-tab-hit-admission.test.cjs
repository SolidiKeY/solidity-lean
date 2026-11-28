// Injected recorded endpoints and fake CDP only: no native, PNG, raster or row evidence.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),os=require('node:os'),{fileURLToPath}=require('node:url'),{createHash}=require('node:crypto');
const renderer=require('../parity/renderer.cjs'),hit=require('../parity/menu-tab-hit.cjs'),lifecycle=require('../parity/menu-lifecycle.cjs'),{hostEvidenceErrors}=require('../parity/core.cjs'),{parse}=require('../parity/run.cjs'),{fixture}=require('./menu-fixture.cjs');
function sample(t,target='local',kind='tab',afterRead=()=>{}){
 const root=fs.mkdtempSync(path.join(os.tmpdir(),'tab-hit-admission-'));t.after(()=>fs.rmSync(root,{recursive:true,force:true}));
 const directory=path.join(root,'phase');fs.mkdirSync(directory);
 const value=fixture(target),row=value.phases.find(r=>r.phase==='tab'),binding=row.binding,config={suite:'contribution-menus',runId:'run',target,workspace:'/',sourceHead:'a'.repeat(40),menuTabHit:hit.version};
 const owner={origin:'vscode.window.tabGroups',runId:'run',sourceHead:config.sourceHead,hostSession:'host',documentSession:binding.session,nonce:'injected-owner',epoch:0,uri:binding.uri,resourcePath:fileURLToPath(binding.uri),viewColumn:1,activeTabIndex:0,tabCount:1,dirty:true,source:{...binding,dirty:true}};
 fs.writeFileSync(path.join(root,'menu-tab-owner.json'),JSON.stringify({status:'current',runId:'run',sourceHead:config.sourceHead,hostSession:owner.hostSession,documentSession:owner.documentSession,nonce:owner.nonce,epoch:0,observed:owner}));
 const lifetime={timeOrigin:123,url:'vscode-file://workbench'},anchor={rendererLifetime:lifetime,activeUri:binding.uri,tabSelected:'true',tabResourceLabels:[owner.resourcePath],rect:{left:10,top:20,right:210,bottom:120,width:200,height:100},viewport:{width:1000,height:800}};
 const point=lifecycle.menuAnchorPoint(anchor,binding.uri),probe={...anchor,origin:'CDP DOM tab-hit',point,ownedTab:true,hitOwned:true,styleChain:[{tag:'DIV',display:'block',visibility:'visible',opacity:'1'}]};
 const menu={rendererLifetime:lifetime,activeUri:binding.uri,tabSelected:'true',tabResourceLabels:[owner.resourcePath],items:[{label:'Copy',ariaDisabled:null,className:'menuitem',withinViewport:true,bounds:{left:1,top:1,right:100,bottom:20}}]};
 const metadata={binding,target,kind,visible:false,...(kind==='tab'?{tabOwnership:owner}:{})},calls=[];let reads=0;
 const client={async request(method,params){
  calls.push({method,params});
  if(method==='Input.dispatchMouseEvent'||method==='Input.dispatchKeyEvent')return{};
  if(method==='Accessibility.getFullAXTree')return{nodes:[{}]};
  if(method==='DOMSnapshot.captureSnapshot')return{documents:[{}]};
  if(method==='Page.captureScreenshot')return{data:Buffer.from('injected placeholder, not PNG evidence').toString('base64')};
  if(method==='Runtime.evaluate'){
   if(params.expression.includes('const e=document.querySelector'))return{result:{value:structuredClone(anchor)}};
   if(params.expression.includes("origin:'CDP DOM tab-hit'"))return{result:{value:structuredClone(probe)}};
   if(params.expression.includes('document.title'))return{result:{value:JSON.stringify({editorCount:1,visibleHovers:[]})}};
   if(params.expression.includes('const nodes=')){reads++;afterRead({reads,directory});return{result:{value:structuredClone(menu)}};}
  }
  throw Error('Unexpected fake CDP request '+method);
 }};
 return{root,directory,value,row,binding,owner,config,anchor,point,probe,client,calls,metadata,context:{root,runId:'run',sourceHead:config.sourceHead}};
}
async function admitted(t,target='local'){
 const f=sample(t,target),metadataHash=createHash('sha256').update(JSON.stringify(f.metadata)).digest('hex');
 const captured=await renderer.captureContributionMenuWithTabHit(f.client,f.directory,f.metadata,f.context);
 f.row.tabOwnership=f.owner;f.row.tabAfter=structuredClone(f.owner);f.row.capture={status:'captured',runId:'run',phase:'menus-tab',metadataHash,capture:captured};f.value.tabHitAdmissionMode=hit.version;
 return f;
}
function errors(f,value=f.value){return lifecycle.validateTabHitCurrent(value,'run',f.config.target,'/',undefined,f.config.sourceHead);}
function result(f,value=f.value){return{schemaVersion:1,runId:'run',target:f.config.target,scenarios:[{id:'native-contribution-menus',status:'partial',observation:value}],checks:[],status:'passed-with-gaps'};}
for(const target of ['local','dafny'])test('recorded '+target+' tuple roundtrips through wrapper and strict host admission',async t=>{
 const f=await admitted(t,target),a=f.row.capture.capture.contributionMenu.tabHitAdmission;
 assert.deepEqual(errors(f),[]);assert.deepEqual(hostEvidenceErrors(result(f),f.config),[]);
 assert.deepEqual(a.anchorRecord,JSON.parse(fs.readFileSync(path.join(f.directory,'menu-anchor.json'),'utf8')));assert.deepEqual(a.hitRecord,JSON.parse(fs.readFileSync(path.join(f.directory,'menu-tab-hit.json'),'utf8')));
 assert.equal(f.row.capture.metadataHash,createHash('sha256').update(JSON.stringify(f.metadata)).digest('hex'));
 assert.deepEqual(f.calls.filter(c=>c.method.startsWith('Input.')).map(c=>c.params.type),['mousePressed','mouseReleased','keyDown','keyUp','keyDown','keyUp']);
});
const mutations={
 missing:m=>delete m.tabHitAdmission,version:m=>m.tabHitAdmission.version='other',extra:m=>m.tabHitAdmission.extra=true,
 anchorBinding:m=>m.tabHitAdmission.anchorRecord.binding.session='foreign',hitBinding:m=>m.tabHitAdmission.hitRecord.binding.sourceHash='0'.repeat(64),
 kind:m=>m.tabHitAdmission.anchorRecord.kind='editor',status:m=>m.tabHitAdmission.anchorRecord.status='failed',
 point:m=>{m.tabHitAdmission.anchorRecord.point.x++;m.tabHitAdmission.hitRecord.probe.point.x++;},
 geometry:m=>m.tabHitAdmission.hitRecord.probe.rect.left++,viewport:m=>m.tabHitAdmission.hitRecord.probe.viewport.width++,
 opacity:m=>m.tabHitAdmission.hitRecord.probe.styleChain[0].opacity='0',style:m=>m.tabHitAdmission.hitRecord.probe.styleChain=[],
 occluded:m=>m.tabHitAdmission.hitRecord.probe.hitOwned=false,publicResource:m=>m.tabHitAdmission.hitRecord.probe.tabResourceLabels=['/foreign'],
 lifetime:m=>m.tabHitAdmission.hitRecord.probe.rendererLifetime.timeOrigin++,
 endpointLifetime:m=>{m.tabHitAdmission.anchorRecord.anchor.rendererLifetime.timeOrigin++;m.tabHitAdmission.hitRecord.probe.rendererLifetime.timeOrigin++;}
};
for(const [name,change] of Object.entries(mutations))test('strict replay refuses '+name+' without repairing observations',async t=>{
 const f=await admitted(t),value=structuredClone(f.value),row=value.phases.find(r=>r.phase==='tab');change(row.capture.capture.contributionMenu);const before=JSON.stringify(value);
 assert.ok(errors(f,value).length);assert.ok(hostEvidenceErrors(result(f,value),f.config).length);assert.equal(JSON.stringify(value),before);
});
for(const change of [v=>delete v.tabHitAdmissionMode,v=>v.tabHitAdmissionMode='other',v=>v.phases[0].capture.capture.contributionMenu.tabHitAdmission=structuredClone(v.phases[3].capture.capture.contributionMenu.tabHitAdmission),v=>v.phases[3].capture.metadataHash='0'.repeat(64)])test('strict mode and transport mismatch refuses',async t=>{
 const f=await admitted(t),v=structuredClone(f.value);change(v);const base=lifecycle.validateCurrent(v,'run','local','/',undefined,f.config.sourceHead),strict=errors(f,v);assert.ok(strict.length);for(const error of base)assert.ok(strict.includes(error));assert.ok(hostEvidenceErrors(result(f,v),f.config).length);
});
test('strict profile never falls back; ordinary legacy validator and fixture stay unchanged',async t=>{
 const f=await admitted(t),legacy=structuredClone(f.value);delete legacy.tabHitAdmissionMode;delete legacy.phases[3].capture.capture.contributionMenu.tabHitAdmission;
 assert.deepEqual(lifecycle.validateCurrent(legacy,'run','local','/',undefined,f.config.sourceHead),[]);assert.ok(errors(f,legacy).length);
 const config={...f.config};delete config.menuTabHit;assert.deepEqual(hostEvidenceErrors(result(f,legacy),config),[]);assert.ok(hostEvidenceErrors(result(f),config).includes('Tab-hit launch mode differs'));
 for(const menuTabHit of [null,'unknown'])assert.ok(hostEvidenceErrors(result(f),{...f.config,menuTabHit}).length);
 for(const extra of [{menuTrust:'transitions'},{menuAnchor:'visible-scrollport-v1'}])assert.ok(hostEvidenceErrors(result(f),{...f.config,...extra}).length);
});
for(const file of ['menu-anchor.json','menu-tab-hit.json'])for(const malformed of [false,true])test('wrapper refuses '+(malformed?'malformed ':'missing ')+file,async t=>{
 const f=sample(t,'local','tab',({reads,directory})=>{if(reads===2){const p=path.join(directory,file);if(malformed)fs.writeFileSync(p,'not JSON');else fs.unlinkSync(p);}});
 await assert.rejects(renderer.captureContributionMenuWithTabHit(f.client,f.directory,f.metadata,f.context));
 assert.deepEqual(f.calls.filter(c=>c.method.startsWith('Input.')).map(c=>c.params.type),['mousePressed','mouseReleased','keyDown','keyUp','keyDown','keyUp']);
});
test('companion preserves non-tab route without requiring tab artifacts',async t=>{
 const f=sample(t,'local','editor');const captured=await renderer.captureContributionMenuWithTabHit(f.client,f.directory,f.metadata,f.context);assert.equal(Object.hasOwn(captured.contributionMenu,'tabHitAdmission'),false);assert.equal(fs.existsSync(path.join(f.directory,'menu-tab-hit.json')),false);
});
test('ordinary base capture remains receipt-free',async t=>{
 const f=sample(t);const captured=await renderer.captureContributionMenu(f.client,f.directory,f.metadata,f.context);assert.equal(Object.hasOwn(captured.contributionMenu,'tabHitAdmission'),false);
});
test('profile parse is explicit, serial and rejects unsupported compositions',()=>{
 const base=['--suite','contribution-menus','--workers','1','--obligations','1','--trials','1','--warmups','0'];assert.equal(parse(base).menuTabHit,undefined);assert.equal(parse([...base,'--menu-tab-hit',hit.version]).menuTabHit,hit.version);
 for(const extra of [['--menu-tab-hit','other'],['--menu-tab-hit',hit.version,'--menu-anchor','visible-scrollport-v1'],['--menu-tab-hit',hit.version,'--menu-trust','transitions'],['--menu-tab-hit',hit.version,'--suite','full'],['--menu-tab-hit',hit.version,'--workers','2']])assert.throws(()=>parse([...base,...extra]));
});
