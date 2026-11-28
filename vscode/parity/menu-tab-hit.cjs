// DOM hit endpoint at the original tab mouse point; no raster or mutation-ABA claim.
'use strict';
const assert=require('node:assert/strict');
function observe(point){
 const tab=document.querySelector('.editor-group-container.active .tabs-container .tab.active'),group=tab?.closest('.editor-group-container.active');
 const visible=nodes=>Array.from(nodes??[]).filter(e=>{const r=e.getBoundingClientRect();return r.width>0&&r.height>0;});
 const tabs=visible(group?.querySelectorAll('.tabs-container .tab.active')),editors=visible(group?.querySelectorAll('.monaco-editor[data-uri]'));
 const hit=document.elementFromPoint(point.x,point.y),r=tab?.getBoundingClientRect(),styleChain=[];
 for(let e=tab;e;e=e.parentElement){const s=getComputedStyle(e);styleChain.push({tag:e.tagName??null,display:s.display,visibility:s.visibility,opacity:s.opacity});}
 return{origin:'CDP DOM tab-hit',rendererLifetime:{timeOrigin:performance.timeOrigin,url:location.href},point,styleChain,ownedTab:!!tab&&tabs.length===1&&tabs[0]===tab,hitOwned:!!tab&&!!hit&&(hit===tab||tab.contains(hit)),activeUri:editors.length===1?editors[0].getAttribute('data-uri'):null,tabSelected:tab?.getAttribute('aria-selected')??null,tabResourceLabels:Array.from(tab?.querySelectorAll('.tab-label[aria-label]')??[]).map(e=>e.getAttribute('aria-label')),rect:r?{left:r.left,top:r.top,right:r.right,bottom:r.bottom,width:r.width,height:r.height}:null,viewport:{width:innerWidth,height:innerHeight},hit:hit?{tag:hit.tagName??null,id:hit.id??null,className:typeof hit.className==='string'?hit.className:null}:null};
}
function assertHit(probe,anchor,point,owner){
 assert.equal(probe?.origin,'CDP DOM tab-hit');
 const lifetime=probe.rendererLifetime;assert.ok(Number.isFinite(lifetime?.timeOrigin)&&lifetime.timeOrigin>0&&typeof lifetime.url==='string'&&lifetime.url.startsWith('vscode-file:'),'Missing tab renderer lifetime');
 assert.deepEqual(lifetime,anchor.rendererLifetime,'Renderer restarted before tab menu input');assert.deepEqual(probe.point,point,'Tab hit point changed');
 assert.equal(probe.ownedTab,true,'Tab hit owner unavailable');assert.equal(probe.hitOwned,true,'Original tab mouse point is occluded');
 assert.deepEqual(probe.rect,anchor.rect,'Tab geometry changed before input');assert.deepEqual(probe.viewport,anchor.viewport,'Tab viewport changed before input');
 assert.ok(Array.isArray(probe.styleChain)&&probe.styleChain.length>0,'Missing tab style ancestry');
 for(let i=0;i<probe.styleChain.length;i++){
  assert.ok(Object.hasOwn(probe.styleChain,i),'Sparse tab style ancestry');const s=probe.styleChain[i],opacity=Number(s?.opacity);
  assert.ok(typeof s?.display==='string'&&s.display.length>0&&s.display!=='none','Hidden tab ancestry');
  assert.ok(typeof s?.opacity==='string'&&s.opacity.trim()===s.opacity&&/^(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?$/.test(s.opacity)&&Number.isFinite(opacity)&&opacity>0&&opacity<=1,'Transparent or invalid tab opacity');
 }
 assert.equal(probe.styleChain[0].visibility,'visible','Hidden tab visibility');
 require('./menu-tab-ownership.cjs').assertDOM(probe,owner);
}
const version='tab-hit-endpoint';
// Replay recorded endpoints only; this does not authenticate input or raster output.
function assertAdmission(admission,binding,owner,before,after){
 assert.ok(admission&&typeof admission==='object'&&!Array.isArray(admission),'Missing tab-hit admission');
 assert.deepEqual(Reflect.ownKeys(admission).sort(),['anchorRecord','hitRecord','version']);
 assert.equal(admission.version,version,'Unknown tab-hit admission version');
 const {anchorRecord:a,hitRecord:h}=admission;
 assert.equal(a?.kind,'tab');assert.equal(a.status,'admitted');
 assert.deepEqual(a.binding,binding,'Foreign tab anchor binding');assert.deepEqual(h?.binding,binding,'Foreign tab hit binding');
 assert.deepEqual(a.point,require('./menu-lifecycle.cjs').menuAnchorPoint(a.anchor,binding.uri),'Tab anchor point changed');
 require('./menu-tab-ownership.cjs').assertDOM(a.anchor,owner);
 assertHit(h.probe,a.anchor,a.point,owner);
 assert.deepEqual(h.probe.rendererLifetime,before?.rendererLifetime,'Tab before lifetime changed');
 assert.deepEqual(h.probe.rendererLifetime,after?.rendererLifetime,'Tab after lifetime changed');
}
module.exports={observe,assertHit,version,assertAdmission};
