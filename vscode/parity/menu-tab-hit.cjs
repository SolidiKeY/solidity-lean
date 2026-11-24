// DOM hit endpoint at the original tab mouse point; no raster or mutation-ABA claim.
'use strict';
const assert=require('node:assert/strict');
function observe(point){
 const tab=document.querySelector('.editor-group-container.active .tabs-container .tab.active'),group=tab?.closest('.editor-group-container.active');
 const visible=nodes=>Array.from(nodes??[]).filter(e=>{const r=e.getBoundingClientRect();return r.width>0&&r.height>0;});
 const tabs=visible(group?.querySelectorAll('.tabs-container .tab.active')),editors=visible(group?.querySelectorAll('.monaco-editor[data-uri]'));
 const hit=document.elementFromPoint(point.x,point.y),r=tab?.getBoundingClientRect();
 return{origin:'CDP DOM tab-hit',point,ownedTab:!!tab&&tabs.length===1&&tabs[0]===tab,hitOwned:!!tab&&!!hit&&(hit===tab||tab.contains(hit)),activeUri:editors.length===1?editors[0].getAttribute('data-uri'):null,tabSelected:tab?.getAttribute('aria-selected')??null,tabResourceLabels:Array.from(tab?.querySelectorAll('.tab-label[aria-label]')??[]).map(e=>e.getAttribute('aria-label')),rect:r?{left:r.left,top:r.top,right:r.right,bottom:r.bottom,width:r.width,height:r.height}:null,viewport:{width:innerWidth,height:innerHeight},hit:hit?{tag:hit.tagName??null,id:hit.id??null,className:typeof hit.className==='string'?hit.className:null}:null};
}
function assertHit(probe,anchor,point,owner){
 assert.equal(probe?.origin,'CDP DOM tab-hit');assert.deepEqual(probe.point,point,'Tab hit point changed');
 assert.equal(probe.ownedTab,true,'Tab hit owner unavailable');assert.equal(probe.hitOwned,true,'Original tab mouse point is occluded');
 assert.deepEqual(probe.rect,anchor.rect,'Tab geometry changed before input');assert.deepEqual(probe.viewport,anchor.viewport,'Tab viewport changed before input');
 require('./menu-tab-ownership.cjs').assertDOM(probe,owner);
}
module.exports={observe,assertHit};
