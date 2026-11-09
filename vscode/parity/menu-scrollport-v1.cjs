// H199 versioned virtual-editor admission; original point and strict path retained.
// DOM/hit endpoints only: no raster or mutation-ABA certification.
'use strict';
const assert=require('node:assert/strict');
const version='visible-scrollport-v1';
function observe(point){
 const e=document.querySelector('.editor-group-container.active .monaco-editor .view-lines'),owner=e?.closest('.monaco-editor'),group=e?.closest('.editor-group-container.active'),scrollport=e?.closest('.monaco-scrollable-element');
 const rect=e=>{const r=e.getBoundingClientRect();return{left:r.left,top:r.top,right:r.right,bottom:r.bottom,width:r.width,height:r.height};},describe=e=>e?{tag:e.tagName,id:e.id,className:typeof e.className==='string'?e.className:null}:null;
 const editors=Array.from(group?.querySelectorAll('.monaco-editor[data-uri]')??[]).filter(x=>{const r=x.getBoundingClientRect();return r.width>0&&r.height>0;});
 const hit=document.elementFromPoint(point.x,point.y),clips=[];for(let a=e?.parentElement;a;a=a.parentElement){const s=getComputedStyle(a),x=/^(hidden|clip|scroll|auto)$/.test(s.overflowX),y=/^(hidden|clip|scroll|auto)$/.test(s.overflowY);if(x||y){const r=a.getBoundingClientRect();clips.push({element:describe(a),scrollport:a===scrollport,x,y,rect:{left:r.left+a.clientLeft,top:r.top+a.clientTop,right:r.left+a.clientLeft+a.clientWidth,bottom:r.top+a.clientTop+a.clientHeight},transform:s.transform});}}
 const opacityChain=[];for(let a=e;a;a=a.parentElement)opacityChain.push({element:describe(a),opacity:getComputedStyle(a).opacity});
 const style=x=>x?{display:getComputedStyle(x).display,visibility:getComputedStyle(x).visibility}:null;
 return{version:'visible-scrollport-v1',origin:'CDP DOM visible-scrollport-v1',point,rendererLifetime:{timeOrigin:performance.timeOrigin,url:location.href},anchorRect:e?rect(e):null,viewport:{width:innerWidth,height:innerHeight},ownerUri:owner?.getAttribute('data-uri')??null,ownedEditor:!!owner&&editors.length===1&&editors[0]===owner,ownedScrollport:!!scrollport&&owner?.contains(scrollport)&&scrollport.contains(e),anchorStyle:style(e),scrollportStyle:style(scrollport),opacityChain,hit:describe(hit),hitOwned:!!hit&&!!e&&(hit===e||e.contains(hit))&&hit.closest('.monaco-editor')===owner,hitOwnerUri:hit?.closest('.monaco-editor')?.getAttribute('data-uri')??null,clips};
}
function point(anchor,uri){
 const r=anchor?.rect,v=anchor?.viewport;assert.equal(anchor?.activeUri,uri,'Foreign visible-scrollport source');assert.ok(r&&v&&['left','top','right','bottom','width','height'].every(k=>Number.isFinite(r[k]))&&[v.width,v.height].every(n=>Number.isFinite(n)&&n>0)&&r.width>0&&r.height>0&&r.right>r.left&&r.bottom>r.top,'Invalid visible-scrollport geometry');
 assert.ok(Math.abs(r.right-r.left-r.width)<0.01&&Math.abs(r.bottom-r.top-r.height)<0.01,'Inconsistent visible-scrollport rectangle');
 return{x:r.left+Math.min(60,r.width/2),y:r.top+Math.min(12,r.height/2)};
}
function admit(probe,anchor,uri){
 const p=point(anchor,uri);assert.equal(probe?.version,version);assert.equal(probe.origin,'CDP DOM visible-scrollport-v1');assert.deepEqual(probe.point,p);assert.deepEqual(probe.anchorRect,anchor.rect);assert.deepEqual(probe.viewport,anchor.viewport);
 assert.equal(probe.ownerUri,uri);assert.equal(probe.ownedEditor,true);assert.equal(probe.ownedScrollport,true);assert.equal(probe.hitOwned,true);assert.equal(probe.hitOwnerUri,uri);assert.ok(probe.hit&&typeof probe.hit.tag==='string');
 assert.ok(Number.isFinite(probe.rendererLifetime?.timeOrigin)&&probe.rendererLifetime.timeOrigin>0&&String(probe.rendererLifetime.url).startsWith('vscode-file:'),'Missing renderer lifetime');
 for(const style of [probe.anchorStyle,probe.scrollportStyle])assert.ok(style&&style.display!=='none'&&!['hidden','collapse'].includes(style.visibility),'Hidden menu anchor/scrollport');
 assert.ok(Array.isArray(probe.opacityChain)&&probe.opacityChain.length>0,'Missing observed opacity ancestry');let opacity=1;for(let index=0;index<probe.opacityChain.length;index++){assert.ok(Object.hasOwn(probe.opacityChain,index),'Sparse opacity ancestry');const entry=probe.opacityChain[index],value=Number(entry?.opacity);assert.ok(entry?.element&&typeof entry.opacity==='string'&&entry.opacity.trim()===entry.opacity&&/^(?:\d+(?:\.\d*)?|\.\d+)(?:[eE][+-]?\d+)?$/.test(entry.opacity)&&Number.isFinite(value)&&value>=0&&value<=1,'Invalid observed opacity');opacity*=value;}assert.ok(opacity>0,'Transparent menu anchor ancestry');
 const clip={left:0,top:0,right:anchor.viewport.width,bottom:anchor.viewport.height};assert.ok(Array.isArray(probe.clips)&&probe.clips.some(c=>c.scrollport),'Missing observed clipping scrollport');
 for(const c of probe.clips){assert.ok(typeof c.x==='boolean'&&typeof c.y==='boolean'&&(c.x||c.y)&&c.element&&['left','top','right','bottom'].every(k=>Number.isFinite(c.rect?.[k]))&&c.rect.right>c.rect.left&&c.rect.bottom>c.rect.top,'Invalid observed clip');assert.ok(c.transform==='none'||/^matrix\(1,\s*0,\s*0,\s*1,\s*0,\s*0\)$/.test(c.transform),'Transformed clipping ancestor not supported');if(c.x){clip.left=Math.max(clip.left,c.rect.left);clip.right=Math.min(clip.right,c.rect.right);}if(c.y){clip.top=Math.max(clip.top,c.rect.top);clip.bottom=Math.min(clip.bottom,c.rect.bottom);}}
 assert.ok(p.x>clip.left&&p.x<clip.right&&p.y>clip.top&&p.y<clip.bottom,'Original mouse point outside observed clip');return{version,checkpoint:'before-native-press',point:p,clip,probe};
}
module.exports={version,observe,point,admit};
