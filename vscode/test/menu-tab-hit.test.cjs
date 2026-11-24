// Synthetic DOM/hit endpoints only; no native or raster evidence.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),vm=require('node:vm'),{observe,assertHit}=require('../parity/menu-tab-hit.cjs');
function fixture(){
 const uri='file:///owned/menus.sol',resourcePath='/owned/menus.sol',rect={left:10,top:20,right:210,bottom:120,width:200,height:100},point={x:30,y:40},label={getAttribute:()=>resourcePath},editor={getBoundingClientRect:()=>rect,getAttribute:()=>uri},child={tagName:'SPAN'},overlay={tagName:'DIV',id:'overlay'};
 const group={querySelectorAll:s=>s.includes('monaco-editor')?[editor]:[tab]},tab={tagName:'DIV',getBoundingClientRect:()=>rect,closest:()=>group,contains:e=>e===child,getAttribute:()=> 'true',querySelectorAll:()=>[label]},document={querySelector:()=>tab,elementFromPoint:()=>child};
 const read=()=>JSON.parse(JSON.stringify(vm.runInNewContext('('+observe.toString()+')('+JSON.stringify(point)+')',{document,innerWidth:1000,innerHeight:800})));
 return{uri,resourcePath,rect,point,child,tab,overlay,group,document,read,anchor:{rect,viewport:{width:1000,height:800}},owner:{uri,resourcePath}};
}
test('original tab or descendant owns the unchanged resource-bound point',()=>{const f=fixture();assertHit(f.read(),f.anchor,f.point,f.owner);f.document.elementFromPoint=()=>f.tab;assertHit(f.read(),f.anchor,f.point,f.owner);});
for(const [name,change] of Object.entries({overlay:f=>f.document.elementFromPoint=()=>f.overlay,missing:f=>f.document.elementFromPoint=()=>null,foreignResource:f=>f.owner.uri='file:///other/menus.sol',foreignPath:f=>f.owner.resourcePath='/other/menus.sol',point:f=>f.point={x:31,y:40},geometry:f=>f.anchor.rect={...f.rect,left:11},viewport:f=>f.anchor.viewport.width=999,unselected:f=>f.tab.getAttribute=()=> 'false',ambiguous:f=>f.group.querySelectorAll=()=>[f.tab,f.tab]}))test('tab hit refuses '+name,()=>{const f=fixture(),probe=f.read();change(f);assert.throws(()=>assertHit(['overlay','missing','unselected','ambiguous'].includes(name)?f.read():probe,f.anchor,f.point,f.owner));});
