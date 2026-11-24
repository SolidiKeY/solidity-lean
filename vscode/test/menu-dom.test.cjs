// DOM protocol fixtures only. No native menu or recovery admission evidence.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),vm=require('node:vm');
const fs=require('node:fs'),os=require('node:os'),path=require('node:path'),{createHash}=require('node:crypto');
const {observeMenuItems,recorder}=require('../parity/menu-dom.cjs');
const rect={left:1,top:2,right:100,bottom:20},viewport={width:800,height:600};
function element(label,attrs,menuItem=null){const e={tagName:'A',textContent:label,className:attrs.class,getAttribute:n=>attrs[n]??null,getBoundingClientRect:()=>rect,getClientRects:()=>[rect]};e.closest=q=>q==='[role=menuitem]'?menuItem:q==='[role]'?e:null;return e;}
function nodes(){const item={tagName:'DIV',className:'action-menu-item',getAttribute:n=>({role:'menuitem','aria-disabled':'false'}[n]??null)};return[element('Copy',{class:'action-label',role:'presentation'},item),element('',{class:'action-label codicon separator disabled',role:'presentation','aria-disabled':'true'})];}
function directory(t){const d=fs.mkdtempSync(path.join(os.tmpdir(),'menu-dom-'));t.after(()=>fs.rmSync(d,{recursive:true,force:true}));return d;}
test('serialized browser query retains legacy null owner and raw presentation attributes',()=>{
 const result=vm.runInNewContext('('+observeMenuItems.toString()+')(nodes,viewport)',{nodes:nodes(),viewport});
 const row=JSON.parse(JSON.stringify(result[1]));assert.deepEqual({...row,roleContext:undefined},{label:'',ariaDisabled:null,className:null,bounds:rect,withinViewport:true,roleContext:undefined});
 assert.equal(row.roleContext.menuItem,null);assert.equal(row.roleContext.label.role,'presentation');assert.equal(row.roleContext.label.ariaDisabled,'true');assert.equal(row.roleContext.nearestRole.className,'action-label codicon separator disabled');
});
test('sidecar joins ordered roles to exact legacy snapshot without changing it',t=>{
 const dir=directory(t),source={runId:'run',sourceHead:'head',binding:{uri:'file:///owned.sol',version:1,session:'doc',sourceHash:'hash'}},record=recorder(dir,source),snapshot={rendererLifetime:{timeOrigin:3,url:'vscode-file://owned'},activeUri:source.binding.uri,items:observeMenuItems(nodes(),viewport)};
 const expected={...snapshot,items:[{label:'Copy',ariaDisabled:'false',className:'action-menu-item',bounds:rect,withinViewport:true},{label:'',ariaDisabled:null,className:null,bounds:rect,withinViewport:true}]};
 source.runId='mutated';assert.deepEqual(record(snapshot),expected);record(snapshot);
 const saved=JSON.parse(fs.readFileSync(path.join(dir,'menu-roles.json')));assert.equal(saved.version,1);assert.equal(saved.reads.length,2);
 for(const [i,row]of saved.reads.entries()){assert.equal(row.index,i);assert.equal(row.context.runId,'run');assert.equal(row.context.sourceHead,'head');assert.equal(row.legacyStateSha256,createHash('sha256').update(JSON.stringify(expected)).digest('hex'));assert.equal(row.roles[1].menuItem,null);assert.equal(row.availability,'present');}
});
test('legacy-only fixtures and empty queries never fabricate role observations',t=>{
 const dir=directory(t),record=recorder(dir,{}),old={items:[{label:'Copy',className:null,ariaDisabled:null}]};assert.deepEqual(record(old),old);record({items:[]});
 const saved=JSON.parse(fs.readFileSync(path.join(dir,'menu-roles.json')));assert.equal(saved.reads[0].availability,'unavailable');assert.deepEqual(saved.reads[0].roles,[null]);assert.equal(saved.reads[1].availability,'empty');
});
test('role evidence write failures propagate instead of returning legacy success',t=>{
 const dir=directory(t);fs.writeFileSync(path.join(dir,'blocked'),'file');const record=recorder(path.join(dir,'blocked'),{});
 assert.throws(()=>record({items:observeMenuItems(nodes(),viewport)}),/ENOTDIR|not a directory/);
});

test('collector executes role query without changing legacy attributes (injected transport)',async t=>{
 const dir=directory(t),uri='file:///owned.sol',items=nodes();items[0].textContent='Solidity Lean';items.push(element('Build Compiler Artifact with Import Options',{class:'action-label',role:'presentation'}));
 const document={querySelectorAll:q=>q==='.monaco-menu .action-label'?items:[],querySelector:q=>q.includes('monaco-editor[data-uri]')?{getAttribute:()=>uri}:null};
 let first=true,reads=0;const client={async request(method,params){
  if(method==='Runtime.evaluate'){
   if(first){first=false;return{result:{value:{activeUri:uri,rect:{left:0,top:0,right:800,bottom:600,width:800,height:600},viewport:{width:1000,height:800}}}};}
   if(params.expression.startsWith('JSON.stringify('))return{result:{value:JSON.stringify({editorCount:1,visibleHovers:[]})}};
   reads++;return{result:{value:JSON.parse(JSON.stringify(vm.runInNewContext(params.expression,{document,performance:{timeOrigin:123},location:{href:'vscode-file://window'},innerWidth:1000,innerHeight:800})))}};
  }
  if(method==='Accessibility.getFullAXTree')return{nodes:[{}]};if(method==='DOMSnapshot.captureSnapshot')return{documents:[{}]};if(method==='Page.captureScreenshot')return{data:Buffer.from('synthetic transport only').toString('base64')};return{};
 }};
 const result=await require('../parity/renderer.cjs').captureContributionMenu(client,dir,{target:'local',kind:'editor',visible:true,binding:{uri}},{runId:'run',sourceHead:'head'});
 assert.equal(reads,3);assert.equal(result.contributionMenu.before.items[1].className,null);assert.equal('roleContext' in result.contributionMenu.before.items[1],false);
 const saved=JSON.parse(fs.readFileSync(path.join(dir,'menu-roles.json')));assert.equal(saved.reads.length,3);assert.equal(saved.reads[0].context.sourceHead,'head');assert.equal(saved.reads[0].roles[1].label.role,'presentation');assert.equal(saved.reads[0].roles[1].menuItem,null);
});
