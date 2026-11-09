// Guard regression: a selected tab must not borrow the neighboring editor URI.
// Public TabInputText ownership joins the observed full-path tab accessibility label.
// File-only endpoints; no filename inference, raster or mutation-ABA guarantee.
'use strict';
const assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),{fileURLToPath,pathToFileURL}=require('node:url'),{createHash,randomUUID}=require('node:crypto');
const filename='menu-tab-owner.json';
function canonicalResourcePath(uri){const url=new URL(uri);assert.ok(url.protocol==='file:'&&!url.hostname&&!url.search&&!url.hash,'Unsupported public tab URI');const file=fileURLToPath(uri);assert.equal(pathToFileURL(file).href,uri,'Noncanonical public tab URI');return file;}
function snapshot(vscode,doc,identity,epoch){
 const groups=vscode.window.tabGroups,group=groups?.activeTabGroup,tab=group?.activeTab,editor=vscode.window.activeTextEditor;
 assert.ok(groups?.all.includes(group)&&groups.all.filter(g=>g.isActive).length===1&&group.isActive&&tab?.isActive&&group.tabs.includes(tab)&&group.tabs.filter(t=>t.isActive).length===1,'Public active tab/group unavailable');
 assert.ok(typeof vscode.TabInputText==='function'&&tab.input instanceof vscode.TabInputText,'Public tab is not a text resource');
 const uri=tab.input.uri.toString(),resourcePath=canonicalResourcePath(uri);
 assert.ok(doc.uri.scheme==='file'&&!doc.isClosed&&editor?.document===doc&&uri===doc.uri.toString(),'Public tab/document resource mismatch');
 assert.ok(Number.isSafeInteger(group.viewColumn)&&group.viewColumn>0&&editor.viewColumn===group.viewColumn&&typeof tab.isDirty==='boolean'&&tab.isDirty===doc.isDirty,'Public tab column/dirty state mismatch');
 return{origin:'vscode.window.tabGroups',...identity,epoch,uri,resourcePath,viewColumn:group.viewColumn,activeTabIndex:group.tabs.indexOf(tab),tabCount:group.tabs.length,dirty:tab.isDirty,source:{uri:doc.uri.toString(),version:doc.version,session:identity.documentSession,sourceHash:createHash('sha256').update(doc.getText()).digest('hex'),dirty:doc.isDirty}};
}
function monitor(vscode,doc,config,documentSession){
 const identity={runId:config.runId,sourceHead:config.sourceHead,hostSession:config.menuHost?.hostSession,documentSession,nonce:randomUUID()},file=path.join(config.dir,filename),journal=path.join(config.dir,'menu-tab-ownership.jsonl'),subscriptions=[];let epoch=0,initial,disposed=false,count=0,bytes=0;
 const append=value=>{const row=JSON.stringify({...value,wallTime:Date.now(),monotonicMs:require('node:perf_hooks').performance.now()})+'\n';if(++count>256||(bytes+=Buffer.byteLength(row))>1024*1024)throw Error('Public tab journal bound exceeded');fs.appendFileSync(journal,row);};
 const save=value=>{require('./phase-capture.cjs').atomicJson(file,value);try{append(value);}catch(error){require('./phase-capture.cjs').atomicJson(file,{status:'failed',...identity,epoch,error:error.message});throw error;}};
 const changed=kind=>{epoch++;let state;try{state=JSON.parse(fs.readFileSync(file,'utf8'));}catch(error){append({status:'failed',...identity,epoch,event:kind,error:error.message});return;}if(state.nonce!==identity.nonce){append({status:'failed',...identity,epoch,event:kind,error:'New owner record retained'});return;}let observed,error;try{observed=snapshot(vscode,doc,identity,epoch);}catch(e){error=e.message;}save({status:'failed',...identity,epoch,event:kind,observed,error:error??'Public tab epoch changed'});};
 const dispose=()=>{if(disposed)return;disposed=true;const errors=[];try{const state=JSON.parse(fs.readFileSync(file,'utf8'));if(state.nonce===identity.nonce)save({status:'retired',...identity,epoch,observed:initial});else append({status:'retired',...identity,epoch,error:'New owner record retained'});}catch(e){errors.push(e);}for(const s of subscriptions)try{s.dispose();}catch(e){errors.push(e);}if(errors.length)throw new AggregateError(errors,'Public tab observer cleanup failed');};
 try{assert.match(identity.sourceHead,/^[a-f0-9]{40}$/);assert.ok(identity.hostSession&&documentSession,'Missing public tab host/document epoch');subscriptions.push(vscode.window.tabGroups.onDidChangeTabs(()=>changed('tabs')));subscriptions.push(vscode.window.tabGroups.onDidChangeTabGroups(()=>changed('groups')));subscriptions.push(vscode.workspace.onDidChangeTextDocument(event=>{if(event.document===doc&&event.contentChanges.length)changed('document');}));subscriptions.push(vscode.workspace.onDidCloseTextDocument(closed=>{if(closed===doc)changed('close');}));initial=snapshot(vscode,doc,identity,epoch);assert.equal(epoch,0,'Public tab epoch changed during admission');save({status:'current',...identity,epoch,observed:initial});}
 catch(error){const cleanup=[];try{save({status:'failed',...identity,epoch,error:error.message});}catch(e){cleanup.push('failure recording: '+e.message);}finally{for(const s of subscriptions)try{s.dispose();}catch(e){cleanup.push('listener disposal: '+e.message);}}if(cleanup.length){error.cleanupErrors=cleanup;try{require('./phase-capture.cjs').atomicJson(file,{status:'failed',...identity,epoch,error:error.message,cleanupErrors:cleanup});}catch(e){cleanup.push('final failure recording: '+e.message);}}throw error;}
 return{initial,assertCurrent(){assert.equal(disposed,false,'Public tab observer retired');assert.equal(epoch,0,'Public tab epoch changed');assert.deepEqual(snapshot(vscode,doc,identity,epoch),initial,'Public tab ownership changed');return initial;},dispose};
}
function assertObservation(o,binding,context){
 assert.equal(o?.origin,'vscode.window.tabGroups');assert.equal(o.runId,context.runId);if(context.sourceHead!==undefined)assert.equal(o.sourceHead,context.sourceHead);assert.match(o.sourceHead,/^[a-f0-9]{40}$/);
 for(const key of ['hostSession','documentSession','nonce'])assert.ok(typeof o[key]==='string'&&o[key],'Missing public tab '+key);
 assert.equal(o.epoch,0);assert.equal(o.documentSession,binding.session);assert.equal(o.uri,binding.uri);assert.equal(o.source.uri,binding.uri);assert.equal(o.source.version,binding.version);assert.equal(o.source.session,binding.session);assert.equal(o.source.sourceHash,binding.sourceHash);assert.equal(typeof o.dirty,'boolean');assert.equal(o.source.dirty,o.dirty);
 assert.ok(Number.isSafeInteger(o.viewColumn)&&o.viewColumn>0&&Number.isSafeInteger(o.tabCount)&&o.tabCount>0&&Number.isSafeInteger(o.activeTabIndex)&&o.activeTabIndex>=0&&o.activeTabIndex<o.tabCount,'Invalid public tab group');
 assert.equal(o.resourcePath,canonicalResourcePath(o.uri));
}
function readCurrent(root,expected,binding,context){
 const file=path.join(root,filename),stat=fs.lstatSync(file);assert.ok(stat.isFile()&&!stat.isSymbolicLink()&&stat.size<=1024*1024,'Invalid public tab record');
 const state=JSON.parse(fs.readFileSync(file,'utf8'));assertObservation(expected,binding,context);
 assert.equal(state.status,'current','Public tab ownership invalidated');assert.equal(state.epoch,0);
 for(const key of ['runId','sourceHead','hostSession','documentSession','nonce'])assert.equal(state[key],expected[key],'Foreign public tab '+key);
 assert.deepEqual(state.observed,expected);return state;
}
function assertDOM(anchor,observation){assert.equal(anchor?.activeUri,observation.uri,'Tab/editor resource differs');assert.equal(anchor?.tabSelected,'true','Native tab is not selected');assert.deepEqual(anchor?.tabResourceLabels,[observation.resourcePath],'Native tab resource accessibility label differs');}
module.exports={snapshot,monitor,readCurrent,assertObservation,assertDOM,filename};
