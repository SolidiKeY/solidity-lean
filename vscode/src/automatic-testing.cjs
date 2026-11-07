// Testing UI projection only. Never starts verification or grants proof/cache authority.
'use strict';
const model=require('./model.cjs');
function install({vscode,controller,itemsFor,cancel,current}){
 const documents=new Map(),manual=new Map();let disposed=false;
 const id=doc=>doc.uri.toString();
 function state(doc){const key=id(doc);let value=documents.get(key);if(value?.doc!==doc||value.version!==doc.version||value.text!==doc.getText()){clear(key);value={doc,version:doc.version,text:doc.getText(),seen:new Map(),group:null,blocked:false};documents.set(key,value);}return value;}
 function finish(group){if(group.ended)return;group.ended=true;group.registration?.dispose();group.run.end();}
 function settle(value,kind='skipped',message='Document verification stopped'){
  const group=value?.group;if(!group)return;
  for(const item of group.pending.values())kind==='errored'?group.run.errored(item,new vscode.TestMessage(message)):group.run.skipped(item);
  group.pending.clear();finish(group);value.group=null;
 }
 function clear(key){const value=documents.get(key);if(value){settle(value);documents.delete(key);}}
 function group(value){if(value.group&&!value.group.ended)return value.group;
  const run=controller.createTestRun(new vscode.TestRunRequest(itemsFor(value.doc)||[]), 'Automatic Solidity outcomes', false),g={run,pending:new Map(),startedAt:new Map(),ended:false};value.group=g;
  g.registration=run.token.onCancellationRequested(()=>{if(g.ended)return;value.blocked=true;const owned=current(value.doc)&&documents.get(id(value.doc))===value&&value.doc.version===value.version&&value.doc.getText()===value.text;settle(value);if(owned)cancel(value.doc.uri);});return g;
 }
 function report(doc,rows,errors=[]){if(disposed)return;const value=state(doc),items=itemsFor(doc);if(!items)return;value.phase="complete";
  const present=new Set(items.map(item=>item.id));
  for(const key of value.seen.keys())if(!present.has(key))value.seen.delete(key);
  if(value.group)for(const [key,item]of value.group.pending)if(!present.has(key)){value.group.run.skipped(item);value.group.pending.delete(key);}
  for(const item of items){const row=rows.find(row=>item.id===itemId(doc,row));if(!row)continue;
   const fingerprint=JSON.stringify([row,errors]),old=value.seen.get(item.id);value.seen.set(item.id,fingerprint);
   if(old===fingerprint||row.status==='ready'||manual.has(id(doc))||value.blocked||value.hidden)continue;
   const g=group(value),kind=errors.length?'errored':model.resultKind(row),duration=row.elapsedMs??(g.startedAt.has(item.id)?Math.max(0,performance.now()-g.startedAt.get(item.id)):undefined);if(kind==='passed')g.run.passed(item,duration);else if(kind==='skipped')g.run.skipped(item);else g.run[kind](item,new vscode.TestMessage(errors.length?errors.map(error=>error.reason).join('\n'):model.detail(row)),duration);g.pending.delete(item.id);g.startedAt.delete(item.id);
  }
  if(value.group&&!value.group.pending.size){finish(value.group);value.group=null;}
 }
 function status(doc,params){if(disposed)return;const value=state(doc);
  if(params.state==='cancelled'||params.state==='error'){value.phase=params.state;value.blocked=true;settle(value,params.state==='error'?'errored':'skipped',params.message||'Document operation failed');return;}
  if(params.state==='queued'&&value.phase!=='queued'){settle(value);value.seen.clear();value.blocked=false;}value.phase=params.state;
  if(manual.has(id(doc))||value.blocked||value.hidden||params.progressScope!=='functions')return;
  const items=itemsFor(doc)||[];
  for(const row of params.functions||[]){if(!['queued','running','stale','cancelled','skip','skipped','internal'].includes(row.status))continue;
   const item=items.find(item=>item.label===row.name&&sameRange(item.range,row.range));if(!item)continue;
   if(!['queued','running'].includes(row.status)&&!value.group?.pending.has(item.id))continue;
   const fingerprint=JSON.stringify(['progress',row.status]);if(value.seen.get(item.id)===fingerprint)continue;value.seen.set(item.id,fingerprint);
   const g=group(value);if(row.status==='queued'||row.status==='running'){g.pending.set(item.id,item);if(row.status==='queued')g.run.enqueued(item);else{g.startedAt.set(item.id,performance.now());g.run.started(item);}}else{g.run.skipped(item);g.pending.delete(item.id);}
  }
  if(value.group&&!value.group.pending.size){finish(value.group);value.group=null;}
 }
 function claim(uris){for(const uri of uris){const key=uri.toString();manual.set(key,(manual.get(key)||0)+1);settle(documents.get(key));}let released=false;return()=>{if(released)return;released=true;for(const uri of uris){const key=uri.toString(),count=manual.get(key)||0;if(count<=1)manual.delete(key);else manual.set(key,count-1);}};}
 return{report,status,clear,claim,
  stop(uri){for(const [key,value]of documents)if(!uri||key===uri.toString()){value.blocked=true;settle(value);}},
  begin(doc){const value=state(doc);value.blocked=false;value.seen.clear();},
  visible(doc,visible){const value=state(doc);value.hidden=!visible;if(!visible)settle(value);},
  dispose(){disposed=true;for(const key of [...documents.keys()])clear(key);manual.clear();}};
}
function sameRange(a,b){return !!a&&!!b&&['start','end'].every(end=>a[end]?.line===b[end]?.line&&a[end]?.character===b[end]?.character);}
function itemId(doc,row){return `${doc.uri.toString()}#${encodeURIComponent(row.contract)}:${encodeURIComponent(row.signature||row.function)}`;}
module.exports={install};
