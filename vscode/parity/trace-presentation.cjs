// Expected presentation from pinned verificationTraceView.ts; never a local trace producer.
'use strict';
const assert=require('node:assert/strict'),{createHash}=require('node:crypto');
const digest=value=>createHash('sha256').update(value).digest('hex');
function normalize(contentText){
 if(contentText.startsWith('assume '))contentText=contentText.substring(7);
 if(contentText.endsWith(';'))contentText=contentText.substring(0,contentText.length-1).trimEnd();
 return contentText.split(' && ').map(value=>{if(/^.* == [\w'?]+$/.test(value)){const parts=value.split(' == ');return parts[1]+' == '+parts[0];}return value;}).join(', ');
}
function wireDocument(records,end,uri){
 let state;
 const offset=(text,position)=>{const lines=text.split('\n');assert.ok(Number.isSafeInteger(position.line)&&position.line>=0&&position.line<lines.length);const line=lines[position.line].replace(/\r$/,'');assert.ok(Number.isSafeInteger(position.character)&&position.character>=0&&position.character<=line.length);return lines.slice(0,position.line).reduce((sum,line)=>sum+line.length+1,0)+position.character;};
 for(let i=0;i<end;i++){const r=records[i],m=r.message,p=m?.params;if(r.direction!=='client'||p?.textDocument?.uri!==uri)continue;
  if(m.method==='textDocument/didClose')state=undefined;
  if(m.method==='textDocument/didOpen')state={text:p.textDocument.text,version:p.textDocument.version,openIndex:i};
  if(m.method==='textDocument/didChange'){assert.ok(state,'wire change without open');assert.ok(p.textDocument.version>state.version);for(const change of p.contentChanges){if(!change.range)state.text=change.text;else{const start=offset(state.text,change.range.start),end=offset(state.text,change.range.end);assert.ok(end>=start);state.text=state.text.slice(0,start)+change.text+state.text.slice(end);}}state.version=p.textDocument.version;}
 }
 assert.ok(state,'no current wire document');return{...state,textHash:digest(state.text)};
}
function traceResponse(records,start,binding){
 const requests=records.slice(start).map((r,i)=>({r,index:start+i})).filter(({r})=>r.direction==='client'&&r.message?.method==='dafny/counterExample'&&r.message.params?.textDocument?.uri===binding.uri);
 assert.equal(requests.length,1,'one unambiguous native trace request required');const {r:request,index}=requests[0];
 const responseIndex=records.findIndex((r,i)=>i>index&&r.direction==='server'&&r.message?.id===request.message.id&&Object.hasOwn(r.message,'result'));
 assert.ok(responseIndex>index,'matching native trace response required');const response=records[responseIndex];assert.ok(Array.isArray(response.message.result));
 const wire=wireDocument(records,index,binding.uri);assert.equal(wire.version,binding.version,'wire version matches source');assert.equal(wire.textHash,binding.textHash,'wire text matches source');assert.equal(wire.openIndex,binding.protocolOpenIndex,'wire open lifetime matches source');
 // This URI-only protocol does not assert a source version. Only a stable interval may be attributed.
 const changes=records.slice(start,responseIndex+1).filter(r=>r.direction==='client'&&['textDocument/didOpen','textDocument/didChange','textDocument/didClose'].includes(r.message?.method)&&r.message.params?.textDocument?.uri===binding.uri);
 assert.equal(changes.length,0,'trace interval crossed a source lifetime/edit boundary');
 return{requestId:request.message.id,requestIndex:index,responseIndex,requestTime:request.time,responseTime:response.time,binding,result:response.message.result};
}
async function closeSourceTabs(vscode,doc){
 const tabs=vscode.window.tabGroups.all.flatMap(group=>group.tabs).filter(tab=>tab.input?.uri?.toString()===doc.uri.toString());assert.ok(tabs.length,'owned source tab exists');assert.equal(await vscode.window.tabGroups.close(tabs,true),true,'owned source tabs close through public API');return tabs.length;
}
function assertPresentation(observed,{binding,trace=[],shown,menu,colors={backgroundColor:'rgb(13, 71, 161)',color:'rgb(227, 242, 253)'}}){
 assert.ok(binding?.session&&binding.uri&&Number.isSafeInteger(binding.version)&&/^[a-f0-9]{64}$/.test(binding.textHash),'complete source binding required');
 assert.equal(observed.activeUri,binding.uri,'renderer active source URI');const annotations=observed.annotations.filter(a=>a.uri===binding.uri);
 const expected=shown?trace.filter(item=>item.position.line>=0).map(item=>({line:item.position.line+1,text:normalize(item.assumption)})):[];
 assert.deepEqual(annotations.map(a=>({line:a.line,text:a.text})).sort((a,b)=>a.line-b.line||a.text.localeCompare(b.text)),expected.sort((a,b)=>a.line-b.line||a.text.localeCompare(b.text)),'exact native annotation content/line or complete disappearance');
 for(const a of annotations){assert.equal(a.backgroundColor,colors.backgroundColor);assert.equal(a.color,colors.color);assert.equal(a.marginLeft,'30px');for(const side of ['marginTop','marginRight','marginBottom'])assert.equal(a[side],'0px');assert.ok(a.visible,'annotation pseudo-element is visible');}
 const labels=observed.menu.labels,show=labels.includes('Dafny: Show verification trace (experimental)'),hide=labels.includes('Dafny: Hide verification trace (experimental)');
 assert.notEqual(show,hide,'exactly one native Show/Hide action');assert.ok(labels.includes('Dafny: Copy verification trace as Dafny (experimental)'));
 if(menu)assert.equal(show,menu==='show','native menu transition');return{...observed,binding,expected,asserted:true};
}
module.exports={normalize,traceResponse,assertPresentation,digest,wireDocument,closeSourceTabs};
