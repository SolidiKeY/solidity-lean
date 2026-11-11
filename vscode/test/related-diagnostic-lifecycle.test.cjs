// Injected lifecycle envelopes, not native UI/proof evidence.
'use strict';
const {test}=require('node:test'),assert=require('node:assert/strict'),{performance}=require('node:perf_hooks');
const {fixture,config}=require('./related-diagnostics-fixture.cjs'),base=require('../parity/related-diagnostics.cjs'),{mode,errors,openViaUi}=require('../parity/related-diagnostic-lifecycle.cjs'),{createHash}=require('node:crypto');
const hash=s=>createHash('sha256').update(s).digest('hex'),c={...config,diagnosticInput:'public-eol-v1',diagnosticLifecycle:mode};
function lifetime(){
 const b=fixture(c.diagnosticInput),protocol=structuredClone(b.protocol),events=structuredClone(b.events),last=b.steps.at(-1),before=structuredClone(last.after),owner=last.process,uri=before.uri,fixed=base.textForInput('fixed',c.diagnosticInput),disk=text=>({text,bytes:Buffer.byteLength(text),sourceHash:hash(text)}),closeIndex=protocol.length;
 protocol.push({...owner,direction:'client',message:{method:'textDocument/didClose',params:{textDocument:{uri}}}});
 const close={status:'observed',before,afterSave:structuredClone(before),saveReturned:true,dirtyAfterSave:false,diskBefore:disk(base.source),diskAfter:disk(fixed),command:'workbench.action.closeActiveEditor',result:{closeEventObserved:true,oldDocumentClosed:true,oldDocumentListed:false},event:{objectMatched:true,session:before.session,closed:true,listed:false},publicBefore:{uri,activeEditorIsTarget:true,documentClosed:false,documentListed:true,matchingTextTabs:1},publicAfter:{uri,documentClosed:true,documentListed:false,activeEditorIsTarget:false,visibleTargetEditors:0,matchingTextTabs:0},diagnostics:[],elapsedMs:1,closeIndex,wireEnd:protocol.length};
 const reopenIndex=protocol.length;protocol.push({...owner,direction:'client',message:{method:'textDocument/didOpen',params:{textDocument:{uri,version:1,text:fixed,synchronizationId:'fresh-sync'}}}});const steps=[];
 for(let i=0;i<2;i++){const text=i?base.source:fixed,binding={...before,version:i+1,session:'fresh-document',sourceHash:hash(text)};if(i)protocol.push({...owner,direction:'client',message:{method:'textDocument/didChange',params:{textDocument:{uri,version:binding.version},contentChanges:[{text}]}}});const diagnostics=i?structuredClone(b.protocol[1].message.params.diagnostics):[],publicationIndex=protocol.length;protocol.push({...owner,direction:'server',message:{method:'textDocument/publishDiagnostics',params:{uri,version:binding.version,sourceHash:binding.sourceHash,synchronizationId:'fresh-sync',diagnostics}}});if(!i)protocol.push({...owner,direction:'server',message:{method:'solidityLean/status',params:{uri,version:binding.version,sourceHash:binding.sourceHash,synchronizationId:'fresh-sync',state:'ready'}}});steps.push({phase:i?'reopened-duplicate':'reopened-fixed',status:'observed',before:binding,after:structuredClone(binding),wireEnd:protocol.length,eventEnd:events.length,publicationIndex,diagnostics:base.wireSnapshot(diagnostics),process:{...owner},elapsedMs:i+1});}
 return{runId:c.runId,target:c.target,sourceHead:c.sourceHead,mode,status:'partial',captureStatus:'observed',base:b,protocol,events,close,newObject:true,reopenIndex,steps,opens:[{command:'vscode.open',uri,status:'observed',elapsedMs:1,binding:structuredClone(b.steps[0].before)},{command:'vscode.open',uri,status:'observed',elapsedMs:1,binding:structuredClone(steps[0].before)}]};
}
test('injected complete close/reopen receipt remains partial after JSON',()=>assert.deepEqual(errors(JSON.parse(JSON.stringify(lifetime())),c),[]));
const changes={
 'missing owned event':o=>o.close.event.objectMatched=false,
 'tab disappearance without model closure':o=>{o.close.publicAfter.documentClosed=false;o.close.result.oldDocumentClosed=false;},
 'old model still listed':o=>o.close.publicAfter.documentListed=true,
 'wrong saved bytes':o=>o.close.diskAfter.text+='x',
 'save refused':o=>o.close.saveReturned=false,
 'wrong document close wire':o=>o.protocol[o.close.closeIndex].message.params.textDocument.uri='file:///foreign',
 'wrong process close wire':o=>o.protocol[o.close.closeIndex].birth='other',
 'missing document close wire':o=>o.protocol[o.close.closeIndex].message.method='unrelated',
 'same object reused':o=>o.newObject=false,
 'same document session reused':o=>o.steps[0].before.session=o.base.steps.at(-1).before.session,
 'same synchronization reused':o=>{o.protocol[o.reopenIndex].message.params.textDocument.synchronizationId='sync-epoch';for(const r of o.protocol.slice(o.reopenIndex))if(r.message?.method==='textDocument/publishDiagnostics')r.message.params.synchronizationId='sync-epoch';},
 'reopen before close':o=>o.reopenIndex=o.close.closeIndex-1,
 'unrelated command':o=>o.opens[1].command='workspace.openTextDocument',
 'late close':o=>o.close.elapsedMs=60000,
 'wrong public close URI':o=>o.close.publicAfter.uri='file:///foreign',
 'missing fresh error':o=>o.steps[1].diagnostics=[],
 'proof action':o=>o.protocol.push({direction:'client',message:{method:'solidityLean/verify'}}),
 'failed receipt':o=>o.status='failed'
};
for(const[name,change]of Object.entries(changes))test('lifetime receipt refuses '+name,()=>{const o=lifetime();change(o);assert.ok(errors(o,c).length);});
test('UI opener uses registered command and actual active document without API-open model reference',async()=>{
 const uri='file:///workspace/source.sol',doc={uri:{toString:()=>uri,scheme:'file'},version:1,isClosed:false,languageId:'solidity',getText:()=>base.source};let commands=0;
 const vscode={Uri:{file:()=>doc.uri},workspace:{isTrusted:true,textDocuments:[doc],openTextDocument(){assert.fail('must not acquire API model reference');}},window:{},commands:{async executeCommand(command,resource,options){commands++;assert.equal(command,'vscode.open');assert.equal(resource,doc.uri);assert.deepEqual(options,{preview:false,preserveFocus:false});vscode.window.activeTextEditor={document:doc};}}};
 const record={};assert.equal(await openViaUi(vscode,'/workspace/source.sol',performance.now()+1000,record,()=> 'session'),doc);assert.equal(commands,1);assert.equal(record.status,'observed');assert.equal(record.binding.uri,uri);
});
test('UI opener refuses a foreign active resource within the same deadline',async()=>{
 const foreign={uri:{toString:()=> 'file:///foreign',scheme:'file'},isClosed:false},vscode={Uri:{file:()=>({toString:()=> 'file:///owned'})},workspace:{textDocuments:[foreign]},window:{activeTextEditor:{document:foreign}},commands:{async executeCommand(){}}},record={};
 await assert.rejects(openViaUi(vscode,'/owned',performance.now()+30,record,()=> 'x'),e=>e.code==='TIMEOUT');assert.equal(record.status,'failed');
});
test('lifecycle launcher requires explicit UI and public EOL inputs within original resource budgets',()=>{
 const {parse}=require('../parity/run.cjs'),args=['--suite','related-diagnostics','--targets','local','--workers','1','--cache','none','--obligations','1','--trials','1','--warmups','0','--diagnostic-lifecycle',mode];assert.throws(()=>parse(args));assert.equal(parse([...args,'--diagnostic-input','public-eol-v1']).diagnosticLifecycle,mode);assert.throws(()=>parse([...args,'--diagnostic-input','public-eol-v1','--operation-timeout-ms','60001']));
});
module.exports={lifetime,c};

test('lifetime rejects contradictory base-event prefix',()=>{const o=lifetime();o.events[0]={...o.events[0],kind:'foreign'};assert.ok(errors(o,c).length);});
test('failed base capture remains in serialized failed lifecycle envelope',async()=>{
 const fs=require('node:fs'),os=require('node:os'),path=require('node:path'),dir=fs.mkdtempSync(path.join(os.tmpdir(),'related-base-failure-')),original=base.run,failed={status:'failed',steps:[{phase:'duplicate',error:'owned base failure'}]};
 try{fs.writeFileSync(path.join(dir,'wire'),'');base.run=async()=>{throw Object.assign(Error('base failed'),{observation:failed});};await assert.rejects(require('../parity/related-diagnostic-lifecycle.cjs').run({vscode:{},config:{...c,dir,trace:path.join(dir,'wire')},events:[],sessionFor:()=>''}),e=>e.message==='base failed'&&e.observation.base===failed);const saved=JSON.parse(fs.readFileSync(path.join(dir,'related-diagnostic-lifecycle-observations.json')));assert.deepEqual(saved.base,failed);assert.equal(saved.status,'failed');}finally{base.run=original;fs.rmSync(dir,{recursive:true,force:true});}
});
test('close observer cleanup cannot replace primary failure or skip final capture',async()=>{
 const fs=require('node:fs'),os=require('node:os'),path=require('node:path'),dir=fs.mkdtempSync(path.join(os.tmpdir(),'related-close-failure-')),original=base.run,b=fixture(c.diagnosticInput),state=b.steps.at(-1).after,file=path.join(dir,'related-diagnostics.sol'),uri={toString:()=>state.uri,scheme:'file'};let registrations=0;
 const doc={uri,version:state.version,isClosed:false,isDirty:false,languageId:'solidity',getText:()=>base.textForInput('fixed',c.diagnosticInput),async save(){fs.writeFileSync(file,this.getText());return true;}};
 const vscode={workspace:{isTrusted:true,textDocuments:[doc],onDidCloseTextDocument(){const first=++registrations===1;return{dispose(){if(first)throw Error('observer cleanup failed');}};}},window:{activeTextEditor:{document:doc},visibleTextEditors:[{document:doc}],tabGroups:{all:[]}},commands:{async executeCommand(){throw Error('primary close refusal');}}};
 try{fs.writeFileSync(file,base.source);fs.writeFileSync(path.join(dir,'wire'),'');base.run=async()=>b;await assert.rejects(require('../parity/related-diagnostic-lifecycle.cjs').run({vscode,config:{...c,workspace:dir,dir,trace:path.join(dir,'wire')},events:b.events,sessionFor:()=>state.session}),e=>e.message==='primary close refusal'&&e.observation.cleanupErrors[0].includes('observer cleanup failed'));const saved=JSON.parse(fs.readFileSync(path.join(dir,'related-diagnostic-lifecycle-observations.json')));assert.match(saved.error,/primary close refusal/);assert.equal(saved.cleanupErrors.length,1);assert.ok(saved.close.closeObservation);assert.deepEqual(saved.events,b.events);assert.equal(registrations,2);}finally{base.run=original;fs.rmSync(dir,{recursive:true,force:true});}
});

for(const carrier of [{},false,'',['failed']])test('reject malformed/nonempty cleanup carrier '+JSON.stringify(carrier),()=>{const o=lifetime();o.cleanupErrors=carrier;assert.ok(errors(o,c).length);});
