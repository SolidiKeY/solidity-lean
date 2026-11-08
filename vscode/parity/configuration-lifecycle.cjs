// Configuration observation in the existing stdio runner. No explicit verification requests.
'use strict';
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict'),{createHash,randomUUID}=require('node:crypto'),{performance}=require('node:perf_hooks');
const initial='method Check() returns (r: int)\n  ensures r == 1\n{ r := 1; }\n';
const modes=['default','never','onsave','restored'];
function schema(){const root=path.resolve(__dirname,'../..'),p=JSON.parse(fs.readFileSync(path.join(root,'.cache/dafny-extension/package.json')));return p.contributes.configuration.properties['dafny.automaticVerification'];}
function launchArgs(mode){assert.ok(modes.includes(mode));return mode==='never'?['--verify-on:Never']:mode==='onsave'?['--verify-on:Save']:[];}
class Exchange{
 constructor(identity,{now=()=>performance.now(),readSchema=schema}={}){this.identity={...identity};this.now=now;this.epoch=0;this.closed=false;this.requests=[];this.schema=structuredClone(readSchema());if(this.schema?.default!=='onchange'||JSON.stringify(this.schema?.enum)!==JSON.stringify(['never','onchange','onsave']))throw Error('Pinned automatic verification schema mismatch');this.default=this.schema.default;}
 effective(){return this.override??this.default;}
 set(value){if(value!==undefined&&!this.schema.enum.includes(value))throw Error('Unsupported pinned automatic verification value');this.override=value;this.epoch++;}
 ticket(params,id){if(this.closed||!Array.isArray(params?.items))throw Error('Invalid configuration request');return{identity:{...this.identity},epoch:this.epoch,at:this.now(),id,params:structuredClone(params)};}
 reply(ticket){if(this.closed||ticket.epoch!==this.epoch||JSON.stringify(ticket.identity)!==JSON.stringify(this.identity)||this.now()-ticket.at>=60000)throw Error('Stale/foreign/late configuration reply');const value=this.effective();const result=ticket.params.items.map(item=>item.section==='dafny'?{automaticVerification:value}:item.section==='dafny.automaticVerification'?value:null);this.requests.push({...ticket,result,scope:'Reference global setting, matching pinned Configuration.get without resource; not a local server effective-mode claim'});return result;}
 close(){this.closed=true;this.epoch++;}
}
function source(doc,session){return{uri:doc.uri,version:doc.version,text:doc.text,sourceHash:createHash('sha256').update(doc.text).digest('hex'),session};}
function currentPacket(packet,binding){return packet?.uri===binding.uri&&packet.version===binding.version&&(packet.sourceHash===undefined||packet.sourceHash===binding.sourceHash);}
function assertUnverified(packets,binding){const owned=packets.filter(p=>currentPacket(p,binding)&&p.namedVerifiables?.length);assert.ok(owned.length,'No owned unverified status observed');assert.ok(owned.every(p=>p.namedVerifiables.every(s=>s.status===0)),'Unexpected verification through observed barrier');}
async function observe({target,mode,peer,request,until,open,change,states,diagnostics,events,exchange,dir}){
 const rows=[],session=randomUUID(),doc=open('configuration',target==='dafny'?initial:require('./workloads.cjs').workload('local',1));let closed=false,failure,restorationError;
 const save=()=>fs.writeFileSync(path.join(dir,'configuration-observations.json'),JSON.stringify({status:failure||restorationError?'failed':'partial',failure:failure?.message,restorationError,target,mode,rowIds:['setting:dafny.automaticVerification','contribution:configuration/0/properties/dafny.automaticVerification','lifecycle:configuration-change','scenario:configuration-changes'],setting:'dafny.automaticVerification',schema:exchange.schema,configuredReferenceClientValue:exchange.effective(),nativeLaunchMode:target==='local'?'never':mode==='never'?'Never':mode==='onsave'?'Save':'CLI default Change',localDeclaredUiDefault:target==='local'?'onchange':undefined,overridePresent:exchange.override!==undefined,rows,configurationRequests:exchange.requests,cancellation:'No native in-flight verification cancellation witness; not passed by completed small fixtures',configurationRequestCoverage:exchange.requests.length?'native requests observed':'missing: native server has not requested workspace/configuration',limitations:['Headless server, not native editor setting UI or client restart behavior.','Client source/session hashes are observation bindings; Dafny does not send those fields. Identical reopen packets remain ambiguous.','Absence is observed only through the recorded resolution/symbol barrier, not an unlimited silence proof.','Local automatic proof modes not executed: compiler-only never mode; injected controls are separate.']},null,2));
 const snapshot=()=>source(doc,session);
 async function barrier(phase,unverified=false){const b=snapshot(),start=events.length,row={phase,binding:b,eventStart:start};rows.push(row);save();try{row.symbols=await request('textDocument/documentSymbol',{textDocument:{uri:doc.uri,version:doc.version}});assert.deepEqual(snapshot(),b);const names=[];const visit=values=>{for(const v of values||[]){names.push(v.name);visit(v.children);}};visit(row.symbols);assert.ok(names.includes(target==='dafny'?'Check':'f0'),'Owned source symbol missing');row.events=events.slice(start);row.eventEnd=events.length;row.observedStates=events.filter(e=>e.kind==='dafny/textDocument/symbolStatus'&&currentPacket(e.data,b));row.diagnostics=diagnostics.get(doc.uri);if(unverified)assertUnverified(row.observedStates.map(e=>e.data),b);save();return row;}catch(error){row.error=error.message;save();throw error;}}
 async function proof(phase,status){await until(()=>{const p=states.get(doc.uri);return currentPacket(p,snapshot())&&p.namedVerifiables?.length&&p.namedVerifiables.every(s=>status===5?s.status===5:[4,5].includes(s.status))&&p.namedVerifiables.some(s=>s.status===status);},phase);if(status===4)await until(()=>{const p=diagnostics.get(doc.uri);return currentPacket(p,snapshot())&&p.diagnostics.some(d=>d.severity===1);},'current automatic error diagnostic');await barrier(phase);}
 const saveDocument=()=>{fs.writeFileSync(require('node:url').fileURLToPath(doc.uri),doc.text);peer.notify('textDocument/didSave',{textDocument:{uri:doc.uri},text:doc.text});};
 const configure=value=>{exchange.set(value);peer.notify('workspace/didChangeConfiguration',{settings:target==='dafny'?{dafny:{automaticVerification:exchange.effective()}}:{automaticVerification:'never'}});};
 try{
  if(target==='local'){await barrier('native-default-never-compiler');configure('never');change(doc,doc.text+'\n// configuration edit\n');await barrier('native-reconfigured-never-compiler');saveDocument();await barrier('native-never-save');exchange.set(undefined);peer.notify('workspace/didChangeConfiguration',{settings:{}});await barrier('native-empty-configuration-retains-never');}
  else if(mode==='default'||mode==='restored'){
   await proof('default-open',5);
   const texts=[initial+'\n// edit\n',initial.replace('r := 1','r := 2'),initial+'\n// fixed\n'];
   for(let i=0;i<texts.length;i++){change(doc,texts[i]+`\nmethod Marker${i+2}() {}\n`);await proof(['edit','broken','fixed'][i],i===1?4:5);}
   configure('never');change(doc,doc.text+'\nmethod Marker5() {}\n');await proof('live-notification-still-launch-mode',5);
   saveDocument();await barrier('save');exchange.set(undefined);peer.notify('workspace/didChangeConfiguration',{settings:{dafny:{}}});await barrier('default-configuration-restored');
  }else if(mode==='never'){await barrier('never-open-resolution',true);change(doc,initial+'\nmethod Marker2() {}\n');await barrier('never-edit-resolution',true);saveDocument();await barrier('never-save-resolution',true);configure('onsave');saveDocument();await barrier('live-onsave-notification-save',true);}
  else{await barrier('save-mode-open-resolution',true);change(doc,initial.replace('r := 1','r := 2')+'\nmethod Marker3() {}\n');await barrier('save-mode-edit-resolution',true);saveDocument();await proof('automatic-save-error',4);change(doc,initial+'\n// fixed\nmethod Marker4() {}\n');await barrier('save-mode-fix-resolution',true);saveDocument();await proof('automatic-save-fixed',5);}
  peer.notify('textDocument/didClose',{textDocument:{uri:doc.uri}});closed=true;rows.push({phase:'closed',binding:snapshot()});save();
  return{status:'partial',mode,rows,configurationRequests:exchange.requests,scope:'Actual server transport and document-driven verification only; restart is separate process per mode; absent config requests and local proof gaps remain missing.'};
 }catch(error){failure=error;throw error;}finally{if(exchange.override!==undefined){exchange.set(undefined);try{peer.notify('workspace/didChangeConfiguration',{settings:target==='dafny'?{dafny:{}}:{}});}catch(error){restorationError=error.message;}}if(!closed)try{peer.notify('textDocument/didClose',{textDocument:{uri:doc.uri}});}catch{}exchange.close();save();if(restorationError&&!failure)throw Error('Configuration restoration failed: '+restorationError);}
}
function auditWire(rows,target,mode){
 const errors=[],versions=new Map(),saved=new Set();let uri;
 for(const {direction,message:m}of rows){if(!m)continue;
  if(direction==='client'&&['solidityLean/verify','dafny/textDocument/verifySymbol'].includes(m.method))errors.push('explicit verification request');
  if(direction==='client'&&m.method==='textDocument/didOpen'){uri=m.params.textDocument.uri;versions.set(uri,m.params.textDocument.version);}
  if(direction==='client'&&m.method==='textDocument/didChange')versions.set(m.params.textDocument.uri,m.params.textDocument.version);
  if(direction==='client'&&m.method==='textDocument/didSave')saved.add(JSON.stringify([m.params.textDocument.uri,versions.get(m.params.textDocument.uri)]));
  if(direction==='server'&&target==='local'&&m.method==='solidityLean/report')errors.push('unexpected local proof report');
  if(direction==='server'&&m.method==='dafny/textDocument/symbolStatus'&&m.params.uri===uri&&(mode==='never'||mode==='onsave'&&!saved.has(JSON.stringify([m.params.uri,m.params.version])))&&m.params.namedVerifiables?.some(s=>s.status!==0))errors.push('unexpected verification through final wire barrier');
 }
 return errors;
}
module.exports={auditWire,assertUnverified,initial,modes,schema,launchArgs,Exchange,source,currentPacket,observe};
