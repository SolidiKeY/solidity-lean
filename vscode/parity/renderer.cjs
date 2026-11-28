'use strict';
const {writeFileSync,mkdirSync,appendFileSync} = require('node:fs');
const {join} = require('node:path');
const {createServer} = require('node:net');
const {performance} = require('node:perf_hooks');
const {randomUUID,createHash}=require('node:crypto');

async function availablePort() {
  const server=createServer();
  await new Promise((resolve,reject)=>{server.once('error',reject);server.listen(0,'127.0.0.1',resolve);});
  const port=server.address().port;await new Promise(resolve=>server.close(resolve));return port;
}
// Bounded phase diagnostics are failure evidence, never a successful capture.
function phaseDiagnostic(file,identity){
 identity=JSON.parse(JSON.stringify(identity));let count=0,bytes=0;
 return event=>{const row=JSON.stringify({...event,...identity})+'\n';if(++count>256||(bytes+=Buffer.byteLength(row))>1024*1024)throw Error('CDP phase diagnostic bound exceeded');appendFileSync(file,row);};
}
class DevTools {
 constructor(url,{socketFactory=url=>new WebSocket(url),now=()=>performance.now(),setTimer=setTimeout,clearTimer=clearTimeout,diagnostic=()=>{},identity={}}={}){
  this.next=0;this.pending=new Map();this.now=now;this.setTimer=setTimer;this.clearTimer=clearTimer;this.diagnostic=diagnostic;this.identity={...identity,connectionId:randomUUID()};this.socket=socketFactory(url);this.connectionStarted=now();
  this.ready=new Promise((resolve,reject)=>{this.readyResolve=resolve;this.readyReject=reject;this.connectTimer=setTimer(()=>this.abort(Error('CDP connection timeout'),'connection.timeout'),5000);});
  this.note('connection.start');
  this.socket.addEventListener('open',()=>{clearTimer(this.connectTimer);if(this.failure)return;if(now()-this.connectionStarted>=5000){this.abort(Error('CDP connection timeout'),'connection.late-open',{elapsedMs:now()-this.connectionStarted});return;}this.note('connection.open');this.readyResolve();},{once:true});
  this.socket.addEventListener('error',event=>this.abort(Error('CDP connection failed'),'socket.error',{message:event.message??null,errorMessage:event.error?.message??null}),{once:true});
  this.socket.addEventListener('close',event=>this.abort(Error('CDP disconnected'),'socket.close',{code:event.code,reason:event.reason}),{once:true});
  this.socket.addEventListener('message',event=>{
   let message;try{message=JSON.parse(event.data);}catch{this.abort(Error('Malformed CDP response'),'response.malformed');return;}
   const object=message!==null&&typeof message==='object'&&!Array.isArray(message),response=object&&Object.hasOwn(message,'id');
   if(!object||(response?(!Number.isSafeInteger(message.id)||message.id<1||(Object.hasOwn(message,'result')===Object.hasOwn(message,'error'))):typeof message.method!=='string')){this.abort(Error('Malformed CDP response'),'response.malformed',{payloadHash:createHash('sha256').update(event.data).digest('hex')});return;}
   const record=x=>x!==null&&typeof x==='object'&&!Array.isArray(x);if(response?(Object.hasOwn(message,'result')?!record(message.result):!record(message.error)||!Number.isSafeInteger(message.error.code)||typeof message.error.message!=='string'):(Object.hasOwn(message,'params')&&!record(message.params))){this.abort(Error('Malformed CDP response'),'response.malformed',{payloadHash:createHash('sha256').update(event.data).digest('hex')});return;}
   if(!response){this.note('notification',{method:message.method,paramsHash:createHash('sha256').update(JSON.stringify(message.params??null)).digest('hex')});return;}
   const task=this.pending.get(message.id);if(!task){this.note('response.unmatched',{id:message.id});return;}
   this.pending.delete(message.id);clearTimer(task.timer);const elapsedMs=now()-task.started;
   if(elapsedMs>=5000){this.note('response.late',{id:message.id,method:task.method,elapsedMs});task.reject(Error('CDP timeout '+task.method));return;}
   if(task.remaining){try{task.remaining();}catch(error){task.reject(error);return;}}
   const ok=this.note('response',{id:message.id,method:task.method,elapsedMs,error:message.error??null,exception:message.result?.exceptionDetails?.text??null,exceptionDetails:message.result?.exceptionDetails??null,bytes:Buffer.byteLength(event.data)});
   if(!ok){task.reject(this.failure);return;}
   if(task.remaining&&Object.hasOwn(this,'failure')){task.reject(this.failure);return;}
   if(message.error){task.reject(Error(JSON.stringify(message.error)));return;}
   if(Object.hasOwn(message.result,'exceptionDetails')){
    task.reject(Object.assign(Error('CDP execution exception: '+(typeof message.result.exceptionDetails?.text==='string'?message.result.exceptionDetails.text:'unknown exception')),{code:'CDP_EXECUTION_EXCEPTION',exceptionDetails:message.result.exceptionDetails}));return;
   }
   const completedMs=this.now()-task.started;
   if(completedMs>=5000){
    const recorded=this.note('response.late',{id:message.id,method:task.method,elapsedMs:completedMs,stage:'after-diagnostic'});
    task.reject(recorded?Error('CDP timeout '+task.method):this.failure);return;
   }
   if(task.remaining){try{task.remaining();}catch(error){task.reject(error);return;}}
   task.resolve(message.result);
  });
 }
 note(event,data={}){if(this.diagnosticFailure)return false;try{this.diagnostic({...this.identity,event,monotonicMs:this.now(),wallTime:Date.now(),...data});return true;}catch(error){this.diagnosticFailure=error;this.abort(error,'diagnostic.failure');return false;}}
 abort(error,event,data={}){if(this.failure)return;this.failure=error;this.clearTimer(this.connectTimer);this.note(event,data);this.readyReject(error);for(const [id,t]of this.pending){this.clearTimer(t.timer);this.note('request.aborted',{id,method:t.method});t.reject(error);}this.pending.clear();try{this.socket.close();}catch(closeError){this.note('socket.close-failed',{error:closeError.message});}}
 async request(method,params={},options=undefined){
  if(options!==undefined)return this.requestBounded(method,params,options);
  await this.ready;if(this.failure)throw this.failure;const id=++this.next,started=this.now();
  return new Promise((resolve,reject)=>{
   const timer=this.setTimer(()=>{this.pending.delete(id);this.note('request.timeout',{id,method,elapsedMs:this.now()-started});reject(Error('CDP timeout '+method));},5000);
   this.pending.set(id,{resolve,reject,timer,started,method});
   if(!this.note('request',{id,method,deadlineMs:5000,paramsHash:createHash('sha256').update(JSON.stringify(params)).digest('hex'),...(method.startsWith('Input.')?{input:params}:{})}))return;
   try{this.socket.send(JSON.stringify({id,method,params}));}catch(error){this.pending.delete(id);this.clearTimer(timer);this.note('request.send-failed',{id,method,error:error.message});reject(error);}
  });
 }
 // Optional caller deadline; ordinary requests retain their existing path.
 async requestBounded(method,params,options){
  if(!options||typeof options!=='object'||Array.isArray(options)||Reflect.ownKeys(options).length!==2||!Object.hasOwn(options,'deadlineWall')||!Object.hasOwn(options,'wallNow'))throw Error('Invalid CDP deadline options');
  const {deadlineWall,wallNow}=options;
  if(!Number.isFinite(deadlineWall)||typeof wallNow!=='function')throw Error('Invalid CDP deadline options');
  let lastWall=-Infinity,started;
  const timeout=()=>Error('CDP timeout '+method);
  const remaining=()=>{
   const wall=wallNow();
   if(Object.hasOwn(this,'failure'))throw this.failure;
   if(!Number.isFinite(wall)||wall<lastWall)throw Error('Invalid CDP deadline clock');
   lastWall=wall;
   const elapsed=started===undefined?0:this.now()-started;
   if(Object.hasOwn(this,'failure'))throw this.failure;
   if(!Number.isFinite(elapsed)||elapsed<0)throw Error('Invalid CDP deadline clock');
   const left=Math.min(deadlineWall-wall,started===undefined?Infinity:5000-elapsed);
   if(left<=0)throw timeout();
   return left;
  };
  let readyTimer;
  try{const left=remaining();await Promise.race([this.ready,new Promise((_,reject)=>{readyTimer=this.setTimer(()=>reject(timeout()),left);})]);}
  finally{if(readyTimer!==undefined)this.clearTimer(readyTimer);}
  if(this.failure)throw this.failure;
  started=this.now();const left=remaining(),id=++this.next;
  return new Promise((resolve,reject)=>{
   let settled=false,timer;
   const settle=(fn,value)=>{if(settled)return;settled=true;this.pending.delete(id);if(timer!==undefined)this.clearTimer(timer);fn(value);};
   const fail=error=>settle(reject,error);
   timer=this.setTimer(()=>{const ok=this.note('request.timeout',{id,method,elapsedMs:this.now()-started});fail(ok?timeout():this.failure);},left);
   this.pending.set(id,{resolve:value=>settle(resolve,value),reject:fail,timer,started,method,remaining});
   try{
    const payload=JSON.stringify({id,method,params}),paramsHash=createHash('sha256').update(JSON.stringify(params)).digest('hex');
    if(!this.note('request',{id,method,deadlineMs:left,deadlineWall,paramsHash,...(method.startsWith('Input.')?{input:params}:{})}))return;
    // No diagnostic, serialization or await between the sampled guard and send.
    remaining();if(settled)return;this.socket.send(payload);
   }catch(error){fail(error);}
  });
 }
 finish(){const failure=this.failure;this.close();if(failure)throw failure;}
 close(){this.abort(Error('CDP closed'),'connection.owned-close');if(this.diagnosticFailure)throw this.diagnosticFailure;}
}
async function connect(port,options={}){
 const {fetchImpl=fetch,now=()=>performance.now(),...clientOptions}=options;
 const start=now(),lookupUrl=`http://127.0.0.1:${port}/json/list`,note=(event,data={})=>clientOptions.diagnostic?.({event,wallTime:Date.now(),monotonicMs:now(),elapsedMs:now()-start,lookupUrl,deadlineMs:1500,...data});
 const onTime=()=>{if(now()-start>=1500)throw Error('CDP target lookup timeout');};
 note('target.lookup.start');
 try{
  const response=await fetchImpl(lookupUrl,{signal:AbortSignal.timeout(1500)});note('target.lookup.headers',{status:response.status});onTime();
  if(!response.ok)throw Error('CDP target lookup HTTP '+response.status);
  const pages=await response.json();note('target.lookup.body');onTime();
  if(!Array.isArray(pages))throw Error('Malformed CDP target list');
  const page=pages.find(p=>p?.type==='page'&&typeof p.url==='string'&&p.url.startsWith('vscode-file:'));if(!page)throw Error('VS Code renderer not ready');
  note('target.lookup.finish',{targetId:page.id,targetUrl:page.url,targetTitle:page.title});onTime();
  return new DevTools(page.webSocketDebuggerUrl,{...clientOptions,now,identity:{...clientOptions.identity,targetId:page.id,targetUrl:page.url,targetTitle:page.title}});
 }catch(error){error=phaseError(error);try{note('target.lookup.failed',{error:error.message});}catch(reporting){(error.reportingErrors??=[]).push(phaseError(reporting).message);}throw error;}
}
function phaseError(reason){
 if(reason instanceof Error)return reason;
 let message;try{const value=reason?.message;if(typeof value==='string'&&value)message=value;}catch{}
 if(!message)message=reason===null||!['object','function'].includes(typeof reason)?'Renderer phase failed: '+String(reason):'Renderer phase failed without an Error';
 return new Error(message,{cause:reason});
}
async function withPhaseRenderer(port,directory,request,config,capturePhase,{connectRenderer=connect}={}){
 const tracked=request.phase.startsWith('menus-')||request.phase.startsWith('diagnostics-problems-');
 const diagnostic=tracked?phaseDiagnostic(join(directory,'cdp-timing.jsonl'),{runId:config.runId,target:config.target,sourceHead:config.sourceHead,phase:request.phase,phaseRequestId:request.requestId,metadataHash:createHash('sha256').update(JSON.stringify(request.metadata??null)).digest('hex'),source:request.metadata?.binding}):undefined;
 const note=(event,data={})=>diagnostic?.({event,wallTime:Date.now(),monotonicMs:performance.now(),...data});
 let client,result,primary;
 try{note('phase.start');client=await connectRenderer(port,{diagnostic});result=await capturePhase(client);}
 catch(error){primary=phaseError(error);}
 finally{try{if(client){if(request.phase.startsWith('menus-'))client.finish();else client.close();}}catch(error){error=phaseError(error);if(primary)(primary.cleanupErrors??=[]).push(error.message);else primary=error;}}
 if(primary){try{note('phase.failed',{error:primary.message,cleanupErrors:primary.cleanupErrors??[]});}catch(reporting){(primary.reportingErrors??=[]).push(phaseError(reporting).message);}throw primary;}
 note('phase.complete');return result;
}
async function capture(client,directory,screenshot=false,surface='editor') {
  const start=performance.now();
  const accessibility=await client.request('Accessibility.getFullAXTree');
  writeFileSync(join(directory,'accessibility.json'),JSON.stringify(accessibility));
  const dom=await client.request('DOMSnapshot.captureSnapshot',{computedStyles:[]});
  writeFileSync(join(directory,'dom.json'),JSON.stringify(dom));
  const inspection=await client.request('Runtime.evaluate',{expression:`JSON.stringify({title:document.title,trustEditorCount:document.querySelectorAll('.workspace-trust-editor').length,editorCount:document.querySelectorAll('.monaco-editor').length,notifications:[...document.querySelectorAll('.notification-list-item')].map(e=>e.textContent),visibleHovers:[...document.querySelectorAll('.monaco-hover')].filter(e=>e.getClientRects().length&&getComputedStyle(e).visibility!=='hidden').map(e=>e.innerText),bodyText:document.body.innerText.slice(0,24000)})`,returnByValue:true});
  const visible=JSON.parse(inspection.result.value);
  if(!(surface==='workspace-trust'?visible.trustEditorCount:visible.editorCount)||!accessibility.nodes?.length||!dom.documents?.length)throw new Error('Renderer has no inspectable editor, DOM or accessibility tree');
  writeFileSync(join(directory,'visible-state.json'),inspection.result.value);
  if(screenshot) {const result=await client.request('Page.captureScreenshot',{format:'png'});writeFileSync(join(directory,'screenshot.png'),Buffer.from(result.data,'base64'),{flag:'wx'});}
  return {captured:true,elapsedMs:performance.now()-start,screenshot,hoverCount:visible.visibleHovers.length,editorCount:visible.editorCount,accessibilityNodes:accessibility.nodes.length};
}
async function inputProbe(client) {
  const focused=await client.request('Runtime.evaluate',{expression:'(()=>{const editor=document.querySelector(".monaco-editor.focused")||document.querySelector(".monaco-editor");editor?.querySelector("textarea, [role=textbox], [contenteditable=true]")?.focus();return !!document.activeElement?.closest(".monaco-editor");})()',returnByValue:true});
  const started=Date.now(),clock=performance.now();
  await client.request('Input.dispatchKeyEvent',{type:'keyDown',key:'ArrowRight',code:'ArrowRight',windowsVirtualKeyCode:39});
  await client.request('Input.dispatchKeyEvent',{type:'keyUp',key:'ArrowRight',code:'ArrowRight',windowsVirtualKeyCode:39});
  await client.request('Runtime.evaluate',{expression:'new Promise(resolve=>requestAnimationFrame(()=>resolve(true)))',awaitPromise:true,returnByValue:true});
  return {started,finished:Date.now(),roundTripMs:performance.now()-clock,focusedEditor:focused.result.value,
    scope:'Arrow-key dispatch and next renderer animation frame; includes DevTools transport and does not isolate paint time.'};
}
const {observeMenuItems,recorder:menuRoleRecorder}=require('./menu-dom.cjs');
const contextMenuNodes='(()=>{const roots=[document],nodes=[];for(let i=0;i<roots.length;i++){const root=roots[i];nodes.push(...root.querySelectorAll(".monaco-menu .action-label"));for(const e of root.querySelectorAll("*"))if(e.shadowRoot)roots.push(e.shadowRoot);}return nodes;})()';
async function captureContributionMenu(client,directory,metadata,context={}){
 const label=metadata.target==='local'?'Solidity Lean':'Dafny',expected=metadata.target==='local'?'Build Compiler Artifact with Import Options':'Build with Custom Arguments';
 if(metadata.anchorAdmission!==undefined&&(metadata.anchorAdmission!=='visible-scrollport-v1'||metadata.kind!=='editor'||metadata.trustObservation))throw Error('Invalid versioned menu anchor request');
 const visibleV1=metadata.anchorAdmission==='visible-scrollport-v1',anchorChecks=[];
 const nodes=contextMenuNodes+'.filter(e=>e.getClientRects().length)';
 const recordRoles=menuRoleRecorder(directory,{binding:metadata.binding,target:metadata.target,kind:metadata.kind,runId:context.runId??null,sourceHead:context.sourceHead??null});
 const read=async()=>{const observed=recordRoles((await client.request('Runtime.evaluate',{expression:'(()=>{const nodes='+nodes+';return{rendererLifetime:{timeOrigin:performance.timeOrigin,url:location.href},activeUri:document.querySelector(".editor-group-container.active .monaco-editor[data-uri]")?.getAttribute("data-uri")??null,tabSelected:document.querySelector(".editor-group-container.active .tabs-container .tab.active")?.getAttribute("aria-selected")??null,tabResourceLabels:Array.from(document.querySelectorAll(".editor-group-container.active .tabs-container .tab.active .tab-label[aria-label]")).map(x=>x.getAttribute("aria-label")),items:('+observeMenuItems.toString()+')(nodes,{width:innerWidth,height:innerHeight})};})()',returnByValue:true})).result.value);if(metadata.kind==='tab')require('node:assert/strict').deepEqual(observed.rendererLifetime,tabHit?.rendererLifetime,'Renderer restarted after tab menu input');return observed;};
 const anchor=(await client.request('Runtime.evaluate',{expression:'(()=>{const e=document.querySelector('+JSON.stringify(metadata.kind==='tab'?'.editor-group-container.active .tabs-container .tab.active':'.editor-group-container.active .monaco-editor .view-lines')+');if(!e)return null;const r=e.getBoundingClientRect(),group=e.closest(".editor-group-container.active"),editors=Array.from(group?.querySelectorAll(".monaco-editor[data-uri]")??[]).filter(x=>{const b=x.getBoundingClientRect();return b.width>0&&b.height>0;}),tabs=Array.from(group?.querySelectorAll(".tabs-container .tab.active")??[]).filter(x=>{const b=x.getBoundingClientRect();return b.width>0&&b.height>0;}),isTab='+JSON.stringify(metadata.kind==='tab')+',owner=isTab?editors[0]:e.closest(".monaco-editor"),owned=editors.length===1&&editors[0]===owner&&(!isTab||tabs.length===1&&tabs[0]===e);return{rendererLifetime:isTab?{timeOrigin:performance.timeOrigin,url:location.href}:null,activeUri:owned?owner.getAttribute("data-uri"):null,tabSelected:isTab?e.getAttribute("aria-selected"):null,tabResourceLabels:isTab?Array.from(e.querySelectorAll(".tab-label[aria-label]")).map(x=>x.getAttribute("aria-label")):null,rect:{left:r.left,top:r.top,right:r.right,bottom:r.bottom,width:r.width,height:r.height},viewport:{width:innerWidth,height:innerHeight}};})()',returnByValue:true})).result.value;
 writeFileSync(join(directory,'menu-anchor.json'),JSON.stringify({binding:metadata.binding,kind:metadata.kind,anchor},null,2));
 const tabGuard=()=>{if(metadata.kind!=='tab')return null;if(!context.root||!context.runId||!context.sourceHead)throw Error('Missing native public tab context');return require('./menu-tab-ownership.cjs').readCurrent(context.root,metadata.tabOwnership,metadata.binding,context);};
 let point,tabRecord,tabHit;try{point=visibleV1?require('./menu-scrollport.cjs').point(anchor,metadata.binding.uri):require('./menu-lifecycle.cjs').menuAnchorPoint(anchor,metadata.binding.uri);tabRecord=tabGuard();if(metadata.kind==='tab')require('./menu-tab-ownership.cjs').assertDOM(anchor,metadata.tabOwnership);}
 catch(error){writeFileSync(join(directory,'menu-anchor.json'),JSON.stringify({status:'failed',error:error.message,origin:'CDP Runtime.evaluate + public tab record',binding:metadata.binding,context,anchor,tabOwnership:metadata.tabOwnership},null,2));throw error;}
 writeFileSync(join(directory,'menu-anchor.json'),JSON.stringify({status:visibleV1?'point-selected':'admitted',binding:metadata.binding,kind:metadata.kind,anchor,point,tabRecord},null,2));
 const attempts=[],deadline=Date.now()+3000,prep=task=>require('./menu-lifecycle.cjs').preparation(task,deadline);let before,primary;
 client.note?.('menu.readiness.start',{deadlineWall:deadline,budgetMs:3000});
 const anchorGuard=async()=>{if(!visibleV1)return;const helper=require('./menu-scrollport.cjs'),probe=(await prep(()=>client.request('Runtime.evaluate',{expression:'('+helper.observe.toString()+')('+JSON.stringify(point)+')',returnByValue:true}))).result.value;attempts.push({stage:'visible-scrollport-probe',probe});const check=helper.admit(probe,anchor,metadata.binding.uri);if(anchorChecks.length)require('node:assert/strict').deepEqual(probe.rendererLifetime,anchorChecks[0].probe.rendererLifetime,'Renderer restarted before menu input');anchorChecks.push(check);writeFileSync(join(directory,'menu-scrollport-v1.json'),JSON.stringify({status:'observed',version:helper.version,binding:metadata.binding,anchor,checks:anchorChecks},null,2));};

 try{if(visibleV1){await anchorGuard();await anchorGuard();}if(metadata.kind==='tab'){const hit=require('./menu-tab-hit.cjs'),probe=(await prep(()=>client.request('Runtime.evaluate',{expression:'('+hit.observe.toString()+')('+JSON.stringify(point)+')',returnByValue:true}))).result.value;writeFileSync(join(directory,'menu-tab-hit.json'),JSON.stringify({binding:metadata.binding,probe},null,2));hit.assertHit(probe,anchor,point,metadata.tabOwnership);tabHit=probe;tabGuard();}for(const type of ['mousePressed','mouseReleased']){attempts.push({stage:'native-input',type,wallTime:Date.now(),deadlineWall:deadline});await require('./menu-lifecycle.cjs').menuMouse(client,{type,...point,button:'right',clickCount:1},tabGuard,deadline);}
  while(Date.now()<deadline){before=await prep(read);attempts.push(before);if(before?.items?.length)break;await new Promise(r=>setTimeout(r,20));}
  if(!before?.items?.length)throw Error('No native context menu opened');
  const submenu=before.items.find(i=>i.label===label);
  if(metadata.trustObservation!==true&&!!submenu!==metadata.visible)throw Error('Native submenu visibility differs from declared predicate');
  if(submenu){await require('./menu-lifecycle.cjs').menuMouse(client,{type:'mouseMoved',x:submenu.bounds.right-5,y:(submenu.bounds.top+submenu.bounds.bottom)/2},tabGuard,deadline);
   while(Date.now()<deadline){before=await prep(read);attempts.push(before);if(before.items.some(i=>i.label.includes(expected)))break;await new Promise(r=>setTimeout(r,20));}
   if(!before.items.some(i=>i.label.includes(expected)))throw Error('Native submenu actions missing');}
  if(before.activeUri!==metadata.binding.uri)throw Error('Foreign active source in menu renderer');
  if(visibleV1)require('node:assert/strict').deepEqual(before.rendererLifetime,anchorChecks[0]?.probe.rendererLifetime,'Renderer restarted after menu input');
  tabGuard();if(metadata.kind==='tab')require('./menu-tab-ownership.cjs').assertDOM(before,metadata.tabOwnership);
  writeFileSync(join(directory,'menu-before.json'),JSON.stringify(before,null,2));const rendered=await capture(client,directory,true),after=await read();tabGuard();if(metadata.kind==='tab')require('./menu-tab-ownership.cjs').assertDOM(after,metadata.tabOwnership);writeFileSync(join(directory,'menu-after.json'),JSON.stringify(after,null,2));require('node:assert/strict').deepEqual(after,before,'Menu changed during AX/PNG capture');
  return{...rendered,contributionMenu:{binding:metadata.binding,before,after,...(visibleV1?{anchorAdmission:{version:'visible-scrollport-v1',anchor,checks:anchorChecks}}:{}),submenuVisible:!!submenu,kind:metadata.kind,...(metadata.kind==='tab'?{tabOwnership:metadata.tabOwnership}:{}),scope:'Native mouse-opened menu endpoints; raw labels/attributes/bounds retained. No raster glyph or mutation-ABA claim.'}};
 }catch(error){primary=error;try{if(visibleV1)writeFileSync(join(directory,'menu-scrollport-v1.json'),JSON.stringify({status:'failed',error:error.message,version:'visible-scrollport-v1',binding:metadata.binding,anchor,checks:anchorChecks},null,2));}catch(reporting){(error.reportingErrors??=[]).push(reporting.message);}try{client.note?.('menu.failed',{error:error.message});}catch(reporting){(error.reportingErrors??=[]).push(reporting.message);}try{await capture(client,directory,true);}catch{}throw error;}
 finally{let finalError;try{writeFileSync(join(directory,'menu-attempts.json'),JSON.stringify(attempts,null,2));}catch(error){if(primary)(primary.reportingErrors??=[]).push(error.message);else finalError=error;}
  const cleanupDeadline=Date.now()+3000;try{for(let i=0;i<2;i++)for(const type of ['keyDown','keyUp'])await require('./menu-lifecycle.cjs').preparation(()=>client.request('Input.dispatchKeyEvent',{type,key:'Escape',code:'Escape',windowsVirtualKeyCode:27}),cleanupDeadline);}catch(error){const decisive=primary??finalError??error;if(decisive!==error)(decisive.cleanupErrors??=[]).push(error.message);try{writeFileSync(join(directory,'menu-cleanup-error.json'),JSON.stringify({error:error.message,primary:primary?.message??null}));}catch(reporting){(decisive.reportingErrors??=[]).push(reporting.message);}if(!primary&&!finalError)finalError=error;}if(!primary&&finalError)throw finalError;}

}
// Companion transports only the original capture's phase-local recorded tuple.
async function captureContributionMenuWithTabHit(client,directory,metadata,context={}){
 const captured=await captureContributionMenu(client,directory,metadata,context);
 if(metadata.kind!=='tab')return captured;
 const fs=require('node:fs'),helper=require('./menu-tab-hit.cjs');
 const admission={version:helper.version,anchorRecord:JSON.parse(fs.readFileSync(join(directory,'menu-anchor.json'),'utf8')),hitRecord:JSON.parse(fs.readFileSync(join(directory,'menu-tab-hit.json'),'utf8'))};
 helper.assertAdmission(admission,metadata.binding,metadata.tabOwnership,captured.contributionMenu.before,captured.contributionMenu.after);
 return{...captured,contributionMenu:{...captured.contributionMenu,tabHitAdmission:admission}};
}
// Only built-in Workspace Trust UI is operated; no context-key or service injection.
async function captureTrustControl(client,directory,metadata,captureSurface=capture){
 const desired=metadata.desired,label=desired?'Trust':"Don't Trust",opposite=desired?"Don't Trust":'Trust';
 if(typeof desired!=='boolean'||metadata.binding?.trusted===desired)throw Error('Invalid native trust transition');
 const read=async()=> (await client.request('Runtime.evaluate',{expression:`(()=>{const root=document.querySelector('.workspace-trust-editor');return{rendererLifetime:{timeOrigin:performance.timeOrigin,url:location.href},visible:!!root?.getClientRects().length,buttons:[...(root?.querySelectorAll('.monaco-button')||[])].filter(e=>e.getClientRects().length).map(e=>{const r=e.getBoundingClientRect();return{label:e.textContent,disabled:e.getAttribute('aria-disabled'),bounds:{left:r.left,top:r.top,right:r.right,bottom:r.bottom}};})};})()`,returnByValue:true})).result.value;
 const deadline=Date.now()+3000,prep=task=>require('./menu-lifecycle.cjs').preparation(task,deadline);let before,after,beforeCaptured,afterCaptured;client.note?.('trust.readiness.start',{deadlineWall:deadline,budgetMs:3000});
 try{
  while(Date.now()<deadline){before=await prep(read);if(before?.visible&&before.buttons.some(b=>b.label===label))break;await new Promise(r=>setTimeout(r,20));}
  const button=before?.buttons.filter(b=>b.label===label);if(button?.length!==1||button[0].disabled==='true')throw Error('Native trust button unavailable');
  writeFileSync(join(directory,'trust-before.json'),JSON.stringify(before));await captureSurface(client,directory,true,'workspace-trust');beforeCaptured=await prep(read);require('node:assert/strict').deepEqual(beforeCaptured,before,'Trust UI changed during before capture');
  const b=button[0].bounds;for(const type of ['mousePressed','mouseReleased'])await prep(()=>client.request('Input.dispatchMouseEvent',{type,x:(b.left+b.right)/2,y:(b.top+b.bottom)/2,button:'left',clickCount:1}));
  while(Date.now()<deadline){after=await prep(read);if(after?.visible&&after.buttons.some(b=>b.label===opposite))break;await new Promise(r=>setTimeout(r,20));}
  if(!after?.visible||!after.buttons.some(b=>b.label===opposite))throw Error('Native trust UI did not transition within original3s');
  const sub=join(directory,'after');mkdirSync(sub,{recursive:true});const captured=await captureSurface(client,sub,true,'workspace-trust');afterCaptured=await read();require('node:assert/strict').deepEqual(afterCaptured,after,'Trust UI changed during after capture');
  return{...captured,trustControl:{desired,binding:metadata.binding,before,after,beforeCaptured,afterCaptured,nativeMouse:true}};
 }finally{writeFileSync(join(directory,'trust-attempt.json'),JSON.stringify({binding:metadata.binding,desired,before,after,beforeCaptured,afterCaptured}));}
}
async function contextSubmenu(client,directory,{label='Solidity Lean',expected='Build Compiler Artifact with Import Options'}={}) {
  const point=await client.request('Runtime.evaluate',{expression:'(()=>{const e=document.querySelector(".monaco-editor.focused .view-lines")||document.querySelector(".monaco-editor .view-lines");if(!e)return null;const r=e.getBoundingClientRect();return{x:r.left+80,y:r.top+12};})()',returnByValue:true});
  if(!point.result.value)throw Error('No source editor for context submenu capture');
  const menuNodes=contextMenuNodes;
  const labels=()=>client.request('Runtime.evaluate',{expression:menuNodes+'.filter(e=>e.getClientRects().length).map(e=>e.textContent)',returnByValue:true});
  try {
    for(const type of ['mousePressed','mouseReleased'])await client.request('Input.dispatchMouseEvent',{type,...point.result.value,button:'right',clickCount:1});
    const deadline=Date.now()+3000;let entry;
    while(Date.now()<deadline){entry=await client.request('Runtime.evaluate',{expression:'(()=>{const e='+menuNodes+'.find(e=>e.textContent==='+JSON.stringify(label)+'&&e.getClientRects().length);if(!e)return null;const r=e.getBoundingClientRect();return{x:r.right-5,y:r.top+r.height/2};})()',returnByValue:true});if(entry.result.value)break;await new Promise(r=>setTimeout(r,20));}
    if(!entry?.result.value)throw Error('Declared Solidity Lean submenu is not visible');
    await client.request('Input.dispatchMouseEvent',{type:'mouseMoved',...entry.result.value});
    let visible;
    while(Date.now()<deadline){visible=(await labels()).result.value;if(visible.some(label=>label.includes(expected)))break;await new Promise(r=>setTimeout(r,20));}
    if(!visible?.some(label=>label.includes(expected)))throw Error('Custom compiler action is not rendered in the submenu');
    const state=await client.request('Runtime.evaluate',{expression:'({items:('+observeMenuItems.toString()+')('+menuNodes+'.filter(e=>e.getClientRects().length),{width:innerWidth,height:innerHeight}),rendererLifetime:{timeOrigin:performance.timeOrigin,url:location.href}})',returnByValue:true});const observed=menuRoleRecorder(directory,{label,expected})(state.result.value);const rendered=await capture(client,directory,true);return{labels:visible,items:observed.items,rendered,scope:'Actual Linux context submenu and raw enabled-state attributes; action execution, pairing and macOS remain separate observations.'};
  } catch(error){try{writeFileSync(join(directory,'attempt-labels.json'),JSON.stringify((await labels()).result.value));await capture(client,directory,true);}catch{}throw error;} finally {for(let i=0;i<2;i++)for(const type of ['keyDown','keyUp'])await client.request('Input.dispatchKeyEvent',{type,key:'Escape',code:'Escape',windowsVirtualKeyCode:27});}
}
async function captureTrace(client,directory,metadata){
 let nativeKey;
 if(metadata.key){if(!['F7','F8'].includes(metadata.key))throw Error('Unsupported native trace key');const focused=await client.request('Runtime.evaluate',{expression:'(()=>{const e=document.querySelector(".monaco-editor.focused")||document.querySelector(".monaco-editor");e?.querySelector("textarea,[role=textbox]")?.focus();return !!document.activeElement?.closest(".monaco-editor");})()',returnByValue:true});if(!focused.result.value)throw Error('No focused trace source');nativeKey=[];for(const type of ['keyDown','keyUp']){const params={type,key:metadata.key,code:metadata.key,windowsVirtualKeyCode:metadata.key==='F7'?118:119,modifiers:0},started=Date.now();await client.request('Input.dispatchKeyEvent',params);nativeKey.push({method:'Input.dispatchKeyEvent',params,started,finished:Date.now()});}
 if(metadata.expectNotice){const deadline=Date.now()+3000;let shown=false;while(Date.now()<deadline){shown=(await client.request('Runtime.evaluate',{expression:'[...document.querySelectorAll(".notification-list-item")].some(e=>e.getClientRects().length&&e.textContent.includes("Positioned verification traces are unavailable"))',returnByValue:true})).result.value;if(shown)break;await new Promise(r=>setTimeout(r,20));}if(!shown)throw Error('Native F7 unavailable notification not visibly observed');}}

 if(metadata.theme){const deadline=Date.now()+3000;let ready;do{ready=(await client.request('Runtime.evaluate',{expression:'!!document.querySelector(".monaco-workbench.'+metadata.theme+'")',returnByValue:true})).result.value;if(ready)break;await new Promise(r=>setTimeout(r,20));}while(Date.now()<deadline);if(!ready)throw Error('Requested native theme did not settle');}
 const inspection=await client.request('Runtime.evaluate',{expression:`(()=>{const editors=[...document.querySelectorAll('.monaco-editor[data-uri]')].filter(e=>e.getClientRects().length),active=editors.find(e=>e.closest('.editor-group-container.active')),annotations=[];for(const editor of editors){const numbers=[...editor.querySelectorAll('.margin-view-overlays .line-numbers')];for(const line of editor.querySelectorAll('.view-lines .view-line')){const y=line.getBoundingClientRect().top,number=numbers.find(n=>Math.abs(n.getBoundingClientRect().top-y)<1);for(const span of line.querySelectorAll('span[class*="TextEditorDecorationType"]')){const style=getComputedStyle(span,'::after');if(['none','normal','""'].includes(style.content))continue;let text;try{text=JSON.parse(style.content);}catch{text=null;}annotations.push({uri:editor.getAttribute('data-uri'),line:number?Number(number.textContent):null,text,content:style.content,className:span.className,color:style.color,backgroundColor:style.backgroundColor,marginLeft:style.marginLeft,marginTop:style.marginTop,marginRight:style.marginRight,marginBottom:style.marginBottom,visible:line.getBoundingClientRect().bottom>editor.getBoundingClientRect().top&&line.getBoundingClientRect().top<editor.getBoundingClientRect().bottom&&style.visibility!=='hidden'&&style.display!=='none'&&style.opacity!=='0'});}}}return{activeUri:active?.getAttribute('data-uri')??null,annotations};})()`,returnByValue:true});
 const observed=inspection.result.value;writeFileSync(join(directory,'trace-rendered.json'),JSON.stringify(observed,null,2));
 const menuDir=join(directory,'menu');require('node:fs').mkdirSync(menuDir,{recursive:true});observed.menu=await contextSubmenu(client,menuDir,{label:metadata.target==='local'?'Solidity Lean':'Dafny',expected:metadata.target==='local'?'Show Verification Trace':'Build with Custom Arguments'});
 const rendered=await capture(client,directory,true);if(metadata.mode==='unavailable')require('./trace-presentation.cjs').assertUnavailable(observed,metadata);else if(metadata.observeOnly){if(observed.activeUri!==metadata.binding.uri)throw Error('Native observation active URI mismatch');}else require('./trace-presentation.cjs').assertPresentation(observed,metadata);return{...rendered,tracePresentation:{...observed,nativeKey,binding:metadata.binding,asserted:!metadata.observeOnly,scope:metadata.observeOnly?'Native upstream state recorded without a lifecycle-success claim':'Exact content/style/disappearance/menu asserted'}};
}
function testingLabel(row){const named=row.querySelector('.label-name');if(named)return named.textContent;const label=row.querySelector('.label');return label?[...label.childNodes].filter(node=>node.nodeType===3).map(node=>node.textContent).join(''):null;}
async function captureProblems(client,directory,metadata,retirePressedInput,contract){
 const started=Date.now(),helper=contract??require('./diagnostic-problems.cjs'),expression=helper.expression?helper.expression():'('+helper.inspect.toString()+')('+helper.effectiveVisible.toString()+')',deadline=Math.min(started+3000,helper.deadline??Infinity),attempts=[],inputs=[];let before,after,lastRead,failure,held=false,inputRetirement,inputRetirementError;
 const bounded=async task=>{const remaining=deadline-Date.now();if(remaining<=0)throw Error('Original3s Problems readiness deadline exhausted');let timer;try{const value=await Promise.race([task(),new Promise((_,reject)=>{timer=setTimeout(()=>reject(Error('Original3s Problems readiness deadline exhausted')),remaining);})]);if(Date.now()>=deadline)throw Error('Late Problems readiness response');return value;}finally{clearTimeout(timer);}};
 const read=async()=>{try{const r=await client.request('Runtime.evaluate',{expression,returnByValue:true});lastRead={at:Date.now(),response:r};if(r.exceptionDetails)throw Error(r.exceptionDetails.text);return r.result.value;}catch(error){lastRead={...lastRead,error:error.stack};throw error;}};
 try{let ready=false;while(Date.now()<deadline){before=await bounded(read);const collapsed=before.roots===1&&before.rows.find(r=>r.expanded==='false');let reason;
  if(collapsed){if(before.activeUri!==metadata.binding.uri)throw Error('Problems active source changed before input');if(!collapsed.point||!collapsed.hitOwned)throw Error('Problems twistie has no observed hit ownership');if(typeof retirePressedInput!=='function')throw Error('Missing owned pressed-input retirement callback');const press={type:'mousePressed',point:collapsed.point,rowId:collapsed.id,status:'started'};inputs.push(press);held=true;await bounded(()=>client.request('Input.dispatchMouseEvent',{type:press.type,...collapsed.point,button:'left',clickCount:1}));press.status='dispatched';const releaseProbe=await bounded(read),same=releaseProbe.rows.filter(r=>r.id===collapsed.id);press.releaseProbe=releaseProbe;if(releaseProbe.roots!==1||releaseProbe.activeUri!==metadata.binding.uri||same.length!==1||!same[0].hitOwned||JSON.stringify(same[0].point)!==JSON.stringify(collapsed.point))throw Error('Problems source/hit changed before release');const release={type:'mouseReleased',point:collapsed.point,rowId:collapsed.id,status:'started'};inputs.push(release);await bounded(()=>client.request('Input.dispatchMouseEvent',{type:release.type,...collapsed.point,button:'left',clickCount:1}));release.status='dispatched';held=false;reason='expanded native Problems row';}
  else{try{helper.assertView(before,metadata);ready=true;}catch(error){reason=error.message;}}
  attempts.push({at:Date.now(),state:before,reason:reason??null});writeFileSync(join(directory,'problems-readiness.json'),JSON.stringify(attempts));if(ready)break;await bounded(()=>new Promise(r=>setTimeout(r,20)));}
 if(!ready)throw Error('Problems view unavailable within original3s readiness deadline');const readyAt=Date.now();if(readyAt>=deadline)throw Error('Late Problems readiness validation');writeFileSync(join(directory,'problems-before.json'),JSON.stringify(before));const captured=await capture(client,directory,true);after=await read();writeFileSync(join(directory,'problems-after.json'),JSON.stringify(after));require('node:assert/strict').deepEqual(after,before,'Problems tree changed during AX/DOM/PNG capture');helper.assertView(after,metadata);return{...captured,problems:{binding:metadata.binding,before,after,preparation:{started,deadline,readyAt},artifacts:helper.artifacts(directory),resourceIdentity:'opaque-row-id; independent Problems resource URI unavailable'}};
 }catch(error){failure=error;if(held)try{inputRetirement=retirePressedInput(error);}catch(cleanup){inputRetirementError=cleanup.stack;error.inputRetirementError=cleanup.stack;}throw error;}finally{try{writeFileSync(join(directory,'problems-attempt.json'),JSON.stringify({metadata,before,after,attempts,inputs,lastRead,inputHeldAtFailure:held,inputRetirement,inputRetirementError,error:failure?.stack}));}catch(error){if(failure)failure.reportingError=error.stack;else throw error;}}
}
async function captureTesting(client,directory,metadata){
 const expression=`(()=>{const all=[...document.querySelectorAll('.test-explorer')],roots=all.filter(e=>e.getClientRects().length),emptyRoot=!${metadata.visible}&&all.length===1&&all[0].closest('.pane')?.querySelector('.welcome-view-content'),welcome=emptyRoot&&emptyRoot.getClientRects().length&&emptyRoot.textContent.includes('No tests have been found in this workspace yet.');if(roots.length!==1&&!welcome)return{unavailable:{roots:roots.length,panes:[...document.querySelectorAll('.sidebar .pane')].map(e=>({id:e.id,className:e.className,text:e.textContent.slice(0,400)}))}};const root=roots[0]||all[0],pane=root.closest('.pane')||root,rows=[...root.querySelectorAll('.monaco-list-row')].filter(e=>e.getClientRects().length).map(e=>{const r=e.getBoundingClientRect();return{label:(${testingLabel.toString()})(e),text:e.textContent,description:e.querySelector('.test-label-description')?.textContent??null,level:e.getAttribute('aria-level'),expanded:e.getAttribute('aria-expanded'),id:e.getAttribute('data-id'),point:{x:r.left+12,y:r.top+r.height/2}};}),toolbar=[...pane.querySelectorAll('.action-label,button')].filter(e=>e.getClientRects().length).map(e=>({label:e.getAttribute('aria-label')||e.getAttribute('title')||e.textContent,disabled:e.getAttribute('aria-disabled'),className:e.className}));return{rootClass:root.className,rootVisible:!!root.getClientRects().length,emptyWelcome:welcome?{visible:true,text:emptyRoot.textContent}:null,paneId:pane.id,activeUri:document.querySelector('.editor-group-container.active .monaco-editor[data-uri]')?.getAttribute('data-uri')??null,rows,toolbar};})()`;
 const read=async()=>{return(await client.request('Runtime.evaluate',{expression,returnByValue:true})).result.value;};
 const deadline=Date.now()+3000,samples=[];writeFileSync(join(directory,'testing-readiness.json'),'[]');
 const prepTask=async(task)=>{const remaining=deadline-Date.now();if(remaining<=0)throw Error('Original3s Testing readiness deadline exhausted');let timer;try{const value=await Promise.race([task(),new Promise((_,reject)=>{timer=setTimeout(()=>reject(Error('Original3s Testing readiness deadline exhausted')),remaining);})]);if(Date.now()>=deadline)throw Error('Late Testing readiness response refused');return value;}finally{clearTimeout(timer);}};
 const prepRead=()=>prepTask(read);
 let before,ready=false;while(Date.now()<deadline){before=await prepRead();let reason=before?.unavailable?'Testing root unavailable':null;if(before&&!before.unavailable){const collapsed=before.rows.find(r=>r.expanded==='false');if(metadata.visible&&collapsed){for(const type of ['mousePressed','mouseReleased'])await prepTask(()=>client.request('Input.dispatchMouseEvent',{type,...collapsed.point,button:'left',clickCount:1}));reason='Expanding compiler hierarchy';}else{try{require('./hierarchy-lifecycle.cjs').assertRenderedTree(before,metadata);ready=true;}catch(error){reason=error.message;}}}samples.push({at:Date.now(),unavailable:before?.unavailable??null,reason});writeFileSync(join(directory,'testing-readiness.json'),JSON.stringify(samples,null,2));if(ready)break;await new Promise(r=>setTimeout(r,20));}
 if(!ready){try{await capture(client,directory,true);}catch{}throw Error('Owned Testing hierarchy did not become ready within original3s deadline');}
 const hover=before.rows.find(r=>r.label==='f');if(hover)await prepTask(()=>client.request('Input.dispatchMouseEvent',{type:'mouseMoved',x:hover.point.x+90,y:hover.point.y}));before=await prepRead();require('./hierarchy-lifecycle.cjs').assertRenderedTree(before,metadata);writeFileSync(join(directory,'testing-before.json'),JSON.stringify(before,null,2));const captured=await capture(client,directory,true),after=await read();writeFileSync(join(directory,'testing-after.json'),JSON.stringify(after,null,2));require('node:assert/strict').deepEqual(after,before,'Testing tree/buttons changed during capture');require('./hierarchy-lifecycle.cjs').assertRenderedTree(before,metadata);return{...captured,testing:{binding:metadata.binding,...before,before,after,scope:'Actual Testing-view DOM before/after AX/PNG, compiler-only hierarchy and raw button attributes; not raster identity or proof outcomes.'}};
}
async function buildKeybinding(client,{operation='build',custom=false,input,cancel=false,dismissOnSubmit=false,onPrompt,directory}={}) {
  if(!['build','run','test'].includes(operation)||custom&&operation!=='build')throw Error('Unsupported native command key operation');
  const focused=await client.request('Runtime.evaluate',{expression:'(()=>{const editor=document.querySelector(".monaco-editor.focused")||document.querySelector(".monaco-editor");editor?.querySelector("textarea, [role=textbox], [contenteditable=true]")?.focus();return !!document.activeElement?.closest(".monaco-editor");})()',returnByValue:true});
  if(!focused.result.value)throw Error('No focused source editor for build keybinding');
  const started=Date.now(),keyEvents=[],inputEvents=[];
  const send=async(method,params,editing=false)=>{const started=Date.now();await client.request(method,params);(editing?inputEvents:keyEvents).push({method,params,started,finished:Date.now()});};
  const key=custom?'F6':operation==='build'?'B':'F5',code=custom?'F6':operation==='build'?'KeyB':'F5',windowsVirtualKeyCode=custom?117:operation==='build'?66:116,modifiers=custom?0:operation==='build'?10:operation==='test'?8:0;
  for(const type of ['keyDown','keyUp'])await send('Input.dispatchKeyEvent',{type,key,code,windowsVirtualKeyCode,modifiers});
  let prompt;
  if(custom){
    const query='(()=>{const roots=[document];for(let i=0;i<roots.length;i++){const root=roots[i];const input=[...root.querySelectorAll(".quick-input-widget input")].find(e=>e.getClientRects().length);if(input)return{value:input.value,focused:input===input.ownerDocument.activeElement||input.getRootNode().activeElement===input};for(const e of root.querySelectorAll("*"))if(e.shadowRoot)roots.push(e.shadowRoot);}return null;})()';
    const deadline=Date.now()+3000;let before;
    while(Date.now()<deadline){before=(await client.request('Runtime.evaluate',{expression:query,returnByValue:true})).result.value;if(before?.focused)break;await new Promise(r=>setTimeout(r,20));}
    if(!before?.focused)throw Error('Actual F6 input prompt is not focused');
    if(onPrompt)await onPrompt({before,deadline});
    if(input!==undefined){for(const type of ['keyDown','keyUp'])await send('Input.dispatchKeyEvent',{type,key:'a',code:'KeyA',windowsVirtualKeyCode:65,modifiers:2},true);await send('Input.insertText',{text:input},true);}
    const submitted=(await client.request('Runtime.evaluate',{expression:query,returnByValue:true})).result.value;if(!submitted?.focused||input!==undefined&&submitted.value!==input)throw Error('F6 prompt contents did not match requested input');
    const rendered=await capture(client,directory,true);prompt={before,submitted,rendered};
    const key=cancel?'Escape':'Enter',code=key,windowsVirtualKeyCode=cancel?27:13;
    for(const type of ['keyDown','keyUp'])await send('Input.dispatchKeyEvent',{type,key,code,windowsVirtualKeyCode});
    if(cancel||dismissOnSubmit){let visible;do{visible=(await client.request('Runtime.evaluate',{expression:query,returnByValue:true})).result.value;if(!visible)break;await new Promise(r=>setTimeout(r,20));}while(Date.now()<deadline);if(visible)throw Error('Submitted/cancelled F6 prompt remains visible');const hidden=join(directory,cancel?'cancelled':'dismissed');require('node:fs').mkdirSync(hidden,{recursive:true});prompt[cancel?'cancelled':'dismissed']={visible:false,rendered:await capture(client,hidden,true)};}
  }
  return {started,finished:Date.now(),focusedEditor:true,chord:custom?'f6':operation==='build'?'ctrl+shift+b':operation==='test'?'shift+f5':'f5',keyEvents,inputEvents,prompt,scope:'Actual Linux renderer key dispatch; outcome requires owned command/terminal or source compiler evidence. Not proof or macOS key-dispatch evidence.'};
}
async function captureProofHover(client,directory,metadata){
 const checks=require('./proof-help.cjs');checks.popupExpected(metadata);
 const expression=`(()=>{const visible=e=>{const s=getComputedStyle(e),r=e.getBoundingClientRect();return r.width>0&&r.height>0&&s.visibility!=='hidden'&&s.display!=='none'&&Number(s.opacity)>0;},active=[...document.querySelectorAll('.monaco-editor[data-uri]')].find(e=>visible(e)&&e.closest('.editor-group-container.active'));return {at:Date.now(),activeUri:active?.getAttribute('data-uri')??null,widgets:[...document.querySelectorAll('.monaco-hover')].filter(visible).map(e=>{const r=e.getBoundingClientRect();return {fullyVisible:r.left>=0&&r.top>=0&&r.right<=innerWidth&&r.bottom<=innerHeight,rows:[...e.querySelectorAll('.hover-row')].map(row=>[...row.querySelectorAll('.rendered-markdown')].flatMap(md=>[...md.children].map(block=>({kind:block.querySelector('.monaco-tokenized-source')?'code':block.tagName==='P'?'paragraph':'unknown',text:block.innerText}))))};})};})()`;
 const inspect=async()=>{const value=(await client.request('Runtime.evaluate',{expression,returnByValue:true})).result.value;return value;};let shown,hidden;
 try{
  const deadline=Date.now()+3000;
  do{shown=await inspect();if(shown?.widgets?.length&&shown.widgets.every(w=>w.fullyVisible))break;await new Promise(r=>setTimeout(r,20));}while(Date.now()<deadline);
  checks.popupObservation(shown,metadata);writeFileSync(join(directory,'hover-rendered.json'),JSON.stringify(shown,null,2));const rendered=await capture(client,directory,true);const shownAfterCapture=await inspect();checks.popupObservation(shownAfterCapture,metadata);writeFileSync(join(directory,'hover-after-capture.json'),JSON.stringify(shownAfterCapture,null,2));
  for(const type of ['keyDown','keyUp'])await client.request('Input.dispatchKeyEvent',{type,key:'Escape',code:'Escape',windowsVirtualKeyCode:27});
  do{hidden=await inspect();if(hidden?.widgets?.length===0)break;await new Promise(r=>setTimeout(r,20));}while(Date.now()<deadline);
  checks.popupObservation(hidden,metadata,true);if(hidden.at<shown.at)throw Error('Renderer observation clock moved backwards');writeFileSync(join(directory,'hover-hidden.json'),JSON.stringify(hidden,null,2));
  const dismissed=join(directory,'dismissed');require('node:fs').mkdirSync(dismissed,{recursive:true});await capture(client,dismissed,true);
  return {...rendered,hoverPopup:{shown,shownAfterCapture,hidden,binding:metadata.binding,scope:'Actual current Linux popup contents and Escape disappearance; no paired Dafny/macOS or inferred per-function proof progress.'}};
 }catch(error){try{writeFileSync(join(directory,'hover-attempt.json'),JSON.stringify({shown,hidden,error:String(error)},null,2));await capture(client,directory,true);}catch{}throw error;}
}
async function captureProofHelp(client,directory,metadata){
 if(metadata.action==='hover')return captureProofHover(client,directory,metadata);
 const inspect=()=>client.request('Runtime.evaluate',{expression:`(()=>{const editors=[...document.querySelectorAll('.monaco-editor[data-uri]')].filter(e=>e.getClientRects().length),active=editors.find(e=>e.closest('.editor-group-container.active')),input=[...document.querySelectorAll('.quick-input-widget input')].find(e=>e.getClientRects().length),items=[...document.querySelectorAll('.quick-input-list .monaco-list-row')].filter(e=>e.getClientRects().length).map(e=>({label:e.querySelector('.label-name')?.textContent??e.innerText.split('\\n')[0],text:e.innerText}));return {activeUri:active?.getAttribute('data-uri')??null,inputFocused:!!input&&input===document.activeElement,inputValue:input?.value??null,items};})()`,returnByValue:true});
 let observed;
 try{
  if(metadata.action==='menu'){
   const deadline=Date.now()+3000;
   do{observed=(await inspect()).result.value;if(observed.inputFocused&&observed.items.some(row=>row.label===metadata.label))break;await new Promise(r=>setTimeout(r,20));}while(Date.now()<deadline);
   require('./proof-help.cjs').menuObservation(observed,metadata.binding,metadata.label);
   writeFileSync(join(directory,'proof-help-rendered.json'),JSON.stringify(observed,null,2));const rendered=await capture(client,directory,true);
   await client.request('Input.insertText',{text:metadata.label});
   let filtered;do{filtered=(await inspect()).result.value;if(filtered.inputFocused&&filtered.items.length===1&&filtered.items[0].label===metadata.label)break;await new Promise(r=>setTimeout(r,20));}while(Date.now()<deadline);
   if(!filtered?.inputFocused||filtered.items.length!==1||filtered.items[0].label!==metadata.label)throw Error('Native proof-help picker did not select exactly the requested action');
   for(const type of ['keyDown','keyUp'])await client.request('Input.dispatchKeyEvent',{type,key:'Enter',code:'Enter',windowsVirtualKeyCode:13});
   return {...rendered,proofHelp:observed,selection:{label:metadata.label,filtered}};
  }
  if(metadata.action!=='document'||!metadata.destination?.uri)throw Error('Missing proof documentation destination');
  const deadline=Date.now()+3000;do{observed=(await inspect()).result.value;if(observed.activeUri===metadata.destination.uri)break;await new Promise(r=>setTimeout(r,20));}while(Date.now()<deadline);
  if(observed.activeUri!==metadata.destination.uri)throw Error('Native documentation editor URI mismatch');writeFileSync(join(directory,'proof-help-rendered.json'),JSON.stringify(observed,null,2));return {...await capture(client,directory,true),proofHelp:observed};
 }catch(error){try{writeFileSync(join(directory,'proof-help-attempt.json'),JSON.stringify(observed??null));await capture(client,directory,true);}catch{}throw error;}
}
// Public output API presentation, observed from real renderer DOM/AX; no proof or full lifecycle equivalence.
async function captureOutput(client,directory,metadata){
 const deadline=performance.now()+15000,visibility=require('./output-visibility.cjs');
 const timeout=()=>Object.assign(Error('Output capture exhausted original15000ms deadline'),{code:'TIMEOUT'});
 const boundedClient={request:async(...args)=>{const remaining=deadline-performance.now();if(remaining<=0)throw timeout();let timer;try{return await Promise.race([client.request(...args),new Promise((_,reject)=>{timer=setTimeout(()=>reject(timeout()),remaining);})]);}finally{clearTimeout(timer);}}};
 const read=async()=>{const result=await boundedClient.request('Runtime.evaluate',{expression:`(()=>{const node=document.querySelector('.output-view')||document.getElementById('workbench.panel.output');if(!node)return null;const visible=e=>!!e&&[...e.getClientRects()].some(r=>r.width>0&&r.height>0)&&getComputedStyle(e).visibility!=='hidden';const panel=node.closest('.part')||node.parentElement;const selects=[...panel.querySelectorAll('.monaco-select-box')].filter(visible).map(e=>({tag:e.tagName,label:(e.selectedOptions?.[0]?.textContent??e.innerText??'').trim(),ariaLabel:e.getAttribute('aria-label'),title:e.title}));const viewport=(node.querySelector('.overflow-guard')||node).getBoundingClientRect();const geometry=[...node.querySelectorAll('.view-line')].map(e=>{const r=e.getBoundingClientRect();return{text:e.textContent,top:r.top,left:r.left,bottom:r.bottom,right:r.right,intersectsViewport:r.bottom>viewport.top&&r.top<viewport.bottom&&r.right>viewport.left&&r.left<viewport.right};});const segments=geometry.map(e=>e.text);return{visible:visible(node),text:node.innerText,segments,geometry,continuousText:segments.join('').replace(/\u00a0/g,' '),selects,selectedChannel:selects.length===1?selects[0].label:null};})()`,returnByValue:true});return result.result.value;};
 const valid=o=>typeof metadata.readinessLine==='string'&&metadata.readinessLine.length>0&&o?.visible&&o.selectedChannel===metadata.channel&&o.continuousText?.includes(metadata.readinessLine);
 const expression='('+visibility.probe.toString()+')('+JSON.stringify(metadata.readinessLine)+')',inspect=async()=>{const result=await boundedClient.request('Runtime.evaluate',{expression,returnByValue:true});return result.result.value;};
 let samples=0,primary;
 try{
  // Initialize the actual AX/DOM inspection path before settling. This diagnostic
  // image is not an accepted bracket; watcher epoch is never reset afterward.
  const initial=await inspect();writeFileSync(join(directory,'output-preparation-initial.json'),JSON.stringify(initial,null,2));
  const preparation=join(directory,'preparation');mkdirSync(preparation,{recursive:true});await capture(boundedClient,preparation,true);
  const prepared=await visibility.prepare({read,inspect,valid,expected:metadata.readinessLine,channel:metadata.channel,deadline,now:()=>performance.now(),delay:ms=>new Promise(resolve=>setTimeout(resolve,ms)),record:async sample=>{writeFileSync(join(directory,'output-preparation-'+String(samples++).padStart(3,'0')+'.json'),JSON.stringify(sample,null,2));}});
  const before=prepared.visible,glyphBefore=prepared.glyph;writeFileSync(join(directory,'output-visible-before.json'),JSON.stringify(before,null,2));writeFileSync(join(directory,'output-glyph-before.json'),JSON.stringify(glyphBefore,null,2));
  // One screenshot bracket only: a failed bracket is never retried or selected away.
  const captured=await capture(boundedClient,directory,true),after=await read(),glyphAfter=await inspect();writeFileSync(join(directory,'output-glyph-after.json'),JSON.stringify(glyphAfter,null,2));writeFileSync(join(directory,'output-visible-after.json'),JSON.stringify(after,null,2));
  const glyphErrors=visibility.errors(glyphBefore,glyphAfter,metadata.readinessLine,metadata.channel);if(glyphErrors.length)throw Error('Output glyph geometry refused: '+glyphErrors.join('; '));
  if(!valid(after)||before.continuousText!==after.continuousText)throw Error('Output content/channel changed during screenshot capture');
  if(performance.now()>=deadline)throw timeout();
  return{...captured,output:{panelVisible:true,readinessVisibility:'not-certified',preparationSamples:samples,glyphGeometry:{before:glyphBefore,after:glyphAfter,scope:'DOM Range geometry/hit-test coverage, not raster glyph identity or unobserved compositor ABA.'},scope:'Visible panel/channel; full owned readiness is DOM-resident. Per-character clipping/visibility is unproved.',selectedChannel:before.selectedChannel,text:before.continuousText,before,after,readinessLine:metadata.readinessLine}};
 }catch(error){primary=error;writeFileSync(join(directory,'output-capture-failure.json'),JSON.stringify({message:error.message,code:error.code,at:performance.now()},null,2));throw error;
 }finally{
  const cleanup={requested:performance.now(),deadline,confirmed:false};let timer;
  try{
   const pending=client.request('Runtime.evaluate',{expression:'('+visibility.probe.toString()+')(null,true)',returnByValue:true}),remaining=deadline-performance.now();
   if(remaining<=0){pending.catch(()=>{});throw timeout();}
   const result=await Promise.race([pending,new Promise((_,reject)=>{timer=setTimeout(()=>reject(timeout()),remaining);})]);
   if(result?.result?.value!==true)throw Error('Output observer cleanup was not confirmed');if(performance.now()>=deadline)throw timeout();cleanup.confirmed=true;
  }catch(error){cleanup.error=error.message;cleanup.connectionRetired=typeof client.close==='function';client.close?.();if(!primary)throw error;
  }finally{clearTimeout(timer);cleanup.finished=performance.now();writeFileSync(join(directory,'output-observer-cleanup.json'),JSON.stringify(cleanup,null,2));}
 }
}
async function captureCompilerConfiguration(client,directory,metadata){
 const settingKey=metadata.section==='dafny'?'dafny.compilerOutputDir':'solidityLean.compilerOutputDir';
 const read=async()=>{const result=await client.request('Runtime.evaluate',{expression:`(()=>{const visible=e=>{const r=e.getBoundingClientRect(),s=getComputedStyle(e);return r.width>0&&r.height>0&&s.visibility!=='hidden'&&s.display!=='none';};const active=[...document.querySelectorAll('.monaco-editor[data-uri]')].find(e=>visible(e)&&e.closest('.editor-group-container.active'));const rows=[...document.querySelectorAll('[data-key='+${JSON.stringify(JSON.stringify(metadata.section==='dafny'?'dafny.compilerOutputDir':'solidityLean.compilerOutputDir'))}+']')].filter(visible).map(e=>({key:e.getAttribute('data-key'),text:e.innerText,values:[...e.querySelectorAll('input')].map(i=>i.value)}));return{activeUri:active?.getAttribute('data-uri'),text:active?[...active.querySelectorAll('.view-line')].map(e=>e.textContent).join('').replace(/\u00a0/g,' '):null,rows};})()`,returnByValue:true});return result.result.value;};
 const valid=s=>metadata.presentation==='default-ui'?s.rows.some(r=>r.key===settingKey&&r.values.includes('bin')):s.activeUri===metadata.settingsUri&&s.text?.includes(JSON.stringify(settingKey))&&s.text.includes(JSON.stringify(metadata.effective));
 const deadline=Date.now()+15000;let before;do{before=await read();if(valid(before))break;await new Promise(resolve=>setTimeout(resolve,50));}while(Date.now()<deadline);writeFileSync(join(directory,'configuration-before.json'),JSON.stringify(before,null,2));const rendered=await capture(client,directory,true),after=await read();writeFileSync(join(directory,'configuration-after.json'),JSON.stringify(after,null,2));
 if(!valid(before)||!valid(after)||JSON.stringify(before)!==JSON.stringify(after))throw Error('Rendered output directory configuration/source changed or missing');return{...rendered,configuration:{before,after,metadata,scope:'Actual Settings UI default or resource JSON DOM/AX/PNG; not full glyph/raster equivalence.'}};
}
module.exports={withPhaseRenderer,phaseDiagnostic,captureTrustControl,captureContributionMenu,captureContributionMenuWithTabHit,testingLabel,captureProblems,captureProblemsScroll:require('./diagnostic-problems-scroll.cjs').capture,captureTesting,availablePort,DevTools,connect,capture,inputProbe,buildKeybinding,contextSubmenu,captureTrace,captureProofHelp,captureProofHover,captureOutput,captureCompilerConfiguration};
