'use strict';
const {writeFileSync} = require('node:fs');
const {join} = require('node:path');
const {createServer} = require('node:net');
const {performance} = require('node:perf_hooks');

async function availablePort() {
  const server=createServer();
  await new Promise((resolve,reject)=>{server.once('error',reject);server.listen(0,'127.0.0.1',resolve);});
  const port=server.address().port;await new Promise(resolve=>server.close(resolve));return port;
}
class DevTools {
  constructor(url) {
    this.next=0;this.pending=new Map();this.socket=new WebSocket(url);
    this.ready=new Promise((resolve,reject)=>{
      const timer=setTimeout(()=>reject(new Error('CDP connection timeout')),5000);
      this.socket.addEventListener('open',()=>{clearTimeout(timer);resolve();},{once:true});
      this.socket.addEventListener('error',()=>{clearTimeout(timer);reject(new Error('CDP connection failed'));},{once:true});
    });
    this.socket.addEventListener('message',event=>{
      const message=JSON.parse(event.data),task=this.pending.get(message.id);
      if(!task)return;this.pending.delete(message.id);clearTimeout(task.timer);
      if(message.error)task.reject(new Error(JSON.stringify(message.error)));else task.resolve(message.result);
    });
  }
  async request(method,params={}) {
    await this.ready;const id=++this.next;
    return new Promise((resolve,reject)=>{
      const timer=setTimeout(()=>{this.pending.delete(id);reject(new Error('CDP timeout '+method));},5000);
      this.pending.set(id,{resolve,reject,timer});this.socket.send(JSON.stringify({id,method,params}));
    });
  }
  close() {
    this.socket.close();
    for(const task of this.pending.values()){clearTimeout(task.timer);task.reject(new Error('CDP closed'));}
    this.pending.clear();
  }
}
async function connect(port) {
  const response=await fetch(`http://127.0.0.1:${port}/json/list`,{signal:AbortSignal.timeout(1500)});
  const pages=await response.json();
  const page=pages.find(p=>p.type==='page'&&p.url.startsWith('vscode-file:'));
  if(!page)throw new Error('VS Code renderer not ready');
  return new DevTools(page.webSocketDebuggerUrl);
}
async function capture(client,directory,screenshot=false) {
  const start=performance.now();
  const accessibility=await client.request('Accessibility.getFullAXTree');
  writeFileSync(join(directory,'accessibility.json'),JSON.stringify(accessibility));
  const dom=await client.request('DOMSnapshot.captureSnapshot',{computedStyles:[]});
  writeFileSync(join(directory,'dom.json'),JSON.stringify(dom));
  const inspection=await client.request('Runtime.evaluate',{expression:`JSON.stringify({title:document.title,editorCount:document.querySelectorAll('.monaco-editor').length,notifications:[...document.querySelectorAll('.notification-list-item')].map(e=>e.textContent),visibleHovers:[...document.querySelectorAll('.monaco-hover')].filter(e=>e.getClientRects().length&&getComputedStyle(e).visibility!=='hidden').map(e=>e.innerText),bodyText:document.body.innerText.slice(0,24000)})`,returnByValue:true});
  const visible=JSON.parse(inspection.result.value);
  if(!visible.editorCount||!accessibility.nodes?.length||!dom.documents?.length)throw new Error('Renderer has no inspectable editor, DOM or accessibility tree');
  writeFileSync(join(directory,'visible-state.json'),inspection.result.value);
  if(screenshot) {const result=await client.request('Page.captureScreenshot',{format:'png'});writeFileSync(join(directory,'screenshot.png'),Buffer.from(result.data,'base64'));}
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
async function contextSubmenu(client,directory,{label='Solidity Lean',expected='Build Compiler Artifact with Import Options'}={}) {
  const point=await client.request('Runtime.evaluate',{expression:'(()=>{const e=document.querySelector(".monaco-editor.focused .view-lines")||document.querySelector(".monaco-editor .view-lines");if(!e)return null;const r=e.getBoundingClientRect();return{x:r.left+80,y:r.top+12};})()',returnByValue:true});
  if(!point.result.value)throw Error('No source editor for context submenu capture');
  const menuNodes='(()=>{const roots=[document],nodes=[];for(let i=0;i<roots.length;i++){const root=roots[i];nodes.push(...root.querySelectorAll(".monaco-menu .action-label"));for(const e of root.querySelectorAll("*"))if(e.shadowRoot)roots.push(e.shadowRoot);}return nodes;})()';
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
    const state=await client.request('Runtime.evaluate',{expression:menuNodes+'.filter(e=>e.getClientRects().length).map(e=>{const item=e.closest("[role=menuitem]");const r=e.getBoundingClientRect();return{label:e.textContent,ariaDisabled:item?.getAttribute("aria-disabled")??null,className:item?.className??null,bounds:{left:r.left,top:r.top,right:r.right,bottom:r.bottom},withinViewport:r.left>=0&&r.top>=0&&r.right<=innerWidth&&r.bottom<=innerHeight};})',returnByValue:true});const rendered=await capture(client,directory,true);return{labels:visible,items:state.result.value,rendered,scope:'Actual Linux context submenu and raw enabled-state attributes; action execution, pairing and macOS remain separate observations.'};
  } catch(error){try{writeFileSync(join(directory,'attempt-labels.json'),JSON.stringify((await labels()).result.value));await capture(client,directory,true);}catch{}throw error;} finally {for(let i=0;i<2;i++)for(const type of ['keyDown','keyUp'])await client.request('Input.dispatchKeyEvent',{type,key:'Escape',code:'Escape',windowsVirtualKeyCode:27});}
}
async function captureTrace(client,directory,metadata){
 if(metadata.theme){const deadline=Date.now()+3000;let ready;do{ready=(await client.request('Runtime.evaluate',{expression:'!!document.querySelector(".monaco-workbench.'+metadata.theme+'")',returnByValue:true})).result.value;if(ready)break;await new Promise(r=>setTimeout(r,20));}while(Date.now()<deadline);if(!ready)throw Error('Requested native theme did not settle');}
 const inspection=await client.request('Runtime.evaluate',{expression:`(()=>{const editors=[...document.querySelectorAll('.monaco-editor[data-uri]')].filter(e=>e.getClientRects().length),active=editors.find(e=>e.closest('.editor-group-container.active')),annotations=[];for(const editor of editors){const numbers=[...editor.querySelectorAll('.margin-view-overlays .line-numbers')];for(const line of editor.querySelectorAll('.view-lines .view-line')){const y=line.getBoundingClientRect().top,number=numbers.find(n=>Math.abs(n.getBoundingClientRect().top-y)<1);for(const span of line.querySelectorAll('span[class*="TextEditorDecorationType"]')){const style=getComputedStyle(span,'::after');if(['none','normal','""'].includes(style.content))continue;let text;try{text=JSON.parse(style.content);}catch{text=null;}annotations.push({uri:editor.getAttribute('data-uri'),line:number?Number(number.textContent):null,text,content:style.content,className:span.className,color:style.color,backgroundColor:style.backgroundColor,marginLeft:style.marginLeft,marginTop:style.marginTop,marginRight:style.marginRight,marginBottom:style.marginBottom,visible:line.getBoundingClientRect().bottom>editor.getBoundingClientRect().top&&line.getBoundingClientRect().top<editor.getBoundingClientRect().bottom&&style.visibility!=='hidden'&&style.display!=='none'&&style.opacity!=='0'});}}}return{activeUri:active?.getAttribute('data-uri')??null,annotations};})()`,returnByValue:true});
 const observed=inspection.result.value;writeFileSync(join(directory,'trace-rendered.json'),JSON.stringify(observed,null,2));
 const menuDir=join(directory,'menu');require('node:fs').mkdirSync(menuDir,{recursive:true});observed.menu=await contextSubmenu(client,menuDir,{label:'Dafny',expected:'Build with Custom Arguments'});
 const rendered=await capture(client,directory,true);if(metadata.observeOnly){if(observed.activeUri!==metadata.binding.uri)throw Error('Native observation active URI mismatch');}else require('./trace-presentation.cjs').assertPresentation(observed,metadata);return{...rendered,tracePresentation:{...observed,binding:metadata.binding,asserted:!metadata.observeOnly,scope:metadata.observeOnly?'Native upstream state recorded without a lifecycle-success claim':'Exact content/style/disappearance/menu asserted'}};
}
async function buildKeybinding(client,{custom=false,input,cancel=false,directory}={}) {
  const focused=await client.request('Runtime.evaluate',{expression:'(()=>{const editor=document.querySelector(".monaco-editor.focused")||document.querySelector(".monaco-editor");editor?.querySelector("textarea, [role=textbox], [contenteditable=true]")?.focus();return !!document.activeElement?.closest(".monaco-editor");})()',returnByValue:true});
  if(!focused.result.value)throw Error('No focused source editor for build keybinding');
  const started=Date.now();
  const key=custom?'F6':'B',code=custom?'F6':'KeyB',windowsVirtualKeyCode=custom?117:66,modifiers=custom?0:10;
  for(const type of ['keyDown','keyUp'])await client.request('Input.dispatchKeyEvent',{type,key,code,windowsVirtualKeyCode,modifiers});
  let prompt;
  if(custom){
    const query='(()=>{const roots=[document];for(let i=0;i<roots.length;i++){const root=roots[i];const input=[...root.querySelectorAll(".quick-input-widget input")].find(e=>e.getClientRects().length);if(input)return{value:input.value,focused:input===input.ownerDocument.activeElement||input.getRootNode().activeElement===input};for(const e of root.querySelectorAll("*"))if(e.shadowRoot)roots.push(e.shadowRoot);}return null;})()';
    const deadline=Date.now()+3000;let before;
    while(Date.now()<deadline){before=(await client.request('Runtime.evaluate',{expression:query,returnByValue:true})).result.value;if(before?.focused)break;await new Promise(r=>setTimeout(r,20));}
    if(!before?.focused)throw Error('Actual F6 input prompt is not focused');
    if(input!==undefined){for(const type of ['keyDown','keyUp'])await client.request('Input.dispatchKeyEvent',{type,key:'a',code:'KeyA',windowsVirtualKeyCode:65,modifiers:2});await client.request('Input.insertText',{text:input});}
    const submitted=(await client.request('Runtime.evaluate',{expression:query,returnByValue:true})).result.value;if(!submitted?.focused||input!==undefined&&submitted.value!==input)throw Error('F6 prompt contents did not match requested input');
    const rendered=await capture(client,directory,true);prompt={before,submitted,rendered};
    const key=cancel?'Escape':'Enter',code=key,windowsVirtualKeyCode=cancel?27:13;
    for(const type of ['keyDown','keyUp'])await client.request('Input.dispatchKeyEvent',{type,key,code,windowsVirtualKeyCode});
    if(cancel){let visible;do{visible=(await client.request('Runtime.evaluate',{expression:query,returnByValue:true})).result.value;if(!visible)break;await new Promise(r=>setTimeout(r,20));}while(Date.now()<deadline);if(visible)throw Error('Cancelled F6 prompt remains visible');const hidden=join(directory,'cancelled');require('node:fs').mkdirSync(hidden,{recursive:true});prompt.cancelled={visible:false,rendered:await capture(client,hidden,true)};}
  }
  return {started,finished:Date.now(),focusedEditor:true,chord:custom?'f6':'ctrl+shift+b',prompt,scope:'Actual Linux renderer key dispatch; success requires the host to observe a fresh source-bound compiler artifact. Not proof or macOS key-dispatch evidence.'};
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
 const read=async()=>{const result=await client.request('Runtime.evaluate',{expression:`(()=>{const node=document.querySelector('.output-view')||document.getElementById('workbench.panel.output');if(!node)return null;const visible=e=>!!e&&[...e.getClientRects()].some(r=>r.width>0&&r.height>0)&&getComputedStyle(e).visibility!=='hidden';const panel=node.closest('.part')||node.parentElement;const selects=[...panel.querySelectorAll('.monaco-select-box')].filter(visible).map(e=>({tag:e.tagName,label:(e.selectedOptions?.[0]?.textContent??e.innerText??'').trim(),ariaLabel:e.getAttribute('aria-label'),title:e.title}));const viewport=(node.querySelector('.overflow-guard')||node).getBoundingClientRect();const geometry=[...node.querySelectorAll('.view-line')].map(e=>{const r=e.getBoundingClientRect();return{text:e.textContent,top:r.top,left:r.left,bottom:r.bottom,right:r.right,intersectsViewport:r.bottom>viewport.top&&r.top<viewport.bottom&&r.right>viewport.left&&r.left<viewport.right};});const segments=geometry.map(e=>e.text);return{visible:visible(node),text:node.innerText,segments,geometry,continuousText:segments.join('').replace(/\u00a0/g,' '),selects,selectedChannel:selects.length===1?selects[0].label:null};})()`,returnByValue:true});return result.result.value;};
 const valid=o=>typeof metadata.readinessLine==='string'&&metadata.readinessLine.length>0&&o?.visible&&o.selectedChannel===metadata.channel&&o.continuousText?.includes(metadata.readinessLine);
 const deadline=Date.now()+15000;let before;do{before=await read();if(valid(before))break;await new Promise(resolve=>setTimeout(resolve,50));}while(Date.now()<deadline);
 writeFileSync(join(directory,'output-visible-before.json'),JSON.stringify(before,null,2));
 if(!valid(before)){await capture(client,directory,true).catch(()=>{});throw Error('Actual visible output channel/owned readiness line did not match');}
 const visibility=require('./output-visibility.cjs'),expression='('+visibility.probe.toString()+')('+JSON.stringify(metadata.readinessLine)+')',inspect=async()=>{const result=await client.request('Runtime.evaluate',{expression,returnByValue:true});return result.result.value;};
 try{
 const glyphBefore=await inspect();writeFileSync(join(directory,'output-glyph-before.json'),JSON.stringify(glyphBefore,null,2));
 const captured=await capture(client,directory,true),after=await read(),glyphAfter=await inspect();writeFileSync(join(directory,'output-glyph-after.json'),JSON.stringify(glyphAfter,null,2));writeFileSync(join(directory,'output-visible-after.json'),JSON.stringify(after,null,2));
 const glyphErrors=visibility.errors(glyphBefore,glyphAfter,metadata.readinessLine,metadata.channel);if(glyphErrors.length)throw Error('Output glyph geometry refused: '+glyphErrors.join('; '));
 if(!valid(after)||before.continuousText!==after.continuousText)throw Error('Output content/channel changed during screenshot capture');
 return{...captured,output:{panelVisible:true,readinessVisibility:'not-certified',glyphGeometry:{before:glyphBefore,after:glyphAfter,scope:'DOM Range geometry/hit-test coverage, not raster glyph identity or unobserved compositor ABA.'},scope:'Visible panel/channel; full owned readiness is DOM-resident. Per-character clipping/visibility is unproved.',selectedChannel:before.selectedChannel,text:before.continuousText,before,after,readinessLine:metadata.readinessLine}};
 }finally{await client.request('Runtime.evaluate',{expression:'('+visibility.probe.toString()+')(null,true)',returnByValue:true}).catch(()=>{});}
}
module.exports={availablePort,DevTools,connect,capture,inputProbe,buildKeybinding,contextSubmenu,captureTrace,captureProofHelp,captureProofHover,captureOutput};
