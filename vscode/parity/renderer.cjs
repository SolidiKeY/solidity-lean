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
    const state=await client.request('Runtime.evaluate',{expression:menuNodes+'.filter(e=>e.getClientRects().length).map(e=>{const item=e.closest("[role=menuitem]");return{label:e.textContent,ariaDisabled:item?.getAttribute("aria-disabled")??null,className:item?.className??null};})',returnByValue:true});const rendered=await capture(client,directory,true);return{labels:visible,items:state.result.value,rendered,scope:'Actual Linux context submenu and raw enabled-state attributes; action execution, pairing and macOS remain separate observations.'};
  } catch(error){try{writeFileSync(join(directory,'attempt-labels.json'),JSON.stringify((await labels()).result.value));await capture(client,directory,true);}catch{}throw error;} finally {for(let i=0;i<2;i++)for(const type of ['keyDown','keyUp'])await client.request('Input.dispatchKeyEvent',{type,key:'Escape',code:'Escape',windowsVirtualKeyCode:27});}
}
async function captureTrace(client,directory,metadata){
 if(metadata.theme){const deadline=Date.now()+3000;let ready;do{ready=(await client.request('Runtime.evaluate',{expression:'!!document.querySelector(".monaco-workbench.'+metadata.theme+'")',returnByValue:true})).result.value;if(ready)break;await new Promise(r=>setTimeout(r,20));}while(Date.now()<deadline);if(!ready)throw Error('Requested native theme did not settle');}
 const inspection=await client.request('Runtime.evaluate',{expression:`(()=>{const editors=[...document.querySelectorAll('.monaco-editor[data-uri]')].filter(e=>e.getClientRects().length),active=editors.find(e=>e.closest('.editor-group-container.active')),annotations=[];for(const editor of editors){const numbers=[...editor.querySelectorAll('.margin-view-overlays .line-numbers')];for(const line of editor.querySelectorAll('.view-lines .view-line')){const y=line.getBoundingClientRect().top,number=numbers.find(n=>Math.abs(n.getBoundingClientRect().top-y)<1);for(const span of line.querySelectorAll('span[class*="TextEditorDecorationType"]')){const style=getComputedStyle(span,'::after');if(['none','normal','""'].includes(style.content))continue;let text;try{text=JSON.parse(style.content);}catch{text=null;}annotations.push({uri:editor.getAttribute('data-uri'),line:number?Number(number.textContent):null,text,content:style.content,className:span.className,color:style.color,backgroundColor:style.backgroundColor,marginLeft:style.marginLeft,marginTop:style.marginTop,marginRight:style.marginRight,marginBottom:style.marginBottom,visible:line.getBoundingClientRect().bottom>editor.getBoundingClientRect().top&&line.getBoundingClientRect().top<editor.getBoundingClientRect().bottom&&style.visibility!=='hidden'&&style.display!=='none'&&style.opacity!=='0'});}}}return{activeUri:active?.getAttribute('data-uri')??null,annotations};})()`,returnByValue:true});
 const observed=inspection.result.value;writeFileSync(join(directory,'trace-rendered.json'),JSON.stringify(observed,null,2));
 const menuDir=join(directory,'menu');require('node:fs').mkdirSync(menuDir,{recursive:true});observed.menu=await contextSubmenu(client,menuDir,{label:'Dafny',expected:'Build with Custom Arguments'});
 const rendered=await capture(client,directory,true);if(metadata.observeOnly){if(observed.activeUri!==metadata.binding.uri)throw Error('Native observation active URI mismatch');}else require('./trace-presentation.cjs').assertPresentation(observed,metadata);return{...rendered,tracePresentation:{...observed,binding:metadata.binding,asserted:!metadata.observeOnly,scope:metadata.observeOnly?'Native upstream state recorded without a lifecycle-success claim':'Exact content/style/disappearance/menu asserted'}};
}
async function buildKeybinding(client,{custom=false,input,directory}={}) {
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
    for(const type of ['keyDown','keyUp'])await client.request('Input.dispatchKeyEvent',{type,key:'Enter',code:'Enter',windowsVirtualKeyCode:13});
  }
  return {started,finished:Date.now(),focusedEditor:true,chord:custom?'f6':'ctrl+shift+b',prompt,scope:'Actual Linux renderer key dispatch; success requires the host to observe a fresh source-bound compiler artifact. Not proof or macOS key-dispatch evidence.'};
}
module.exports={availablePort,DevTools,connect,capture,inputProbe,buildKeybinding,contextSubmenu,captureTrace};
