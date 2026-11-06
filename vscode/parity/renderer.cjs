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
async function contextSubmenu(client,directory) {
  const point=await client.request('Runtime.evaluate',{expression:'(()=>{const e=document.querySelector(".monaco-editor.focused .view-lines")||document.querySelector(".monaco-editor .view-lines");if(!e)return null;const r=e.getBoundingClientRect();return{x:r.left+80,y:r.top+12};})()',returnByValue:true});
  if(!point.result.value)throw Error('No source editor for context submenu capture');
  const menuNodes='(()=>{const roots=[document],nodes=[];for(let i=0;i<roots.length;i++){const root=roots[i];nodes.push(...root.querySelectorAll(".monaco-menu .action-label"));for(const e of root.querySelectorAll("*"))if(e.shadowRoot)roots.push(e.shadowRoot);}return nodes;})()';
  const labels=()=>client.request('Runtime.evaluate',{expression:menuNodes+'.filter(e=>e.getClientRects().length).map(e=>e.textContent)',returnByValue:true});
  try {
    for(const type of ['mousePressed','mouseReleased'])await client.request('Input.dispatchMouseEvent',{type,...point.result.value,button:'right',clickCount:1});
    const deadline=Date.now()+3000;let entry;
    while(Date.now()<deadline){entry=await client.request('Runtime.evaluate',{expression:'(()=>{const e='+menuNodes+'.find(e=>e.textContent==="Solidity Lean"&&e.getClientRects().length);if(!e)return null;const r=e.getBoundingClientRect();return{x:r.right-5,y:r.top+r.height/2};})()',returnByValue:true});if(entry.result.value)break;await new Promise(r=>setTimeout(r,20));}
    if(!entry?.result.value)throw Error('Declared Solidity Lean submenu is not visible');
    await client.request('Input.dispatchMouseEvent',{type:'mouseMoved',...entry.result.value});
    let visible;
    while(Date.now()<deadline){visible=(await labels()).result.value;if(visible.some(label=>label.includes('Build Compiler Artifact with Import Options')))break;await new Promise(r=>setTimeout(r,20));}
    if(!visible?.some(label=>label.includes('Build Compiler Artifact with Import Options')))throw Error('Custom compiler action is not rendered in the submenu');
    const rendered=await capture(client,directory,true);return{labels:visible,rendered,scope:'Actual trusted Linux Solidity context submenu; native action execution and Dafny/macOS correspondence are separate obligations.'};
  } catch(error){try{writeFileSync(join(directory,'attempt-labels.json'),JSON.stringify((await labels()).result.value));await capture(client,directory,true);}catch{}throw error;} finally {for(let i=0;i<2;i++)for(const type of ['keyDown','keyUp'])await client.request('Input.dispatchKeyEvent',{type,key:'Escape',code:'Escape',windowsVirtualKeyCode:27});}
}
async function buildKeybinding(client) {
  const focused=await client.request('Runtime.evaluate',{expression:'(()=>{const editor=document.querySelector(".monaco-editor.focused")||document.querySelector(".monaco-editor");editor?.querySelector("textarea, [role=textbox], [contenteditable=true]")?.focus();return !!document.activeElement?.closest(".monaco-editor");})()',returnByValue:true});
  if(!focused.result.value)throw Error('No focused source editor for build keybinding');
  const started=Date.now();
  await client.request('Input.dispatchKeyEvent',{type:'keyDown',key:'B',code:'KeyB',windowsVirtualKeyCode:66,modifiers:10});
  await client.request('Input.dispatchKeyEvent',{type:'keyUp',key:'B',code:'KeyB',windowsVirtualKeyCode:66,modifiers:10});
  return {started,finished:Date.now(),focusedEditor:true,chord:'ctrl+shift+b',scope:'Actual Linux renderer key dispatch; success requires the host to observe a fresh source-bound compiler artifact. Not proof or macOS key-dispatch evidence.'};
}
module.exports={availablePort,DevTools,connect,capture,inputProbe,buildKeybinding,contextSubmenu};
