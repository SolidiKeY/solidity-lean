// Positioned trace presentation only. Guards stale editor data, never derives positions from proof/model reports.
// Production has NO positioned producer: request is null. Test injection exercises this consumer,
// not certification. A future real adapter must establish provenance before supplying this boundary.
'use strict';
const {createHash,randomUUID}=require('node:crypto');
const hash=text=>createHash('sha256').update(text).digest('hex');
const unavailable='Positioned verification traces are unavailable: the backend does not expose a source-bound trace producer.';
function normalize(text){if(text.startsWith('assume '))text=text.slice(7);if(text.endsWith(';'))text=text.slice(0,-1).trimEnd();return text.split(' && ').map(v=>/^.* == [\w'?]+$/.test(v)?v.split(' == ')[1]+' == '+v.split(' == ')[0]:v).join(', ');}
function install(vscode,context,{request=null,clock={set:setTimeout,clear:clearTimeout},notify=message=>vscode.window.showInformationMessage?.(message)}={}){
 const states=new Map(),sessions=new WeakMap();let disposed=false;
 const uri=d=>d.uri.toString(),eligible=e=>!disposed&&vscode.workspace.isTrusted&&e&&!e.document.isClosed&&e.document.uri.scheme==='file'&&/\.sol$/i.test(e.document.uri.fsPath);
 const colors=d=>vscode.workspace.getConfiguration('solidityLean',d.uri).get('verificationTraceColor',{backgroundColor:null,fontColor:null});
 function session(doc){if(!sessions.has(doc))sessions.set(doc,randomUUID());return sessions.get(doc);}
 function state(doc){let s=states.get(uri(doc));if(s&&s.doc!==doc){stop(s);states.delete(uri(doc));s=null;}if(!s){s={doc,enabled:false,epoch:0};states.set(uri(doc),s);}return s;}
 function stop(s,clearDisplay=true){s.epoch++;if(s.timer!==undefined)clock.clear(s.timer);s.timer=undefined;s.abort?.abort();s.abort=null;if(clearDisplay){s.decoration?.dispose();s.decoration=null;s.items=null;}}
 function menu(){const e=vscode.window.activeTextEditor,s=e&&states.get(uri(e.document)),valid=eligible(e)&&s?.doc===e.document;for(const [key,value]of [['CanShow',eligible(e)&&!s?.enabled],['CanHide',valid&&!!s.enabled],['CanCopy',valid&&!!s.items]])Promise.resolve(vscode.commands.executeCommand('setContext','solidityLean.verificationTrace.'+key,!!value)).catch(()=>{});}
 function binding(doc){return{uri:uri(doc),version:doc.version,sourceHash:hash(doc.getText()),session:session(doc),requestId:randomUUID()};}
 function current(editor,s,b,epoch,config){return eligible(editor)&&vscode.window.activeTextEditor===editor&&states.get(b.uri)===s&&s.doc===editor.document&&s.epoch===epoch&&!s.abort?.signal.aborted&&editor.document.version===b.version&&hash(editor.document.getText())===b.sourceHash&&session(editor.document)===b.session&&JSON.stringify(colors(editor.document))===config;}
 function validate(value,b,doc){if(!value||JSON.stringify(value.binding)!==JSON.stringify(b)||!Array.isArray(value.items))throw Error('Trace source/session binding is missing or changed');const lines=doc.getText().split(/\r?\n/);for(const item of value.items){const p=item?.position;if(typeof item?.assumption!=='string'||!p||!Number.isSafeInteger(p.line)||!Number.isSafeInteger(p.character)||p.line<0||p.line>=lines.length||p.character<0||p.character>lines[p.line].length)throw Error('Trace item has no exact in-source UTF16 position');}return value.items;}
 async function fetch(editor,s,copy=false){
  stop(s,!copy);const b=binding(s.doc),epoch=s.epoch,config=JSON.stringify(colors(s.doc));s.abort=new AbortController();menu();
  if(!request){stop(s);s.enabled=false;menu();notify(unavailable);return;}
  try{const value=await request(Object.freeze({...b}),{signal:s.abort.signal});if(!current(editor,s,b,epoch,config))return;if(value===null){stop(s);s.enabled=false;menu();notify(unavailable);return;}const items=validate(value,b,s.doc);
   if(copy){const text=items.map(i=>i.assumption).join('\n\n');if(text)await vscode.env.clipboard.writeText(text);return;}
   if(!s.enabled)return;const options=colors(s.doc)||{},after=(backgroundColor,color)=>({after:{backgroundColor:options.backgroundColor??backgroundColor,color:options.fontColor??color,margin:'0 0 0 30px'}});s.decoration=vscode.window.createTextEditorDecorationType({dark:after('#0d47a1','#e3f2fd'),light:after('#bbdefb','#102027')});s.items=items;editor.setDecorations(s.decoration,items.map(i=>({range:new vscode.Range(i.position.line,i.position.character+1,i.position.line,Number.MAX_VALUE),renderOptions:{after:{contentText:normalize(i.assumption)}}})));menu();
  }catch(error){if(current(editor,s,b,epoch,config)&&error.name!=='AbortError'){notify('Verification trace request failed: '+error.message);menu();}}
 }
 function update(editor,immediate=false){if(!eligible(editor)){menu();return;}const s=state(editor.document);stop(s);menu();if(s.enabled){if(immediate)return fetch(editor,s);s.timer=clock.set(()=>{s.timer=undefined;void fetch(editor,s);},1000);}}
 function reset(target){for(const [id,s]of states)if(!target||id===(typeof target==='string'?target:target.toString())){stop(s);s.enabled=false;}menu();}
 const subscriptions=[
  vscode.commands.registerCommand('solidityLean.showVerificationTrace',()=>{const e=vscode.window.activeTextEditor;if(!eligible(e))return;const s=state(e.document);s.enabled=true;return update(e,true);}),
  vscode.commands.registerCommand('solidityLean.hideVerificationTrace',()=>{const e=vscode.window.activeTextEditor;if(e)reset(e.document.uri);}),
  vscode.commands.registerCommand('solidityLean.copyVerificationTrace',()=>{const e=vscode.window.activeTextEditor;if(!eligible(e))return;const s=state(e.document);return fetch(e,s,true);}),
  vscode.workspace.onDidChangeTextDocument(e=>{if(e.contentChanges.length){const s=states.get(uri(e.document));if(s?.doc===e.document){stop(s);if(vscode.window.activeTextEditor?.document===e.document)update(vscode.window.activeTextEditor);}}}),
  vscode.workspace.onDidCloseTextDocument(doc=>{const s=states.get(uri(doc));if(s?.doc===doc){stop(s);states.delete(uri(doc));}menu();}),
  vscode.workspace.onDidChangeConfiguration(e=>{for(const s of states.values())if(e.affectsConfiguration('solidityLean',s.doc.uri)){stop(s);if(vscode.window.activeTextEditor?.document===s.doc)update(vscode.window.activeTextEditor);}menu();}),
  vscode.window.onDidChangeActiveTextEditor?.(editor=>{for(const s of states.values())stop(s);update(editor);}),
  vscode.workspace.onDidChangeWorkspaceFolders?.(()=>reset())
 ].filter(Boolean);
 const api={reset,dispose(){if(disposed)return;disposed=true;for(const s of states.values())stop(s);states.clear();for(const sub of subscriptions)sub.dispose();menu();}};context.subscriptions.push(api);menu();return api;
}
module.exports={install,normalize,unavailable};
