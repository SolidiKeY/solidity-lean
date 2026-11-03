/* global require, monaco */
'use strict';
// Monaco's delayed word-highlighting timer rejects with CancellationError when
// a model is switched before the timer fires. Treat that exact cancellation as
// expected, while leaving every other unhandled failure visible.
window.addEventListener('unhandledrejection',event=>{if(event.reason?.name==='Canceled'&&event.reason?.message==='Canceled')event.preventDefault();});
const $ = selector => document.querySelector(selector);
const $$ = selector => [...document.querySelectorAll(selector)];
const usingNativeBackend=new URLSearchParams(location.search).get('backend')==='native';
const icons = {
  explorer:'<path d="M8 3h9l4 4v14H8z"/><path d="M17 3v5h4M5 7H3v14h2"/>',
  search:'<circle cx="10.5" cy="10.5" r="6.5"/><path d="m16 16 5 5"/>',
  changes:'<circle cx="7" cy="5" r="2.5"/><circle cx="7" cy="20" r="2.5"/><circle cx="18" cy="7" r="2.5"/><path d="M7 7.5v10M7 14h4a7 7 0 0 0 7-4.5"/>',
  run:'<path d="m7 4 14 8-14 8z"/>',
  extensions:'<path d="M3 3h8v8H3zM3 13h8v8H3zM13 13h8v8h-8zM17 2l5 5-5 5-5-5z"/>',
  testing:'<path d="M9 3h6M10 3v7L4 20q0 1 1 1h14q1 0 1-1l-6-10V3M7 15h10"/>',
  settings:'<path d="m10 2 4 0 .7 3 2 .9 2.7-1.4 2 3.5-2 2.1v2.5l2 2.1-2 3.5-2.7-1.4-2 .9-.7 3h-4l-.7-3-2-.9-2.7 1.4-2-3.5 2-2.1v-2.5l-2-2.1 2-3.5L7.3 6l2-.9z"/><circle cx="12" cy="12" r="3.5"/>',
  offline:'<path d="M4 6h16v12H4zM8 21h8M12 18v3"/><path d="m9 11 2 2 4-4"/>',
  runAll:'<path d="m3 4 12 8-12 8zM15 4l7 8-7 8"/>',
  refresh:'<path d="M20 7a9 9 0 1 0 0 10M20 3v5h-5"/>',
  stop:'<path d="M5 5h14v14H5z"/>',
  plus:'<path d="M12 4v16M4 12h16"/>',
  file:'<path d="M5 2h10l5 5v15H5zM15 2v6h5M8 14h9M12.5 10v9"/>',
  upload:'<path d="M4 15v6h16v-6M12 17V3m-5 5 5-5 5 5"/>',
  collapse:'<path d="M4 9h13v12H4zM8 5h13v12M7 15h7"/>',
  clear:'<path d="m7 3 11 12-6 6-11-12zM12 21h11M7 15l6-6"/>',
  layout:'<path d="M3 4h18v16H3zM3 15h18"/>',
  bell:'<path d="M5 17h14l-2-3V9a5 5 0 0 0-10 0v5zM10 20h4"/>'
};
function svg(name) { return `<svg viewBox="0 0 24 24" aria-hidden="true">${icons[name] || icons.file}</svg>`; }
for (const b of $$('[data-view]')) b.insertAdjacentHTML('afterbegin', svg(b.dataset.view));
$('#offline-button').innerHTML = svg('offline'); $('#notification-button').innerHTML = svg('bell');
$('#verify-button').innerHTML = svg('run'); $('#layout-button').innerHTML = svg('layout'); $('#clear-output').innerHTML = svg('clear');
const store = {
  read(key, fallback) { try { return JSON.parse(localStorage.getItem(`solidity-lean:${key}`)) ?? fallback; } catch { return fallback; } },
  write(key, value) { try { localStorage.setItem(`solidity-lean:${key}`, JSON.stringify(value)); return true; } catch { toast('Browser storage is full. Export your files to keep your changes.'); return false; } }
};
const state = {
  files:{}, baselines:{}, active:'Counter.sol', view:'explorer', panel:'problems', testFilter:'', diagnostics:new Map(), reports:new Map(),
  statuses:new Map(), models:new Map(), views:new Map(), opened:new Set(), dirty:new Set(), versions:new Map(),
  symbols:new Map(), decorations:new Map(), synced:new Map(), syncing:new Map(), workspaceSynced:new Map(), runtime:{mode:usingNativeBackend?'native':'browser',proofReady:usingNativeBackend}, revision:0, logs:[], timing:[], settings:store.read('settings', {automaticVerification:'never',counterexamples:false,auditPreconditions:false,workers:1}), connected:false
};
let editor, socket, requestID = 0, reconnectTimer, symbolTimer, saveTimer, toastTimer, paletteIndex = 0, paletteCommands = [];
const requests = new Map();
function toast(text) { $('#toast').textContent = text; $('#toast').hidden = false; clearTimeout(toastTimer); toastTimer = setTimeout(() => {$('#toast').hidden = true;}, 7000); }
function log(message) { state.logs.push(message); if (state.logs.length > 1000) state.logs.shift(); if (state.panel === 'output') renderPanel(); }
function persistNow() { return store.write('workspace',{files:state.files,baselines:state.baselines,active:state.active,opened:[...state.opened],dirty:[...state.dirty]}); }
function persist() { clearTimeout(saveTimer); saveTimer = setTimeout(persistNow,150); }
function rpc(method, params = {}) {
  if (!state.connected || socket?.readyState !== 1) return Promise.reject(new Error(usingNativeBackend?'Native development backend disconnected.':'The browser compiler is still preparing.'));
  const id = ++requestID;
  return new Promise((resolve,reject) => {
    const timeout=!usingNativeBackend&&method==='verify'?(state.settings.timeoutMs||600000)+10000:150000;
    const timer = setTimeout(() => {requests.delete(id);if(!usingNativeBackend&&method==='verify')socket.send(JSON.stringify({id:++requestID,method:'cancel',params:{name:params.name}}));reject(new Error('Browser operation timed out'));}, timeout);
    requests.set(id, {resolve,reject,timer}); socket.send(JSON.stringify({id,method,params}));
  });
}
function notifyError(error) { if (!['CANCELLED',-32800,-32801].includes(error?.code) && !/content changed|version must increase/.test(error?.message || '')) toast(error.message || String(error)); }
function currentVersion(name) { return state.models.get(name)?.getVersionId() || 1; }
function filename(uri) { return decodeURIComponent(uri?.split('/').pop() || ''); }
function connect() {
  clearTimeout(reconnectTimer);
  socket = usingNativeBackend?new WebSocket(`${location.protocol === 'https:' ? 'wss:' : 'ws:'}//${location.host}/lsp`):new BrowserConnection();
  socket.onopen = async () => {
    globalThis.singleFileIDE?.compilerStarted();
    state.connected = true; state.synced.clear(); state.workspaceSynced.clear(); $('#connection-status').textContent = usingNativeBackend?'Native development':'Browser · Offline'; $('.statusbar').classList.remove('reconnecting');
    try { await syncWorkspace(); await rpc('configure',state.settings); await syncAll(); updateStatus(); refreshSymbols(); log(usingNativeBackend?'Connected to the native development backend.':'Solidity WebAssembly compiler and language services are running in this browser.'); } catch (error) {notifyError(error);}
  };
  socket.onmessage = event => {
    let message; try { message = JSON.parse(event.data); } catch { return; }
    if (message.id !== undefined) {
      const pending = requests.get(message.id); if (!pending) return;
      clearTimeout(pending.timer); requests.delete(message.id);
      if (message.error) pending.reject(Object.assign(new Error(message.error.message),{code:message.error.code})); else pending.resolve(message.result);
      return;
    }
    const {method,params:p} = message;
    if(method==='runtime'){Object.assign(state.runtime,p);if(p.error)globalThis.singleFileIDE?.invalidate();log(p.message||'Browser runtime ready.');updateStatus();if(state.view==='settings')renderSidebar();return;}
    if (method === 'backendError') {globalThis.singleFileIDE?.runtimeFailure(new Error(p.message)); log(`Backend error: ${p.message}`); toast(p.message); return; }
    if (method === 'log') { log(p.message); return; }
    if (!p.name || !state.models.has(p.name) || p.version !== currentVersion(p.name)) return;
    if (method !== 'invalidated' && !allSynced()) return;
    if (method === 'diagnostics') {state.diagnostics.set(p.name,p.diagnostics); applyMarkers(p.name); renderPanel(); renderCounts();}
    if (method === 'invalidated') {state.reports.delete(p.name); state.statuses.delete(p.name); drawGutters(p.name); renderSidebar(); renderPanel();}
    if (method === 'status') {state.statuses.set(p.name,p); drawGutters(p.name); updateStatus();}
    if (method === 'report') {
      const previous = state.reports.get(p.name);
      const rows = p.selection?.function && previous ? [...previous.results.filter(old => !p.report.results.some(row => row.contract === old.contract && (row.signature || row.function) === (old.signature || old.function))), ...p.report.results] : p.report.results;
      state.reports.set(p.name,{...p.report,results:rows});
      for (const row of p.report.results) log(`${row.contract}.${row.signature || row.function}: ${displayStatus(row)}${row.reason ? ` — ${row.reason}` : ''}${row.reading ? `\nObligation reading: ${row.reading}` : ''}`);
      for (const error of p.report.errors) log(`Error: ${error.reason}`);
      renderSidebar(); renderPanel(); renderCounts();
    }
  };
  socket.onclose = () => {
    state.connected = false; state.synced.clear();
    for (const pending of requests.values()) {clearTimeout(pending.timer); pending.reject(new Error('Runtime stopped'));} requests.clear();
    // Never retain certified status after losing the backend connection.
    state.reports.clear(); state.statuses.clear(); state.diagnostics.clear();
    for (const name of state.models.keys()) {applyMarkers(name); drawGutters(name);}
    $('#connection-status').textContent = usingNativeBackend?'Backend disconnected':'Browser runtime stopped'; $('.statusbar').classList.add('reconnecting');
    updateStatus(); renderSidebar(); renderPanel(); renderCounts(); reconnectTimer = setTimeout(connect,3000);
  };
  socket.onerror = event => {if(!usingNativeBackend)globalThis.singleFileIDE?.runtimeFailure(new Error(event?.message||'Embedded compiler worker failed'));};
}
async function sync(name = state.active) {
  const model = state.models.get(name); if (!model) return;
  const version = model.getVersionId();
  if (state.synced.get(name)?.version === version) return;
  const pending = state.syncing.get(name);
  if (pending) {await pending; return sync(name);}
  const promise = rpc('open',{name,text:model.getValue(),version}).then(result => {state.synced.set(name,{version:result.version,uri:result.uri}); return result;});
  state.syncing.set(name,promise);
  try {await promise;} catch (error) {state.synced.delete(name); throw error;}
  finally {if(state.syncing.get(name)===promise)state.syncing.delete(name);}
  if(state.models.has(name)&&currentVersion(name)!==version)return sync(name);
}
async function syncWorkspace() {
  const files=Object.fromEntries(Object.entries(state.files).filter(([name,text])=>state.workspaceSynced.get(name)!==text));
  for(const [name,text]of Object.entries(files)){await rpc('workspace',{files:{[name]:text}});state.workspaceSynced.set(name,text);}
}
function allSynced(){return [...state.models].every(([name,model])=>state.synced.get(name)?.version===model.getVersionId());}
async function syncAll(){const revision=state.revision;await syncWorkspace();await Promise.all([...state.models.keys()].map(name=>sync(name)));if(state.revision!==revision)throw Object.assign(new Error('Document content changed'),{code:-32801});}
async function language(method, model, params = {}) {
  const name = filename(model.uri.toString()); await syncAll();const revision=state.revision;
  const result=await rpc(method,{name,version:model.getVersionId(),...params});
  if(revision!==state.revision)throw Object.assign(new Error('Document content changed'),{code:-32801});
  return result;
}
const range = r => ({startLineNumber:r.start.line+1,startColumn:r.start.character+1,endLineNumber:r.end.line+1,endColumn:r.end.character+1});
const position = p => ({line:p.lineNumber-1,character:p.column-1});
const lspRange = r => ({start:{line:r.startLineNumber-1,character:r.startColumn-1},end:{line:r.endLineNumber-1,character:r.endColumn-1}});
const content = value => typeof value === 'string' ? value : value?.value || '';
function modelURI(uri) { return monaco.Uri.parse(`file:///workspace/${filename(uri)}`); }
function applyMarkers(name) {
  if (!state.models.has(name)) return;
  monaco.editor.setModelMarkers(state.models.get(name),'solidity-lean',(state.diagnostics.get(name) || []).map(d => ({...range(d.range),severity:({1:monaco.MarkerSeverity.Error,2:monaco.MarkerSeverity.Warning,3:monaco.MarkerSeverity.Info,4:monaco.MarkerSeverity.Hint})[d.severity],message:d.message,source:d.source,code:String(d.code || '')})));
}
function drawGutters(name) {
  const model = state.models.get(name); if (!model) return;
  const functions = state.statuses.get(name)?.functions || [];
  const rows=state.reports.get(name)?.results||[];
  const next = functions.filter(f => f.range).flatMap(f => {
    const row=rows.find(r=>r.range?.start.line===f.range.start.line);
    const decorations=[];
    for(let line=f.range.start.line;line<=f.range.end.line;line++){
      const runnable=row&&line===f.range.start.line;
      decorations.push({range:new monaco.Range(line+1,1,line+1,1),options:{isWholeLine:true,glyphMarginClassName:runnable?'glyph-run':`glyph-${f.status}`,glyphMarginHoverMessage:{value:runnable?`Verify ${row.contract}.${row.signature||row.function}`:f.status}}});
    }
    return decorations;
  });
  state.decorations.set(name,model.deltaDecorations(state.decorations.get(name) || [],next));
}
function registerLanguage(grammar) {
  monaco.languages.register({id:'solidity',extensions:['.sol'],aliases:['Solidity']});
  monaco.languages.setLanguageConfiguration('solidity',{comments:{lineComment:'//',blockComment:['/*','*/']},brackets:[['{','}'],['[',']'],['(',')']],autoClosingPairs:[{open:'{',close:'}'},{open:'[',close:']'},{open:'(',close:')'},{open:'"',close:'"'},{open:"'",close:"'"}]});
  // Reuse the extension's exact token patterns rather than maintaining another
  // Solidity keyword list. Its small TextMate grammar needs no Oniguruma/WASM.
  const shared = grammar.patterns.filter(p => p.match && !p.name.startsWith('comment.')).map(p => [new RegExp(p.match),p.name.replace(/\.solidity$/,'')]);
  monaco.languages.setMonarchTokensProvider('solidity',{tokenizer:{
    root:[[/\/\/.*$/,'comment'],[/\/\*/,'comment','@comment'],[/"/,'string','@doubleString'],[/'/,'string','@singleString'],...shared,[/[a-zA-Z_$][\w$]*/,'identifier'],[/[{}()[\]]/,'delimiter'],[/./,'']],
    comment:[[/[^/*]+/,'comment'],[/\*\//,'comment','@pop'],[/[/*]/,'comment']],
    doubleString:[[/\\./,'string.escape'],[/[^"\\]+/,'string'],[/"/,'string','@pop']],
    singleString:[[/\\./,'string.escape'],[/[^'\\]+/,'string'],[/'/,'string','@pop']]
  }});
  monaco.editor.defineTheme('solidity-extension',{base:'vs-dark',inherit:true,rules:[
    {token:'keyword.control',foreground:'C586C0'},{token:'storage.modifier',foreground:'569CD6'},
    {token:'storage.type',foreground:'569CD6'},{token:'constant.language',foreground:'569CD6'},
    {token:'constant.numeric',foreground:'B5CEA8'},{token:'comment',foreground:'6A9955'},
    {token:'string',foreground:'CE9178'},{token:'string.escape',foreground:'D7BA7D'},
    {token:'identifier',foreground:'D4D4D4'},{token:'delimiter',foreground:'D4D4D4'}
  ],colors:{'editor.background':'#1e1e1e','editor.foreground':'#d4d4d4'}});
  monaco.languages.registerHoverProvider('solidity',{async provideHover(model,p){try{const r=await language('textDocument/hover',model,{position:position(p)});return r?{range:r.range?range(r.range):undefined,contents:(Array.isArray(r.contents)?r.contents:[r.contents]).map(c=>({value:c?.kind==='plaintext'?content(c).replace(/[\\`*_{}\[\]()#+.!<>|~-]/g,'\\$&'):content(c),isTrusted:false,supportHtml:false}))}:null;}catch{return null;}}});
  const completionKinds=['Text','Method','Function','Constructor','Field','Variable','Class','Interface','Module','Property','Unit','Value','Enum','Keyword','Snippet','Color','File','Reference','Folder','EnumMember','Constant','Struct','Event','Operator','TypeParameter'];
  monaco.languages.registerCompletionItemProvider('solidity',{triggerCharacters:['.'],async provideCompletionItems(model,p){try{const r=await language('textDocument/completion',model,{position:position(p)});const word=model.getWordUntilPosition(p);return {suggestions:(r?.items||r||[]).map(item=>({label:item.label,kind:monaco.languages.CompletionItemKind[completionKinds[(item.kind||1)-1]]??monaco.languages.CompletionItemKind.Text,detail:item.detail,documentation:item.documentation,insertText:item.textEdit?.newText||item.insertText||item.label,range:item.textEdit?.range?range(item.textEdit.range):new monaco.Range(p.lineNumber,word.startColumn,p.lineNumber,word.endColumn)}))};}catch{return {suggestions:[]};}}});
  monaco.languages.registerDefinitionProvider('solidity',{async provideDefinition(model,p){try{const r=await language('textDocument/definition',model,{position:position(p)});return (Array.isArray(r)?r:r?[r]:[]).map(l=>({uri:modelURI(l.uri),range:range(l.range)}));}catch{return [];}}});
  monaco.languages.registerReferenceProvider('solidity',{async provideReferences(model,p,context){try{return (await language('textDocument/references',model,{position:position(p),context})||[]).map(l=>({uri:modelURI(l.uri),range:range(l.range)}));}catch{return [];}}});
  monaco.languages.registerDocumentHighlightProvider('solidity',{async provideDocumentHighlights(model,p){try{return (await language('textDocument/documentHighlight',model,{position:position(p)})||[]).map(h=>({range:range(h.range),kind:h.kind}));}catch{return [];}}});
  monaco.languages.registerDocumentSymbolProvider('solidity',{async provideDocumentSymbols(model){try{const rows=await language('textDocument/documentSymbol',model);const convert=s=>({...s,kind:s.kind-1,range:range(s.range),selectionRange:range(s.selectionRange),children:s.children?.map(convert)});return rows.map(convert);}catch{return [];}}});
  monaco.languages.registerSignatureHelpProvider('solidity',{signatureHelpTriggerCharacters:['(', ','],async provideSignatureHelp(model,p){try{const value=await language('textDocument/signatureHelp',model,{position:position(p)});return value?{value,dispose(){}}:null;}catch{return null;}}});
  monaco.languages.registerDocumentFormattingEditProvider('solidity',{async provideDocumentFormattingEdits(model,options){try{const rows=await language('textDocument/formatting',model,{options});return (rows||[]).map(e=>({range:range(e.range),text:e.newText}));}catch(error){notifyError(error);return [];}}});
  function workspaceEdit(result) {
    return {edits:(result?.documentChanges||[]).flatMap(change=>{
      const name=filename(change.textDocument.uri);let model=state.models.get(name);
      if(!(name in state.files))throw new Error('Unknown refactoring target');
      if(!model){if(state.models.size>=4)throw new Error('Open the refactoring target after closing another editor tab');state.opened.add(name);model=createModel(name,state.files[name]);renderTabs();}
      if(change.textDocument.version!==null&&change.textDocument.version!==model.getVersionId())throw Object.assign(new Error('Document content changed'),{code:-32801});
      return change.edits.map(e=>({resource:modelURI(change.textDocument.uri),versionId:model.getVersionId(),textEdit:{range:range(e.range),text:e.newText}}));
    })};
  }
  monaco.languages.registerRenameProvider('solidity',{async resolveRenameLocation(model,p){try{const r=await language('textDocument/prepareRename',model,{position:position(p)});return r?{range:range(r.range),text:r.placeholder||model.getWordAtPosition(p)?.word}:null;}catch(error){return {range:new monaco.Range(p.lineNumber,p.column,p.lineNumber,p.column),text:'',rejectReason:error.message};}},async provideRenameEdits(model,p,newName){try{return workspaceEdit(await language('textDocument/rename',model,{position:position(p),newName}));}catch(error){return {edits:[],rejectReason:error.message};}}});
  monaco.languages.registerCodeActionProvider('solidity',{providedCodeActionKinds:['quickfix'],async provideCodeActions(model,selection,context){try{const diagnostics=context.markers.map(m=>({range:lspRange(m),message:m.message,code:typeof m.code==='object'?m.code.value:m.code,severity:m.severity===8?1:2}));const actions=await language('textDocument/codeAction',model,{range:lspRange(selection),context:{diagnostics}});return {actions:(actions||[]).map(a=>({title:a.title,kind:a.kind||'quickfix',edit:workspaceEdit(a.edit),diagnostics:context.markers})),dispose(){}};}catch{return {actions:[],dispose(){}};}}});
}
function createModel(name,text) {
  const model=monaco.editor.createModel(text,'solidity',monaco.Uri.parse(`file:///workspace/${name}`)); state.models.set(name,model); state.versions.set(name,1);
  model.updateOptions({bracketColorizationOptions:{enabled:false,independentColorPoolPerBracketType:false}});
  model.onDidChangeContent(() => {
    state.files[name]=model.getValue();state.revision++; if(model.getValue()===state.baselines[name])state.dirty.delete(name);else state.dirty.add(name);
    clearResults(); renderTabs(); persist();
    // Each edit is sent immediately, so switching files cannot cancel another
    // buffer's synchronization or leave imported declarations behind.
    if(state.connected)sync(name).catch(notifyError);
    clearTimeout(symbolTimer); symbolTimer=setTimeout(()=>refreshSymbols(name),250);
  }); return model;
}
async function openFile(name) {
  if (!(name in state.files)) return;
  if (!state.models.has(name) && state.models.size>=4) {toast('Close an editor tab before opening another file. The runtime supports four open documents.');return;}
  if (editor?.getModel()) state.views.set(state.active,editor.saveViewState());
  state.active=name; state.opened.add(name);
  const model=state.models.get(name)||createModel(name,state.files[name]); editor.setModel(model); editor.restoreViewState(state.views.get(name)||null); editor.focus();
  document.title=`${name} — Solidity Lean`; $('#title').textContent=`${name} — solidity-lean [Offline]`; $('#breadcrumb-file').textContent=name;
  renderTabs(); renderSidebar(); renderOutline(); updateStatus(); persist();
  if (state.connected) try{await sync(name); await refreshSymbols(name);}catch(error){notifyError(error);}
}
async function closeFile(name) {
  if (state.dirty.has(name)) { // Buffers are persisted before a tab is disposed.
    persistNow();
  }
  if(state.connected)try{await sync(name);await rpc('close',{name});}catch(error){notifyError(error);}
  state.synced.delete(name); state.opened.delete(name); state.models.get(name)?.dispose(); state.models.delete(name); state.diagnostics.delete(name); state.statuses.delete(name); state.reports.delete(name);
  if(state.active===name){const next=[...state.opened][0]||Object.keys(state.files).find(n=>n!==name);if(next)await openFile(next);else{editor.setModel(null);$('#breadcrumb-file').textContent='No file open';}}
  renderTabs();renderSidebar();renderPanel();renderCounts();persist();
}
function renderTabs(){
  $('#tabs').replaceChildren();
  for(const name of state.opened){const tab=document.createElement('div');tab.className=`tab${name===state.active?' selected':''}`;tab.setAttribute('role','tab');tab.setAttribute('aria-selected',String(name===state.active));tab.tabIndex=name===state.active?0:-1;
    const symbol=document.createElement('span');symbol.className='sol-icon';symbol.textContent='◈';const label=document.createElement('span');label.textContent=name;
    const close=document.createElement('button');close.className=`close-tab${state.dirty.has(name)?' dirty':''}`;close.textContent=state.dirty.has(name)?'●':'×';close.title=`Close ${name}`;close.setAttribute('aria-label',`Close ${name}`);close.onclick=e=>{e.stopPropagation();closeFile(name);};tab.append(symbol,label,close);tab.onclick=()=>openFile(name);tab.onkeydown=e=>{if(e.key==='Enter')openFile(name);};$('#tabs').append(tab);
  }
}
function actionButton(icon,label,handler){const b=document.createElement('button');b.innerHTML=svg(icon);b.className='icon-button';b.title=label;b.setAttribute('aria-label',label);b.onclick=handler;return b;}
function setView(view){state.view=view;document.body.classList.remove('sidebar-hidden');for(const b of $$('[data-view]'))b.classList.toggle('active',b.dataset.view===view);renderSidebar();}
function renderSidebar(){
  const el=$('#sidebar-content'),actions=$('#view-actions');el.replaceChildren();actions.replaceChildren();$('#view-title').textContent=({changes:'LOCAL CHANGES',run:'RUN AND VERIFY',extensions:'EXTENSIONS'})[state.view]||state.view.toUpperCase();$('#outline').hidden=state.view!=='explorer';
  if(state.view==='explorer'){
    actions.append(actionButton('file','New Solidity File',newFile),actionButton('upload','Open Solidity Files',()=>$('#file-picker').click()));
    const heading=document.createElement('div');heading.className='section-heading';heading.textContent='⌄  SOLIDITY-LEAN';el.append(heading);
    for(const name of Object.keys(state.files)){const b=document.createElement('button');b.className=`file-row${name===state.active?' active':''}`;b.innerHTML='<span class="sol-icon">◈</span>';const text=document.createElement('span');text.textContent=name;b.append(text);if(state.dirty.has(name)){const dot=document.createElement('span');dot.className='dirty-dot';dot.textContent='●';b.append(dot);}b.onclick=()=>openFile(name);el.append(b);}
  }else if(state.view==='testing'){
    actions.append(actionButton('refresh','Discover Obligations',()=>verify(true)),actionButton('runAll','Verify File',()=>verify()),actionButton('stop','Cancel Verification',cancel));
    const more=document.createElement('button');more.textContent='···';more.title='Testing commands';more.setAttribute('aria-label','Testing commands');more.onclick=()=>openPalette();actions.append(more);
    const filterBox=document.createElement('div');filterBox.className='test-filter';const filter=document.createElement('input');filter.placeholder='Filter (text, !exclude, @status)';filter.setAttribute('aria-label','Filter verification tests');filter.value=state.testFilter;filterBox.append(filter);el.append(filterBox);
    let count=0,proved=0,pending=0;
    for(const report of state.reports.values())for(const row of report.results){count++;if(row.status==='proved')proved++;if(['pending','refuted','unsupported','notRun','error'].includes(row.status))pending++;}
    const summary=document.createElement('div');summary.className='test-summary test-summary-top';summary.textContent=count?`${proved} correct · ${pending} need attention`:'No verification results yet.';el.append(summary);
    for(const name of Object.keys(state.files)){const report=state.reports.get(name);const file=document.createElement('button');file.className='file-row testing-file';file.innerHTML=`<span>${report?'⌄':'›'}</span><span>○</span>`;const fileLabel=document.createElement('span');fileLabel.textContent=name;file.append(fileLabel);file.onclick=()=>openFile(name);el.append(file);
      for(const row of report?.results||[]){
        const b=document.createElement('div');b.className='test-row';b.tabIndex=0;b.setAttribute('role','button');b.title=detail(row);b.dataset.testText=`${name} ${row.contract}.${row.signature||row.function}`.toLowerCase();b.dataset.status=row.status;const img=document.createElement('img');img.src=iconPath(row.status);img.alt=row.status;const label=document.createElement('span');label.className='test-label';label.textContent=`${row.contract}.${row.signature||row.function}`;const desc=document.createElement('span');desc.className='test-description';desc.textContent=displayStatus(row);b.append(img,label,desc);const run=actionButton('run','Verify '+label.textContent,async e=>{e.stopPropagation();await openFile(name);verify(false,row);});run.classList.add('run-single');b.append(run);b.onclick=()=>reveal(name,row.range);b.onkeydown=e=>{if(e.key==='Enter')reveal(name,row.range);};el.append(b);
      }
    }
    filter.oninput=()=>{state.testFilter=filter.value;const terms=filter.value.toLowerCase().split(/\s+/).filter(Boolean);for(const row of el.querySelectorAll('.test-row'))row.hidden=!terms.every(term=>term[0]==='!'?!row.dataset.testText.includes(term.slice(1)):term[0]==='@'?row.dataset.status===term.slice(1):row.dataset.testText.includes(term));};filter.oninput();
  }else if(state.view==='search'){
    const box=document.createElement('div');box.className='search-content';const input=document.createElement('input');input.placeholder='Search';input.setAttribute('aria-label','Search workspace');const help=document.createElement('p');help.textContent='Search all local Solidity buffers';box.append(input,help);const matches=document.createElement('div');el.append(box,matches);
    input.oninput=()=>{matches.replaceChildren();const q=input.value.toLowerCase();if(!q)return;for(const [name,text]of Object.entries(state.files)){const lines=text.split('\n');const hits=lines.map((line,i)=>({line,i})).filter(h=>h.line.toLowerCase().includes(q));if(!hits.length)continue;const h=document.createElement('div');h.className='search-file';h.textContent=`◈ ${name} (${hits.length})`;matches.append(h);for(const hit of hits){const b=document.createElement('button');b.className='search-match';b.textContent=`${hit.i+1}: ${hit.line.trim()}`;b.onclick=()=>reveal(name,{start:{line:hit.i,character:0},end:{line:hit.i,character:hit.line.length}});matches.append(b);}}};setTimeout(()=>input.focus(),0);
  }else if(state.view==='changes'){
    el.innerHTML='<div class="section-heading">⌄ &nbsp; CHANGES</div>';
    for(const name of state.dirty){const b=document.createElement('button');b.className='file-row';b.textContent=`◈ ${name}   M`;b.title='Compare with last saved version';b.onclick=()=>showDiff(name);el.append(b);}
    const info=document.createElement('p');info.className='test-summary';info.textContent=state.dirty.size?'Select a file to compare it with the last saved version.':'No changes since the last save.';el.append(info);
  }else if(state.view==='run'){
    el.innerHTML='<div class="settings-content"><button id="run-verify">Verify File</button><button id="run-discover">Discover Obligations</button><button id="run-cancel">Cancel Verification</button><h3>Solidity Lean</h3><p>Check the current source buffer with the local verifier.</p><p>Open goals appear in Problems. The Testing view lists individual obligations.</p></div>';
    $('#run-verify').onclick=()=>verify();$('#run-discover').onclick=()=>verify(true);$('#run-cancel').onclick=cancel;
  }else if(state.view==='extensions'){
    el.innerHTML='<div class="section-heading">⌄ &nbsp; BUILT-IN</div><div class="settings-content"><h3>◈ Solidity Lean Verification</h3><p>Compiler-backed language services and verification results.</p><small>SolidiKeY · Browser runtime</small><h3>Monaco Editor</h3><p>The editor that powers VS Code. Bundled for offline use.</p><small>Microsoft · MIT</small><h3>Solidity Language</h3><p>The VS Code extension’s syntax grammar and proof gutter icons.</p><small>SolidiKeY · MIT</small></div>';
  }else if(state.view==='settings'){
    el.innerHTML='<div class="settings-content"><h3>Solidity Lean</h3><p>Program verification on this computer.</p><label for="auto-setting">Automatic verification</label><select id="auto-setting"><option value="never">Never — verify manually</option><option value="change">On change</option><option value="save">On save</option></select><label for="worker-setting">Proof workers</label><select id="worker-setting"><option>1</option><option>2</option><option>3</option><option>4</option></select><button id="restart-button">Restart Language Server</button><h3>Offline workspace</h3><p>Files stay in this browser. Export a file to keep a copy on disk.</p><p>Compiler and proof checking run in the local Node and Lean runtime. No Internet or remote service is used.</p><small>To verify, keep the local server running. Editing remains available in the cached app when it is disconnected.</small></div>';
    if(!usingNativeBackend){const paragraphs=el.querySelectorAll('.settings-content>p');paragraphs[0].textContent='Solidity compilation and language services run inside this browser.';paragraphs[2].textContent=state.runtime.proofReady?'The verifier runs entirely in WebAssembly in this browser.':'The local WebAssembly verifier is being prepared.';el.querySelector('.settings-content small').textContent='After the offline assets finish caching, no network or local server is needed.';$('#restart-button').textContent='Restart Browser Runtime';$('#worker-setting').innerHTML='<option>1</option>';for(const selector of ['#auto-setting','#worker-setting'])$(selector).disabled=!state.runtime.proofReady;}
    $('#auto-setting').value=state.settings.automaticVerification;$('#worker-setting').value=usingNativeBackend?state.settings.workers:1;
    for(const selector of ['#auto-setting','#worker-setting'])$(selector).onchange=async()=>{state.settings={automaticVerification:$('#auto-setting').value,counterexamples:false,auditPreconditions:false,workers:Number($('#worker-setting').value)};store.write('settings',state.settings);try{await rpc('configure',state.settings);clearResults();}catch(error){notifyError(error);}};
    $('#restart-button').onclick=restart;
  }
}
function iconPath(status){const path=`/media/${status==='proved'?'proved':['refuted','error'].includes(status)?'error':status==='running'?'running':'pending'}.svg`;return globalThis.singleFileIDE?.assetURL(path)||path;}
function displayStatus(row){return row.verification==='direct'?({proved:'correct',refuted:'wrong',pending:'unknown',unsupported:'unknown'})[row.status]||row.status:row.status;}
function detail(row){return `${row.contract}.${row.signature||row.function}: ${displayStatus(row)}${row.reason?` — ${row.reason}`:''}${row.reading?`\nObligation reading: ${row.reading}`:''}${row.preconditions?`\nEntry condition: ${row.preconditions}`:''}${row.counterexample?`\n${row.counterexample.certified?'Certified model prestate':'Counterexample'}: ${JSON.stringify(row.counterexample,null,2)}`:''}`;}
async function reveal(name,r){await openFile(name);if(r){editor.setSelection(range(r));editor.revealLineInCenter(r.start.line+1);}editor.focus();}
async function refreshSymbols(name=state.active,attempt=0){if(!state.models.has(name)||!state.connected)return;try{const version=currentVersion(name);const rows=await language('textDocument/documentSymbol',state.models.get(name));if(currentVersion(name)!==version)return;state.symbols.set(name,rows);if(name===state.active)renderOutline();}catch(error){if(attempt<2&&state.connected&&[-32800,-32801].includes(error.code))setTimeout(()=>refreshSymbols(name,attempt+1),250);}}
function renderOutline(){const root=$('#outline-content');root.replaceChildren();function add(rows,depth=0){for(const s of rows||[]){const b=document.createElement('button');b.className='outline-row';b.style.paddingLeft=`${18+depth*12}px`;const icon=document.createElement('span');icon.className='symbol';icon.textContent=s.kind===5?'◇':s.kind===12?'ƒ':'○';const name=document.createElement('span');name.textContent=s.name;b.append(icon,name);b.onclick=()=>reveal(state.active,s.selectionRange||s.range);root.append(b);add(s.children,depth+1);}}add(state.symbols.get(state.active));}
function renderCounts(){let errors=0,warnings=0;for(const list of state.diagnostics.values())for(const d of list){if(d.severity===1)errors++;if(d.severity===2)warnings++;}$('#problem-count').textContent=errors+warnings;$('#errors-status').textContent=`⊗ ${errors}   △ ${warnings}`;const count=[...state.reports.values()].reduce((n,r)=>n+r.results.filter(x=>['pending','refuted','error'].includes(x.status)).length,0);$('#test-badge').hidden=!count;$('#test-badge').textContent=count;}
function renderPanel(){
  for(const b of $$('[data-panel]'))b.classList.toggle('selected',b.dataset.panel===state.panel);
  $('#output-channel').hidden=state.panel!=='output';$('#clear-output').hidden=state.panel!=='output';const el=$('#panel-content');el.replaceChildren();
  if(state.panel==='output'){const pre=document.createElement('pre');pre.className='output-text';pre.textContent=state.logs.join('\n');el.append(pre);el.scrollTop=el.scrollHeight;return;}
  if(state.panel==='results'){let count=0;for(const [name,report]of state.reports)for(const row of report.results){count++;const item=document.createElement('div');item.className='result-item';const img=document.createElement('img');img.src=iconPath(row.status);img.alt=row.status;const body=document.createElement('div');const title=document.createElement('button');title.className='result-label';title.textContent=`${row.contract}.${row.signature||row.function} — ${displayStatus(row)}`;title.onclick=()=>reveal(name,row.range);const d=document.createElement('div');d.className='result-detail';d.textContent=detail(row);body.append(title,d);const time=document.createElement('span');time.className='result-time';time.textContent=row.elapsedMs!==undefined?`${row.elapsedMs} ms`:'';item.append(img,body,time);el.append(item);}if(!count)el.innerHTML='<div class="empty-message">No verification results. Run Verify File to check the program.</div>';return;}
  let count=0;for(const [name,diagnostics]of state.diagnostics){if(!diagnostics.length)continue;const file=document.createElement('div');file.className='problem-file';file.textContent=`⌄  ◈  ${name}`;const badge=document.createElement('span');badge.className='count';badge.textContent=diagnostics.length;file.append(badge);el.append(file);for(const d of diagnostics){count++;const b=document.createElement('button');b.className='problem-row';const icon=document.createElement('span');icon.className=d.severity===1?'severity-error':'severity-warning';icon.textContent=d.severity===1?'⊗':'△';const msg=document.createElement('span');msg.className='message';msg.textContent=d.message;const source=document.createElement('span');source.className='source';source.textContent=`${d.source||'Solidity Lean'}${d.code?`(${d.code})`:''} [Ln ${d.range.start.line+1}, Col ${d.range.start.character+1}]`;b.append(icon,msg,source);b.title=d.message;b.onclick=()=>reveal(name,d.range);el.append(b);}}
  if(!count)el.innerHTML='<div class="empty-message">No problems have been detected in the workspace.</div>';
}
function showPanel(panel){state.panel=panel;document.body.classList.remove('panel-hidden');renderPanel();editor?.layout();}
function proofStatus(text){$('#proof-status').innerHTML=svg('testing');$('#proof-status').append(document.createTextNode(`Solidity Lean: ${text}`));}
function updateStatus(){const s=state.statuses.get(state.active);const text=!state.connected?'preparing':s?.state||'ready';proofStatus(text);$('#verify-button').disabled=!state.connected||!state.runtime.proofReady;$('#verify-button').title=state.runtime.proofReady?'Verify File (Ctrl+Shift+Enter)':state.runtime.error||'Pinned browser proof runtime is not ready yet';}
async function verify(listing=false,row){
  const name=state.active;if(!state.models.has(name))return;
  try{await syncAll();const version=currentVersion(name),revision=state.revision,start=performance.now();log(`${listing?'Discovering':'Verifying'} ${name}${row?` — ${row.contract}.${row.signature||row.function}`:''}`);proofStatus('running');
    const report=await rpc('verify',{name,version,listing,...(row?{contract:row.contract,function:row.signature||row.function}:{})});const elapsed=performance.now()-start;
    if(currentVersion(name)!==version||state.revision!==revision)return;state.timing.push({name,listing,elapsedMs:+elapsed.toFixed(1),results:report.results.map(r=>({function:r.signature||r.function,status:r.status}))});log(`${listing?'Discovery':'Verification'} completed in ${elapsed.toFixed(0)} ms.`);setView('testing');if(!listing)showPanel('results');updateStatus();return report;
  }catch(error){notifyError(error);log(`Verification stopped: ${error.message}`);updateStatus();}
}
async function cancel(){try{await rpc('cancel',{});log('Verification cancelled.');}catch(error){notifyError(error);}}
function clearResults(){state.reports.clear();state.statuses.clear();state.diagnostics.clear();for(const name of state.models.keys()){applyMarkers(name);drawGutters(name);}renderSidebar();renderPanel();renderCounts();updateStatus();}
async function restart(){if(!usingNativeBackend){socket?.close();log('Browser compiler and proof workers restarting.');toast('Restarting the browser runtime.');return;}try{await rpc('restart');clearResults();log('Language server restarted.');toast('Solidity Lean language server restarted.');}catch(error){notifyError(error);}}
async function save(){const name=state.active,model=state.models.get(name);if(!model)return;const version=model.getVersionId(),text=model.getValue();try{await syncAll();if(currentVersion(name)!==version)throw Object.assign(new Error('Document content changed'),{code:-32801});await rpc('save',{name});const previous=state.baselines[name];if(currentVersion(name)===version&&state.files[name]===text){state.baselines[name]=text;state.dirty.delete(name);}const persisted=persistNow();if(!persisted){state.baselines[name]=previous;if(state.files[name]!==previous)state.dirty.add(name);}renderTabs();renderSidebar();if(persisted)log(`Saved ${name} in the local session workspace and browser storage.`);}catch(error){notifyError(error);}}
function showDiff(name){
  const dialog=document.createElement('dialog');dialog.className='diff-dialog';const heading=document.createElement('div');heading.className='diff-heading';heading.textContent=`${name} — Last saved ↔ Current buffer`;const close=document.createElement('button');close.textContent='×';close.setAttribute('aria-label','Close comparison');close.onclick=()=>dialog.close();heading.append(close);const host=document.createElement('div');host.className='diff-host';dialog.append(heading,host);document.body.append(dialog);dialog.showModal();
  const original=monaco.editor.createModel(state.baselines[name]||'','solidity');const modified=monaco.editor.createModel(state.files[name],'solidity');const diff=monaco.editor.createDiffEditor(host,{theme:'solidity-extension',readOnly:true,automaticLayout:true,fontSize:14,lineHeight:20,renderSideBySide:innerWidth>800});diff.setModel({original,modified});dialog.onclose=()=>{diff.dispose();original.dispose();modified.dispose();dialog.remove();};
}
function exportFile(){const blob=new Blob([state.files[state.active]],{type:'text/plain'});const a=document.createElement('a');a.href=URL.createObjectURL(blob);a.download=state.active;a.click();setTimeout(()=>URL.revokeObjectURL(a.href),1000);}
function promptName(label,initial,submit='Create'){return new Promise(resolve=>{const dialog=$('#input-dialog');$('#input-label').textContent=label;$('#input-value').value=initial;$('#input-error').textContent='';$('#input-submit').textContent=submit;dialog.onclose=()=>resolve(dialog.returnValue==='ok'?$('#input-value').value:null);dialog.showModal();$('#input-value').focus();$('#input-value').select();});}
const validFileName=name=>/^[A-Za-z0-9_$][A-Za-z0-9_.$-]*\.sol$/.test(name)&&name.length<=120;
async function newFile(){const name=await promptName('New Solidity file','Contract.sol');if(!name)return;if(!validFileName(name)){toast('Use a Solidity file name such as Contract.sol. Directory paths are not supported.');return;}if(name in state.files){toast('That file already exists.');return;}state.files[name]='// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34;\n\ncontract '+name.slice(0,-4).replace(/[^A-Za-z0-9_$]/g,'_')+' {\n}\n';state.dirty.add(name);await openFile(name);persist();}
const commands=[
  {label:'Solidity Lean: Verify File',key:'Ctrl+Shift+Enter',run:()=>verify()},
  {label:'Solidity Lean: Discover Obligations',run:()=>verify(true)},
  {label:'Solidity Lean: Cancel Verification',run:cancel},
  {label:'Solidity Lean: Restart Language Server',run:restart},
  {label:'File: New Solidity File',key:'Ctrl+N',run:newFile},
  {label:'File: Open Solidity Files…',key:'Ctrl+O',run:()=>$('#file-picker').click()},
  {label:'File: Save',key:'Ctrl+S',run:save},
  {label:'File: Export Current File',run:exportFile},
  ...(globalThis.singleFileIDE?[{label:'File: Download Offline IDE',run:()=>{const link=document.createElement('a');link.href=location.href;link.download='Solidity-Lean-IDE.html';link.click();}},{label:'Help: Third Party Notices',run:()=>{const link=document.createElement('a');link.href=singleFileIDE.assetURL('/THIRD_PARTY_NOTICES.txt');link.download='THIRD_PARTY_NOTICES.txt';link.click();}}]:[]),
  {label:'View: Explorer',key:'Ctrl+Shift+E',run:()=>setView('explorer')},
  {label:'View: Testing',run:()=>setView('testing')},
  {label:'View: Search',key:'Ctrl+Shift+F',run:()=>setView('search')},
  {label:'View: Problems',key:'Ctrl+Shift+M',run:()=>showPanel('problems')},
  {label:'View: Output',run:()=>showPanel('output')},
  {label:'View: Test Results',run:()=>showPanel('results')},
  {label:'View: Toggle Panel',key:'Ctrl+J',run:()=>{document.body.classList.toggle('panel-hidden');editor.layout();}},
  {label:'View: Toggle Side Bar',key:'Ctrl+B',run:()=>{document.body.classList.toggle('sidebar-hidden');editor.layout();}},
  {label:'Preferences: Open Settings',key:'Ctrl+,',run:()=>setView('settings')},
  {label:'Format Document',key:'Shift+Alt+F',run:()=>editor.getAction('editor.action.formatDocument').run().catch(notifyError)},
  {label:'Go to Definition',key:'F12',run:()=>editor.getAction('editor.action.revealDefinition').run()},
  {label:'Rename Symbol',key:'F2',run:()=>editor.getAction('editor.action.rename').run()},
  {label:'Help: Offline IDE',run:()=>toast(usingNativeBackend?'Native development backend. Keep its local process running.':'This website runs in your browser.\n'+(globalThis.singleFileIDE?'File → Download Offline IDE saves the complete website as one HTML file.\nReopen that file for offline use.\n':'The compiler and editor work without a network after initial caching.\n')+'F1 opens commands. Ctrl+S saves browser files; Export keeps a disk copy.\n'+(state.runtime.proofReady?'Lean proof checking also runs in this browser.':'The compatible Lean proof runtime is still being prepared.'))}
];
function openPalette(mode='commands'){const dialog=$('#palette');dialog.dataset.mode=mode;$('#palette-input').value=mode==='commands'?'>':'';$('#palette-input').placeholder=mode==='files'?'Search files by name':'Type a command';paletteIndex=0;renderPalette();dialog.showModal();$('#palette-input').focus();}
function renderPalette(){const mode=$('#palette').dataset.mode,q=$('#palette-input').value.replace(/^>/,'').toLowerCase();paletteCommands=(mode==='files'?Object.keys(state.files).map(name=>({label:name,run:()=>openFile(name)})):commands).filter(c=>c.label.toLowerCase().includes(q));paletteIndex=Math.max(0,Math.min(paletteIndex,paletteCommands.length-1));$('#palette-items').replaceChildren();paletteCommands.forEach((c,i)=>{const b=document.createElement('button');b.className=i===paletteIndex?'chosen':'';b.setAttribute('role','option');b.setAttribute('aria-selected',String(i===paletteIndex));const t=document.createElement('span');t.textContent=c.label;b.append(t);if(c.key){const k=document.createElement('kbd');k.textContent=c.key;b.append(k);}b.onclick=()=>chooseCommand(i);$('#palette-items').append(b);});}
function chooseCommand(i=paletteIndex){$('#palette').close();paletteCommands[i]?.run();}
$('#palette-input').oninput=()=>{paletteIndex=0;renderPalette();};$('#palette-input').onkeydown=e=>{if(e.key==='ArrowDown'||e.key==='ArrowUp'){e.preventDefault();paletteIndex+=e.key==='ArrowDown'?1:-1;renderPalette();$('#palette-items .chosen')?.scrollIntoView({block:'nearest'});}if(e.key==='Enter'){e.preventDefault();chooseCommand();}};
for(const dialog of $$('dialog'))dialog.addEventListener('click',e=>{if(e.target===dialog){const r=dialog.getBoundingClientRect();if(e.clientX<r.left||e.clientX>r.right||e.clientY<r.top||e.clientY>r.bottom)dialog.close();}});
function wireUI(){
  $('#main-menu-button').onclick=()=>openPalette();
  for(const b of $$('[data-view]'))b.onclick=()=>setView(b.dataset.view);
  for(const b of $$('[data-panel]'))b.onclick=()=>showPanel(b.dataset.panel);
  $('#title').onclick=()=>openPalette();$('#more-button').onclick=()=>openPalette();$('#verify-button').onclick=()=>verify();$('#proof-status').onclick=()=>verify();$('#errors-status').onclick=()=>showPanel('problems');$('#offline-button').onclick=()=>commands.at(-1).run();$('#notification-button').onclick=()=>toast(usingNativeBackend?'Native development backend: '+(state.connected?'connected':'disconnected'):state.connected?'The compiler runs in WebAssembly in this browser. No remote service is used.':'The browser runtime is preparing.');
  $('#layout-button').onclick=$('#close-panel').onclick=()=>{document.body.classList.toggle('panel-hidden');editor.layout();};$('#clear-output').onclick=()=>{state.logs=[];renderPanel();};$('#outline-toggle').onclick=()=>{$('#outline-content').hidden=!$('#outline-content').hidden;};
  $('#file-picker').onchange=async e=>{for(const file of e.target.files){if(!validFileName(file.name)||file.size>8*1024*1024){toast('Open a .sol file smaller than 8 MiB with a simple file name.');continue;}if(file.name in state.files&&state.files[file.name]!==await file.text()){toast(`${file.name} already exists. Rename the imported file before opening it.`);continue;}state.files[file.name]=await file.text();await openFile(file.name);}persist();e.target.value='';};
  const menus={File:['File:'],Edit:['Format Document','Rename Symbol'],Selection:[],View:['View: Explorer','View: Search','View: Testing','View: Problems','View: Output','View: Toggle'],Go:['Go to Definition'],Run:['Solidity Lean:'],Help:['Help:']};
  for(const button of $$('[data-menu]'))button.onclick=e=>{e.stopPropagation();$('.menu-popup')?.remove();const box=document.createElement('div');box.className='menu-popup';box.style.left=`${button.getBoundingClientRect().left}px`;const items=button.dataset.menu==='Selection'?[{label:'Select All',run:()=>{editor.focus();editor.trigger('keyboard','editor.action.selectAll');}}]:commands.filter(c=>menus[button.dataset.menu].some(prefix=>c.label.startsWith(prefix)));for(const c of items){const b=document.createElement('button');b.textContent=c.label.replace(/^(File|View|Help): /,'');if(c.key){const k=document.createElement('kbd');k.textContent=c.key;b.append(k);}b.onclick=()=>{box.remove();c.run();};box.append(b);}document.body.append(box);};
  document.addEventListener('click',()=>$('.menu-popup')?.remove());
  document.addEventListener('keydown',e=>{if($$('dialog[open]').length)return;const mod=e.ctrlKey||e.metaKey;let action;
    if(e.key==='F1'||mod&&e.shiftKey&&e.key.toLowerCase()==='p')action=()=>openPalette();else if(mod&&!e.shiftKey&&e.key.toLowerCase()==='p')action=()=>openPalette('files');
    else if(mod&&e.shiftKey&&e.key==='Enter')action=()=>verify();else if(mod&&e.key.toLowerCase()==='s')action=save;else if(mod&&e.key.toLowerCase()==='o')action=()=>$('#file-picker').click();else if(mod&&e.key.toLowerCase()==='n')action=newFile;
    else if(mod&&e.shiftKey&&e.key.toLowerCase()==='e')action=()=>setView('explorer');else if(mod&&e.shiftKey&&e.key.toLowerCase()==='f')action=()=>setView('search');else if(mod&&e.shiftKey&&e.key.toLowerCase()==='m')action=()=>showPanel('problems');
    else if(mod&&e.key.toLowerCase()==='j')action=()=>$('#layout-button').click();else if(mod&&e.key.toLowerCase()==='w')action=()=>closeFile(state.active);else if(mod&&e.key.toLowerCase()==='b')action=()=>{document.body.classList.toggle('sidebar-hidden');editor.layout();};else if(mod&&e.key===',')action=()=>setView('settings');
    if(action){e.preventDefault();e.stopPropagation();action();}
  },true);
  for(const [selector,axis]of [['.sidebar-resize','x'],['.panel-resize','y']]){const handle=$(selector);handle.onpointerdown=e=>{e.preventDefault();handle.setPointerCapture(e.pointerId);handle.classList.add('dragging');const move=event=>{const value=axis==='x'?Math.max(180,Math.min(600,event.clientX-48)):Math.max(90,Math.min(innerHeight-200,innerHeight-event.clientY-22));document.documentElement.style.setProperty(axis==='x'?'--sidebar-width':'--panel-height',`${value}px`);editor.layout();};handle.onpointermove=move;handle.onpointerup=()=>{handle.classList.remove('dragging');handle.onpointermove=null;};};handle.onkeydown=e=>{const amount=e.key==='ArrowLeft'||e.key==='ArrowDown'?-10:e.key==='ArrowRight'||e.key==='ArrowUp'?10:0;if(!amount)return;e.preventDefault();const key=axis==='x'?'--sidebar-width':'--panel-height';const value=parseInt(getComputedStyle(document.documentElement).getPropertyValue(key))+amount;document.documentElement.style.setProperty(key,`${Math.max(axis==='x'?180:90,value)}px`);editor.layout();};}
}
async function boot(){
  if(!usingNativeBackend&&!globalThis.singleFileIDE&&!('serviceWorker'in navigator))throw new Error('Use HTTPS or localhost to prepare this offline website');
  const start=performance.now();let bootstrap;
  try{bootstrap=await (await fetch(usingNativeBackend?'/api/bootstrap':'/bootstrap.json')).json();store.write('examples',bootstrap.files);}catch{bootstrap={files:store.read('examples',{})};}
  const saved=store.read('workspace',{});state.files=saved.files&&Object.keys(saved.files).length?saved.files:bootstrap.files;state.baselines=saved.baselines||{...bootstrap.files};state.active=saved.active in state.files?saved.active:Object.keys(state.files)[0];state.dirty=new Set(saved.dirty||[]);
  if(!Object.keys(state.files).length){state.files={'Contract.sol':'// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34;\ncontract Contract {}\n'};state.active='Contract.sol';}
  // Control the first Monaco load, so its AMD chunks and workers are cached on
  // the very first visit rather than only after a second online page load.
  if(!globalThis.singleFileIDE&&'serviceWorker'in navigator){
    navigator.serviceWorker.addEventListener('message',event=>{if(event.data?.method==='offlineProgress'&&$('#editor .loading'))$('#editor .loading').textContent=`Preparing offline website… ${event.data.done}/${event.data.total} local assets cached`;});
    try{const registration=await navigator.serviceWorker.register('/sw.js');
      await new Promise((resolve,reject)=>{
        const observed=new Set();const finish=error=>{clearTimeout(timer);registration.removeEventListener('updatefound',observe);for(const worker of observed)worker.removeEventListener('statechange',observe);error?reject(error):resolve();};
        const observe=event=>{if(event?.target?.state==='redundant')return finish(new Error('Offline preparation failed. Check available browser storage and reload to retry.'));const worker=registration.installing||registration.waiting||registration.active;if(!worker)return;if(!observed.has(worker)){observed.add(worker);worker.addEventListener('statechange',observe);}if(worker.state==='redundant')finish(new Error('Offline preparation failed. Check available browser storage and reload to retry.'));else if(worker.state==='activated')finish();};
        const timer=setTimeout(()=>finish(new Error('Offline preparation timed out. Reconnect and reload to retry.')),600000);registration.addEventListener('updatefound',observe);observe();
      });
      if(!navigator.serviceWorker.controller)await new Promise(resolve=>navigator.serviceWorker.addEventListener('controllerchange',resolve,{once:true}));
    }catch(error){log(`Offline asset cache: ${error.message}`);if(!usingNativeBackend)throw error;}
  }
  if(!globalThis.singleFileIDE){require.config({paths:{vs:'/vendor/vs'}});
    await new Promise((resolve,reject)=>require(['vs/editor/editor.main'],resolve,reject));}
  const grammar=await (await fetch('/syntax.json')).json();
  registerLanguage(grammar);$('#editor').replaceChildren();
  editor=monaco.editor.create($('#editor'),{theme:'solidity-extension',fontFamily:"'Droid Sans Mono', monospace",fontSize:14,lineHeight:20,automaticLayout:true,minimap:{enabled:true},glyphMargin:true,lineNumbersMinChars:3,scrollBeyondLastLine:false,tabSize:4,insertSpaces:true,padding:{top:0},renderWhitespace:'none',bracketPairColorization:{enabled:false},stickyScroll:{enabled:false},quickSuggestions:{other:true,comments:false,strings:false}});
  editor.onDidChangeCursorPosition(e=>{$('#position-status').textContent=`Ln ${e.position.lineNumber}, Col ${e.position.column}`;});
  editor.onMouseDown(e=>{if(e.target.type!==monaco.editor.MouseTargetType.GUTTER_GLYPH_MARGIN)return;const line=e.target.position?.lineNumber;const row=state.reports.get(state.active)?.results.find(r=>r.range?.start.line+1===line);if(row)verify(false,row);});
  monaco.editor.registerEditorOpener({async openCodeEditor(_source,resource,selection){const name=filename(resource.toString());if(!(name in state.files))return false;await openFile(name);if(state.active!==name||editor.getModel()?.uri.toString()!==modelURI(resource.toString()).toString())return false;if(selection){if(selection.startLineNumber){editor.setSelection(selection);editor.revealLineInCenter(selection.startLineNumber);}else{editor.setPosition(selection);editor.revealLineInCenter(selection.lineNumber);}}return true;}});
  editor.onDidChangeModelContent(()=>persist());
  for(const name of (saved.opened||[]).filter(n=>n in state.files).slice(0,3)){state.opened.add(name);createModel(name,state.files[name]);}
  await openFile(state.active);wireUI();renderPanel();renderCounts();connect();
  window.addEventListener('pagehide',persistNow);
  state.startupMs=+(performance.now()-start).toFixed(1);log(`Offline workbench ready in ${state.startupMs} ms.`);
  if(!globalThis.singleFileIDE&&'serviceWorker'in navigator)navigator.serviceWorker.register('/sw.js').catch(error=>log(`Offline asset cache: ${error.message}`));
  // A small inspection surface for reproducible browser parity and latency tests.
  window.solidityIDE={state,editor,verify,openFile,setView,showPanel,rpc,sync,restart,save,language,get ready(){return !!editor;}};
}
const bootPromise=boot();if(globalThis.singleFileIDE)singleFileIDE.bootPromise=bootPromise;
bootPromise.catch(error=>{globalThis.singleFileIDE?.invalidate();$('#editor').textContent=`Unable to start the editor: ${error.message}. Reload after the website assets finish downloading.`;console.error(error);});
