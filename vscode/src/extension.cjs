'use strict';
const { resolve, extname, dirname } = require('node:path');
const { createHash } = require('node:crypto');
const { runBackend } = require('./backend.cjs');
const model = require('./model.cjs');
const { validateCounterexample } = require('./counterexample.cjs');

const hash = text => createHash('sha256').update(text, 'utf8').digest('hex');

/** Injectable VS Code boundary; production and tests exercise the same controller. */
function createExtension(vscode, context, backend = runBackend, service = null) {
  const diagnostics = vscode.languages.createDiagnosticCollection('solidity-lean');
  const controller = vscode.tests.createTestController('solidityLean', 'Solidity Lean');
  const output = vscode.window.createOutputChannel('Solidity Lean');
  let outputClosed=false;const outputOwner={dispose(){if(!outputClosed){outputClosed=true;output.dispose();}}};
  const active = new Map(), saving = new Map(), reports = new Map(), metadata = new Map(), documents = new Map();
  let editorServices;
  const testingTree=require('./testing-tree.cjs').install(vscode,controller,metadata),symbolSnapshots=new Map();
  const automaticTests=require('./automatic-testing.cjs').install({vscode,controller,
    itemsFor:doc=>testingTree.leaves(doc.uri),
    cancel:uri=>cancel(uri),current:doc=>!disposed&&!doc.isClosed&&documents.get(key(doc.uri))===doc});
  function disposeTesting(){for(const snapshot of symbolSnapshots.values())snapshot.abort.abort();symbolSnapshots.clear();automaticTests.dispose();for(const file of require('./testing-tree.cjs').items(controller.items))testingTree.clear(file.uri);}
  context.subscriptions.push({dispose:disposeTesting});
  const testRunCancellations=new Set();
  let discoveryVersion = 0;
  let disposed=false,restartGeneration=0,disposal;
  const documentGenerations=new Map();
  const key = uri => uri.toString();
  const isSolidity = doc => doc?.uri.scheme === 'file' && extname(doc.uri.fsPath).toLowerCase() === '.sol';
  const toRange = range => new vscode.Range(range.start.line, range.start.character, range.end.line, range.end.character);
  function settings(doc) {
    const cfg = vscode.workspace.getConfiguration('solidityLean', doc.uri);
    const workspace = vscode.workspace.getWorkspaceFolder(doc.uri)?.uri.fsPath;
    const configured = cfg.get('backendPath', '');
    if (!configured && !workspace) throw new Error('Set solidityLean.backendPath to the Solidity Lean repository directory');
    const automatic = cfg.get('verifyOnSave', false) ? 'onsave' : cfg.get('automaticVerification', 'onchange');
    return { backendPath: resolve(workspace || '.', configured || '.'), nodePath: cfg.get('nodePath', 'node'), timeoutMs: cfg.get('timeoutMs', 600000), auditPreconditions: cfg.get('auditPreconditions', false), counterexamples: cfg.get('counterexamples', false),
      projectRoot:workspace||dirname(doc.uri.fsPath),includePaths:cfg.get('includePaths',[]),remappings:cfg.get('remappings',[]),compilerOutputDir:cfg.get('compilerOutputDir','bin'),
      workers: cfg.get('workers', 1), automaticVerification: {onchange:'change',onsave:'save',never:'never'}[automatic] || 'never' };
  }
  const sourceCommands=require('./source-commands.cjs').install(vscode,context,{settings,output,cancelVerification:uri=>cancel(uri,true)});
  function cancel(uri,preserveSource=false) {
    if(!preserveSource)sourceCommands.cancel(uri?key(uri):undefined);
    automaticTests.stop(uri);
    service?.cancel(uri);
    if (uri) { saving.delete(key(uri)); active.get(key(uri))?.abort(); }
    else {
      discoveryVersion++;
      saving.clear();
      for (const job of active.values()) job.abort();
    }
  }
  function clearTests(uri,preserveAutomatic=false) {
    if(!preserveAutomatic)automaticTests.clear(key(uri));
    symbolSnapshots.get(key(uri))?.abort.abort();symbolSnapshots.delete(key(uri));
    testingTree.clear(uri);
  }
  function clear(uri,notifyServer=true) {
    if(notifyServer)cancel(uri);
    diagnostics.delete(uri);
    reports.delete(key(uri));
    editorServices?.clear(uri);
    clearTests(uri);
  }
  const shownErrors=new WeakSet();
  function showError(error) {
    if (disposed) return;
    if (error.code === 'CANCELLED' || [-32800,-32801].includes(error.code)) return;
    if(error.code==='STARTUP'&&error.uris&&!error.uris.some(uri=>{const doc=documents.get(uri);return doc&&!doc.isClosed;}))return;
    if(shownErrors.has(error))return;shownErrors.add(error);
    output.appendLine(error.message);
    if(error.code!=='STARTUP'){vscode.window.showErrorMessage(`Solidity Lean: ${error.message}`);return;}
    const generation=restartGeneration,actionDocuments=error.uris?.map(uri=>({doc:documents.get(uri),generation:documentGenerations.get(uri)||0})),actions=['Change configuration'];if(error.setting==='nodePath')actions.push('Node.js downloads');
    Promise.resolve(vscode.window.showErrorMessage(`Solidity Lean: ${error.message}`, ...actions)).then(async selection=>{
      if(disposed||!vscode.workspace.isTrusted)return;
      if(actionDocuments?!actionDocuments.some(({doc,generation})=>doc&&!doc.isClosed&&documents.get(key(doc.uri))===doc&&(documentGenerations.get(key(doc.uri))||0)===generation):generation!==restartGeneration)return;
      if(selection==='Change configuration')await vscode.commands.executeCommand('workbench.action.openSettings','@ext:SolidiKeY.solidity-lean '+(error.setting?'solidityLean.'+error.setting:''));
      else if(selection==='Node.js downloads')await vscode.env.openExternal(vscode.Uri.parse('https://nodejs.org/en/download'));
    }).catch(actionError=>{if(!disposed)output.appendLine('Startup action failed: '+actionError.message);});
  }
  function publish(doc, report) {
    reports.set(key(doc.uri), report);
    const converted = model.diagnostics(report).filter(d => !d.source || resolve(d.source) === resolve(doc.uri.fsPath)).map(d => {
      const diag = new vscode.Diagnostic(toRange(d.range), d.message, d.severity === 'error' ? vscode.DiagnosticSeverity.Error : vscode.DiagnosticSeverity.Warning);
      diag.source = 'Solidity Lean'; diag.code = d.code;
      return diag;
    });
    if (!service) diagnostics.set(doc.uri, converted);
    if (!vscode.workspace.getConfiguration('solidityLean',doc.uri).get('displayVerificationAsTests',true)) {
      automaticTests.visible(doc,false);clearTests(doc.uri,true);return;
    }
    const id=key(doc.uri),previous=symbolSnapshots.get(id);
    testingTree.render(doc,report,previous?.doc===doc&&previous.version===doc.version&&previous.text===doc.getText()?previous.symbols:null);
    if(!service?.request)return;
    previous?.abort.abort();const snapshot={doc,version:doc.version,text:doc.getText(),report,abort:new AbortController(),symbols:null};symbolSnapshots.set(id,snapshot);
    const current=()=>!disposed&&!doc.isClosed&&!snapshot.abort.signal.aborted&&documents.get(id)===doc&&doc.version===snapshot.version&&doc.getText()===snapshot.text&&reports.get(id)===report&&symbolSnapshots.get(id)===snapshot&&vscode.workspace.getConfiguration('solidityLean',doc.uri).get('displayVerificationAsTests',true);
    Promise.resolve().then(()=>{if(current())return service.request('textDocument/documentSymbol',doc,{}, {signal:snapshot.abort.signal});}).then(symbols=>{
      if(!current())return;const validated=require('./testing-tree.cjs').currentSymbols(symbols,snapshot.text);snapshot.symbols=validated;testingTree.render(doc,report,validated);
    }).catch(error=>{if(current()&&![-32800,-32801].includes(error.code)&&error.code!=='CANCELLED')output.appendLine('Testing symbols unavailable: '+error.message);});
  }
  function accept(doc, report, config, options = {}) {
    const identities=report.results.map(row=>require('./testing-tree.cjs').rowId(key(doc.uri),row));if(new Set(identities).size!==identities.length)throw new Error('Verifier report has duplicate obligation identities');
    if (report.results.some(row => resolve(row.source) !== resolve(doc.uri.fsPath))) throw new Error('Verifier report refers to a different source file');
    const hashes = new Set([hash(doc.getText()), hash('\uFEFF' + doc.getText())]);
    if (report.results.some(row => !hashes.has(row.sourceHash))) throw new Error('Verifier source hash does not match the open file; use a current backend and save the file');
    for (const row of report.results) validateCounterexample(row);
    if ((!config.counterexamples || options.listing) && report.results.some(row => row.status === 'refuted' && row.verification !== 'direct')) throw new Error('Verifier returned unrequested certified model prestate evidence');
    const existing = reports.get(key(doc.uri));
    const merged = options.function && existing ? {...report,results:[...existing.results.filter(old => !report.results.some(row => row.contract === old.contract && (row.signature || row.function) === (old.signature || old.function))),...report.results]} : report;
    publish(doc, merged);
    if(!options.listing)automaticTests.report(doc, merged.results, merged.errors);
  }
  async function verify(doc, options = {}) {
    if(disposed)throw Object.assign(new Error('Extension disposed'),{code:'CANCELLED'});
    if (!vscode.workspace.isTrusted) throw new Error('Verification requires a trusted workspace');
    if (!isSolidity(doc)) throw new Error('Open a Solidity file on disk to verify');
    documents.set(key(doc.uri), doc);
    const cancellationVersion = discoveryVersion;
    const request = {}, requestId = key(doc.uri);
    saving.set(requestId, request);
    try {
      const superseded = () => saving.get(requestId) !== request || cancellationVersion !== discoveryVersion || options.token?.isCancellationRequested || doc.isClosed;
      let attempts = 0;
      while (!service && doc.isDirty) {
        const saved = await doc.save();
        if (superseded()) return null;
        if (!saved) throw new Error('Save the Solidity file before verification');
        // VS Code can resolve a joined save for an older buffer snapshot.
        // Complete the current save before capturing the backend's source hash.
        if (++attempts >= 3 && doc.isDirty) throw new Error('The Solidity file is still changing; retry verification after saving');
      }
      // Edits, closure, cancellation or a newer request can supersede this
      // request while VS Code is saving, before an active backend exists.
      if (superseded()) return null;
    } finally { if (saving.get(requestId) === request) saving.delete(requestId); }
    const config = settings(doc);
    const id = key(doc.uri), version = doc.version, text = doc.getText();
    cancel(doc.uri);automaticTests.begin(doc);
    const abort = new AbortController();
    active.set(id, abort);
    const registration = options.token?.onCancellationRequested(() => abort.abort());
    if (options.token?.isCancellationRequested) abort.abort();
    try {
      output.appendLine(`${options.listing ? 'Discovering' : 'Verifying'} ${doc.uri.fsPath}`);
      const report = await backend({ ...config, ...(service ? {document:doc} : {}), source: doc.uri.fsPath, listing: options.listing, contract: options.contract, function: options.function, signal: abort.signal });
      if (abort.signal.aborted || active.get(id) !== abort || doc.version !== version || doc.getText() !== text || doc.isClosed) return null;
      accept(doc, report, config, options);
      for (const row of report.results) output.appendLine(model.detail(row));
      for (const error of report.errors) output.appendLine(`Error: ${error.reason}`);
      return report;
    } finally {
      registration?.dispose();
      if (active.get(id) === abort) active.delete(id);
    }
  }
  async function activeCommand(listing) {
    const doc = vscode.window.activeTextEditor?.document;
    try {
      await vscode.window.withProgress({ location: vscode.ProgressLocation.Notification, title: listing ? 'Discovering Solidity obligations' : 'Verifying Solidity', cancellable: true }, (_, token) => verify(doc, { listing, token }));
    } catch (error) { showError(error); }
  }
  async function discover() {
    if (!vscode.workspace.isTrusted) return;
    const generation = ++discoveryVersion;
    const uris = await vscode.workspace.findFiles('**/*.sol', '**/{.git,.lake,node_modules}/**');
    for (const uri of uris) {
      if (generation !== discoveryVersion) break;
      try {
        const doc = await vscode.workspace.openTextDocument(uri);
        if (generation !== discoveryVersion) break;
        await verify(doc, { listing: true });
      }
      catch (error) { showError(error); }
    }
  }
  controller.resolveHandler = async item => { if (!item) await discover(); };
  controller.refreshHandler = discover;
  controller.createRunProfile('Verify', vscode.TestRunProfileKind.Run, async (request, profileToken) => {
    const run=controller.createTestRun(request),cancellation=new vscode.CancellationTokenSource();
    testRunCancellations.add(cancellation);
    const tokens=[profileToken,run.token].filter(Boolean);
    const registrations=tokens.map(token=>token.onCancellationRequested(()=>cancellation.cancel()));
    if(tokens.some(token=>token.isCancellationRequested))cancellation.cancel();
    const token=cancellation.token,excluded=new Set((request.exclude||[]).map(item=>item.id)),selected=new Map();
    const live=item=>testingTree.live(item);
    const collect=item=>{
      if(!item||!testingTree.live(item)||testingTree.excluded(item,excluded))return;
      const meta=metadata.get(item.id);if(!meta||excluded.has(key(meta.uri)))return;
      if(meta.row){if(live(item))selected.set(item.id,item);}
      else item.children.forEach(collect);
    };
    (request.include||require('./testing-tree.cjs').items(controller.items)).forEach(collect);
    const currentSelection=(item,doc)=>{
      const meta=live(item);return meta&&key(doc.uri)===key(meta.uri)&&!doc.isClosed&&new Set([hash(doc.getText()),hash('\uFEFF'+doc.getText())]).has(meta.row.sourceHash);
    };
    const releaseAutomatic=automaticTests.claim([...new Map([...selected.values()].map(item=>{const uri=metadata.get(item.id).uri;return [key(uri),uri];})).values()]);
    async function runItem(item){
      const meta=live(item);
      if(disposed||token.isCancellationRequested||!meta){run.skipped(item);return;}
      try{
        const doc=await vscode.workspace.openTextDocument(meta.uri);
        if(disposed||token.isCancellationRequested||!currentSelection(item,doc)){run.skipped(item);return;}
        run.started(item);
        const report=await verify(doc,{contract:meta.row.contract,function:meta.row.signature||meta.row.function,token});
        if(!report||disposed||token.isCancellationRequested||!currentSelection(item,doc)){run.skipped(item);return;}
        const row=report.results.find(row=>row.contract===meta.row.contract&&(row.signature||row.function)===(meta.row.signature||meta.row.function));
        if(report.errors.length||!row)run.errored(item,new vscode.TestMessage(report.errors.map(e=>e.reason).join('\n')||'Verifier returned no selected obligation'));
        else{
          const kind=model.resultKind(row);
          if(kind==='passed')run.passed(item,row.elapsedMs);
          else if(kind==='skipped')run.skipped(item);
          else run[kind](item,new vscode.TestMessage(model.detail(row)),row.elapsedMs);
        }
      }catch(error){
        if(disposed||token.isCancellationRequested||error.code==='CANCELLED'||[-32800,-32801].includes(error.code))run.skipped(item);
        else run.errored(item,new vscode.TestMessage(error.message));
      }
    }
    try{
      for(const item of selected.values())run.enqueued(item);
      for(const item of selected.values())await runItem(item);
    }finally{
      releaseAutomatic();registrations.forEach(registration=>registration.dispose());testRunCancellations.delete(cancellation);cancellation.dispose();run.end();
    }
  },true);
  context.subscriptions.push(
    diagnostics, controller, outputOwner,
    vscode.commands.registerCommand('solidityLean.verify', () => activeCommand(false)),
    vscode.commands.registerCommand('solidityLean.list', () => activeCommand(true)),
    vscode.commands.registerCommand('solidityLean.cancel', () => {for(const cancellation of testRunCancellations)cancellation.cancel();cancel();}),
    vscode.commands.registerCommand('solidityLean.showOutput', () => output.show(true)),
    vscode.workspace.onDidChangeConfiguration(event=>{
      for(const doc of documents.values())if(event.affectsConfiguration('solidityLean.displayVerificationAsTests',doc.uri)){
        if(!vscode.workspace.getConfiguration('solidityLean',doc.uri).get('displayVerificationAsTests',true)){automaticTests.visible(doc,false);clearTests(doc.uri,true);}
        else {automaticTests.visible(doc,true);const report=reports.get(key(doc.uri));if(report&&!doc.isClosed)publish(doc,report);}
      }
    }),
    vscode.workspace.onDidSaveTextDocument(doc => {
      if (service && isSolidity(doc)) service.save(doc);
      else if (isSolidity(doc) && vscode.workspace.getConfiguration('solidityLean', doc.uri).get('verifyOnSave', false)) verify(doc).catch(showError);
    }),
    vscode.workspace.onDidChangeTextDocument(event => {
      if (event.contentChanges.length) {clear(event.document.uri);if(service && isSolidity(event.document)) {documents.set(key(event.document.uri),event.document);service.open(event.document).catch(showError);}}
    }),
    vscode.workspace.onDidCloseTextDocument(doc => {clear(doc.uri);documents.delete(key(doc.uri));service?.close(doc.uri);}),
    vscode.languages.registerHoverProvider({ scheme: 'file', pattern: '**/*.sol' }, {
      provideHover(doc, position, token) {
        if(disposed||doc.isClosed||token?.isCancellationRequested)return null;
        const version=doc.version,text=doc.getText(),generation=restartGeneration;
        if (service) {
          const controller=new AbortController(),registration=token?.onCancellationRequested(()=>controller.abort());
          if(token?.isCancellationRequested)controller.abort();
          return service.request('textDocument/hover', doc, {position}, {signal:controller.signal}).then(result => {
          if (!result||disposed||doc.isClosed||controller.signal.aborted||doc.version!==version||doc.getText()!==text||restartGeneration!==generation) return null;
          const markdown=new vscode.MarkdownString();if(result.contents.kind==='markdown')markdown.appendMarkdown(result.contents.value);else markdown.appendText(result.contents.value);
          return new vscode.Hover(markdown,toRange(result.range));
        }).catch(error => {if(![-32800,-32801].includes(error.code))showError(error);return null;}).finally(()=>registration?.dispose());
        }
        const matches = reports.get(key(doc.uri))?.results.filter(row => toRange(model.rangeOf(row)).contains(position));
        // A synthesized constructor spans the contract. Prefer the function
        // declaration under the cursor to that broader deployment result.
        const row = matches?.find(row => Number.isSafeInteger(row.sourceId) && row.sourceId >= 0) || matches?.[0];
        if (!row) return null;
        const markdown = new vscode.MarkdownString();
        markdown.appendText(model.detail(row));
        return new vscode.Hover(markdown, toRange(model.rangeOf(row)));
      }
    }),
    { dispose: () => cancel() }
  );
  if(service) {
    editorServices=require('./editor-services.cjs').install(vscode,context,service,showError);
    const open=(doc,again=false)=>{if(!disposed&&!doc.isClosed&&isSolidity(doc)){documents.set(key(doc.uri),doc);const generation=documentGenerations.get(key(doc.uri))||0;
      const current=()=>!disposed&&!doc.isClosed&&documents.get(key(doc.uri))===doc&&generation===(documentGenerations.get(key(doc.uri))||0);
      return service.open(doc).then(client=>{if(current()&&client?.serverInfo?.name){const feedback=again?require('./status-summary.cjs').issueURL(client):null;output.appendLine(`Solidity Lean is ready${again?' again':''} for ${key(doc.uri)} (language services; version ${client.serverInfo.version||'unknown'}).`+(feedback?'\nIf you have time, please let us know why you needed to restart by filing an issue:\n'+feedback:''));}}).catch(error=>{if(current()&&![-32800,-32801].includes(error.code)&&error.code!=='CANCELLED'){output.appendLine(`Language server startup failed for ${key(doc.uri)}: ${error.message}`);showError(Object.assign(error,{uris:error.uris||[key(doc.uri)]}));}});
    }};
    const receive=params=>{
      const doc=documents.get(params.uri);if(!doc||doc.isClosed||doc.version!==params.version||hash(doc.getText())!==params.sourceHash)return;
      try{accept(doc,params.report,settings(doc),params.selection);}catch(error){showError(error);}
    };
    const receiveStatus=params=>{
      const doc=documents.get(params.uri);if(disposed||!doc||doc.isClosed||doc.version!==params.version||hash(doc.getText())!==params.sourceHash)return;
      if(!vscode.workspace.getConfiguration('solidityLean',doc.uri).get('displayVerificationAsTests',true))return;
      if(!Array.isArray(params.functions)||params.functions.some(row=>!row||!model.validRange(row.range)||typeof row.status!=='string'||row.name!==undefined&&typeof row.name!=='string'))return;
      automaticTests.status(doc,params);
    };
    const receiveDiagnostics=params=>{
      const doc=documents.get(params.uri);if(!doc||doc.isClosed||doc.version!==params.version)return;
      diagnostics.set(doc.uri,params.diagnostics.map(row=>{const d=new vscode.Diagnostic(toRange(row.range),row.message,row.severity-1);d.source=row.source;d.code=row.code;if(row.relatedInformation)d.relatedInformation=row.relatedInformation.map(r=>new vscode.DiagnosticRelatedInformation(new vscode.Location(vscode.Uri.parse(r.location.uri),toRange(r.location.range)),r.message));return d;}));
    };
    const invalidated=params=>{const doc=documents.get(params.uri);if(doc?.version===params.version)clear(doc.uri,false);};
    service.on('invalidated',invalidated);
    const serverError=error=>{
      if(disposed||[-32800,-32801].includes(error.code)||error.code==='CANCELLED')return;
      if(error.uris&&!error.uris.some(uri=>{const doc=documents.get(uri);return doc&&!doc.isClosed;}))return;
      const affected=error.uris?new Set(error.uris):null;
      for(const [id,doc]of documents)if(!affected||affected.has(id)){
        saving.delete(id);active.get(id)?.abort();clear(doc.uri,false);editorServices?.clearIdentity(doc.uri);
      }
      showError(error);
    };
    const log=message=>output.appendLine(message);
    service.on('status',receiveStatus);service.on('report',receive);service.on('diagnostics',receiveDiagnostics);service.on('serverError',serverError);service.on('log',log);
    const restart=async selected=>{
      if(disposed)return;
      const operation=++restartGeneration;const targets=selected||[...documents.values()],generations=new Map();
      if(!selected)cancel();
      for(const doc of targets){const id=key(doc.uri),generation=(documentGenerations.get(id)||0)+1;documentGenerations.set(id,generation);generations.set(id,generation);if(selected)cancel(doc.uri);clear(doc.uri,false);editorServices?.clearIdentity(doc.uri);}
      const current=doc=>!disposed&&!doc.isClosed&&documentGenerations.get(key(doc.uri))===generations.get(key(doc.uri));
      output.appendLine('Terminating Solidity Lean language services...');
      try{await service.restart(selected?targets.map(doc=>doc.uri):undefined);}catch(error){if(targets.some(current)||!disposed&&!selected&&!targets.length&&restartGeneration===operation){output.appendLine('Language server stop failed: '+error.message);showError(error);}return;}
      await Promise.all(targets.filter(current).map(doc=>open(doc,true)));
    };
    const serverSettings=['backendPath','nodePath','timeoutMs','workers','automaticVerification','verifyOnSave','includePaths','remappings','counterexamples','auditPreconditions'];
    context.subscriptions.push(vscode.workspace.onDidOpenTextDocument(open),
      vscode.commands.registerCommand('solidityLean.restartServer',()=>restart().catch(showError)),
      vscode.workspace.onDidChangeConfiguration(event=>{const affected=[...documents.values()].filter(doc=>serverSettings.some(setting=>event.affectsConfiguration('solidityLean.'+setting,doc.uri)));if(affected.length)restart(affected).catch(showError);}),
      {dispose(){service.removeListener('invalidated',invalidated);service.removeListener('status',receiveStatus);service.removeListener('report',receive);service.removeListener('diagnostics',receiveDiagnostics);service.removeListener('serverError',serverError);service.removeListener('log',log);}});
    for(const doc of vscode.workspace.textDocuments)open(doc);
  }
  return { verify, cancel, controller, diagnostics, reports, service,
    dispose(){
      if(disposal)return disposal;disposed=true;
      let resolveDisposal,rejectDisposal;disposal=new Promise((resolve,reject)=>{resolveDisposal=resolve;rejectDisposal=reject;});
      const cleanup=async()=>{
        const errors=[],pending=[];
        const attempt=fn=>{try{const result=fn();if(result!==disposal&&result&&typeof result.then==='function')pending.push(Promise.resolve(result).catch(error=>{errors.push(error);}));}catch(error){errors.push(error);}};
        attempt(disposeTesting);for(const cancellation of testRunCancellations)attempt(()=>cancellation.cancel());attempt(cancel);
        for(const item of context.subscriptions)if(item!==outputOwner)attempt(()=>item.dispose());
        attempt(()=>service?.dispose());attempt(()=>sourceCommands.dispose());
        try{await Promise.all(pending);}finally{attempt(()=>outputOwner.dispose());}
        const failures=[...new Set(errors)];if(failures.length)throw failures.length===1?failures[0]:new AggregateError(failures,'Extension cleanup failed');
      };
      cleanup().then(resolveDisposal,rejectDisposal);return disposal;
    } };
}
let runtime;
function activate(context) {
  const vscode=require('vscode');
  const configuration=doc=>{
    if(!vscode.workspace.isTrusted)throw new Error('Language services require a trusted workspace');
    const cfg=vscode.workspace.getConfiguration('solidityLean',doc.uri),workspace=vscode.workspace.getWorkspaceFolder(doc.uri)?.uri.fsPath;
    const configured=cfg.get('backendPath','');if(!configured&&!workspace)throw require('./startup.cjs').startupError('Set solidityLean.backendPath to the repository directory','backendPath');
    return {projectRoot:workspace||dirname(doc.uri.fsPath),includePaths:cfg.get('includePaths',[]),remappings:cfg.get('remappings',[]),backendPath:resolve(workspace||'.',configured||'.'),nodePath:cfg.get('nodePath','node'),timeoutMs:cfg.get('timeoutMs',600000),workers:cfg.get('workers',1),
      automaticVerification:cfg.get('verifyOnSave',false)?'save':({onchange:'change',onsave:'save',never:'never'}[cfg.get('automaticVerification','onchange')]||'never'),
      counterexamples:cfg.get('counterexamples',false),auditPreconditions:cfg.get('auditPreconditions',false)};
  };
  const service=new (require('./lsp-client.cjs').LanguageServers)(configuration);
  const api=createExtension(vscode,context,args=>service.verify(args),service);
  context.subscriptions.push({dispose:()=>service.dispose()});runtime=api;return api;
}
function deactivate(){return runtime?.dispose();}
module.exports = { activate, deactivate, createExtension };
