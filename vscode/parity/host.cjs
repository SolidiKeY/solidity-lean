'use strict';
const assert = require('node:assert/strict');
const {readFileSync,writeFileSync,appendFileSync,existsSync} = require('node:fs');
const {join} = require('node:path');
const {performance} = require('node:perf_hooks');
const {createHash}=require('node:crypto');
const {observe} = require('./observe.cjs');
const {workload,symbolPosition} = require('./workloads.cjs');

async function run() {
  const vscode = require('vscode');
  const config = JSON.parse(readFileSync(process.env.PARITY_HOST_CONFIG,'utf8'));
  // Desktop VS Code may resolve a login-shell PATH. Preserve the explicitly
  // selected backend toolchain rather than silently switching installations.
  Object.assign(process.env,config.runtimeEnvironment||{});
  const target = config.target, metrics = {}, scenarios = [], events = [], states = new Map();
  const started = performance.now();
  const record = (kind,data) => {
    const event = {ms:performance.now()-started,kind,data}; events.push(event);
    appendFileSync(config.events,JSON.stringify(event)+'\n');
  };
  const extension=vscode.extensions.getExtension(target==='dafny'?'dafny-lang.ide-vscode':'SolidiKeY.solidity-lean');
  assert.ok(extension,'target extension is installed');
  const observation = observe(vscode,record,extension.extensionPath,config.recordProtocol?config.trace:null);
  const heartbeat = [];
  let last = performance.now();
  const timer = setInterval(()=>{const now=performance.now();heartbeat.push(Math.max(0,now-last-25));last=now;},25);
  const result = {schemaVersion:1,runId:config.runId,target,startedWallTime:Date.now(),metrics,scenarios,observations:{},checks:[],status:'running'};
  let api, client, activeScenario = null;
  const timeout = config.operationTimeoutMs;
  async function bounded(promise,label) {
    let timer;
    try{return await Promise.race([promise,new Promise((_,reject)=>{timer=setTimeout(()=>reject(Object.assign(new Error('Timed out: '+label),{code:'TIMEOUT'})),timeout);})]);}
    finally{clearTimeout(timer);}
  }
  async function until(predicate,label) {
    const start=performance.now();
    while (!predicate()) {
      if (performance.now()-start > timeout) throw Object.assign(new Error('Timed out: '+label),{code:'TIMEOUT'});
      await new Promise(resolve=>setTimeout(resolve,20));
    }
  }
  async function scenario(id, fn) {
    const start=performance.now(); activeScenario=id;
    record('scenario.start',{id});
    try {
      const observation=await fn();
      const status=['partial','missing','unexamined'].includes(observation?.status)?observation.status:'passed';
      scenarios.push({id,status,elapsedMs:performance.now()-start,observation});
      if(status==='passed')result.checks.push(id);
    }
    catch(error) {scenarios.push({id,status:error.code === 'TIMEOUT' ? 'timeout' : 'broken',elapsedMs:performance.now()-start,error:error.stack});}
    record('scenario.end',{id}); activeScenario=null;
  }
  const file = name => join(config.workspace,name+(target==='dafny'?'.dfy':'.sol'));
  async function open(name,count=1,failing=false) {
    const path=file(name); writeFileSync(path,workload(target,count,failing));
    const doc=await vscode.workspace.openTextDocument(path);
    await vscode.window.showTextDocument(doc,{preview:false}); return doc;
  }
  function current(doc) { const state=states.get(doc.uri.toString());return state?.version === doc.version ? state : null; }
  async function verify(doc,count) {
    if (target==='local') {
      const report=await api.verify(doc);
      assert.ok(report,'verification discarded');
      assert.equal(report.errors.length,0,JSON.stringify(report.errors));
      assert.equal(report.results.filter(r=>/^f\d+$/.test(r.function)).length,count,'all paired obligations must be reported');
      return report;
    }
    await until(()=>{const state=current(doc);return state?.namedVerifiables.length===count && state.namedVerifiables.every(s=>s.status>=4);},'final current-version symbol status');
    return current(doc);
  }
  function snapshot(doc) {
    const diagnostics=vscode.languages.getDiagnostics(doc.uri).map(d=>({severity:d.severity,code:d.code,message:d.message,range:d.range,source:d.source}));
    const tests=[];
    const visit=items=>items.forEach(item=>{if(item.uri?.toString()===doc.uri.toString())tests.push({label:item.label,description:item.description,range:item.range});visit(item.children);});
    observation.controllers.forEach(c=>visit(c.items));
    const outcomes=target==='local'?(api.reports.get(doc.uri.toString())?.results||[]).filter(r=>/^f\d+$/.test(r.function)).map(r=>({function:r.function,nativeStatus:r.status})):
      (states.get(doc.uri.toString())?.namedVerifiables||[]).map(r=>({function:doc.getText(new vscode.Range(new vscode.Position(r.nameRange.start.line,r.nameRange.start.character),new vscode.Position(r.nameRange.end.line,r.nameRange.end.character))),nativeStatus:r.status}));
    return {version:doc.version,diagnostics,tests,outcomes,visible:!!vscode.window.visibleTextEditors.find(e=>e.document===doc)};
  }
  async function replace(doc,text) {
    const edit=new vscode.WorkspaceEdit();
    edit.replace(doc.uri,new vscode.Range(doc.positionAt(0),doc.positionAt(doc.getText().length)),text);
    assert.equal(await vscode.workspace.applyEdit(edit),true);
    assert.equal(doc.getText(),text,'the editor must contain the exact intended edit');
  }
  async function request(command,doc,position,extra) {
    const start=performance.now();
    const value=await vscode.commands.executeCommand(command,doc.uri,new vscode.Position(position.line,position.character),...extra);
    return {elapsedMs:performance.now()-start,value};
  }
  try {
    const activation=performance.now(); api=await bounded(extension.activate(),'extension activation');
    metrics.activationMs=performance.now()-activation;
    assert.ok(api,'activation returned no runtime');
    if (target==='dafny') {
      client=api.client; assert.ok(client,'Dafny runtime client unavailable');
      result.observations.serverCapabilities=client.initializeResult?.capabilities;
      // The LSP connection allows one handler per method. Use Dafny's public
      // multicast event so observation cannot replace its UI handlers.
      client.OnVerificationSymbolStatus(params=>{states.set(params.uri,params);record('symbolStatus',params);});
    }
    const initialStart=performance.now();
    let doc;
    await scenario('initial-verification',async()=>{
      doc=await open('initial',config.obligations);
      const report=await verify(doc,config.obligations);
      if(target==='local') assert.ok(report.results.filter(r=>/^f\d+$/.test(r.function)).every(r=>r.status==='proved'));
      else assert.ok(report.namedVerifiables.every(r=>r.status===5));
      metrics.initialVerificationMs=performance.now()-initialStart;
      result.initialCompletedSinceHostMs=performance.now()-started;
      metrics.throughputObligationsPerSecond=config.obligations/(metrics.initialVerificationMs/1000);
      return snapshot(doc);
    });
    if (!doc) throw new Error('Initial document failed to open');
    const initialEvents=events.filter(e=>e.ms>=initialStart-started);
    const useful=initialEvents.find(e=>e.kind==='symbolStatus' && e.data.namedVerifiables.some(s=>s.status>=4) || e.kind==='diagnostics' && e.data.diagnostics.length>0);
    metrics.firstUsefulFeedbackMs=useful?useful.ms-(initialStart-started):metrics.initialVerificationMs;
    result.observations.feedbackDefinition='First terminal symbol or nonempty diagnostic; local proved reports use completion time.';
    if(config.suite==='full')await scenario('testing-explorer',async()=>{
      const leaves=[];
      const visit=items=>items.forEach(item=>{if(item.children.size)visit(item.children);else if(item.uri?.toString()===doc.uri.toString())leaves.push(item);});
      observation.controllers.forEach(c=>visit(c.items));
      const item=leaves.find(i=>i.label.includes('f0'));assert.ok(item,'paired obligation in Testing API');
      const profile=observation.profiles.find(p=>p.name==='Verify');assert.ok(profile,'Verify run profile');
      const source=new vscode.CancellationTokenSource();
      try{await profile.handler(new vscode.TestRunRequest([item],leaves.filter(i=>i!==item)),source.token);}finally{source.dispose();}
      return {status:'partial',selected:item.label,excluded:leaves.filter(i=>i!==item).map(i=>i.label),
        scope:'Real run-profile handler invoked; comprehensive queued/stale/exclusion/cancel transitions require more scenarios.'};
    });
    const pos=symbolPosition(target,doc.getText());
    for (const [id,command] of [['hover','vscode.executeHoverProvider'],['completion','vscode.executeCompletionItemProvider'],
      ['definition','vscode.executeDefinitionProvider'],['references','vscode.executeReferenceProvider'],['signature-help','vscode.executeSignatureHelpProvider']]) {
      await scenario(id,async()=>{
        const response=await request(command,doc,pos,[]);metrics[id+(id==='hover'?'Ms':'ProbeMs')]=response.elapsedMs;
        if(id==='hover') assert.ok(response.value?.length,'expected verification hover');
        const value=id==='hover'?response.value?.map(h=>({range:h.range,contents:h.contents.map(c=>typeof c==='string'?c:{value:c.value,language:c.language,isTrusted:c.isTrusted})})):response.value;
        const present=Array.isArray(response.value)?response.value.length>0:response.value?.items?response.value.items.length>0:!!response.value;
        return {status:id==='hover'?'passed':target==='local'?'missing':'unexamined',present,value,
          scope:id==='hover'?'verified declaration hover':'Discovery probe at declaration; dedicated trigger/call-site tests are required.'};
      });
    }
    if(config.suite==='full')await scenario('symbols-and-formatting',async()=>({
      status:target==='local'?'missing':'partial',
      symbols:await vscode.commands.executeCommand('vscode.executeDocumentSymbolProvider',doc.uri),
      formatting:await vscode.commands.executeCommand('vscode.executeFormatDocumentProvider',doc.uri,{tabSize:2,insertSpaces:true})
    }));
    await scenario('incremental-verification',async()=>{
      const start=performance.now();await replace(doc,workload(target,config.obligations+1));
      await verify(doc,config.obligations+1);metrics.incrementalVerificationMs=performance.now()-start;return snapshot(doc);
    });
    if(config.suite==='full')await scenario('rapid-edits-stale-results',async()=>{
      // A false obligation is immediately replaced by the proved version.
      await replace(doc,workload(target,config.obligations+1,true));
      if(target==='local')await doc.save();
      const before=events.length;
      const obsolete=target==='local'?api.verify(doc).catch(e=>{if(e.code==='CANCELLED')return {cancelled:true};throw e;}):Promise.resolve();
      if(target==='local')assert.ok(events.slice(before).some(e=>e.kind==='output'&&e.data.text.startsWith('Verifying ')),'false-version backend started before the edit');
      // A new declaration also changes the symbol set. Dafny deliberately
      // deduplicates identical status arrays across versions, so a comment-only
      // restore cannot be used as a terminal-notification barrier.
      await replace(doc,workload(target,config.obligations+2,false)+'\n// newest\n');
      await obsolete;await verify(doc,config.obligations+2);
      assert.equal(snapshot(doc).diagnostics.length,0,'obsolete failure diagnostics must not survive');return snapshot(doc);
    });
    if(config.suite==='full')await scenario('save-edit-race',async()=>{
      if(target==='dafny')return {status:'unexamined',reason:'Automatic in-memory verification does not use the local command save boundary.'};
      await replace(doc,workload(target,config.obligations+1,true));
      const saving=api.verify(doc).catch(e=>{if(e.code==='CANCELLED')return null;throw e;});
      await replace(doc,workload(target,config.obligations+2,false)+'\n// edited during save\n');
      const old=await saving;assert.equal(old,null,'edit supersedes a request still awaiting save');
      const hash=text=>createHash('sha256').update(text).digest('hex');
      const saveBoundary={version:doc.version,isDirty:doc.isDirty,bufferHash:hash(doc.getText()),diskHash:hash(readFileSync(doc.uri.fsPath))};
      // VS Code can mark the new buffer clean after persisting an older snapshot.
      // Record that upstream persistence boundary rather than weakening hashes.
      // This explicit Save command forces the currently displayed test file to disk.
      await vscode.commands.executeCommand('workbench.action.files.save');
      await verify(doc,config.obligations+2);assert.equal(snapshot(doc).diagnostics.length,0);
      return {status:'partial',saveBoundary,state:snapshot(doc),scope:'The obsolete request is suppressed. Latest verification requires explicit Save after this VS Code persistence race; automatic recovery remains open.'};
    });
    if(config.suite==='full')await scenario('failure-diagnostics',async()=>{
      await replace(doc,workload(target,config.obligations,true));await verify(doc,config.obligations);
      const state=snapshot(doc);assert.ok(state.diagnostics.length>0,'false postcondition must be visible');return state;
    });
    if(config.suite==='full')await scenario('counterexamples',async()=>{
      if (target==='dafny') {
        const value=await client.sendRequest('dafny/counterExample',{textDocument:{uri:doc.uri.toString()},counterExampleDepth:2});
        assert.ok(value?.some(item=>typeof item.assumption==='string'&&item.position),'positioned counterexample evidence');
        return {status:'partial',value,scope:'Positioned model trace exists; source-level witness equivalence is not established.'};
      }
      await vscode.workspace.getConfiguration('solidityLean').update('counterexamples',true,vscode.ConfigurationTarget.Workspace);
      const report=await api.verify(doc);
      const rows=report.results.filter(r=>/^f\d+$/.test(r.function));
      assert.ok(rows.some(r=>r.status==='refuted'&&r.counterexample),'certified counterexample evidence');
      return {status:'partial',rows:rows.map(r=>({function:r.function,status:r.status,counterexample:r.counterexample})),scope:'Certified model prestate, without a positioned trace.'};
    });
    await scenario('concurrent-files-and-requests',async()=>{
      const start=performance.now();
      const docs=await Promise.all([open('parallel-a',config.obligations),open('parallel-b',config.obligations)]);
      writeFileSync(join(config.dir,'renderer-probe.json'),JSON.stringify({started:Date.now()}));
      const work=Promise.all(docs.map(d=>verify(d,config.obligations)));
      const hover=await request('vscode.executeHoverProvider',doc,pos,[]);
      await work;metrics.crossFileVerificationMs=performance.now()-start;metrics.hoverDuringVerificationMs=hover.elapsedMs;
      writeFileSync(join(config.dir,'renderer-probe-end.json'),JSON.stringify({finished:Date.now()}));
      return {files:docs.map(snapshot),hoverPresent:!!hover.value?.length};
    });
    await vscode.workspace.saveAll();
    await vscode.commands.executeCommand('workbench.action.closeAllEditors');
    await scenario('cancellation',async()=>{
      const busy=await open('cancel',Math.max(64,config.obligations));
      const pending=target==='local'?api.verify(busy).catch(e=>({error:e.code})):Promise.resolve();
      let witness;
      if(target==='dafny') {
        await until(()=>current(busy)?.namedVerifiables.some(s=>s.status===1||s.status===2),'queued or running cancellation witness');
        witness=current(busy).namedVerifiables.find(s=>s.status===2)||current(busy).namedVerifiables.find(s=>s.status===1);
      } else await new Promise(resolve=>setTimeout(resolve,150));
      const start=performance.now();
      if(target==='local') {api.cancel(); const report=await pending;assert.ok(report?.error==='CANCELLED' || report===null,'job was not interrupted');}
      else {
        const position=witness.nameRange.start;
        const accepted=await client.sendRequest('dafny/textDocument/cancelVerifySymbol',{textDocument:{uri:busy.uri.toString()},position});
        assert.equal(accepted,true,'server did not accept cancellation');
      }
      metrics.cancellationRequestMs=performance.now()-start;
      // This measures acknowledgement/CLI abort. Solver quiescence is a separate observation.
      return {status:'partial',latencyKind:target==='local'?'backend-abort-acknowledgement':'symbol-cancel-acknowledgement',
        witness,scope:'Acknowledgement only. Solver quiescence and cancellation of the entire file remain unexamined.',state:snapshot(busy)};
    });
    await vscode.workspace.saveAll();
    await vscode.commands.executeCommand('workbench.action.closeAllEditors');
    if(config.suite==='full')await scenario('configuration-and-save',async()=>{
      const saved=await open('save',1);
      if(target==='local') await vscode.workspace.getConfiguration('solidityLean').update('verifyOnSave',true,vscode.ConfigurationTarget.Workspace);
      await replace(saved,workload(target,1)+'\n// save trigger\n');await saved.save();
      if(target==='local') await until(()=>api.reports.has(saved.uri.toString()),'save verification report');
      else await verify(saved,1);
      return snapshot(saved);
    });
    await scenario('server-restart',async()=>{
      if(target==='local') return {status:'missing',reason:'CLI backend has no restart command or persistent LSP server'};
      const start=performance.now();await vscode.commands.executeCommand('dafny.restartServer');
      metrics.restartMs=performance.now()-start;
      const restarted=await open('restarted',1);await verify(restarted,1);return snapshot(restarted);
    });
    result.observations.commands=(await vscode.commands.getCommands(true)).filter(c=>c.startsWith(target==='local'?'solidityLean.':'dafny.'));
    result.observations.decorations=observation.decorations;
    result.observations.testEvents=events.filter(e=>e.kind.startsWith('test.'));
    result.observations.errors=events.filter(e=>e.kind==='error');
    metrics.extensionHostMaxDelayMs=Math.max(0,...heartbeat);
    metrics.extensionHostP95DelayMs=require('./core.cjs').statistics(heartbeat).p95;
    result.observations.responsivenessScope='Extension-host timer delay. Renderer responsiveness requires DOM automation.';
    result.status=scenarios.some(s=>s.status==='timeout')?'timeout':scenarios.some(s=>s.status==='broken')?'broken':
      scenarios.every(s=>s.status==='passed')?'passed':'passed-with-gaps';
  } catch(error) {result.status=error.code==='TIMEOUT'?'timeout':'broken';result.error=error.stack;}
  finally {
    clearInterval(timer);observation.restore();result.elapsedMs=performance.now()-started;
    writeFileSync(config.result,JSON.stringify(result,null,2));
    if(target==='local') api?.cancel();
    const captureStart=performance.now();
    while(!existsSync(join(config.dir,'renderer-done'))&&performance.now()-captureStart<15000)
      await new Promise(resolve=>setTimeout(resolve,50));
  }
  // The launcher validates fresh structured evidence and retains failed scenarios.
}
module.exports = {run};
