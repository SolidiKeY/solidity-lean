'use strict';
const assert = require('node:assert/strict');
const {readFileSync,writeFileSync,appendFileSync,existsSync,mkdirSync,unlinkSync} = require('node:fs');
const {join} = require('node:path');
const {performance} = require('node:perf_hooks');
const {createHash}=require('node:crypto');
const {observe} = require('./observe.cjs');
const {workload,symbolPosition,verificationOutcomes,servicesWorkload,assertServiceResponse} = require('./workloads.cjs');

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
  const observation = observe(vscode,record,extension.extensionPath,config.recordProtocol?config.trace:null,config.workspace);
  const heartbeat = [];
  let last = performance.now();
  const timer = setInterval(()=>{const now=performance.now();heartbeat.push(Math.max(0,now-last-25));last=now;},25);
  const result = {schemaVersion:1,runId:config.runId,target,startedWallTime:Date.now(),metrics,scenarios,observations:{},checks:[],status:'running'};
  let api, client, activeScenario = null, localRetirementStarted=false;
  let localStatus;
  const visual=config.suite==='visual',traceSessions=new WeakMap(),sessionFor=doc=>{if(!traceSessions.has(doc))traceSessions.set(doc,require('node:crypto').randomUUID());return traceSessions.get(doc);};
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
  function keybindingRequest(request){require('./phase-capture.cjs').atomicJson(join(config.dir,'keybinding-request.json'),request);}
  const file = name => join(config.workspace,name+(target==='dafny'?'.dfy':'.sol'));
  async function open(name,count=1,failing=false) {
    const path=file(name); writeFileSync(path,workload(target,count,failing));
    const doc=await vscode.workspace.openTextDocument(path);
    await vscode.window.showTextDocument(doc,{preview:false}); return doc;
  }
  function current(doc) { const state=states.get(doc.uri.toString());return state?.version === doc.version ? state : null; }
  async function verify(doc,count,expected='proved') {
    if (target==='local') {
      const report=await api.verify(doc);
      assert.ok(report,'verification discarded');
      verificationOutcomes(target,report,count,expected);
      return report;
    }
    await until(()=>{const state=current(doc);return state?.namedVerifiables.length===count && state.namedVerifiables.every(s=>s.status>=4);},'final current-version symbol status');
    verificationOutcomes(target,current(doc),count,expected);
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
    if(config.suite==='output-lifecycle'){
      await scenario('native-output-restart',async()=>{
        const name=target==='local'?'Solidity Lean':'Dafny VSCode',channel=events.filter(e=>e.kind==='output.create'&&e.data.channel===name);assert.equal(channel.length,1,'one actual extension output channel');
        const outputUri=vscode.Uri.file(file('output-lifecycle'));writeFileSync(outputUri.fsPath,workload(target,1));await vscode.commands.executeCommand('vscode.open',outputUri,{preview:false});await until(()=>vscode.window.activeTextEditor?.document.uri.toString()===outputUri.toString(),'real source editor open');let doc=vscode.window.activeTextEditor.document;const source=doc.getText(),version=doc.version;
        await until(()=>events.some(e=>e.kind==='output'&&e.data.channelId===channel[0].data.channelId&&e.data.text.startsWith(target==='local'?`Solidity Lean is ready for ${doc.uri.toString()} (`:'Dafny is ready')),'actual startup/version readiness output');
        const startup=events.find(e=>e.kind==='output'&&e.data.channelId===channel[0].data.channelId&&e.data.text.startsWith(target==='local'?`Solidity Lean is ready for ${doc.uri.toString()} (`:'Dafny is ready'));
        const start=events.length,command=target==='local'?'solidityLean.restartServer':'dafny.restartServer';await vscode.commands.executeCommand(command);
        await until(()=>events.slice(start).some(e=>e.kind==='output'&&e.data.channelId===channel[0].data.channelId&&e.data.text.startsWith(target==='local'?`Solidity Lean is ready again for ${doc.uri.toString()} (`:'Dafny is ready again.')),'actual restart/version readiness output');
        const rows=events.slice(start),termination=rows.findIndex(e=>e.kind==='output'&&e.data.channelId===channel[0].data.channelId&&e.data.text.startsWith('Terminating')),ready=rows.findIndex(e=>e.kind==='output'&&e.data.channelId===channel[0].data.channelId&&e.data.text.startsWith(target==='local'?`Solidity Lean is ready again for ${doc.uri.toString()} (`:'Dafny is ready again.'));
        assert.ok(termination>=0&&ready>termination);assert.ok(!rows.some(e=>e.kind==='output.dispose'&&e.data.channelId===channel[0].data.channelId));assert.equal(events.filter(e=>e.kind==='output.create'&&e.data.channel===name).length,1);assert.ok(!doc.isClosed);assert.equal(doc.version,version);assert.equal(doc.getText(),source);
        const observed={status:'partial',channel:channel[0],channels:events.filter(e=>['output.create','output.dispose'].includes(e.kind)&&e.data.channel===name),startup,events:rows,uri:doc.uri.toString(),version,sourceHash:createHash('sha256').update(source).digest('hex'),scope:'Actual native output API and registered restart action. No output-panel rendering, failed/native overlap matrix, performance, kernel or exact branded-text parity. Upstream readiness is global; local readiness names the document.'};assert.deepEqual(require('./core.cjs').outputLifecycleErrors(observed,target),[]);
        if(target==='local'){const owner=api.service.owners.get(doc.uri.toString());assert.ok(owner);const identity={serverInfo:owner.serverInfo,runtimeInfo:{version:owner.runtimeInfo?.version||'unknown'}},url=require('../src/status-summary.cjs').issueURL(identity);assert.ok(url);assert.ok(rows[ready].data.text.endsWith('\n'+url),'actual current metadata issue draft after restart');observed.feedback={identity,url,scope:'Existing repository-derived status-menu issue draft, printed only; no source attached/submission.'};}
        if(target==='local')await vscode.commands.executeCommand('solidityLean.showOutput');else{const owned=observation.outputs.filter(o=>o.name===name&&o.channelId===channel[0].data.channelId);assert.equal(owned.length,1);owned[0].channel.show(true);}
        observed.panel=await require('./phase-capture.cjs').requestPhase(config.dir,config.runId,'output-channel',{uri:observed.uri,version,sourceHash:observed.sourceHash,sourceSession:rows.find(e=>e.kind==='command.end'&&e.data.id===command)?.data.source.session,channelId:channel[0].data.channelId,channel:name,readinessPrefix:target==='local'?'Solidity Lean is ready again':'Dafny is ready again.',readinessLine:rows[ready].data.text.split('\n')[0]},timeout);
        assert.equal(doc.version,version);assert.equal(doc.getText(),source);assert.ok(!doc.isClosed);observed.panelScope='Actual output panel shown through registered local Show Output or captured public Dafny OutputChannel.show; visible panel/channel DOM/AX/PNG and owned DOM-resident readiness; full source-path glyph visibility is unproved, not a Dafny contribution action or full phase/lifecycle equivalence.';
        if(target==='local'){
          const lifecycle={},scope=vscode.workspace.getConfiguration('solidityLean',doc.uri),configurationTarget=vscode.workspace.workspaceFile?vscode.ConfigurationTarget.WorkspaceFolder:vscode.ConfigurationTarget.Workspace,previous=configurationTarget===vscode.ConfigurationTarget.WorkspaceFolder?scope.inspect('nodePath')?.workspaceFolderValue:scope.inspect('nodePath')?.workspaceValue,runtime=scope.get('nodePath'),badRuntime=join(config.workspace,'missing-output-lifecycle-runtime'),own=e=>e.kind==='output'&&e.data.channel===name&&e.data.channelId===channel[0].data.channelId;const progress=stage=>require('./phase-capture.cjs').atomicJson(join(config.dir,'output-lifecycle-progress.json'),{runId:config.runId,uri:doc.uri.toString(),version,sourceHash:observed.sourceHash,stage,document:{closed:doc.isClosed,listed:vscode.workspace.textDocuments.includes(doc),tabs:vscode.window.tabGroups.all.flatMap(group=>group.tabs).filter(tab=>tab.input?.uri?.toString()===doc.uri.toString()).length},lifecycle});assert.equal(existsSync(badRuntime),false);const runtimeOwner=api.service.owners.get(doc.uri.toString());assert.ok(runtimeOwner);lifecycle.runtimeBeforeReported={...runtimeOwner.runtimeInfo};let restored=false;
          try{const failureStart=events.length;await scope.update('nodePath',badRuntime,configurationTarget);await until(()=>events.slice(failureStart).some(e=>own(e)&&e.data.text.startsWith(`Language server startup failed for ${doc.uri.toString()}:`)),'actual missing configured runtime failure');lifecycle.failureEvents=events.slice(failureStart);progress('runtime-failed');assert.ok(!lifecycle.failureEvents.some(e=>own(e)&&e.data.text.startsWith('Solidity Lean is ready')));const recoveryStart=events.length;await scope.update('nodePath',previous,configurationTarget);restored=true;await until(()=>events.slice(recoveryStart).some(e=>own(e)&&e.data.text.startsWith(`Solidity Lean is ready again for ${doc.uri.toString()} (`)),'actual corrected runtime initialize/version recovery');lifecycle.recoveryEvents=events.slice(recoveryStart);lifecycle.runtimeBefore=runtime;lifecycle.rejectedRuntime=badRuntime;lifecycle.runtimeRestored=vscode.workspace.getConfiguration('solidityLean',doc.uri).get('nodePath');const recovered=api.service.owners.get(doc.uri.toString());assert.ok(recovered);lifecycle.runtimeRecoveredReported={...recovered.runtimeInfo};assert.equal(lifecycle.runtimeRestored,runtime);assert.equal(lifecycle.runtimeRecoveredReported.configuredPath,lifecycle.runtimeBeforeReported.configuredPath);assert.equal(lifecycle.runtimeRecoveredReported.version,lifecycle.runtimeBeforeReported.version);progress('runtime-recovered');}finally{if(!restored)await scope.update('nodePath',previous,configurationTarget);}
          const tools=require('./trace-presentation.cjs'),records=()=>readFileSync(config.trace,'utf8').trim().split('\n').filter(Boolean).map(line=>JSON.parse(line)),oldDoc=doc,before=records(),oldWire=tools.wireDocument(before,before.length,doc.uri.toString()),oldSession=sessionFor(doc),reopenStart=events.length;assert.equal(oldWire.textHash,observed.sourceHash);await tools.closeSourceTabs(vscode,doc);progress('source-tabs-closed');await until(()=>oldDoc.isClosed&&!vscode.workspace.textDocuments.includes(oldDoc),'actual output source close');await until(()=>records().some((r,i)=>i>=before.length&&r.direction==='client'&&r.message?.method==='textDocument/didClose'&&r.message.params.textDocument.uri===observed.uri),'actual source wire close');const closed=records(),closeIndex=closed.findIndex((r,i)=>i>=before.length&&r.direction==='client'&&r.message?.method==='textDocument/didClose'&&r.message.params.textDocument.uri===observed.uri);await vscode.commands.executeCommand('vscode.open',oldDoc.uri,{preview:false});await until(()=>vscode.window.activeTextEditor?.document.uri.toString()===oldDoc.uri.toString()&&vscode.window.activeTextEditor.document!==oldDoc,'real source editor reopen');doc=vscode.window.activeTextEditor.document;assert.notEqual(doc,oldDoc);await until(()=>events.slice(reopenStart).some(e=>own(e)&&e.data.text.startsWith(`Solidity Lean is ready for ${doc.uri.toString()} (`)),'actual reopened source readiness');const reopened=records(),wire=tools.wireDocument(reopened,reopened.length,doc.uri.toString());assert.ok(wire.openIndex>closeIndex);assert.equal(doc.version,version);assert.equal(doc.getText(),source);assert.equal(wire.textHash,observed.sourceHash);assert.notEqual(sessionFor(doc),oldSession);const oldSynchronizationId=before[oldWire.openIndex].message.params.textDocument.synchronizationId,newSynchronizationId=reopened[wire.openIndex].message.params.textDocument.synchronizationId;assert.ok(typeof oldSynchronizationId==='string'&&oldSynchronizationId&&typeof newSynchronizationId==='string'&&newSynchronizationId);assert.notEqual(oldSynchronizationId,newSynchronizationId);lifecycle.reopen={beforeSynchronizationId:oldSynchronizationId,afterSynchronizationId:newSynchronizationId,beforeOpenRecord:before[oldWire.openIndex],beforeSession:oldSession,afterSession:sessionFor(doc),beforeWire:oldWire,closeIndex,closeRecord:closed[closeIndex],openIndex:wire.openIndex,openRecord:reopened[wire.openIndex],afterWire:wire};observed.resourceLifecycle=lifecycle;progress('source-reopened');
          const state=require('../src/process-state.cjs'),clients=[...api.service.clients.values()],children=clients.map(client=>({client,child:client.child,before:state.processState(client.child.pid),workers:[...client.ownedProcesses.values()]}));assert.ok(children.length,'actual current native language client required');const shutdownStart=events.length;
          for(const {child}of children)for(const event of ['exit','close'])child.once(event,()=>record('output.shutdown.'+event,{pid:child.pid,birth:child.processBirth}));
          localRetirementStarted=true;const pending=api.dispose();assert.equal(events.slice(shutdownStart).some(e=>e.kind==='output.dispose'&&e.data.channelId===channel[0].data.channelId),false,'channel remains pending retirement');assert.equal(api.dispose(),pending);await pending;assert.equal(api.dispose(),pending);
          observed.shutdown={ownerPid:process.pid,events:events.slice(shutdownStart),children:children.map(({client,child,before,workers})=>({pid:child.pid,birth:child.processBirth,before,confirmedClose:client.childClosureConfirmed,exitCode:child.exitCode,signalCode:child.signalCode,afterGroup:state.groupMembers(child),workers:workers.map(worker=>({pid:worker.pid,birth:worker.processBirth,afterGroup:state.groupMembers(worker)}))})),scope:'Actual local extension API retirement, physical child close and registered-worker group readback. Not paired upstream context shutdown or all unobserved descendant/kernel evidence.'};
          assert.equal(observed.shutdown.events.filter(e=>e.kind==='output.dispose'&&e.data.channelId===channel[0].data.channelId).length,1);for(const child of observed.shutdown.children){assert.ok(child.confirmedClose);assert.deepEqual(child.afterGroup,[]);for(const worker of child.workers)assert.deepEqual(worker.afterGroup,[]);}
        }
        return observed;
      });
    }else if(['trace-visibility','trace-light-show'].includes(config.suite)){
      await scenario(config.suite==='trace-light-show'?'native-trace-light-show-hide':'native-trace-tab-visibility-theme',async()=>{
        const tools=require('./trace-presentation.cjs'),records=()=>readFileSync(config.trace,'utf8').trim().split('\n').map(line=>JSON.parse(line));let doc=await open('trace-visibility',1,true);await verify(doc,1,'failed');
        const snapshot=()=>{assert.ok(!doc.isClosed&&vscode.workspace.textDocuments.includes(doc));assert.equal(vscode.window.activeTextEditor?.document,doc);const wire=tools.wireDocument(records(),records().length,doc.uri.toString());assert.equal(wire.version,doc.version);assert.equal(wire.textHash,tools.digest(doc.getText()));return{uri:doc.uri.toString(),version:doc.version,textHash:wire.textHash,protocolOpenIndex:wire.openIndex,session:sessionFor(doc)};};
        const capture=async(phase,trace,options)=>{const binding=snapshot(),reply=await require('./phase-capture.cjs').requestPhase(config.dir,config.runId,phase,{binding,trace,...options},timeout);assert.deepEqual(snapshot(),binding);return reply;};
        const show=async()=>{const start=records().length,binding=snapshot();await bounded(vscode.commands.executeCommand('dafny.showVerificationTrace'),'native visibility trace');assert.deepEqual(snapshot(),binding);const response=tools.traceResponse(records(),start,binding);record('trace.visibilityResponse',response);return response.result;};
        const workbench=vscode.workspace.getConfiguration('workbench',doc.uri),previousTheme=workbench.inspect('colorTheme')?.workspaceValue,observations={};
        try{
          if(config.suite==='trace-light-show'){await workbench.update('colorTheme','Default Light Modern',vscode.ConfigurationTarget.Workspace);const trace=await show();observations.lightExplicit=await capture('trace-light-explicit',trace,{shown:true,menu:'hide',theme:'vs',colors:{backgroundColor:'rgb(187, 222, 251)',color:'rgb(16, 32, 39)'}});await vscode.commands.executeCommand('dafny.hideVerificationTrace');observations.lightHidden=await capture('trace-light-explicit-hidden',[],{shown:false,menu:'show',theme:'vs'});return{status:'partial',observations,scope:'Independent actual show/hide under default light theme. Does not replace failed existing-trace theme continuity, document close, local producer or paired parity obligations.'};}
          let trace=await show();observations.shown=await capture('trace-visibility-shown',trace,{shown:true,menu:'hide'});await doc.save();const oldDoc=doc,old=snapshot(),start=records().length;await tools.closeSourceTabs(vscode,doc);assert.ok(!vscode.window.tabGroups.all.flatMap(g=>g.tabs).some(t=>t.input?.uri?.toString()===old.uri),'exact source tab absent');observations.afterTabClose={old,modelClosed:doc.isClosed,protocol:records().slice(start)};
          doc=await vscode.workspace.openTextDocument(doc.uri);await vscode.window.showTextDocument(doc,{preview:false});if(doc!==oldDoc)await until(()=>{try{return tools.wireDocument(records(),records().length,doc.uri.toString()).openIndex>old.protocolOpenIndex;}catch{return false;}},'actual new wire model when one exists');await verify(doc,1,'failed');observations.tabReopen={sameDocumentObject:doc===oldDoc,old,current:snapshot(),classification:doc===oldDoc?'cached live model tab reopen; NOT document close/reopen':'new document model'};observations.reopened=await capture('trace-tab-reopened',[],{observeOnly:true});
          await vscode.commands.executeCommand('dafny.hideVerificationTrace');trace=await show();await workbench.update('colorTheme','Default Light Modern',vscode.ConfigurationTarget.Workspace);observations.light=await capture('trace-light',trace,{shown:true,menu:'hide',theme:'vs',colors:{backgroundColor:'rgb(187, 222, 251)',color:'rgb(16, 32, 39)'}});await vscode.commands.executeCommand('dafny.hideVerificationTrace');observations.lightHidden=await capture('trace-light-hidden',[],{shown:false,menu:'show',theme:'vs'});
          return{status:'partial',observations,scope:'Actual default dark/light native presentation and tab visibility. Cached model tab reopening is not true document close/reopen or instance disposal; original close deadline failure remains retained.'};
        }finally{writeFileSync(join(config.dir,'trace-visibility-observations.json'),JSON.stringify(observations,null,2));await workbench.update('colorTheme',previousTheme,vscode.ConfigurationTarget.Workspace);if(!doc.isClosed){await vscode.window.showTextDocument(doc,{preview:false});await vscode.commands.executeCommand('dafny.hideVerificationTrace');}}
      });
    }else if(['commands','custom-commands','custom-default-commands','custom-import-actions'].includes(config.suite)){
      assert.ok(target==='local'||['custom-default-commands','custom-import-actions'].includes(config.suite),'paired source default-custom scenario only');
      let commandDocument;const importActions=config.suite==='custom-import-actions',custom=['custom-commands','custom-default-commands','custom-import-actions'].includes(config.suite),withImports=config.suite==='custom-commands'||importActions;
      await scenario(importActions?'command-custom-import-actions':withImports?'command-custom-build-keybinding':custom?'command-custom-default-build-keybinding':'command-build-keybinding',async()=>{
        if(target==='dafny'){
          const terminal=vscode.window.createTerminal({name:'Parity pinned SDK',cwd:config.workspace});observation.ownTerminal(terminal);terminal.show();await until(()=>terminal.shellIntegration,'real terminal shell integration');const start=events.length,probeCommand='command -v dotnet && dotnet --version && dotnet --list-runtimes';terminal.shellIntegration.executeCommand(probeCommand);let probeId;
          await until(()=>{const matches=events.slice(start).filter(e=>e.kind==='terminal.start'&&e.data.commandLine===probeCommand);assert.ok(matches.length<=1);probeId=matches[0]?.data.executionId;return probeId!==undefined&&events.some(e=>e.kind==='terminal.end'&&e.data.executionId===probeId)&&events.some(e=>e.kind==='terminal.output.end'&&e.data.executionId===probeId);},'native terminal SDK identity');const owned=events.slice(start).filter(e=>e.data?.executionId===probeId),output=owned.filter(e=>e.kind==='terminal.output').map(e=>e.data.data).join('');writeFileSync(join(config.dir,'terminal-sdk.txt'),output);assert.equal(owned.find(e=>e.kind==='terminal.end').data.exitCode,0);assert.ok(!owned.some(e=>e.kind==='terminal.output.error'));const identity=require('./core.cjs').terminalSdkIdentity(output,config.dotnetExecutable,config.dotnetVersion);result.observations.terminalSdk={...identity,executionId:probeId,output};
        }
        if(importActions)await vscode.commands.executeCommand('workbench.action.closePanel');
        let doc;if(importActions){const fixture=require('./workloads.cjs').customImportWorkload(target),path=file('commands');mkdirSync(require('node:path').dirname(join(config.workspace,fixture.path)),{recursive:true});writeFileSync(join(config.workspace,fixture.path),fixture.dependency);writeFileSync(path,fixture.source);doc=await vscode.workspace.openTextDocument(path);await vscode.window.showTextDocument(doc,{preview:false});if(target==='local'){const scoped=vscode.workspace.getConfiguration('solidityLean',doc.uri);await scoped.update('includePaths',['vendor with spaces'],vscode.ConfigurationTarget.WorkspaceFolder);await scoped.update('remappings',['alias/=lib/'],vscode.ConfigurationTarget.WorkspaceFolder);}}else doc=await open('commands',1);commandDocument=doc;if(withImports&&!importActions){mkdirSync(join(config.workspace,'vendor with spaces/lib'),{recursive:true});writeFileSync(join(config.workspace,'vendor with spaces/lib/Dependency.sol'),'pragma solidity ^0.8.34; contract Dependency {}');await replace(doc,doc.getText().replace('contract Parity {','import \"alias/Dependency.sol\";\ncontract Parity {'));}const lineEnding=new vscode.WorkspaceEdit();lineEnding.set(doc.uri,[vscode.TextEdit.setEndOfLine(vscode.EndOfLine.CRLF)]);assert.equal(await vscode.workspace.applyEdit(lineEnding),true);assert.equal(doc.eol,vscode.EndOfLine.CRLF);await replace(doc,doc.getText()+'\r\n// unsaved UTF16 edit 🦀\r\n');assert.equal(doc.isDirty,true,'keyboard build begins with unsaved source');let source=doc.getText(),version=doc.version;
        await vscode.commands.executeCommand('workbench.action.focusActiveEditorGroup');
        const fs=require('node:fs'),artifactSnapshot=()=>Object.fromEntries(fs.readdirSync(config.workspace,{recursive:true}).filter(name=>/\.(cs|csproj|dll)$/.test(name)&&fs.lstatSync(join(config.workspace,name)).isFile()).map(name=>[name,createHash('sha256').update(fs.readFileSync(join(config.workspace,name))).digest('hex')])),beforeArtifacts=target==='dafny'?artifactSnapshot():{},eventStart=events.length;
        if(importActions&&target==='local'){
          const cancelStart=events.length,requestId=require('node:crypto').randomUUID();
          keybindingRequest({runId:config.runId,requestId,cancel:true,uri:doc.uri.toString(),version,sourceHash:createHash('sha256').update(source).digest('hex')});
          await until(()=>existsSync(join(config.dir,'keybinding-reply.json')),'native cancellation renderer reply');
          const reply=JSON.parse(readFileSync(join(config.dir,'keybinding-reply.json'),'utf8'));assert.equal(reply.runId,config.runId);assert.equal(reply.requestId,requestId,reply.error);if(reply.error)throw Error(reply.error);
          assert.ok(reply.observation.prompt.cancelled?.rendered.screenshot,'actual cancelled prompt disappearance');assert.equal(reply.observation.prompt.before.value,JSON.stringify({includePaths:['vendor with spaces'],remappings:['alias/=lib/']}));assert.equal(reply.observation.prompt.submitted.value,reply.observation.prompt.before.value);
          await until(()=>events.slice(cancelStart).some(e=>e.kind==='command.end'&&e.data.id==='solidityLean.buildCustomArgs'),'actual cancelled command completion');
          const observed=events.slice(cancelStart);assert.ok(!observed.some(e=>e.kind==='error'),'cancelled local prompt has no error notice');const begin=observed.filter(e=>e.kind==='command.start'&&e.data.id==='solidityLean.buildCustomArgs'),end=observed.filter(e=>e.kind==='command.end'&&e.data.id==='solidityLean.buildCustomArgs');assert.equal(begin.length,1);assert.equal(end.length,1);assert.equal(begin[0].data.invocationId,end[0].data.invocationId);assert.equal(begin[0].data.source.uri,doc.uri.toString());assert.equal(begin[0].data.source.version,version);assert.equal(end[0].data.source.uri,doc.uri.toString());assert.equal(end[0].data.source.version,version);assert.equal(begin[0].data.source.textHash,createHash('sha256').update(source).digest('hex'));assert.equal(end[0].data.source.textHash,begin[0].data.source.textHash);assert.equal(begin[0].data.source.trusted,true);assert.ok(!doc.isClosed&&vscode.workspace.textDocuments.includes(doc));assert.equal(end[0].data.source.session,begin[0].data.source.session);assert.ok(!observed.some(e=>e.kind==='output'&&(()=>{try{return JSON.parse(e.data.text).kind==='source-command';}catch{return false;}})()),'cancelled prompt admits no source process');
          assert.equal(doc.version,version);assert.equal(doc.getText(),source);assert.equal(doc.isDirty,false);result.observations.customCancellation={source,request:reply,events:observed,uri:doc.uri.toString(),version,sourceHash:createHash('sha256').update(source).digest('hex'),trusted:vscode.workspace.isTrusted};unlinkSync(join(config.dir,'keybinding-reply.json'));
        }
        if(importActions){await replace(doc,doc.getText()+'// custom import build-stage edit 🦀\r\n');source=doc.getText();version=doc.version;assert.equal(doc.isDirty,true,'both accepted custom actions start with a new dirty source');}
        const requestId=require('node:crypto').randomUUID();
        keybindingRequest({runId:config.runId,requestId,uri:doc.uri.toString(),version,sourceHash:createHash('sha256').update(source).digest('hex'),customInput:custom&&target==='local'&&!importActions?JSON.stringify({includePaths:withImports?['vendor with spaces']:[],remappings:withImports?['alias/=lib/']:[]}):undefined});
        await until(()=>existsSync(join(config.dir,'keybinding-reply.json')),'renderer keybinding dispatch');
        const reply=JSON.parse(readFileSync(join(config.dir,'keybinding-reply.json'),'utf8'));assert.equal(reply.runId,config.runId);assert.equal(reply.requestId,requestId,reply.error);if(reply.error)throw Error(reply.error);assert.equal(reply.observation.focusedEditor,true);assert.ok(reply.observation.contextMenu.labels.some(label=>label.includes(target==='local'?'Build Compiler Artifact with Import Options':'Build with Custom Arguments')),'actual context submenu contains custom compiler action');
        if(target==='dafny'){
          assert.equal(reply.observation.chord,'f6');assert.equal(reply.observation.prompt.before.value,reply.observation.prompt.submitted.value,'upstream default custom arguments preserved');assert.match(reply.observation.prompt.submitted.value,/^build\b/);assert.ok(!reply.observation.prompt.submitted.value.includes('--no-verify'),'default build proof profile not weakened');
          assert.equal(doc.version,version);assert.equal(doc.getText(),source);assert.equal(doc.isDirty,false);assert.equal(readFileSync(doc.uri.fsPath,'utf8'),source);
          assert.ok(observation.terminalSupported,'native terminal integration required, no synthetic exit');
          const expectedSuffix=' '+reply.observation.prompt.submitted.value.split(' ').map(arg=>JSON.stringify(arg)).join(' ')+' '+JSON.stringify(doc.uri.fsPath),pinnedExecutableHash=createHash('sha256').update(readFileSync(config.dafnyExecutable)).digest('hex');
          const starts=()=>events.slice(eventStart).filter(e=>{if(e.kind!=='terminal.start')return false;const command=e.data.commandLine,match=/^"([^"]+)"(.*)$/.exec(command);return !!match&&match[2]===expectedSuffix&&fs.existsSync(match[1])&&createHash('sha256').update(readFileSync(match[1])).digest('hex')===pinnedExecutableHash;});let executionId;
          await until(()=>{const candidates=starts();assert.ok(candidates.length<=1,'ambiguous native build terminal execution');executionId=candidates[0]?.data.executionId;return executionId!==undefined&&events.some(e=>e.kind==='terminal.end'&&e.data.executionId===executionId)&&events.some(e=>e.kind==='terminal.output.end'&&e.data.executionId===executionId);},'same native Dafny build execution completion');
          const owned=events.slice(eventStart).filter(e=>e.data?.executionId===executionId),end=owned.find(e=>e.kind==='terminal.end'),output=owned.filter(e=>e.kind==='terminal.output').map(e=>e.data.data).join('');writeFileSync(join(config.dir,'compiler-terminal.txt'),output);assert.ok(!owned.some(e=>e.kind==='terminal.output.error'),'complete terminal output required');assert.equal(end.data.exitCode,0,'actual default Dafny custom Build exit');assert.ok(vscode.workspace.textDocuments.includes(doc),'same live document still owned');assert.equal(doc.version,version);assert.equal(doc.getText(),source);assert.equal(doc.isDirty,false);assert.equal(readFileSync(doc.uri.fsPath,'utf8'),source);const afterArtifacts=artifactSnapshot(),outputs=Object.entries(afterArtifacts).filter(([name,hash])=>beforeArtifacts[name]!==hash).map(([name,sha256])=>({path:name,bytes:fs.statSync(join(config.workspace,name)).size,sha256}));writeFileSync(join(config.dir,'compiler-artifacts.json'),JSON.stringify(outputs,null,2));assert.ok(outputs.length,'new or changed upstream compiler artifacts required');
          result.observations.commandScope='Actual Linux F6/default upstream prompt, save, real terminal execution and exit. External Dafny verification/compiler evidence, not Lean kernel or Solidity equivalence.';return{request:reply,version,source,terminal:end.data,scope:result.observations.commandScope};
        }
        let report,commandOwnership;
        await until(()=>{const packets=events.slice(eventStart).filter(e=>e.kind==='output').flatMap(event=>{try{return[JSON.parse(event.data.text)];}catch{return[];}}),operation=custom?'buildCustomArgs':'build',sourceHash=createHash('sha256').update(source).digest('hex'),starts=packets.filter(p=>p.kind==='source-command'&&p.phase==='started'&&p.operation===operation&&p.uri===doc.uri.toString()&&p.version===version&&p.sourceHash===sourceHash);assert.ok(starts.length<=1,'ambiguous source command ownership');const failure=starts[0]&&packets.find(p=>p.kind==='source-command'&&p.phase==='failed'&&p.commandId===starts[0].commandId&&p.sourceSession===starts[0].sourceSession&&p.uri===doc.uri.toString()&&p.version===version&&p.sourceHash===sourceHash);if(failure){assert.equal(doc.version,version);assert.equal(doc.getText(),source);writeFileSync(join(config.dir,'source-command-failure.json'),JSON.stringify(failure,null,2));throw Object.assign(Error(failure.message),{code:failure.code});}const completion=starts[0]&&packets.find(p=>p.kind==='source-command'&&p.phase==='completed'&&p.commandId===starts[0].commandId&&p.sourceSession===starts[0].sourceSession&&p.uri===doc.uri.toString()&&p.version===version&&p.sourceHash===sourceHash);if(!completion)return false;commandOwnership={started:starts[0],completed:completion};assert.equal(doc.version,version);assert.equal(doc.getText(),source);report=packets.find(p=>p.operation===operation&&p.source===doc.uri.fsPath&&p.sourceHash===sourceHash&&p.artifact===completion.artifact);return !!report;},'native compiler Build output after key dispatch');
        assert.ok(!doc.isClosed&&vscode.workspace.textDocuments.includes(doc)&&vscode.window.activeTextEditor?.document===doc,'same live source document owns compiler result');assert.equal(doc.version,version);assert.equal(doc.getText(),source);assert.equal(doc.isDirty,false,'Build saved the current buffer');assert.equal(readFileSync(doc.uri.fsPath,'utf8'),source);assert.equal(report.sourceHash,createHash('sha256').update(source).digest('hex'));assert.equal(report.kind,'compiler-ast');assert.equal(report.verification,'not-run');
        const artifact=JSON.parse(readFileSync(report.artifact,'utf8'));assert.ok(artifact.ast||artifact.sourceUnits,'actual compiler artifact has source AST');assert.equal(artifact.header?.sourceSha256??artifact.sourceUnits?.find(unit=>unit.name===artifact.header.mainSource)?.sourceSha256,report.sourceHash,'artifact header binds exact current source');if(custom){assert.equal(reply.observation.chord,'f6');assert.deepEqual(report.compilerOptions,{includePaths:withImports?['vendor with spaces']:[],remappings:withImports?['alias/=lib/']:[]});if(withImports)assert.equal(artifact.sourceUnits.length,2);if(importActions){const expected={'commands.sol':report.sourceHash,'lib/Dependency.sol':createHash('sha256').update(readFileSync(join(config.workspace,'vendor with spaces/lib/Dependency.sol'))).digest('hex')};assert.deepEqual(Object.fromEntries(artifact.sourceUnits.map(unit=>[unit.name,unit.sourceSha256])),expected,'exact admitted primary/dependency bytes');writeFileSync(join(config.dir,'compiler-source-binding.json'),JSON.stringify({units:expected,artifact:report.artifact,sha256:createHash('sha256').update(readFileSync(report.artifact)).digest('hex'),commandOwnership},null,2));assert.equal(reply.observation.prompt.before.value,JSON.stringify({includePaths:['vendor with spaces'],remappings:['alias/=lib/']}));assert.equal(reply.observation.prompt.submitted.value,reply.observation.prompt.before.value);result.observations.customImportScope={trusted:vscode.workspace.isTrusted,uri:doc.uri.toString(),version,sourceHash:report.sourceHash,compilerOptions:report.compilerOptions,verification:'not-run',upstreamCancellation:'unexamined'};}assert.ok(events.some(e=>e.kind==='output'&&e.data.text==='buildCustomArgs: '+doc.uri.fsPath),'actual custom handler, not ordinary Build');}writeFileSync(join(config.dir,'compiler.ast.json'),readFileSync(report.artifact));
        result.observations.commandScope='Actual Linux keyboard and real input prompt when custom -> registered compiler action -> source-bound native solc AST. Not kernel proof or macOS evidence.';
        return {request:reply,report,commandOwnership,version,source,scope:result.observations.commandScope};
      });
      if(target==='dafny'&&config.suite==='custom-default-commands')for(const operation of ['run','test'])await scenario('native-dafny-'+operation+'-action',async()=>{
        const doc=commandDocument;assert.ok(doc);const program=operation==='run'?'method Main() { print "parity-native-run\\n"; }\n':'method {:test} NativeTest() { expect 1 == 1; }\n';await replace(doc,program.replaceAll('\n','\r\n'));const version=doc.version,source=doc.getText(),start=events.length;assert.equal(doc.isDirty,true);await bounded(vscode.commands.executeCommand('dafny.'+operation),'actual upstream '+operation+' action');
        const expectedSuffix=' '+[operation,'--no-verify',doc.uri.fsPath].map(arg=>JSON.stringify(arg)).join(' '),pinned=createHash('sha256').update(readFileSync(config.dafnyExecutable)).digest('hex');let executionId;
        await until(()=>{const candidates=events.slice(start).filter(e=>{if(e.kind!=='terminal.start')return false;const match=/^"([^"]+)"(.*)$/.exec(e.data.commandLine);return !!match&&match[2]===expectedSuffix&&existsSync(match[1])&&createHash('sha256').update(readFileSync(match[1])).digest('hex')===pinned;});assert.ok(candidates.length<=1,'ambiguous native action execution');executionId=candidates[0]?.data.executionId;return executionId!==undefined&&events.some(e=>e.kind==='terminal.end'&&e.data.executionId===executionId)&&events.some(e=>e.kind==='terminal.output.end'&&e.data.executionId===executionId);},'native upstream '+operation+' output and exit');
        const owned=events.slice(start).filter(e=>e.data?.executionId===executionId),output=owned.filter(e=>e.kind==='terminal.output').map(e=>e.data.data).join(''),end=owned.find(e=>e.kind==='terminal.end');writeFileSync(join(config.dir,operation+'-terminal.txt'),output);assert.ok(!owned.some(e=>e.kind==='terminal.output.error'));assert.equal(end.data.exitCode,0);assert.ok(vscode.workspace.textDocuments.includes(doc));assert.equal(doc.version,version);assert.equal(doc.getText(),source);assert.equal(doc.isDirty,false);assert.equal(readFileSync(doc.uri.fsPath,'utf8'),source);const plain=require('node:util').stripVTControlCharacters(output);assert.ok(plain.includes(operation==='run'?'parity-native-run':'NativeTest: PASSED'),'authentic runtime/test output');return{version,sourceHash:createHash('sha256').update(source).digest('hex'),execution:end.data,output,scope:'Actual upstream registered action and default --no-verify arguments observed, not a locally selected profile or Lean/EVM equivalence; keyboard/macOS correspondence remains pending.'};
      });
      if(target==='dafny'&&config.suite==='custom-default-commands')await scenario('native-trace-show-copy-hide',async()=>{
        const doc=commandDocument;assert.ok(doc);await replace(doc,workload('dafny',1,true).replaceAll('\n','\r\n'));await verify(doc,1,'failed');const version=doc.version,text=doc.getText(),session=sessionFor(doc),binding={uri:doc.uri.toString(),version,textHash:createHash('sha256').update(text).digest('hex'),session};
        const stable=()=>{assert.ok(!doc.isClosed&&vscode.workspace.textDocuments.includes(doc));assert.equal(vscode.window.activeTextEditor?.document,doc);assert.equal(doc.version,version);assert.equal(doc.getText(),text);};
        const records=()=>readFileSync(config.trace,'utf8').trim().split('\n').map(line=>JSON.parse(line));
        binding.protocolOpenIndex=require('./trace-presentation.cjs').wireDocument(records(),records().length,binding.uri).openIndex;
        const responseAfter=start=>{stable();const response=require('./trace-presentation.cjs').traceResponse(records(),start,binding);record('trace.boundResponse',response);return response.result;};
        const capture=async(phase,trace)=>{stable();const value=await require('./phase-capture.cjs').requestPhase(config.dir,config.runId,phase,{binding,trace,shown:phase!=='trace-hidden',menu:phase==='trace-hidden'?'show':'hide'},timeout);stable();return value;};
        let start=records().length;await bounded(vscode.commands.executeCommand('dafny.showVerificationTrace'),'actual trace show');const shown=responseAfter(start);assert.ok(shown.some(item=>typeof item.assumption==='string'&&item.position?.line>=0),'nonempty positioned native trace required');const shownCapture=await capture('trace-shown',shown);
        const previousClipboard=await vscode.env.clipboard.readText();let copy,copyCapture;
        try{await vscode.env.clipboard.writeText('parity-'+config.runId);start=records().length;await bounded(vscode.commands.executeCommand('dafny.copyVerificationTrace'),'actual trace copy');copy=responseAfter(start);const expected=copy.map(item=>item.assumption).join('\n\n');assert.ok(expected);const deadline=Date.now()+timeout;let actual;do{actual=await vscode.env.clipboard.readText();if(actual===expected)break;if(Date.now()>=deadline)throw Object.assign(Error('Native trace clipboard did not match response'),{code:'TIMEOUT'});await new Promise(r=>setTimeout(r,20));}while(true);copyCapture=await capture('trace-copied',copy);}
        finally{await vscode.env.clipboard.writeText(previousClipboard);}
        await bounded(vscode.commands.executeCommand('dafny.hideVerificationTrace'),'actual trace hide');const hiddenCapture=await capture('trace-hidden',[]);
        return{status:'partial',version,shown,copy,shownCapture,copyCapture,hiddenCapture,clipboardRestored:true,scope:'Actual pinned Dafny counterexample producer/show/copy/hide and native pixels; no local positioned trace or kernel equivalence established.'};
      });
      if(target==='dafny'&&config.suite==='custom-default-commands')await scenario('native-trace-lifecycle',async()=>{
        const traceTools=require('./trace-presentation.cjs'),records=()=>readFileSync(config.trace,'utf8').trim().split('\n').map(line=>JSON.parse(line));
        const snapshot=doc=>{assert.ok(!doc.isClosed&&vscode.workspace.textDocuments.includes(doc));assert.equal(vscode.window.activeTextEditor?.document,doc);const result={uri:doc.uri.toString(),version:doc.version,textHash:traceTools.digest(doc.getText()),session:sessionFor(doc)};const wire=traceTools.wireDocument(records(),records().length,result.uri);assert.equal(wire.version,result.version);assert.equal(wire.textHash,result.textHash);result.protocolOpenIndex=wire.openIndex;return result;};
        const stable=(doc,binding)=>assert.deepEqual(snapshot(doc),binding,'same active document lifetime/source for entire observation');
        const capture=async(phase,doc,options)=>{const binding=snapshot(doc),reply=await require('./phase-capture.cjs').requestPhase(config.dir,config.runId,phase,{binding,...options},timeout);stable(doc,binding);return reply;};
        const resultFor=async(start,doc)=>{const binding=snapshot(doc);await until(()=>{const list=records(),requests=list.slice(start).filter(r=>r.direction==='client'&&r.message?.method==='dafny/counterExample'&&r.message.params?.textDocument?.uri===binding.uri);return requests.some(request=>list.some(r=>r.direction==='server'&&r.message?.id===request.message.id&&Array.isArray(r.message.result)));},'native lifecycle trace reply');stable(doc,binding);const value=traceTools.traceResponse(records(),start,binding);const bodyLine=doc.getText().split('\n').findIndex(line=>line.includes('{ r := 1; }'));assert.ok(bodyLine>=0);assert.ok(value.result.length&&value.result.every(item=>item.position.line===bodyLine),'trace positions match unchanged semantic workload body');record('trace.lifecycleResponse',value);return value;};
        const show=async doc=>{const start=records().length;await bounded(vscode.commands.executeCommand('dafny.showVerificationTrace'),'actual lifecycle show');return resultFor(start,doc);};
        let doc=commandDocument,other;assert.ok(doc);const observations={};
        const configuration=vscode.workspace.getConfiguration('dafny',doc.uri),previousColor=configuration.inspect('colorVerificationTrace')?.workspaceValue;
        try{
          let value=await show(doc);observations.initial=await capture('trace-lifecycle-shown',doc,{trace:value.result,shown:true,menu:'hide'});
          await replace(doc,'// trace edit 🦀\r\n'+doc.getText());await verify(doc,1,'failed');await until(()=>{try{return traceTools.wireDocument(records(),records().length,doc.uri.toString()).version===doc.version;}catch{return false;}},'edited wire source');const list=records(),editIndex=list.findLastIndex(r=>r.direction==='client'&&r.message?.method==='textDocument/didChange'&&r.message.params.textDocument.uri===doc.uri.toString()&&r.message.params.textDocument.version===doc.version);value=await resultFor(editIndex+1,doc);observations.edited=await capture('trace-edited',doc,{trace:value.result,shown:true,menu:'hide'});
          other=await open('trace-other',1);await verify(other,1,'proved');observations.switched=await capture('trace-switched',other,{trace:[],shown:false});
          const start=records().length;await vscode.window.showTextDocument(doc,{preview:false});value=await resultFor(start,doc);observations.returned=await capture('trace-returned',doc,{trace:value.result,shown:true,menu:'hide'});
          await configuration.update('colorVerificationTrace',{backgroundColor:'#224466',fontColor:'#ddeeff'},vscode.ConfigurationTarget.Workspace);await vscode.commands.executeCommand('dafny.hideVerificationTrace');value=await show(doc);observations.customColor=await capture('trace-custom-color',doc,{trace:value.result,shown:true,menu:'hide',colors:{backgroundColor:'rgb(34, 68, 102)',color:'rgb(221, 238, 255)'}});
          const raceStart=records().length,pending=vscode.commands.executeCommand('dafny.showVerificationTrace');await vscode.commands.executeCommand('dafny.hideVerificationTrace');await bounded(pending,'in-flight show after hide');value=await resultFor(raceStart,doc);observations.hideInFlight=await capture('trace-hide-inflight',doc,{observeOnly:true});observations.hideInFlight.annotationsReappeared=observations.hideInFlight.capture.tracePresentation.annotations.some(a=>a.uri===doc.uri.toString());observations.hideInFlight.cancellations=records().slice(raceStart).filter(r=>r.direction==='client'&&r.message?.method==='$/cancelRequest'&&r.message.params.id===value.requestId);
          await vscode.commands.executeCommand('dafny.hideVerificationTrace');observations.cleanup=await capture('trace-cleanup',doc,{trace:[],shown:false,menu:'show'});
          await configuration.update('colorVerificationTrace',previousColor,vscode.ConfigurationTarget.Workspace);value=await show(doc);observations.beforeClose=await capture('trace-beforeclose',doc,{trace:value.result,shown:true,menu:'hide'});await doc.save();const old=snapshot(doc);await traceTools.closeSourceTabs(vscode,doc);await until(()=>doc.isClosed,'old trace source closed');const reopened=await vscode.workspace.openTextDocument(doc.uri);await vscode.window.showTextDocument(reopened,{preview:false});await verify(reopened,1,'failed');await until(()=>{try{const wire=traceTools.wireDocument(records(),records().length,reopened.uri.toString());return wire.openIndex>old.protocolOpenIndex&&wire.version===reopened.version&&wire.textHash===traceTools.digest(reopened.getText());}catch{return false;}},'new wire open lifetime');const fresh=snapshot(reopened);assert.notEqual(old.session,fresh.session);assert.notEqual(old.protocolOpenIndex,fresh.protocolOpenIndex);observations.reopenedBeforeAction=await capture('trace-reopened-observed',reopened,{observeOnly:true});doc=reopened;
          await vscode.commands.executeCommand('dafny.hideVerificationTrace');value=await show(doc);observations.reopened=await capture('trace-reopened-shown',doc,{trace:value.result,shown:true,menu:'hide'});await vscode.commands.executeCommand('dafny.hideVerificationTrace');observations.reopenedHidden=await capture('trace-reopened-hidden',doc,{trace:[],shown:false,menu:'show'});
          const closeStart=records().length,closing=snapshot(doc),closingShow=vscode.commands.executeCommand('dafny.showVerificationTrace');await doc.save();await traceTools.closeSourceTabs(vscode,doc);await until(()=>doc.isClosed,'in-flight trace source close');await bounded(closingShow,'show settling after source close');await vscode.window.showTextDocument(other,{preview:false});observations.closeInFlight=await capture('trace-close-inflight',other,{observeOnly:true});await until(()=>records().slice(closeStart).some(r=>r.direction==='client'&&r.message?.method==='textDocument/didClose'&&r.message.params.textDocument.uri===closing.uri),'wire close barrier');try{const historical=traceTools.traceResponse(records(),closeStart,closing);observations.closeInFlight.stableIntervalAccepted=true;observations.closeInFlight.historicalInterval=historical;}catch(error){observations.closeInFlight.stableIntervalAccepted=false;observations.closeInFlight.authorityRejection=error.message;}observations.closeInFlight.protocol=records().slice(closeStart);observations.closeInFlight.currentAuthority=!doc.isClosed&&vscode.workspace.textDocuments.includes(doc);assert.equal(observations.closeInFlight.currentAuthority,false,'closed source never receives current authority; historical response may have won the race');
          return{status:'partial',observations,scope:'Native pinned lifecycle observations, including upstream race/menu state; observeOnly phases are recorded, not claimed successful suppression. No local positioned producer, rendered parity, native macOS or extension-decoration disposal proof.'};
        }finally{writeFileSync(join(config.dir,'trace-lifecycle-observations.json'),JSON.stringify(observations,null,2));await configuration.update('colorVerificationTrace',previousColor,vscode.ConfigurationTarget.Workspace);if(!doc.isClosed){await vscode.window.showTextDocument(doc,{preview:false});await vscode.commands.executeCommand('dafny.hideVerificationTrace');}if(other&&!other.isClosed){await vscode.window.showTextDocument(other,{preview:false});await other.save();await vscode.commands.executeCommand('workbench.action.closeActiveEditor');}}
      });
    }else if(['proof-help','proof-hover'].includes(config.suite)){
      await scenario('native-certified-proof-help',async()=>{
        assert.equal(target,'local');assert.ok(api.service,'actual production language service required');
        const checks=require('./proof-help.cjs'),tools=require('./trace-presentation.cjs'),capture=require('./phase-capture.cjs'),fs=require('node:fs');
        localStatus=p=>{states.set(p.uri,p);record('localStatus',p);};api.service.on('status',localStatus);
        const doc=await open('proof-help',1,true),records=()=>readFileSync(config.trace,'utf8').trim().split('\n').filter(Boolean).map(line=>JSON.parse(line));
        const binding=()=>{const rows=records(),wire=tools.wireDocument(rows,rows.length,doc.uri.toString());wire.synchronizationId=rows[wire.openIndex].message.params.textDocument.synchronizationId;return checks.sourceBinding(doc,sessionFor(doc),wire);};
        const before=await bounded(checks.synchronizedBinding(api.service,doc,binding),'production document synchronization'),observations={initiator:'Explicit existing production LSP certify:true request; ordinary product verification defaults unchanged',menuInitiator:'Registered solidityLean.openStatusBarMenu command via API; native picker selection via CDP keyboard',before};
        const save=()=>writeFileSync(join(config.dir,'proof-help-observations.json'),JSON.stringify(observations,null,2));save();
        const verificationStart=records().length;let proofDone=false;
        const proof=bounded(api.service.request('solidityLean/verify',doc,{options:{certify:true,counterexamples:true,function:'f0()'}}),'actual certified refutation').finally(()=>{proofDone=true;});proof.catch(()=>{});
        await until(()=>!proofDone&&current(doc)?.state==='running','actual in-flight verification request');checks.sameSource(before,binding());
        const expectedHover=checks.proofHoverExpected(doc.getText()),hoverPosition=new vscode.Position(expectedHover.position.line,expectedHover.position.character),nativeHovers=await bounded(vscode.commands.executeCommand('vscode.executeHoverProvider',doc.uri,hoverPosition),'native provider hover during genuine verification');
        assert.equal(proofDone,false,'native hover returned before verification response');checks.sameSource(before,binding());assert.equal(nativeHovers.length,1,'one actual registered provider');const hover=nativeHovers[0];assert.equal(hover.contents.length,1);assert.equal(typeof hover.contents[0].value,'string');assert.ok(hover.range);const point=p=>({line:p.line,character:p.character}),hoverValue={contents:{kind:'markdown',value:hover.contents[0].value},range:{start:point(hover.range.start),end:point(hover.range.end)}};
        require('./workloads.cjs').assertHoverObservation(hoverValue,expectedHover);observations.hoverDuringVerification={binding:before,position:expectedHover.position,expected:expectedHover,value:hoverValue,initiator:'Actual vscode.executeHoverProvider through the registered production provider; no injected verifier or delay'};save();
        if(config.suite==='proof-hover'){
          assert.equal(proofDone,false,'verification request still pending before native popup');assert.equal(current(doc)?.state,'running');checks.sameSource(before,binding());const editor=vscode.window.activeTextEditor;assert.equal(editor?.document,doc);editor.selection=new vscode.Selection(hoverPosition,hoverPosition);
          await bounded(vscode.commands.executeCommand('editor.action.showHover'),'actual native hover popup command');observations.hoverPopupAttempt={command:'editor.action.showHover',binding:binding(),position:expectedHover.position,at:Date.now()};save();
          let popupReply;await until(()=>{const rows=records(),requests=rows.filter(r=>r.direction==='client'&&r.message?.method==='textDocument/hover'&&r.message.params?.textDocument?.uri===before.uri&&r.message.params.position?.line===expectedHover.position.line&&r.message.params.position?.character===expectedHover.position.character);assert.ok(requests.length<=2,'only API and popup hover requests');const request=requests[1];if(!request)return false;popupReply=rows.find(r=>r.direction==='server'&&r.message?.id===request.message.id&&(Object.hasOwn(r.message,'result')||Object.hasOwn(r.message,'error')));if(popupReply?.message.error)throw Error('Native popup hover failed: '+JSON.stringify(popupReply.message.error));return !!popupReply;},'actual native popup hover reply');assert.deepEqual(popupReply.message.result,hoverValue);observations.hoverPopupReply=popupReply;save();
          observations.hoverPopup=await capture.requestPhase(config.dir,config.runId,'proof-help-hover',{action:'hover',binding:before,expectedHover,status:current(doc)},timeout);checks.sameSource(before,binding());assert.equal(proofDone,false,'popup observation precedes verification response');assert.equal(current(doc)?.state,'running');save();
        }
        const report=await proof;observations.hoverDuringVerification.wire=checks[config.suite==='proof-hover'?'verificationPopupOrder':'verificationHoverOrder'](records(),verificationStart,before,expectedHover.position,hoverValue,report);save();
        checks.sameSource(before,binding());checks.assertCertifiedFailureObservation(report,before,doc.uri.fsPath);observations.report=report;save();
        await until(()=>checks.currentFailureStatus(current(doc),before,report.results[0]),'current native failed function status');
        await until(()=>api.reports.get(doc.uri.toString())?.results?.some(row=>row.status==='refuted'&&row.counterexample?.certified===true),'accepted current certified report');
        observations.status=current(doc);observations.actions=[];save();
        for(const [choice,label,fileName]of [['guide','Help with a proof','calculus.md'],['index','Proof documentation index','README.md']]){
          await vscode.window.showTextDocument(doc,{preview:false});const owner=binding();checks.sameSource(before,owner);
          let completed=false;const pending=bounded(vscode.commands.executeCommand('solidityLean.openStatusBarMenu'),'owned native proof-help menu').finally(()=>{completed=true;});pending.catch(()=>{});
          try{
            const menu=await capture.requestPhase(config.dir,config.runId,'proof-help-menu-'+choice,{action:'menu',binding:owner,label,status:current(doc)},timeout);
            await pending;checks.sameSource(owner,binding());const destination=vscode.window.activeTextEditor?.document,expected=fs.realpathSync(join(config.backendPath,'docs',fileName));
            // Resolve the recorded actual backend repository, never a guessed documentation URL.
            assert.ok(destination&&!destination.isClosed);assert.equal(destination.uri.fsPath,expected);const destinationHash=createHash('sha256').update(destination.getText()).digest('hex');assert.equal(destinationHash,createHash('sha256').update(readFileSync(expected)).digest('hex'));
            const targetBinding={uri:destination.uri.toString(),version:destination.version,textHash:destinationHash,path:expected};
            const document=await capture.requestPhase(config.dir,config.runId,'proof-help-'+choice,{action:'document',binding:owner,destination:targetBinding},timeout);
            checks.sameSource(owner,binding());assert.equal(vscode.window.activeTextEditor?.document,destination);assert.equal(createHash('sha256').update(destination.getText()).digest('hex'),targetBinding.textHash);
            observations.actions.push({choice,label,source:owner,destination:targetBinding,menu,document});save();
          }finally{if(!completed)await vscode.commands.executeCommand('workbench.action.closeQuickOpen');await pending.catch(()=>{});}
        }
        return {status:'partial',observations,scope:'Actual Linux certified service response and native VS Code picker/document rendering. Not default automatic kernel verification, paired Dafny/macOS, failed-clause metadata, EVM or complete parity.'};
      });
    }else if(visual){
      const {requestPhase,phaseObserved}=require('./phase-capture.cjs');
      const localStates=new Map();
      if(target==='local'){
        assert.ok(api.service,'Visual lifecycle needs the real persistent service');
        localStatus=p=>{localStates.set(p.uri,p);record('localStatus',p);};api.service.on('status',localStatus);
      }
      let visualDoc;
      const native=()=>{const s=target==='local'?localStates.get(visualDoc.uri.toString()):current(visualDoc);return s?.version===visualDoc.version?s:null;};
      const capture=async phase=>{
        const before=native(),version=visualDoc.version,source=visualDoc.getText();
        // Request overview pixels before awaiting a language provider: provider latency can miss early phases.
        const value=await requestPhase(config.dir,config.runId,phase,{state:snapshot(visualDoc),source,uri:visualDoc.uri.toString(),nativeBefore:before},timeout);
        const after=native();assert.equal(visualDoc.version,version,'capture source version stable');assert.equal(visualDoc.getText(),source,'capture source text stable');
        const observed=phaseObserved(phase,before,after);
        const observation={status:observed?'partial':'missing',capture:value,nativeBefore:before,nativeAfter:after,phaseObserved:observed,
          scope:observed?'Native state brackets this capture; actual visible differences still require independent inspection.':'Requested early phase was missed or ambiguous; this image is not evidence for that phase.'};
        if(['verified','proof-broken','proof-fixed'].includes(phase)){
          const pos=symbolPosition(target,source),editor=vscode.window.activeTextEditor;
          assert.equal(editor?.document,visualDoc,'hover capture uses the same active file');editor.selection=new vscode.Selection(pos.line,pos.character,pos.line,pos.character);
          const hover=await vscode.commands.executeCommand('vscode.executeHoverProvider',visualDoc.uri,new vscode.Position(pos.line,pos.character));
          await vscode.commands.executeCommand('editor.action.showHover');
          const hoverCapture=await requestPhase(config.dir,config.runId,phase+'-hover',{version,source,uri:visualDoc.uri.toString(),hover},timeout);
          observation.hover={status:hoverCapture.capture.hoverCount>0?'partial':'missing',capture:hoverCapture,provider:hover,
            scope:'Only a rendered visible hover widget can evidence appearance; provider data alone cannot.'};
          const hide=(await vscode.commands.getCommands(true)).find(c=>c==='hideHover'||c==='editor.action.hideHover');if(hide)await vscode.commands.executeCommand(hide);
          assert.equal(visualDoc.version,version,'hover source version stable');assert.equal(visualDoc.getText(),source,'hover source text stable');
        }
        writeFileSync(join(config.dir,'phases',phase,'observation.json'),JSON.stringify(observation,null,2));return observation;
      };
      const automatic=async(expected,count)=>{
        await until(()=>target==='local'?
          localStates.get(visualDoc.uri.toString())?.version===visualDoc.version&&localStates.get(visualDoc.uri.toString())?.state==='complete'&&api.reports.has(visualDoc.uri.toString()):
          current(visualDoc)?.namedVerifiables?.length===count&&current(visualDoc).namedVerifiables.every(s=>s.status>=4),'automatic current-version verification');
        const report=target==='local'?api.reports.get(visualDoc.uri.toString()):current(visualDoc);verificationOutcomes(target,report,count,expected);
      };
      await scenario('visual-open',async()=>{visualDoc=await open('visual',config.obligations);return capture('open');});
      await scenario('visual-first-feedback',async()=>{
        await until(()=>target==='local'?localStates.get(visualDoc.uri.toString())?.version===visualDoc.version:!!current(visualDoc),'first native status feedback');return capture('first-feedback');
      });
      await scenario('visual-verified',async()=>{await automatic('proved',config.obligations);return capture('verified');});
      await scenario('visual-proof-broken',async()=>{await replace(visualDoc,workload(target,config.obligations+1,true));await automatic('failed',config.obligations+1);return capture('proof-broken');});
      await scenario('visual-proof-fixed',async()=>{await replace(visualDoc,workload(target,config.obligations+2));await automatic('proved',config.obligations+2);return capture('proof-fixed');});
    }else{
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
    if(target==='local'&&api.service){
      const client=await api.service.open(doc);result.observations.serverCapabilities=client.capabilities;
      await scenario('warm-snapshot-cache',async()=>{
        const before=await client.peer.request('solidityLean/stats',{}),start=performance.now();
        const cached=await api.verify(doc);metrics.warmVerificationMs=performance.now()-start;
        const after=await client.peer.request('solidityLean/stats',{});
        assert.ok(after.cacheHits>before.cacheHits,'unchanged snapshot reuses checked proof results');
        return {workerPid:cached.backend?.workerPid,leanServerPid:cached.backend?.leanServerPid,cacheHits:after.cacheHits};
      });
    }
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
        return {status:id==='hover'?'passed':target==='local'&&!api.service?'missing':'unexamined',present,value,
          scope:id==='hover'?'verified declaration hover':'Discovery probe at declaration; dedicated trigger/call-site tests are required.'};
      });
    }
    if(config.suite==='full')await scenario('symbols-and-formatting',async()=>{
      const symbols=await vscode.commands.executeCommand('vscode.executeDocumentSymbolProvider',doc.uri);
      const names=[];const visit=rows=>{for(const s of rows||[]){names.push(s.name);visit(s.children);}};visit(symbols);
      assert.ok(names.some(n=>n.includes('f0')),'function document symbol');
      const formatting=await vscode.commands.executeCommand('vscode.executeFormatDocumentProvider',doc.uri,{tabSize:2,insertSpaces:true});
      assert.ok(Array.isArray(formatting),'formatter response (already formatted input may have no edits)');
      return {status:'partial',symbols,formatting,scope:'Document symbols and formatter invocation; formatting edit semantics need dedicated fixtures.'};
    });
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
      if(api.service){
        const disk=readFileSync(doc.uri.fsPath,'utf8');
        await verify(doc,config.obligations+2);assert.equal(snapshot(doc).diagnostics.length,0);
        assert.equal(readFileSync(doc.uri.fsPath,'utf8'),disk,'in-memory verification must not overwrite the saved source');
        return {state:snapshot(doc),inMemory:true};
      }
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
      await replace(doc,workload(target,config.obligations,true));await verify(doc,config.obligations,'failed');
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
      assert.ok(rows.some(r=>r.status==='refuted'&&r.counterexample),'counterexample evidence');
      return {status:'partial',rows:rows.map(r=>({function:r.function,status:r.status,counterexample:r.counterexample})),scope:'Model prestate, without a positioned trace. Certificate presence is retained per row.'};
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
      if(target==='local'&&!api.service) return {status:'missing',reason:'CLI backend has no restart command or persistent LSP server'};
      const start=performance.now();await vscode.commands.executeCommand(target==='local'?'solidityLean.restartServer':'dafny.restartServer');
      metrics.restartMs=performance.now()-start;
      const restarted=await open('restarted',1);await verify(restarted,1);return snapshot(restarted);
    });
    if(config.suite==='full')await scenario('language-services-callsite',async()=>{
      const fixture=servicesWorkload(target);
      const project=join(config.workspace,'language-services-project');mkdirSync(project,{recursive:true});
      if(target==='dafny')writeFileSync(join(project,'dfyconfig.toml'),'includes = ["*.dfy"]\n');
      const path=join(project,'language-services'+(target==='dafny'?'.dfy':'.sol'));
      writeFileSync(path,fixture.text);const languageDoc=await vscode.workspace.openTextDocument(path);
      await vscode.window.showTextDocument(languageDoc,{preview:false});
      const definition=await request('vscode.executeDefinitionProvider',languageDoc,fixture.call,[]);
      assertServiceResponse('definition',fixture,languageDoc.uri.toString(),definition.value);
      const references=await request('vscode.executeReferenceProvider',languageDoc,fixture.call,[]);
      assertServiceResponse('references',fixture,languageDoc.uri.toString(),references.value);
      const signature=await request('vscode.executeSignatureHelpProvider',languageDoc,fixture.signature,[]);
      assert.match(signature.value?.signatures?.[0]?.label||'',/helper/);
      const secondParameter=await request('vscode.executeSignatureHelpProvider',languageDoc,fixture.signatureSecond,[]);
      const point=new vscode.Position(fixture.call.line,fixture.call.character);
      const rename=await vscode.commands.executeCommand('vscode.executeDocumentRenameProvider',languageDoc.uri,point,'renamed');
      assertServiceResponse('rename',fixture,languageDoc.uri.toString(),{changes:{[languageDoc.uri.toString()]:rename?.get(languageDoc.uri)||[]}});
      let completion;
      const completionEdit=new vscode.WorkspaceEdit();completionEdit.insert(languageDoc.uri,new vscode.Position(fixture.completionInsertion.line,fixture.completionInsertion.character),' + this.');
      assert.equal(await vscode.workspace.applyEdit(completionEdit),true);
      try{
        completion=await request('vscode.executeCompletionItemProvider',languageDoc,fixture.completion,['.']);
        assert.ok(completion.value?.items.some(i=>(typeof i.label==='string'?i.label:i.label.label)==='helper'),'member completion on incomplete receiver');
        metrics.completionMs=completion.elapsedMs;
      }finally{await replace(languageDoc,fixture.text);}

      return {status:'partial',definitions:definition.value,references:references.value,completionLabels:completion.value.items.map(i=>i.label),signature:signature.value,secondParameter:secondParameter.value,renameEdits:rename.get(languageDoc.uri),
        scope:'Paired real call-site APIs; additional language-specific behavior remains unexamined.'};
    });
    }
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
    if(localStatus)api.service.removeListener('status',localStatus);
    clearInterval(timer);observation.restore();result.elapsedMs=performance.now()-started;
    writeFileSync(config.result,JSON.stringify(result,null,2));
    if(target==='local'&&!localRetirementStarted) api?.cancel();
    const captureStart=performance.now();
    while(!existsSync(join(config.dir,'renderer-done'))&&performance.now()-captureStart<15000)
      await new Promise(resolve=>setTimeout(resolve,50));
  }
  // The launcher validates fresh structured evidence and retains failed scenarios.
}
module.exports = {run};
