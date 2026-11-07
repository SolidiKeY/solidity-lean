#!/usr/bin/env node
'use strict';
// Real server comparisons for machines without an Electron display. This does
// not substitute for the extension-host/renderer suite in run.cjs.
const assert=require('node:assert/strict');
const fs=require('node:fs');
const {resolve,join}=require('node:path');
const {tmpdir,cpus}=require('node:os');
const {pathToFileURL}=require('node:url');
const {spawn,spawnSync}=require('node:child_process');
const {randomUUID,createHash}=require('node:crypto');
const {performance}=require('node:perf_hooks');
const {RpcPeer}=require('../src/rpc.cjs');
const {terminateTree}=require('../src/backend.cjs');
const {processState,groupMembers,running}=require('../src/process-state.cjs');
const {waitForGroup}=require('../src/child-lifetime.cjs');
const {ProcessSampler,summarize,scaling,normalize,differences,protocol}=require('./core.cjs');
const {activity}=require('./analyze.cjs');
const {workload,servicesWorkload,verificationOutcomes,assertServiceResponse,assertServiceSymbols}=require('./workloads.cjs');
const repo=resolve(__dirname,'../..');

function parse(args) {
  const o={targets:['dafny','local'],workers:[1,2,4],trials:5,warmups:1,scope:'services',timeoutMs:60000,obligations:8,memoryReserveMiB:12288,memoryMaxMiB:4096};
  const keys={'--dafny':'dafny','--output':'output','--targets':'targets','--workers':'workers','--trials':'trials','--warmups':'warmups','--scope':'scope','--timeout-ms':'timeoutMs','--obligations':'obligations','--memory-reserve-mib':'memoryReserveMiB','--memory-max-mib':'memoryMaxMiB'};
  for(let i=0;i<args.length;i++){
    if(args[i]==='--help')return {help:true};
    const k=keys[args[i]],v=args[++i];if(!k||!v||v.startsWith('--'))throw new Error('Invalid option '+args[i-1]);
    o[k]=['targets','workers'].includes(k)?v.split(',').map(x=>k==='workers'?Number(x):x):['trials','warmups','timeoutMs','obligations','memoryReserveMiB','memoryMaxMiB'].includes(k)?Number(v):v;
  }
  if(!['services','full'].includes(o.scope))throw new Error('Invalid scope');
  for(const k of ['trials','warmups','timeoutMs','obligations','memoryReserveMiB','memoryMaxMiB'])if(!Number.isSafeInteger(o[k])||o[k]<(k==='warmups'?0:1))throw new Error('Invalid '+k);
  if(o.trials>100||o.warmups>10||o.obligations>1000||o.timeoutMs>3600000)throw new Error('Excessive dimensions');
  for(const k of ['workers','targets'])if(new Set(o[k]).size!==o[k].length)throw new Error('Duplicate '+k);
  if(o.targets.some(t=>!['dafny','local'].includes(t))||o.workers.some(w=>!Number.isSafeInteger(w)||w<1||w>(o.targets.includes('local')?4:32)))throw new Error('Invalid target/workers');
  if(!o.output||o.targets.includes('dafny')&&!o.dafny)throw new Error('Use --output DIR and --dafny PATH (unless --targets local)');
  return o;
}

async function trial(target,workers,options,dir) {
  fs.mkdirSync(dir,{recursive:true});
  const workspace=join(dir,'workspace');fs.mkdirSync(workspace);
  if(target==='dafny'){fs.mkdirSync(join(workspace,'services-project'));fs.writeFileSync(join(workspace,'services-project','dfyconfig.toml'),'includes = ["*.dfy"]\n');}
  const trace=join(dir,'lsp.jsonl'),events=[],scenarios=[],metrics={},states=new Map(),diagnostics=new Map();
  const begin=performance.now(),runId=randomUUID();
  const command=target==='dafny'?resolve(options.dafny):process.execPath;
  const args=target==='dafny'?['server','--verify-on','Never','--cores',String(workers),'--cache-verification','0','--verification-time-limit','20']:[join(repo,'vscode/src/lsp-server.cjs')];
  fs.writeFileSync(join(dir,'config.json'),JSON.stringify({runId,target,workers,...options,command,args,workspace,
    runtimeEnvironment:Object.fromEntries(['LEAN_NUM_THREADS','SOLKEY_ROOT'].filter(k=>process.env[k]!==undefined).map(k=>[k,process.env[k]]))},null,2));
  const child=spawn(command,args,{cwd:repo,detached:process.platform!=='win32',stdio:['pipe','pipe','pipe']});
  child.ownedGroup=process.platform!=='win32';child.processBirth=processState(child.pid)?.birth;
  const ownedGroups=new Map(),sampler=new ProcessSampler(child.pid),peer=new RpcPeer(child.stdout,child.stdin);
  const log=fs.openSync(join(dir,'server.log'),'w');child.stderr.on('data',b=>fs.writeSync(log,b));
  let exited=false,resourceStop=false,exitCode,exitSignal,forcedShutdown=false,shutdownAcknowledged=false;
  const closed=new Promise(resolve=>child.once('close',(code,signal)=>{exited=true;exitCode=code;exitSignal=signal;resolve();}));
  child.once('error',e=>peer.close(e));child.once('exit',(code,signal)=>peer.close(new Error(`Server exited ${code??signal}`)));
  const append=r=>fs.appendFileSync(trace,JSON.stringify({time:Date.now(),...r})+'\n');
  const write=peer.write.bind(peer);peer.write=m=>{append({direction:'client',message:m});return write(m);};
  const receive=peer.receive.bind(peer);peer.receive=m=>{append({direction:'server',message:m});return receive(m);};
  peer.on('close',error=>{try{peer.frames.end();append({direction:'server',framingFinalized:true});}catch(e){append({direction:'server',error:e.message});}});
  const record=(kind,data)=>events.push({ms:performance.now()-begin,kind,data});
  for(const method of ['dafny/textDocument/symbolStatus','solidityLean/status','solidityLean/report','textDocument/publishDiagnostics','dafny/compilation/status'])
    peer.onNotification(method,p=>{record(method,p);if(method.includes('symbolStatus'))states.set(p.uri,p);if(method==='textDocument/publishDiagnostics')diagnostics.set(p.uri,p);});
  if(target==='local')peer.onRequest('solidityLean/registerOwnedProcess',params=>{const owned=require('../src/process-state.cjs').ownedProcess(params,child);ownedGroups.set(owned.pid,owned);sampler.seen.set(owned.pid,owned.processBirth);record('owned-process-registration',{...params});return true;});
  if(target==='local')peer.onNotification('solidityLean/ownedProcess',params=>{const owned=ownedGroups.get(params.pid);if(params.event==='closed'&&owned?.processBirth===params.birth&&!groupMembers(owned).some(running))ownedGroups.delete(params.pid);});
  peer.onRequest('workspace/configuration',p=>p.items.map(()=>null));
  peer.onRequest('client/registerCapability',()=>null);peer.onRequest('window/workDoneProgress/create',()=>null);
  const request=(method,params)=>peer.request(method,params,{timeoutMs:options.timeoutMs});
  const until=async(predicate,label)=>{
    const start=performance.now();while(!predicate()){
      if(peer.closed)throw new Error('Server closed during '+label);
      if(performance.now()-start>options.timeoutMs)throw Object.assign(new Error('Timed out: '+label),{code:'TIMEOUT'});
      await new Promise(r=>setTimeout(r,10));
    }
  };
  const scenario=async(id,fn)=>{
    record('scenario.start',{id});const start=performance.now();
    try{const observation=await fn();scenarios.push({id,status:observation?.status||'passed',elapsedMs:performance.now()-start,observation});}
    catch(e){scenarios.push({id,status:e.code===-32601?'missing':e.code==='TIMEOUT'||/timed out/i.test(e.message)?'timeout':'broken',elapsedMs:performance.now()-start,error:e.stack});}
    record('scenario.end',{id});
  };
  const open=(name,text)=>{
    const path=join(workspace,...(target==='dafny'&&name==='services'?['services-project']:[]),name+(target==='dafny'?'.dfy':'.sol')),uri=pathToFileURL(path).href;
    fs.writeFileSync(path,text);const doc={uri,text,version:1};
    peer.notify('textDocument/didOpen',{textDocument:{...doc,languageId:target==='dafny'?'dafny':'solidity'}});return doc;
  };
  const change=(doc,text)=>{doc.text=text;doc.version++;peer.notify('textDocument/didChange',{textDocument:{uri:doc.uri,version:doc.version},contentChanges:[{text}]});};
  const at=(doc,position)=>({textDocument:{uri:doc.uri,version:doc.version},position});
  const verify=async(doc,count,expected='proved')=>{
    let report;
    if(target==='local')report=await request('solidityLean/verify',{textDocument:{uri:doc.uri,version:doc.version}});
    else{
      const symbols=await request('textDocument/documentSymbol',{textDocument:{uri:doc.uri}}),selected=[];
      const visit=rows=>{for(const s of rows||[]){if(/^f\d+$/.test(s.name))selected.push(s);visit(s.children);}};visit(symbols);
      assert.equal(selected.length,count,'all requested verification symbols resolved');
      await Promise.all(selected.map(s=>request('dafny/textDocument/verifySymbol',{textDocument:{uri:doc.uri},position:(s.selectionRange||s.range).start})));
      await until(()=>{const s=states.get(doc.uri);return s?.version===doc.version&&s.namedVerifiables.length===count&&s.namedVerifiables.every(v=>v.status>=4);},'current verification outcome');
      report=states.get(doc.uri);
    }
    verificationOutcomes(target,report,count,expected);return report;
  };
  const stop=()=>{resourceStop=true;terminateTree(child);};
  const guard=setInterval(()=>{
    if(process.platform!=='linux')return;
    const available=Number(fs.readFileSync('/proc/meminfo','utf8').match(/MemAvailable:\s+(\d+)/)[1])*1024;
    if(sampler.samples.at(-1)?.rssBytes>options.memoryMaxMiB*1024**2||available<options.memoryReserveMiB*1024**2)stop();
  },250);
  process.once('SIGTERM',stop);process.once('SIGINT',stop);
  let initialization;
  try{
    const start=performance.now();
    initialization=await request('initialize',{processId:process.pid,rootUri:pathToFileURL(workspace).href,capabilities:{experimental:target==='local'?{solidityLeanOwnedProcess:true}:undefined,
      workspace:{configuration:true,workspaceFolders:true},textDocument:{documentSymbol:{hierarchicalDocumentSymbolSupport:true},publishDiagnostics:{versionSupport:true},
        completion:{completionItem:{snippetSupport:true}},codeAction:{codeActionLiteralSupport:{codeActionKind:{valueSet:['quickfix']}}}}},
      initializationOptions:target==='local'?{backendPath:repo,settings:{projectRoot:workspace,workers,automaticVerification:'never',timeoutMs:options.timeoutMs}}:undefined});
    peer.notify('initialized',{});metrics.initializeRequestMs=performance.now()-start;metrics.coldStartupMs=performance.now()-begin;
    const fixture=servicesWorkload(target),doc=open('services',fixture.text);
    await scenario('document-symbols',async()=>{
      const value=await request('textDocument/documentSymbol',{textDocument:{uri:doc.uri}});
      const names=[];const visit=rows=>{for(const s of rows||[]){names.push(s.name);visit(s.children);}};visit(value);
      assert.ok(names.includes('helper'),'helper document symbol');return {value};
    });
    for(const [id,method,position,extra,check] of [
      ['definition','definition',fixture.call,{},v=>assertServiceResponse('definition',fixture,doc.uri,v)],
      ['references','references',fixture.call,{context:{includeDeclaration:true}},v=>assertServiceResponse('references',fixture,doc.uri,v)],
      ['hover','hover',fixture.call,{},v=>assertServiceResponse('hover',fixture,doc.uri,v)],
      ['signature-help','signatureHelp',fixture.signature,{},v=>{assert.ok(v?.signatures?.[0]?.label.includes('helper'),'signature at opening parenthesis');}],
      ['rename','rename',fixture.call,{newName:'renamed'},v=>assertServiceResponse('rename',fixture,doc.uri,v)]
    ])await scenario(id,async()=>{const start=performance.now(),value=await request('textDocument/'+method,{...at(doc,position),...extra});check(value);metrics[id+'Ms']=performance.now()-start;return {value};});
    await scenario('signature-active-parameter',async()=>{
      const value=await request('textDocument/signatureHelp',at(doc,fixture.signatureSecond));
      return {status:value?.activeParameter===1?'passed':'partial',value,scope:'Active second parameter is compared separately from opening-parenthesis support.'};
    });
    await scenario('completion',async()=>{
      doc.text=fixture.completionText;doc.version++;peer.notify('textDocument/didChange',{textDocument:{uri:doc.uri,version:doc.version},contentChanges:[{range:{start:fixture.completionInsertion,end:fixture.completionInsertion},text:' + this.'}]});
      try{
        const start=performance.now(),value=await request('textDocument/completion',{...at(doc,fixture.completion),context:{triggerKind:2,triggerCharacter:'.'}});
        assert.ok((value?.items||value)?.some(i=>i.label==='helper'),'member completion on incomplete receiver');metrics.completionMs=performance.now()-start;return {value};
      }finally{change(doc,fixture.text);}
    });
    await scenario('completion-after-full-replacement',async()=>{
      // Reduce the discovered difference: retaining the previous AST across a
      // small insertion differs from replacing the entire document with invalid
      // code. Keep both operations explicit in the native protocol evidence.
      await request('textDocument/documentSymbol',{textDocument:{uri:doc.uri,version:doc.version}});
      change(doc,fixture.completionText);
      try{
        const value=await request('textDocument/completion',{...at(doc,fixture.completion),context:{triggerKind:2,triggerCharacter:'.'}});
        const present=(value?.items||value)?.some(i=>i.label==='helper');
        return {status:present?'passed':'partial',memberPresent:present,value,scope:'Completion after a full replacement with incomplete code; empty results remain an explicit behavior difference.'};
      }finally{change(doc,fixture.text);}
    });
    await scenario('workspace-symbols',async()=>{
      const value=await request('workspace/symbol',{query:'helper'});
      assert.ok(value?.some(s=>s.name==='helper'),'helper workspace symbol');return {value};
    });
    await scenario('formatting',async()=>{
      const value=await request('textDocument/formatting',{textDocument:{uri:doc.uri},options:{tabSize:2,insertSpaces:true}});
      assert.ok(Array.isArray(value),'formatter returns edits');
      return {status:'partial',value,scope:'Formatter invocation only; edit application and semantics are not certified.'};
    });
    await scenario('concurrent-requests',async()=>{
      const start=performance.now(),values=await Promise.all(Array.from({length:8},()=>request('textDocument/hover',at(doc,fixture.call))));
      values.forEach(v=>assertServiceResponse('hover',fixture,doc.uri,v));metrics.concurrentRequestsMs=performance.now()-start;return {responses:values.length};
    });
    await require('./hover-observations.cjs').run({target,open,change,request,peer,scenario,workspace,diagnostics,until});
    if(target==='local')await scenario('compiler-secondary-locations',async()=>{
      const source='// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34;\n// 😀 source offsets\ncontract Duplicate {\n  function same() public {}\n  function same() public {}\n}\n';
      const duplicate=open('duplicate-locations',source);
      try{
        await request('textDocument/documentSymbol',{textDocument:{uri:duplicate.uri,version:duplicate.version}});
        await until(()=>diagnostics.get(duplicate.uri)?.version===duplicate.version&&diagnostics.get(duplicate.uri).diagnostics.some(d=>d.severity===1),'current duplicate-declaration diagnostics');
        const values=diagnostics.get(duplicate.uri),error=values.diagnostics.find(d=>String(d.code)==='1686');
        assert.ok(error,'native solc duplicate declaration code');
        assert.deepEqual(error.range,{start:{line:4,character:2},end:{line:4,character:27}});
        assert.ok(error.relatedInformation?.some(r=>r.location.uri===duplicate.uri&&JSON.stringify(r.location.range)===JSON.stringify({start:{line:5,character:2},end:{line:5,character:27}})),'other declaration location retains UTF8-to-UTF16 mapping');
        change(duplicate,source.replace('function same() public {}\n}', 'function different() public {}\n}'));
        await request('textDocument/documentSymbol',{textDocument:{uri:duplicate.uri,version:duplicate.version}});
        await until(()=>diagnostics.get(duplicate.uri)?.version===duplicate.version&&diagnostics.get(duplicate.uri).diagnostics.every(d=>d.severity!==1),'fixed declaration clears current-version error');
        return{status:'partial',before:values,after:diagnostics.get(duplicate.uri),scope:'Real solc related locations and versioned fix; no rendered VS Code, proof diagnostics or Dafny equivalence claim.'};
      }finally{peer.notify('textDocument/didClose',{textDocument:{uri:duplicate.uri}});}
    });
    if(target==='local')await scenario('compiler-foreign-related-locations',async()=>{
      const parentPath=join(workspace,'RelatedParent.sol'),parentUri=pathToFileURL(parentPath).href;
      const parent='// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34;\n// 😀 foreign source\ncontract Parent {\n  function check() public virtual {}\n}\n';
      fs.writeFileSync(parentPath,parent);
      const childSource='// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34;\nimport "./RelatedParent.sol";\ncontract Child is Parent {\n  function check() public {}\n}\n';
      const inherited=open('inherited-related',childSource);
      try{
        await request('textDocument/documentSymbol',{textDocument:{uri:inherited.uri,version:inherited.version}});
        await until(()=>diagnostics.get(inherited.uri)?.diagnostics.some(d=>String(d.code)==='9456'),'native missing-override error');
        const before=diagnostics.get(inherited.uri),error=before.diagnostics.find(d=>String(d.code)==='9456');
        assert.deepEqual(error.range,{start:{line:4,character:2},end:{line:4,character:28}});
        assert.ok(error.relatedInformation?.some(r=>r.location.uri===parentUri&&JSON.stringify(r.location.range)===JSON.stringify({start:{line:4,character:2},end:{line:4,character:36}})),'overridden declaration keeps its own source range');
        change(inherited,childSource.replace('check() public {}','check() public override {}'));
        await request('textDocument/documentSymbol',{textDocument:{uri:inherited.uri,version:inherited.version}});
        await until(()=>diagnostics.get(inherited.uri)?.version===inherited.version&&diagnostics.get(inherited.uri).diagnostics.every(d=>d.severity!==1),'override fix clears error');
        const fixed=diagnostics.get(inherited.uri);
        fs.writeFileSync(parentPath,parent.replace('\n}\n','\n  function check() public virtual {}\n}\n'));
        peer.notify('workspace/didChangeWatchedFiles',{changes:[{uri:parentUri,type:2}]});
        await request('textDocument/documentSymbol',{textDocument:{uri:inherited.uri,version:inherited.version}});
        await until(()=>diagnostics.get(inherited.uri)?.diagnostics.some(d=>String(d.code)==='import:1686'),'foreign primary duplicate declaration');
        const imported=diagnostics.get(inherited.uri),duplicate=imported.diagnostics.find(d=>String(d.code)==='import:1686');
        assert.deepEqual(duplicate.range,{start:{line:0,character:0},end:{line:0,character:0}});
        assert.deepEqual(duplicate.relatedInformation.map(r=>r.location),[
          {uri:parentUri,range:{start:{line:4,character:2},end:{line:4,character:36}}},
          {uri:parentUri,range:{start:{line:5,character:2},end:{line:5,character:36}}}
        ],'foreign primary and secondary retain distinct exact source ranges');
        return{status:'partial',before,fixed,imported,scope:'Real solc primary/secondary imported ranges, fix and watched-file invalidation; no proof or rendered editor equivalence.'};
      }finally{peer.notify('textDocument/didClose',{textDocument:{uri:inherited.uri}});}
    });
    if(target==='local')await scenario('lookup-migration-incomplete-edit',async()=>{
      const initial='// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34;\n// 😀 UTF16 positions\ncontract Lookup {\n  uint public field;\n  function read() public view returns(uint) { return field; }\n  function later() public pure returns(uint) { return 1; }\n}\n';
      const lookup=open('lookup-migration',initial),point={line:5,character:initial.split('\n')[5].indexOf('field')};
      const params=()=>({textDocument:{uri:lookup.uri,version:lookup.version},position:point});
      try{
        const before=await request('textDocument/definition',params());assert.deepEqual(before,{uri:lookup.uri,range:{start:{line:4,character:14},end:{line:4,character:19}}});
        const insertion='  function broken( {\n',lines=initial.split('\n');lookup.text=lines.slice(0,6).join('\n')+'\n'+insertion+lines.slice(6).join('\n');lookup.version++;
        peer.notify('textDocument/didChange',{textDocument:{uri:lookup.uri,version:lookup.version},contentChanges:[{range:{start:{line:6,character:0},end:{line:6,character:0}},text:insertion}]});
        const migrated=await request('textDocument/definition',params());assert.deepEqual(migrated,before);
        const hover=await request('textDocument/hover',params());assert.equal(hover.contents.value,'Outdated: field: uint256');
        const symbols=await request('textDocument/documentSymbol',{textDocument:{uri:lookup.uri,version:lookup.version}});
        const later=symbols[0].children.find(s=>s.name==='later');assert.deepEqual(later.selectionRange,{start:{line:7,character:11},end:{line:7,character:16}});assert.ok(later.detail.startsWith('Outdated: '));
        assert.equal(await request('textDocument/prepareRename',params()),null);
        assert.equal(await request('textDocument/rename',{...params(),newName:'changed'}),null);
        change(lookup,lookup.text+'\n// full replacement\n');const cleared=await request('textDocument/definition',params());assert.equal(cleared,null);
        return{status:'partial',before,migrated,hover,symbols,cleared,scope:'Real compiler-backed historical readonly lookup; no current compiler/proof/edit authority or rendered parity.'};
      }finally{peer.notify('textDocument/didClose',{textDocument:{uri:lookup.uri}});}
    });
    if(target==='local')await scenario('lookup-migration-foreign-dependency',async()=>{
      const libPath=join(workspace,'LookupLib.sol'),libUri=pathToFileURL(libPath).href,library='// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34;\nlibrary LookupLib {\n  function value(uint a) internal pure returns(uint) { return a; }\n}\n';fs.writeFileSync(libPath,library);
      const initial='// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34;\nimport "./LookupLib.sol";\ncontract LookupUser {\n  function run(uint a) public pure returns(uint) { return LookupLib.value(a); }\n}\n',lookup=open('lookup-foreign',initial),point={line:4,character:initial.split('\n')[4].indexOf('.value')+1};
      const params=()=>({textDocument:{uri:lookup.uri,version:lookup.version},position:point});
      try{
        const before=await request('textDocument/definition',params());assert.deepEqual(before,{uri:libUri,range:{start:{line:3,character:11},end:{line:3,character:16}}});
        const insertion='  function broken( {\n';lookup.text=initial.replace('\n}\n','\n'+insertion+'}\n');lookup.version++;
        peer.notify('textDocument/didChange',{textDocument:{uri:lookup.uri,version:lookup.version},contentChanges:[{range:{start:{line:5,character:0},end:{line:5,character:0}},text:insertion}]});
        const migrated=await request('textDocument/definition',params());assert.deepEqual(migrated,before);
        fs.writeFileSync(libPath,library+'// external change without watcher\n');
        const invalidated=await request('textDocument/definition',params());assert.equal(invalidated,null);
        change(lookup,initial);const restored=await request('textDocument/definition',params());assert.deepEqual(restored,before);
        return{status:'partial',before,migrated,invalidated,restored,scope:'Real imported URI/ranges and dependency-byte invalidation without a watcher event; no proof or full Dafny/UI parity.'};
      }finally{peer.notify('textDocument/didClose',{textDocument:{uri:lookup.uri}});}
    });
    if(target==='local')await scenario('lookup-structural-provenance',async()=>{
      const initial='// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34;\ncontract AncestorA { uint internal field; }\ncontract AncestorB { uint internal field; }\ncontract Child is AncestorA {\n  function read() public view returns(uint) { return field; }\n}\n';
      const doc=open('lookup-structural',initial),point={line:5,character:initial.split('\n')[5].indexOf('field')},observations=[];
      const params=()=>({textDocument:{uri:doc.uri,version:doc.version},position:point});
      const incremental=(range,text)=>{doc.text=require('../src/language-services.cjs').applyChanges(doc.text,[{range,text}]);doc.version++;peer.notify('textDocument/didChange',{textDocument:{uri:doc.uri,version:doc.version},contentChanges:[{range,text}]});};
      try{
        const before=await request('textDocument/definition',params());assert.deepEqual(before,{uri:doc.uri,range:{start:{line:2,character:35},end:{line:2,character:40}}});observations.push({phase:'initial',version:doc.version,definition:before});
        incremental({start:{line:6,character:0},end:{line:6,character:0}},'  function broken( {\n');
        const safe=await request('textDocument/definition',params());assert.deepEqual(safe,before);observations.push({phase:'safe-incomplete-sibling',version:doc.version,definition:safe});
        incremental({start:{line:4,character:18},end:{line:4,character:27}},'AncestorB');
        const invalidated=await request('textDocument/definition',params());observations.push({phase:'base-changed-while-incomplete',version:doc.version,definition:invalidated});assert.equal(invalidated,null,'changed inheritance must not retain AncestorA.field binding');
        const restoredText=initial.replace('Child is AncestorA','Child is AncestorB');change(doc,restoredText);
        const recovered=await request('textDocument/definition',params());assert.deepEqual(recovered,{uri:doc.uri,range:{start:{line:3,character:35},end:{line:3,character:40}}});observations.push({phase:'valid-recompile',version:doc.version,definition:recovered});
        return{status:'partial',observations,scope:'Ordered real solc inherited-member binding, safe migration, structural invalidation and new compiler binding; no proof or rendered parity.'};
      }finally{peer.notify('textDocument/didClose',{textDocument:{uri:doc.uri}});}
    });
    if(target==='local')await scenario('lookup-moved-block-binding',async()=>{
      const initial='// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34;\ncontract Scope {\n  uint internal field;\n  function read() public view returns(uint) {\n    { uint field=1;\n    }\n    return field;\n  }\n}\n';
      const doc=open('lookup-block',initial),observations=[];
      const params=line=>({textDocument:{uri:doc.uri,version:doc.version},position:{line,character:11}});
      const edit=changes=>{doc.text=require('../src/language-services.cjs').applyChanges(doc.text,changes);doc.version++;peer.notify('textDocument/didChange',{textDocument:{uri:doc.uri,version:doc.version},contentChanges:changes});};
      try{
        const before=await request('textDocument/definition',params(7));assert.deepEqual(before,{uri:doc.uri,range:{start:{line:3,character:16},end:{line:3,character:21}}});observations.push({phase:'initial-state-member',version:doc.version,definition:before});
        edit([{range:{start:{line:6,character:0},end:{line:7,character:0}},text:''},{range:{start:{line:7,character:0},end:{line:7,character:0}},text:'    }\n'},{range:{start:{line:9,character:0},end:{line:9,character:0}},text:'  function broken( {\n'}]);
        const invalidated=await request('textDocument/definition',params(6));observations.push({phase:'moved-close-brace-while-incomplete',version:doc.version,definition:invalidated});assert.equal(invalidated,null,'occurrence moved inside local field scope must not retain state member');
        change(doc,doc.text.replace('  function broken( {\n',''));
        const recovered=await request('textDocument/definition',params(6));assert.deepEqual(recovered,{uri:doc.uri,range:{start:{line:5,character:11},end:{line:5,character:16}}});observations.push({phase:'valid-recompile-local-member',version:doc.version,definition:recovered});
        return{status:'partial',observations,scope:'Real solc scope ownership, invalidation and recovery; no proof or rendered parity.'};
      }finally{peer.notify('textDocument/didClose',{textDocument:{uri:doc.uri}});}
    });
    if(target==='local')await scenario('lookup-overload-expression-provenance',async()=>{
      const initial='// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34;\ncontract Calls {\n  function choose(uint a) internal pure returns(uint) { return a; }\n  function choose(bool a) internal pure returns(uint) { return a ? 1 : 0; }\n  function run() public pure returns(uint) { return choose(1); }\n}\n';
      const doc=open('lookup-overload',initial),point={line:5,character:initial.split('\n')[5].indexOf('choose')},observations=[];
      const params=()=>({textDocument:{uri:doc.uri,version:doc.version},position:point});
      try{
        const before=await request('textDocument/definition',params());assert.deepEqual(before,{uri:doc.uri,range:{start:{line:3,character:11},end:{line:3,character:17}}});observations.push({phase:'initial-uint-overload',version:doc.version,definition:before});
        const column=initial.split('\n')[5].indexOf('(1)')+1,changes=[{range:{start:{line:5,character:column},end:{line:5,character:column+1}},text:'true'},{range:{start:{line:6,character:0},end:{line:6,character:0}},text:'  function broken( {\n'}];
        doc.text=require('../src/language-services.cjs').applyChanges(doc.text,changes);doc.version++;peer.notify('textDocument/didChange',{textDocument:{uri:doc.uri,version:doc.version},contentChanges:changes});
        const invalidated=await request('textDocument/definition',params());observations.push({phase:'changed-call-argument-while-incomplete',version:doc.version,definition:invalidated});assert.equal(invalidated,null,'argument change must retire overload binding');
        change(doc,initial.replace('choose(1)','choose(true)'));const recovered=await request('textDocument/definition',params());assert.deepEqual(recovered,{uri:doc.uri,range:{start:{line:4,character:11},end:{line:4,character:17}}});observations.push({phase:'valid-bool-overload',version:doc.version,definition:recovered});
        return{status:'partial',observations,scope:'Native compiler overload, expression invalidation and recovery; not proof or rendered parity.'};
      }finally{peer.notify('textDocument/didClose',{textDocument:{uri:doc.uri}});}
    });
    await scenario('rapid-edits-language-services',async()=>{
      change(doc,fixture.text.replaceAll('helper','obsolete'));change(doc,fixture.text.replaceAll('helper','newest'));
      const value=await request('textDocument/documentSymbol',{textDocument:{uri:doc.uri,version:doc.version}});
      assertServiceSymbols(value,'newest',['obsolete','helper']);return {version:doc.version,value};
    });
    await scenario('close-reopen-language-services',async()=>{
      peer.notify('textDocument/didClose',{textDocument:{uri:doc.uri}});
      doc.version=1;doc.text=fixture.text.replaceAll('helper','reopened');
      peer.notify('textDocument/didOpen',{textDocument:{uri:doc.uri,languageId:target==='dafny'?'dafny':'solidity',version:doc.version,text:doc.text}});
      const value=await request('textDocument/documentSymbol',{textDocument:{uri:doc.uri,version:doc.version}});
      assertServiceSymbols(value,'reopened',['newest','obsolete','helper']);return{version:doc.version,value};
    });
    await scenario('multi-file-language-services',async()=>{
      const other=open('isolated-services',fixture.text.replaceAll('helper','isolated'));
      try{
        const values=await Promise.all([doc,other].map(d=>request('textDocument/documentSymbol',{textDocument:{uri:d.uri,version:d.version}})));
        assertServiceSymbols(values[0],'reopened',['isolated']);
        assertServiceSymbols(values[1],'isolated',['reopened']);return{uris:[doc.uri,other.uri],values};
      }finally{peer.notify('textDocument/didClose',{textDocument:{uri:other.uri}});}
    });
    await scenario('cancel-service-request',async()=>{
      const abort=new AbortController(),start=performance.now();
      const pending=peer.request('textDocument/documentSymbol',{textDocument:{uri:doc.uri,version:doc.version}},{signal:abort.signal,timeoutMs:options.timeoutMs});
      abort.abort();await assert.rejects(pending,error=>error.code===-32800);
      const clientAcknowledgementMs=performance.now()-start;
      const value=await request('textDocument/documentSymbol',{textDocument:{uri:doc.uri,version:doc.version}});
      assertServiceSymbols(value,'reopened',['newest','obsolete']);
      return{status:'partial',clientAcknowledgementMs,value,scope:'Real request and $/cancelRequest recorded; client rejection and follow-up service success, not proof-worker quiescence.'};
    });
    if(options.scope==='full'){
      let proof;
      await scenario('initial-verification',async()=>{
        const start=performance.now();proof=open('proof',workload(target,options.obligations));
        const report=await verify(proof,options.obligations);metrics.initialVerificationMs=performance.now()-start;
        const first=events.find(e=>e.ms>=start-begin&&e.data?.uri===proof.uri&&
          (e.kind==='solidityLean/report'||e.data.namedVerifiables?.some(s=>s.status>=4)||e.kind==='textDocument/publishDiagnostics'&&e.data.diagnostics?.length));
        if(first)metrics.firstUsefulFeedbackMs=first.ms-(start-begin);
        metrics.throughputObligationsPerSecond=options.obligations/(metrics.initialVerificationMs/1000);return report;
      });
      if(proof){
        await scenario('incremental-verification',async()=>{const start=performance.now();change(proof,workload(target,options.obligations+1));const report=await verify(proof,options.obligations+1);metrics.incrementalVerificationMs=performance.now()-start;return report;});
        await scenario('failure-diagnostics',async()=>{
          change(proof,workload(target,options.obligations,true));const report=await verify(proof,options.obligations,'failed');
          await until(()=>diagnostics.get(proof.uri)?.version===proof.version&&diagnostics.get(proof.uri)?.diagnostics.length>0,'current-version failure diagnostics');return {report,diagnostics:diagnostics.get(proof.uri)};
        });
        await scenario('rapid-edits-stale-results',async()=>{
          change(proof,workload(target,options.obligations+1,true));change(proof,workload(target,options.obligations+2));
          const report=await verify(proof,options.obligations+2);
          await until(()=>diagnostics.get(proof.uri)?.version===proof.version&&diagnostics.get(proof.uri)?.diagnostics.length===0,'current-version obsolete diagnostics cleared');return {version:proof.version,report};
        });
        await scenario('concurrent-files-and-requests',async()=>{
          const start=performance.now(),docs=[open('parallel-a',workload(target,options.obligations)),open('parallel-b',workload(target,options.obligations))];
          const reports=await Promise.all(docs.map(d=>verify(d,options.obligations)));metrics.crossFileVerificationMs=performance.now()-start;return reports;
        });
      }
    }
  }catch(e){scenarios.push({id:'server-initialization',status:'broken',error:e.stack});}
  finally{
    try{await peer.request('shutdown',null,{timeoutMs:2000});shutdownAcknowledged=true;peer.notify('exit',null);append({direction:'client',framingFinalized:true});}catch(e){record('shutdown.error',{message:e.message});}
    await Promise.race([closed,new Promise(r=>setTimeout(r,1000))]);
    if(!exited){forcedShutdown=true;terminateTree(child);}
    clearInterval(guard);process.removeListener('SIGTERM',stop);process.removeListener('SIGINT',stop);
    const resources=sampler.stop();resources.clockOffsetMs=sampler.start-begin;
    resources.phases=scenarios.map(s=>{
      const from=events.find(e=>e.kind==='scenario.start'&&e.data.id===s.id)?.ms,to=events.find(e=>e.kind==='scenario.end'&&e.data.id===s.id)?.ms;
      const samples=resources.samples.filter(p=>p.ms+resources.clockOffsetMs>=from&&p.ms+resources.clockOffsetMs<=to);
      return {scenario:s.id,fromMs:from,toMs:to,sampleCount:samples.length,activity:samples.length>=2?activity({platform:resources.platform,samples}):{status:'unexamined',reason:'Too few samples in phase'}};
    });
    for(const p of sampler.survivors())if(sampler.survivors().some(r=>r.pid===p.pid&&r.start===p.start))terminateTree({pid:p.pid,processBirth:p.start});
    await Promise.race([closed,new Promise(r=>setTimeout(r,1000))]);
    const groupErrors=[];const groupDeadline=Date.now()+1000;for(const owned of ownedGroups.values())try{await waitForGroup(owned,{deadline:groupDeadline,kill:true});}catch(error){groupErrors.push(error.message);}
    peer.close();resources.cleanup={remaining:sampler.survivors(),groupErrors};
    scenarios.push({id:'server-lifecycle',status:shutdownAcknowledged&&exited&&exitCode===0&&!forcedShutdown&&!groupErrors.length?'passed':'broken',observation:{shutdownAcknowledged,exited,exitCode,exitSignal,forcedShutdown}});
    fs.writeFileSync(join(dir,'resources.json'),JSON.stringify(resources));fs.closeSync(log);
    fs.writeFileSync(join(dir,'events.jsonl'),events.map(e=>JSON.stringify(e)).join('\n')+'\n');
    const status=resourceStop?'resource-stop':resources.cleanup.remaining.length||groupErrors.length?'broken':scenarios.some(s=>s.status==='timeout')?'timeout':scenarios.some(s=>s.status==='broken')?'broken':scenarios.every(s=>s.status==='passed')?'passed':'passed-with-gaps';
    const result={schemaVersion:1,runId,target,status,metrics,scenarios,checks:scenarios.filter(s=>s.status==='passed').map(s=>s.id),serverCapabilities:initialization?.capabilities};
    fs.writeFileSync(join(dir,'result.json'),JSON.stringify(result,null,2));
    return {target,workers,cache:'none',suite:'stdio-'+options.scope,status,result,artifacts:dir,protocol:protocol(trace),resources:{...resources,samples:undefined}};
  }
}

async function main(args=process.argv.slice(2)){
  const options=parse(args);if(options.help){process.stdout.write('node vscode/parity/stdio.cjs --dafny PATH --output DIR [--scope services|full] [--workers 1,2,4] [--trials 5] [--warmups 1]\n');return;}
  const output=resolve(options.output);if(fs.existsSync(output))throw new Error('Choose a new output directory');fs.mkdirSync(output,{recursive:true});
  const hash=p=>createHash('sha256').update(fs.readFileSync(p)).digest('hex');
  const report={schemaVersion:1,started:new Date().toISOString(),options,fullParityEstablished:false,runs:[],comparisons:[],environment:{node:process.version,cpu:cpus()[0]?.model,
    localCommit:spawnSync('git',['rev-parse','HEAD'],{cwd:repo,encoding:'utf8'}).stdout.trim(),sourceHashes:Object.fromEntries(['stdio','core','workloads','analyze'].map(n=>[n+'.cjs',hash(join(__dirname,n+'.cjs'))])),
    cpuQuota:process.platform==='linux'?fs.readFileSync('/sys/fs/cgroup/cpu.max','utf8').trim():null,
    memoryLimit:process.platform==='linux'?fs.readFileSync('/sys/fs/cgroup/memory.max','utf8').trim():null,
    backendSourceHashes:Object.fromEntries(fs.readdirSync(join(repo,'vscode/src')).filter(n=>n.endsWith('.cjs')).sort().map(n=>[n,hash(join(repo,'vscode/src',n))])),
    fixtureHashes:Object.fromEntries(['services.dfy','services.sol'].map(n=>[n,hash(join(repo,'tests/editor-parity',n))])),
    dafnyVersion:options.dafny?spawnSync(resolve(options.dafny),['--version'],{encoding:'utf8',timeout:10000,maxBuffer:1024*1024}).stdout?.trim():null},
    limitations:['Stdio-only: no VS Code API, UI, DOM, accessibility or renderer measurements.','Services scope does not execute verification; full scope requires a freshly built local backend. Dafny automatic verification is disabled; native verifySymbol requests explicitly schedule only the proof fixtures.',
      'Constant-return proof workload is a shared fragment, not general semantic equivalence.','Process-cold startup retains OS caches; cache policies and solver resource limits are not equivalent.',
      'Raw responses preserve native ranges, diagnostics and strings. Differences are evidence, not automatically regressions.','Frontend, VC, solver and UI phase timing are not isolated.']};
  const lock=join(tmpdir(),'solidity-lean-editor-parity.lock');fs.mkdirSync(lock);fs.writeFileSync(join(lock,'owner.json'),JSON.stringify({pid:process.pid,output}));
  const save=()=>{
    report.summary=summarize(report.runs);report.parallelScaling=options.scope==='full'?scaling(report.summary):[];
    const inventory=require('./inventory.cjs').loadInventory();
    report.featureParity=inventory.features.map(f=>{
      const evidence=report.runs.filter(r=>!r.warmup).flatMap(r=>r.result.scenarios.filter(s=>f.assessment.scenarioIds.includes(s.id)).map(s=>({target:r.target,scenario:s.id,status:s.status,artifact:join(r.artifacts,'result.json')})));
      return {id:f.id,sourceAssessment:f.assessment.status,status:evidence.some(e=>['broken','timeout'].includes(e.status))?'broken':f.assessment.status,
        runtimeAssessment:evidence.length?'observed-related-scenarios':'unexamined',reason:f.assessment.reason,evidence};
    });
    fs.writeFileSync(join(output,'report.json'),JSON.stringify(report,null,2));
    const lines=['# Stdio LSP comparison','',`Full parity: **not established**. Scope: ${options.scope}. Status: ${report.status||'running'}.`,'',
      '| Target | Workers | Trials | Valid timing trials | Failures | Startup median / p95 ms | Hover median / p95 ms |','|---|---:|---:|---:|---:|---:|---:|'];
    const fmt=s=>s?.n?`${s.median.toFixed(1)} / ${s.p95.toFixed(1)}`:'unmeasured';
    for(const s of report.summary)lines.push(`| ${s.target} | ${s.workers} | ${s.trials} | ${s.validTrials} | ${s.failures} | ${fmt(s.metrics.coldStartupMs)} | ${fmt(s.metrics.hoverMs)} |`);
    lines.push('','See report.json for per-scenario native responses, protocol differences, variability, resource use and scaling.','',...report.limitations.map(l=>'- '+l),'');
    fs.writeFileSync(join(output,'summary.md'),lines.join('\n'));
  };
  try{
    for(const workers of options.workers)for(let i=-options.warmups;i<options.trials;i++)for(const target of i%2===0?options.targets:[...options.targets].reverse()){
      process.stdout.write(`Stdio ${target} workers=${workers} trial=${i}\n`);
      const run=await trial(target,workers,options,join(output,`${target}-w${workers}-${i}`));run.trial=i;run.warmup=i<0;report.runs.push(run);save();
      if(run.status==='resource-stop'||run.resources.cleanup.remaining.length)throw new Error('Resource/cleanup guard stopped the suite');
    }
    for(const a of report.runs.filter(r=>r.target==='dafny'&&!r.warmup)){
      const b=report.runs.find(r=>r.target==='local'&&r.workers===a.workers&&r.trial===a.trial);if(!b)continue;
      for(const id of new Set([...a.result.scenarios,...b.result.scenarios].map(s=>s.id)))report.comparisons.push({scenario:id,workers:a.workers,trial:a.trial,
        differences:differences(normalize(a.result.scenarios.find(s=>s.id===id)?.observation,[a.artifacts]),normalize(b.result.scenarios.find(s=>s.id===id)?.observation,[b.artifacts])),
        statuses:{dafny:a.result.scenarios.find(s=>s.id===id)?.status,local:b.result.scenarios.find(s=>s.id===id)?.status}});
    }
    report.status=report.runs.every(r=>['passed','passed-with-gaps'].includes(r.status))?'completed-with-gaps':'incomplete';
  }catch(e){report.status='incomplete';report.error=e.stack;throw e;}
  finally{try{report.finished=new Date().toISOString();save();}finally{fs.rmSync(lock,{recursive:true,force:true});}}
  if(report.status==='incomplete')process.exitCode=1;return report;
}
module.exports={parse,trial,main};
if(require.main===module)main().catch(e=>{process.stderr.write(e.stack+'\n');process.exitCode=1;});
