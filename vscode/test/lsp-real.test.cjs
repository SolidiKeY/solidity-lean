'use strict';
const {test}=require('node:test');
const assert=require('node:assert/strict');
const {spawn}=require('node:child_process');
const {mkdtempSync,writeFileSync,readFileSync,rmSync}=require('node:fs');
const {tmpdir}=require('node:os');
const {join,resolve}=require('node:path');
const {pathToFileURL}=require('node:url');
const {createHash}=require('node:crypto');
const {RpcPeer}=require('../src/rpc.cjs');
const {terminateTree}=require('../src/backend.cjs');
const {position}=require('../src/language-services.cjs');
const {workload}=require('../parity/workloads.cjs');

test('real Solidity LSP keeps Lean warm and verifies versioned in-memory snapshots',
  {skip:!process.env.SOLIDITY_LEAN_REAL_BACKEND,timeout:180000},async t=>{
  const root=resolve(process.env.SOLIDITY_LEAN_REAL_BACKEND),scratch=mkdtempSync(join(tmpdir(),'solidity-lsp-real-'));
  const child=spawn(process.execPath,[join(__dirname,'../src/lsp-server.cjs')],{cwd:root,detached:true,stdio:['pipe','pipe','pipe']});
  const rpc=new RpcPeer(child.stdout,child.stdin),events=[];let stderr='';
  child.stderr.on('data',chunk=>{stderr=(stderr+chunk).slice(-10000);});child.on('exit',code=>rpc.close(new Error(`Server exited ${code}: ${stderr}`)));
  rpc.onNotification('solidityLean/report',params=>events.push({kind:'report',...params}));
  rpc.onNotification('textDocument/publishDiagnostics',params=>events.push({kind:'diagnostics',...params}));
  const states=[];rpc.onNotification('solidityLean/status',params=>states.push(params));
  const source=join(scratch,'Editor.sol'),uri=pathToFileURL(source).href;
  const saved='// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34; contract Saved {}\n';writeFileSync(source,saved);
  const original=`// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34;\ncontract Editor {\n  /// @custom:key ensures \\result == 1\n  function f() public pure returns(uint256 result) { return 1; }\n  function helper(uint x) public pure returns(uint) { return x; }\n  function caller() public pure returns(uint) { return helper(1); }\n}\n`;
  let text=original,version=1,cold;
  const change=next=>{text=next;rpc.notify('textDocument/didChange',{textDocument:{uri,version:++version},contentChanges:[{text}]});};
  const verify=options=>rpc.request('solidityLean/verify',{textDocument:{uri,version},options:{function:'f()',...options}},{timeoutMs:60000});
  try{
    const initialization=await rpc.request('initialize',{rootUri:pathToFileURL(root).href,initializationOptions:{settings:{workers:2,automaticVerification:'never',timeoutMs:60000}}});
    assert.equal(initialization.capabilities.textDocumentSync.change,2);rpc.notify('initialized',{});rpc.notify('textDocument/didOpen',{textDocument:{uri,version,text}});
    await t.test('unsaved snapshot produces a real kernel proof without changing disk',async()=>{
      cold=await verify();assert.equal(cold.results.find(r=>r.function==='f').status,'proved');assert.equal(cold.errors.length,0);
      assert.equal(cold.results[0].sourceHash,createHash('sha256').update(text).digest('hex'));assert.equal(readFileSync(source,'utf8'),saved);
      assert.ok(cold.backend.leanServerPid);assert.ok(cold.backend.workerPid);
    });
    await t.test('exact snapshots reuse checked reports',async()=>{
      const second=await verify();assert.equal(second.backend.leanServerPid,cold.backend.leanServerPid);
      assert.equal(second.backend.leanDocumentVersion,cold.backend.leanDocumentVersion);
      assert.ok((await rpc.request('solidityLean/stats',{})).cacheHits>=1);
    });
    await t.test('completion, definitions, references, symbols, signatures and rename use current source',async()=>{
      const point=position(text,text.indexOf('helper(1)')+2);
      const definition=await rpc.request('textDocument/definition',{textDocument:{uri,version},position:point});
      assert.equal(definition.range.start.line,5);assert.equal(definition.uri,uri);
      const references=await rpc.request('textDocument/references',{textDocument:{uri,version},position:point,context:{includeDeclaration:true}});
      assert.equal(references.length,2);
      const completion=await rpc.request('textDocument/completion',{textDocument:{uri,version},position:point});assert.ok(completion.items.some(i=>i.label==='helper'));
      const signatures=await rpc.request('textDocument/signatureHelp',{textDocument:{uri,version},position:position(text,text.indexOf('helper(1)')+'helper('.length)});
      assert.match(signatures.signatures[0].label,/helper/);assert.equal(signatures.signatures[0].parameters.length,1);
      const symbols=await rpc.request('textDocument/documentSymbol',{textDocument:{uri,version}});assert.ok(symbols[0].children.some(s=>s.name==='helper'));
      const prepared=await rpc.request('textDocument/prepareRename',{textDocument:{uri,version},position:point});assert.equal(prepared.range.start.line,6);
      const edit=await rpc.request('textDocument/rename',{textDocument:{uri,version},position:point,newName:'renamed'});
      assert.equal(edit.documentChanges[0].textDocument.version,version);assert.equal(edit.documentChanges[0].edits.length,2);
      await assert.rejects(rpc.request('textDocument/rename',{textDocument:{uri,version},position:point,newName:'while'}),/identifier/);
    });
    await t.test('incomplete edits get live-text completion and positioned compiler diagnostics',async()=>{
      change(original.replace('return helper(1);','this.\nreturn helper(1);'));
      const completion=await rpc.request('textDocument/completion',{textDocument:{uri,version},position:position(text,text.indexOf('this.')+5)});
      assert.ok(completion.items.some(i=>i.label==='helper'));assert.ok(events.some(e=>e.kind==='diagnostics'&&e.version===version&&e.diagnostics.some(d=>d.source==='solc'&&d.severity===1)));
    });
    await t.test('changed snapshots rerun proofs in the same Lean process',async()=>{
      change(original.replace('return 1;','return 2;'));
      const result=await verify();assert.equal(result.results.find(r=>r.function==='f').status,'pending');
      assert.equal(result.backend.leanServerPid,cold.backend.leanServerPid);assert.ok(result.backend.leanDocumentVersion>cold.backend.leanDocumentVersion);
    });
    await t.test('exact false obligations can produce certified model evidence',async()=>{
      const result=await verify({counterexamples:true});const row=result.results.find(r=>r.function==='f');assert.equal(row.status,'refuted');assert.ok(row.counterexample);
    });
    await t.test('rapid changes cancel old Lean work and suppress obsolete reports',async()=>{
      change(original.replace('return 1;','return 2;')+'\n// distinct in-flight snapshot\n');const oldVersion=version;
      const old=verify().then(result=>({result}),error=>({error}));
      const deadline=Date.now()+10000;while(!states.some(s=>s.version===oldVersion&&s.state==='running')){assert.ok(Date.now()<deadline,'proof must start');await new Promise(r=>setTimeout(r,10));}
      change(original+'\n// newest snapshot\n');const latest=await verify();assert.equal(latest.results.find(r=>r.function==='f').status,'proved');
      const obsolete=await old;assert.ok([-32800,-32801].includes(obsolete.error?.code),'old request must be cancelled');
      assert.equal(events.filter(e=>e.kind==='report'&&e.version===oldVersion).length,0);assert.equal(readFileSync(source,'utf8'),saved);
      if(process.platform==='linux'){
        let live=false;try{const stat=readFileSync(`/proc/${cold.backend.leanServerPid}/stat`,'utf8');live=stat.slice(stat.lastIndexOf(')')+2).split(' ')[0]!=='Z';}catch{}
        assert.equal(live,false,'the cancelled Lean process must be quiescent');
      }
    });
    await t.test('two files can occupy separate bounded proof workers',async()=>{
      const uris=['ParallelA.sol','ParallelB.sol'].map(name=>pathToFileURL(join(scratch,name)).href);
      for(const parallelUri of uris){const body=workload('local',16);rpc.notify('textDocument/didOpen',{textDocument:{uri:parallelUri,version:1,text:body}});await rpc.request('textDocument/documentSymbol',{textDocument:{uri:parallelUri,version:1}});}
      const results=await Promise.all(uris.map(parallelUri=>rpc.request('solidityLean/verify',{textDocument:{uri:parallelUri,version:1},options:{function:'f0()'}},{timeoutMs:60000})));
      assert.notEqual(results[0].backend.workerPid,results[1].backend.workerPid);assert.equal((await rpc.request('solidityLean/stats',{})).workers.length,2);
      results.forEach(r=>assert.equal(r.results.find(row=>row.function==='f0').status,'proved'));
    });
    await t.test('multiple contracts retain their own proof and declaration identities',async()=>{
      const multiUri=pathToFileURL(join(scratch,'Multi.sol')).href;
      const body=`// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34;\ncontract A {\n/// @custom:key ensures \\result == 1\nfunction f() public pure returns(uint) { return 1; }\n}\ncontract B {\n/// @custom:key ensures \\result == 2\nfunction f() public pure returns(uint) { return 2; }\n}\n`;
      rpc.notify('textDocument/didOpen',{textDocument:{uri:multiUri,version:1,text:body}});
      const report=await rpc.request('solidityLean/verify',{textDocument:{uri:multiUri,version:1},options:{}},{timeoutMs:60000});
      assert.equal(report.errors.length,0);const functions=report.results.filter(r=>r.function==='f');
      assert.deepEqual(functions.map(r=>[r.contract,r.status]),[['A','proved'],['B','proved']]);
      assert.notEqual(functions[0].sourceId,functions[1].sourceId);assert.notEqual(functions[0].range.start.line,functions[1].range.start.line);
    });
    await t.test('a crashed native Lean server reopens its document in the replacement session',async()=>{
      const session=new (require('../src/lean-session.cjs').LeanSession)(root,join(scratch,'native-restart'));
      try{
        const input='import Solidity.Frontend.Testing\n#check Nat\n';await session.check(input,60000);const first=session.child;
        const stopped=new Promise(resolve=>first.once('exit',resolve));first.kill('SIGTERM');await stopped;
        const diagnostics=await session.check(input,60000);assert.notEqual(session.child.pid,first.pid);assert.equal(session.version,1);
        assert.equal(diagnostics.filter(d=>d.severity===1).length,0);
      }finally{session.dispose();}
    });
  }finally{
    try{await rpc.request('shutdown',null,{timeoutMs:5000});rpc.notify('exit',null);}catch{}
    terminateTree(child);rpc.close();rmSync(scratch,{recursive:true,force:true});
  }
});
