'use strict';
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {chromium}=require('playwright');
// Retain at most 100 old protocol objects instead of 10,000. Offline imports
// generate thousands of asset requests; assertions consume their events live.
require(path.join(path.dirname(require.resolve('playwright-core/package.json')),'lib/coreBundle.js')).server.setMaxDispatchersForTest(100);
const {createStaticServer}=require('../tools/serve-static.cjs');
const artifacts=path.resolve(__dirname,'../artifacts');
const withProofs=process.argv.includes('--proofs');
const single=process.argv.includes('--single');
const localFile=process.argv.includes('--file'),published=process.env.SOLIDITY_IDE_URL;
const report={singleFile:single,proofs:withProofs,startedAt:new Date().toISOString(),assetBuild:JSON.parse(fs.readFileSync(path.resolve(__dirname,single?'../single-file/build.json':'../dist/asset-manifest.json'),'utf8')).build,protocolHistoryLimit:100,checks:[],webSockets:[],requests:[],errors:[]};
async function main(){
  const app=localFile||published?{close:async()=>{}}:createStaticServer({port:0,...(single?{root:path.resolve(__dirname,'../single-file')}:{} )});
  const url=localFile?require('node:url').pathToFileURL(path.resolve(__dirname,'../single-file')).href:published?.replace(/\/$/,'')||await app.listen();let serverClosed=false;
  const documentURL=url+(single?'/index.html?backend=native':'');
  // Private contexts keep CacheStorage in RAM. Use a disposable disk-backed
  // profile, matching an offline website's normal persistent browser storage.
  const profiles=path.join(artifacts,'browser-profiles');fs.mkdirSync(profiles,{recursive:true});
  const profile=fs.mkdtempSync(path.join(profiles,'website-'));
  const context=await chromium.launchPersistentContext(profile,{executablePath:process.env.CHROMIUM_PATH||'/usr/bin/chromium',args:['--no-sandbox'],viewport:{width:1440,height:900}});
  if(localFile)await context.setOffline(true);
  await context.addInitScript(()=>{globalThis.WebSocket=class{constructor(){throw new Error('This test forbids all WebSocket/backend connections');}};});
  context.on('request',request=>{if(!/^(blob:|data:)/.test(request.url())&&new URL(request.url()).origin!==new URL(url).origin)report.requests.push(request.url());if(single&&/^(https?:|file:)/.test(request.url())){report.documentRequests??=[];report.documentRequests.push(request.url());}});
  const page=context.pages()[0]||await context.newPage();page.on('pageerror',e=>report.errors.push(e.stack));page.on('websocket',socket=>report.webSockets.push(socket.url()));
  page.on('console',message=>{if(message.type()==='error')console.log('Browser:',message.text().slice(0,1200));});
  async function check(name,run){const start=performance.now();await run();report.checks.push({name,elapsedMs:+(performance.now()-start).toFixed(1)});console.log('PASS',name);}
  try{
    await check('a plain static website boots a real Solidity WASM compiler without any backend',async()=>{
      if(!single){await page.goto(url+'/cache-preparation');await page.evaluate(async()=>{await caches.open('solidity-lean-browser-workbench-old');await caches.open('solidity-lean-workbench-old');await caches.open('unrelated-cache');});}
      const start=performance.now();await page.goto(documentURL,{timeout:300000,waitUntil:single?'domcontentloaded':'load'});await page.waitForFunction(()=>{const error=document.querySelector('#editor')?.textContent;if(error?.startsWith('Unable to'))throw new Error(error);return window.solidityIDE?.state.connected;},null,{timeout:300000});await page.waitForFunction(()=>solidityIDE.state.symbols.get('Counter.sol')?.length);report.startupMs=+(performance.now()-start).toFixed(1);assert.equal(await page.evaluate(()=>solidityIDE.state.runtime.mode),'browser');assert.equal(await page.evaluate(()=>solidityIDE.state.runtime.compilerReady),true);if(!localFile)assert.equal((await fetch(url+'/api/bootstrap')).status,404);
      if(single){report.embedded=await page.evaluate(()=>({build:singleFileIDE.build,assets:singleFileIDE.expected,preparationMs:singleFileIDE.preparationMs,reused:singleFileIDE.reused,remainingDataNodes:document.querySelectorAll('script[data-asset]').length}));assert.equal(report.embedded.build,report.assetBuild,'The opened HTML must match the exact generated artifact');assert.equal(report.embedded.remainingDataNodes,0);if(!localFile)assert.deepEqual(await page.evaluate(async()=>(await navigator.serviceWorker.getRegistrations()).map(r=>r.scope)),[]);
        await page.locator('[data-menu="File"]').click();assert.equal(await page.locator('.menu-popup').getByRole('button',{name:'Download Offline IDE',exact:true}).isVisible(),true);await page.locator('#breadcrumbs').click();
        if(!localFile){const reload=performance.now();await page.reload({timeout:300000});await page.waitForFunction(()=>window.solidityIDE?.state.connected,null,{timeout:300000});assert.equal(await page.evaluate(()=>singleFileIDE.reused),true);report.reopenMs=+(performance.now()-reload).toFixed(1);}}
      else{const keys=await page.evaluate(()=>caches.keys());assert.ok(!keys.includes('solidity-lean-browser-workbench-old'));assert.ok(!keys.includes('solidity-lean-workbench-old'));assert.ok(keys.includes('unrelated-cache'));}
    });
    await check('the unchanged compiler helpers produce exact source provenance and AST language services',async()=>{
      await page.evaluate(()=>solidityIDE.openFile('Identity.sol'));
      const r=await page.evaluate(async()=>{const ide=solidityIDE,m=ide.editor.getModel(),p=m.getPositionAt(m.getValue().indexOf('identity(1)')+2),position={line:p.lineNumber-1,character:p.column-1};return {hover:await ide.language('textDocument/hover',m,{position}),definition:await ide.language('textDocument/definition',m,{position}),references:await ide.language('textDocument/references',m,{position,context:{includeDeclaration:true}}),completion:await ide.language('textDocument/completion',m,{position})};});
      assert.match(r.hover.contents.value,/identity/);assert.equal(r.definition.range.start.line,5);assert.equal(r.references.length,2);assert.ok(r.completion.items.some(i=>i.label==='identity'));
    });
    await check('Monaco rename and compiler-validated formatting run in the worker',async()=>{
      await page.evaluate(()=>{const e=solidityIDE.editor,m=e.getModel();e.setPosition(m.getPositionAt(m.getValue().indexOf('identity(1)')+2));e.focus();});await page.keyboard.press('F2');const input=page.locator('.rename-box input');await input.waitFor();await input.fill('echoValue');await input.press('Enter');await page.waitForFunction(()=>solidityIDE.editor.getValue().includes('echoValue(1)'));
      await page.evaluate(async()=>{solidityIDE.editor.setValue(solidityIDE.editor.getValue().replace('contract Identity {','contract Identity{'));await solidityIDE.editor.getAction('editor.action.formatDocument').run();});assert.match(await page.evaluate(()=>solidityIDE.editor.getValue()),/contract Identity \{/);
    });
    await check('compiler errors come from solc running inside the browser',async()=>{await page.evaluate(()=>solidityIDE.editor.setValue(solidityIDE.editor.getValue().replace('return echoValue(1);','return ;!;')));await page.waitForFunction(()=>(solidityIDE.state.diagnostics.get('Identity.sol')||[]).some(d=>d.severity===1));await page.evaluate(()=>solidityIDE.editor.setValue(solidityIDE.state.baselines['Identity.sol']));await page.waitForFunction(()=>(solidityIDE.state.diagnostics.get('Identity.sol')||[]).every(d=>d.severity!==1));});
    await check('unopened imports and cross-file definitions use the browser filesystem',async()=>{
      const result=await page.evaluate(async()=>{const ide=solidityIDE;ide.state.files['Base.sol']='// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34; contract Base { function value() public pure returns(uint256) { return 7; } }';ide.state.files['Derived.sol']='// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34; import "./Base.sol"; contract Derived is Base { function f() public pure returns(uint256) { return value(); } }';await ide.openFile('Derived.sol');const m=ide.editor.getModel(),p=m.getPositionAt(m.getValue().lastIndexOf('value()')+2);return ide.language('textDocument/definition',m,{position:{line:p.lineNumber-1,character:p.column-1}});});assert.match(result.uri,/Base\.sol$/);
    });
    await check('rename includes and validates a closed sibling importer',async()=>{
      const changes=await page.evaluate(async()=>{const ide=solidityIDE;ide.state.files['Sibling.sol']='// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34; import "./Base.sol"; contract Sibling is Base { function f() public pure returns(uint256) { return value(); } }';const m=ide.editor.getModel(),p=m.getPositionAt(m.getValue().lastIndexOf('value()')+2);const options={position:{line:p.lineNumber-1,character:p.column-1},newName:'renamedValue'};return ide.language('textDocument/rename',m,options);});
      assert.deepEqual(changes.documentChanges.map(c=>c.textDocument.uri.split('/').pop()).sort(),['Base.sol','Derived.sol','Sibling.sol']);
    });
    await check('an unresolved import produces a positioned Problems error',async()=>{
      await page.evaluate(async()=>{await solidityIDE.openFile('Counter.sol');solidityIDE.editor.setValue('// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34; import "./Missing.sol"; contract Counter {}');});
      await page.waitForFunction(()=>(solidityIDE.state.diagnostics.get('Counter.sol')||[]).some(d=>d.severity===1&&d.message.includes('Cannot resolve Solidity import')));
      await page.evaluate(()=>solidityIDE.editor.setValue(solidityIDE.state.baselines['Counter.sol']));await page.waitForFunction(()=>(solidityIDE.state.diagnostics.get('Counter.sol')||[]).every(d=>d.severity!==1));
    });
    await check('failed browser storage never marks an unsaved edit clean',async()=>{
      const result=await page.evaluate(async()=>{const ide=solidityIDE,original=ide.editor.getValue(),write=Storage.prototype.setItem;ide.editor.setValue(original+'\n// storage quota regression\n');Storage.prototype.setItem=function(){throw new DOMException('Storage quota exceeded','QuotaExceededError');};try{await ide.save();return {dirty:ide.state.dirty.has('Counter.sol'),baseline:ide.state.baselines['Counter.sol'],original,message:document.querySelector('#toast').textContent};}finally{Storage.prototype.setItem=write;ide.editor.setValue(original);}});
      assert.equal(result.dirty,true);assert.equal(result.baseline,result.original);assert.match(result.message,/storage is full/);
    });
    if(!withProofs)await check('compiler success never silently claims a kernel proof',async()=>{await page.evaluate(()=>solidityIDE.openFile('Counter.sol'));if(!single&&!fs.existsSync(path.resolve(__dirname,'../dist/lean/manifest.json'))){const proof=await page.evaluate(async()=>{try{return await solidityIDE.rpc('verify',{name:'Counter.sol',version:solidityIDE.editor.getModel().getVersionId()});}catch(error){return {error:error.message};}});assert.match(proof.error,/proof runtime is not installed/);}assert.equal(await page.evaluate(()=>solidityIDE.state.reports.size),0);});
    if(withProofs){
      await check('the exact Lean kernel boots entirely in a browser worker',async()=>{await page.waitForFunction(()=>solidityIDE.state.runtime.proofReady||solidityIDE.state.runtime.error,null,{timeout:600000});report.runtime=await page.evaluate(()=>solidityIDE.state.runtime);assert.equal(report.runtime.proofReady,true,report.runtime.error);assert.equal(report.runtime.lean,'4.24.0');});
      await check('real browser proofs match the extension and a false specification stays pending',async()=>{
        await page.evaluate(()=>solidityIDE.openFile('Counter.sol'));report.proofTrials=[];
        for(let trial=0;trial<2;trial++){const start=performance.now();const result=await page.evaluate(()=>solidityIDE.rpc('verify',{name:'Counter.sol',version:solidityIDE.editor.getModel().getVersionId()}));report.proofTrials.push({elapsedMs:+(performance.now()-start).toFixed(1),report:result});assert.deepEqual(result.errors,[]);assert.deepEqual(result.results.map(r=>[r.function,r.status]),[['increment','proved'],['reset','proved'],['one','proved'],['openGoal','pending']]);}
        const native=path.join(artifacts,'native-report.json');if(fs.existsSync(native)){const expected=JSON.parse(fs.readFileSync(native,'utf8')).trials[0].report.results.map(r=>[r.function,r.status]);assert.deepEqual(report.proofTrials[0].report.results.map(r=>[r.function,r.status]),expected);}
        await page.evaluate(()=>{solidityIDE.setView('testing');solidityIDE.showPanel('problems');});await page.mouse.move(1300,650);await page.screenshot({path:path.join(artifacts,'website-proofs.png')});
      });
      await check('editing terminates an active obsolete browser proof',async()=>{
        await page.evaluate(async()=>{solidityIDE.editor.setValue(solidityIDE.editor.getValue()+'\n// cancellation regression\n');await solidityIDE.language('textDocument/documentSymbol',solidityIDE.editor.getModel());window.cancelledProof=solidityIDE.rpc('verify',{name:'Counter.sol',version:solidityIDE.editor.getModel().getVersionId()}).then(()=>({finished:true}),error=>({error:error.message,code:error.code}));});
        await page.waitForFunction(()=>solidityIDE.state.statuses.get('Counter.sol')?.state==='running');
        await page.evaluate(()=>solidityIDE.editor.setValue(solidityIDE.state.baselines['Counter.sol']));
        const cancelled=await page.evaluate(()=>window.cancelledProof);assert.ok(['CANCELLED',-32801].includes(cancelled.code),JSON.stringify(cancelled));
        await page.waitForFunction(()=>!solidityIDE.state.reports.has('Counter.sol'));await page.waitForFunction(()=>solidityIDE.state.runtime.proofReady,null,{timeout:600000});
      });
      await check('an edited false result cannot retain a green proof',async()=>{
        await page.evaluate(()=>solidityIDE.editor.setValue(solidityIDE.editor.getValue().replace('return 1;','return 2;')));await page.waitForFunction(()=>!solidityIDE.state.reports.has('Counter.sol'));
        const result=await page.evaluate(async()=>{await solidityIDE.language('textDocument/documentSymbol',solidityIDE.editor.getModel());return solidityIDE.rpc('verify',{name:'Counter.sol',version:solidityIDE.editor.getModel().getVersionId(),function:'one()'});});assert.deepEqual(result.errors,[]);assert.equal(result.results.find(r=>r.function==='one').status,'pending');
        await page.evaluate(()=>solidityIDE.editor.setValue(solidityIDE.state.baselines['Counter.sol']));await page.waitForFunction(()=>!solidityIDE.state.reports.has('Counter.sol'));
      });
    }
    if(withProofs)await check('opt-in counterexamples are certified by the browser kernel',async()=>{
      const result=await page.evaluate(async()=>{await solidityIDE.language('textDocument/documentSymbol',solidityIDE.editor.getModel());return solidityIDE.rpc('verify',{name:'Counter.sol',version:solidityIDE.editor.getModel().getVersionId(),function:'openGoal()',counterexamples:true});});
      assert.deepEqual(result.errors,[]);const row=result.results.find(r=>r.function==='openGoal');assert.equal(row.status,'refuted');assert.ok(row.counterexample);report.counterexample=row;
    });
    await check(single&&!localFile?'a fully disconnected fresh browser runtime still compiles and proves new edits':'after one visit a fully disconnected reload still compiles new edits',async()=>{
      await page.evaluate(()=>solidityIDE.save());await app.close();serverClosed=true;report.staticServerStopped=true;await context.setOffline(true);
      if(single&&!localFile){await page.evaluate(()=>solidityIDE.restart());await page.waitForFunction(()=>!solidityIDE.state.connected);}
      else await page.reload();
      await page.waitForFunction(()=>window.solidityIDE?.state.connected,null,{timeout:60000});assert.equal(await page.evaluate(()=>solidityIDE.state.runtime.mode),'browser');
      if(localFile)assert.equal(await page.evaluate(()=>singleFileIDE.reused),true);
      await page.evaluate(()=>solidityIDE.editor.setValue(solidityIDE.editor.getValue().replace('return 1;','return ;!;')));await page.waitForFunction(()=>(solidityIDE.state.diagnostics.get('Counter.sol')||[]).some(d=>d.severity===1));
      await page.evaluate(()=>solidityIDE.editor.setValue(solidityIDE.state.baselines['Counter.sol']));await page.waitForFunction(()=>(solidityIDE.state.diagnostics.get('Counter.sol')||[]).every(d=>d.severity!==1));
      if(withProofs){
        await page.waitForFunction(()=>solidityIDE.state.runtime.proofReady,null,{timeout:600000});
        // Prove a semantically new program in this fresh disconnected worker,
        // not just the original source after checking a syntax-error edit.
        await page.evaluate(()=>solidityIDE.editor.setValue(solidityIDE.editor.getValue().replace('return 1;','return 3;').replace('ensures \\result == 1','ensures \\result == 3')));
        const start=performance.now();
        const result=await page.evaluate(async()=>{await solidityIDE.language('textDocument/documentSymbol',solidityIDE.editor.getModel());return solidityIDE.rpc('verify',{name:'Counter.sol',version:solidityIDE.editor.getModel().getVersionId()});});
        const source=await page.evaluate(()=>solidityIDE.editor.getValue()),sourceHash=require('node:crypto').createHash('sha256').update(source).digest('hex');
        report.offlineProof={elapsedMs:+(performance.now()-start).toFixed(1),sourceHash,report:result};
        assert.deepEqual(result.errors,[]);
        assert.deepEqual(result.results.map(r=>[r.function,r.status]),[['increment','proved'],['reset','proved'],['one','proved'],['openGoal','pending']]);
        for(const row of result.results)assert.equal(row.sourceHash,sourceHash);
      }
      await page.screenshot({path:path.join(artifacts,withProofs?'website-offline-proofs.png':'website-offline-compiler.png')});
    });
    if(single)assert.deepEqual(report.documentRequests,[documentURL,documentURL]);
    assert.deepEqual(report.requests,[]);assert.deepEqual(report.webSockets,[]);assert.deepEqual(report.errors,[]);report.passed=true;
  }catch(error){await page.screenshot({path:path.join(artifacts,'website-failure.png')});console.log(await page.evaluate(()=>({runtime:window.solidityIDE?.state.runtime,logs:window.solidityIDE?.state.logs})));throw error;}
  finally{await context.close();fs.rmSync(profile,{recursive:true,force:true});if(!serverClosed)await app.close();fs.mkdirSync(artifacts,{recursive:true});fs.writeFileSync(path.join(artifacts,localFile?'single-file-disk-report.json':published?'published-report.json':single?'single-file-report.json':'website-report.json'),JSON.stringify(report,null,2)+'\n');}
}
main().catch(error=>{console.error(error);process.exitCode=1;});
