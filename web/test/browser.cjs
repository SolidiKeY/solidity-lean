'use strict';
// Runs the real browser, local compiler and extension language server. Proofs
// are opt-in because a fresh checkout may first need its bounded Lean build.
const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const {chromium} = require('playwright');
const {createServer} = require('../server.cjs');
const artifacts = path.resolve(__dirname,'../artifacts');
const proofs = process.argv.includes('--proofs');
const report = {startedAt:new Date().toISOString(), proofs, checks:[], externalRequests:[], pageErrors:[]};
async function main(){
  fs.mkdirSync(artifacts,{recursive:true});
  const app=createServer({port:0});const url=await app.listen();
  const executablePath=process.env.CHROMIUM_PATH || (fs.existsSync('/usr/bin/chromium')?'/usr/bin/chromium':undefined);
  const browser=await chromium.launch({executablePath,headless:true,args:['--no-sandbox','--disable-dev-shm-usage']});
  const context=await browser.newContext({viewport:{width:1440,height:900},deviceScaleFactor:1});
  await context.route('**/*',route=>{const request=route.request().url();if(new URL(request).origin===url)return route.continue();report.externalRequests.push(request);return route.abort();});
  const page=await context.newPage();page.on('pageerror',error=>{report.pageErrors.push(error.message);console.log('BROWSER ERROR',error.stack);});
  async function check(name,run){const start=performance.now();await run();report.checks.push({name,elapsedMs:+(performance.now()-start).toFixed(1)});console.log('PASS',name);}
  async function ready(){await page.waitForFunction(()=>window.solidityIDE?.ready,{timeout:60000});await page.waitForFunction(()=>solidityIDE.state.connected);}
  try{
    await check('cold startup, local assets, shared Solidity syntax and compiler symbols',async()=>{
      const start=performance.now();await page.goto(url+'/?backend=native');await ready();report.startupMs=+(performance.now()-start).toFixed(1);
      await page.waitForFunction(()=>solidityIDE.state.symbols.get('Counter.sol')?.some(s=>s.name==='Counter'));
      assert.equal(await page.evaluate(()=>solidityIDE.editor.getModel().getLanguageId()),'solidity');
      assert.equal(await page.evaluate(()=>solidityIDE.editor.getModel().getOptions().bracketPairColorizationOptions.enabled),false);
      assert.equal(await page.evaluate(()=>monaco.editor.tokenize('contract Counter {}','solidity')[0][0].type),'keyword.control.solidity');
      await page.screenshot({path:path.join(artifacts,'web-explorer.png')});
    });
    await check('command palette, panel switching and workspace search',async()=>{
      await page.keyboard.press('F1');await page.getByRole('textbox',{name:'Type a command'}).fill('>View: Output');await page.keyboard.press('Enter');
      assert.equal(await page.evaluate(()=>solidityIDE.state.panel),'output');
      await page.getByRole('button',{name:'Search',exact:true}).click();await page.getByRole('textbox',{name:'Search workspace'}).fill('openGoal');
      assert.match(await page.locator('#sidebar-content').innerText(),/openGoal/);
      await page.getByRole('button',{name:'Explorer',exact:true}).click();
    });
    await check('language services on exact unsaved source: completion, hover, definition and references',async()=>{
      await page.evaluate(()=>solidityIDE.openFile('Identity.sol'));
      const services=await page.evaluate(async()=>{
        const ide=solidityIDE,m=ide.editor.getModel(),text=m.getValue(),offset=text.indexOf('identity(1)')+2,p=m.getPositionAt(offset),position={line:p.lineNumber-1,character:p.column-1};
        return {completion:await ide.language('textDocument/completion',m,{position}),hover:await ide.language('textDocument/hover',m,{position}),definition:await ide.language('textDocument/definition',m,{position}),references:await ide.language('textDocument/references',m,{position,context:{includeDeclaration:true}})};
      });
      assert.ok(services.completion.items.some(i=>i.label==='identity'));assert.match(services.hover.contents.value,/identity/);assert.equal(services.definition.range.start.line,5);assert.equal(services.references.length,2);
    });
    await check('real Monaco rename provider updates declaration and call',async()=>{
      await page.evaluate(()=>{const m=solidityIDE.editor.getModel();solidityIDE.editor.setPosition(m.getPositionAt(m.getValue().indexOf('identity(1)')+2));solidityIDE.editor.focus();});
      await page.keyboard.press('F2');const input=page.locator('.rename-box input');await input.waitFor();await input.fill('echoValue');await input.press('Enter');
      await page.waitForFunction(()=>solidityIDE.editor.getValue().includes('return echoValue(1)'));
      assert.match(await page.evaluate(()=>solidityIDE.editor.getValue()),/function echoValue/);
    });
    await check('compiler formatting and save retain current buffer identity',async()=>{
      await page.evaluate(async()=>{solidityIDE.editor.setValue(solidityIDE.editor.getValue().replace('contract Identity {','contract Identity{'));await solidityIDE.editor.getAction('editor.action.formatDocument').run();});
      assert.match(await page.evaluate(()=>solidityIDE.editor.getValue()),/contract Identity \{/);
      await page.evaluate(()=>solidityIDE.save());assert.equal(await page.evaluate(()=>solidityIDE.state.dirty.has('Identity.sol')),false);
      const race=await page.evaluate(async()=>{const ide=solidityIDE;ide.editor.setValue(ide.editor.getValue()+'\n// before save\n');const pending=ide.save();ide.editor.setValue(ide.editor.getValue()+'// after save\n');await ide.openFile('Counter.sol');await pending;return {identityDirty:ide.state.dirty.has('Identity.sol'),counterDirty:ide.state.dirty.has('Counter.sol')};});
      assert.equal(race.identityDirty,true);assert.equal(race.counterDirty,false);
    });
    await check('unopened imports compile and F12 opens the target file',async()=>{
      await page.evaluate(async()=>{const ide=solidityIDE;ide.state.files['Base.sol']='// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34; contract Base { function value() public pure returns(uint256) { return 7; } }\n';ide.state.files['Derived.sol']='// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34; import "./Base.sol"; contract Derived is Base { function callValue() public pure returns(uint256) { return value(); } }\n';await ide.openFile('Derived.sol');});
      await page.waitForFunction(()=>solidityIDE.state.symbols.get('Derived.sol')?.some(s=>s.name==='Derived'));
      assert.equal(await page.evaluate(()=>(solidityIDE.state.diagnostics.get('Derived.sol')||[]).filter(d=>d.severity===1).length),0);
      await page.evaluate(()=>{const m=solidityIDE.editor.getModel();solidityIDE.editor.setPosition(m.getPositionAt(m.getValue().lastIndexOf('value()')+2));solidityIDE.editor.focus();});
      await page.keyboard.press('F12');await page.waitForFunction(()=>solidityIDE.state.active==='Base.sol');
    });
    await check('rapid edits in two files synchronize both latest versions',async()=>{
      const versions=await page.evaluate(async()=>{const ide=solidityIDE;const base=ide.state.models.get('Base.sol');const derived=ide.state.models.get('Derived.sol');base.setValue(base.getValue()+'// latest base\n');derived.setValue(derived.getValue()+'// latest derived\n');await ide.language('textDocument/documentSymbol',derived);return [...ide.state.models].map(([name,m])=>({name,current:m.getVersionId(),synced:ide.state.synced.get(name)?.version}));});
      assert.ok(versions.every(row=>row.current===row.synced));
      await page.getByRole('button',{name:'Close Base.sol',exact:true}).click();
      await page.waitForFunction(()=>!solidityIDE.state.models.has('Base.sol'));
      await page.evaluate(()=>solidityIDE.openFile('Derived.sol'));
      const definition=await page.evaluate(async()=>{const ide=solidityIDE,m=ide.editor.getModel(),p=m.getPositionAt(m.getValue().lastIndexOf('value()')+2);return ide.language('textDocument/definition',m,{position:{line:p.lineNumber-1,character:p.column-1}});});
      assert.match(definition.uri,/Base\.sol$/);
    });
    await check('local changes diff, settings, and versioned compiler diagnostics',async()=>{
      await page.getByRole('button',{name:'Local changes',exact:true}).click();await page.locator('#sidebar-content .file-row').first().click();await page.locator('.diff-dialog').waitFor();await page.getByRole('button',{name:'Close comparison'}).click();
      await page.getByRole('button',{name:'Settings',exact:true}).click();await page.locator('#worker-setting').selectOption('1');
      await page.evaluate(()=>solidityIDE.openFile('Counter.sol'));
      await page.evaluate(()=>solidityIDE.editor.setValue(solidityIDE.editor.getValue().replace('return 1;','return ;!;')));
      await page.waitForFunction(()=>(solidityIDE.state.diagnostics.get('Counter.sol')||[]).some(d=>d.severity===1));
      await page.evaluate(()=>solidityIDE.showPanel('problems'));await page.screenshot({path:path.join(artifacts,'web-compiler-error.png')});
      await page.evaluate(()=>solidityIDE.editor.setValue(solidityIDE.state.baselines['Counter.sol']));
      await page.waitForFunction(()=>(solidityIDE.state.diagnostics.get('Counter.sol')||[]).every(d=>d.severity!==1));
    });
    if(proofs){
      await check('real kernel proofs, pending false obligation, warm cache and proof hover',async()=>{
        for(const name of ['Identity.sol','Derived.sol']){await page.locator('.tab').filter({hasText:name}).hover();await page.getByRole('button',{name:`Close ${name}`,exact:true}).click();await page.waitForFunction(name=>!solidityIDE.state.models.has(name),name);}
        await page.evaluate(()=>{delete solidityIDE.state.files['Base.sol'];delete solidityIDE.state.files['Derived.sol'];});
        await page.evaluate(()=>solidityIDE.openFile('Counter.sol'));
        const cold=await page.evaluate(()=>solidityIDE.verify());assert.ok(cold, 'verification must complete');assert.deepEqual(cold.errors,[]);
        assert.equal(cold.results.find(r=>r.function==='one').status,'proved');assert.equal(cold.results.find(r=>r.function==='openGoal').status,'pending');
        report.proofReport=cold;report.proofDiagnostics=await page.evaluate(()=>solidityIDE.state.diagnostics.get('Counter.sol'));
        const warm=await page.evaluate(()=>solidityIDE.verify());assert.equal(warm.results.find(r=>r.function==='one').status,'proved');
        report.proofTimings=await page.evaluate(()=>solidityIDE.state.timing);report.backendStats=await page.evaluate(()=>solidityIDE.rpc('stats'));
        assert.ok(report.backendStats.cacheHits>=1);await page.screenshot({path:path.join(artifacts,'web-verified.png')});
        await page.locator('[data-panel="problems"]').click();await page.mouse.move(1300,650);await page.screenshot({path:path.join(artifacts,'web-problems.png')});
        const hover=await page.evaluate(()=>solidityIDE.language('textDocument/hover',solidityIDE.editor.getModel(),{position:{line:17,character:15}}));assert.match(hover.contents.value,/proved/);
      });
      await check('Testing filters and function gutter execute the exact selected obligation',async()=>{
        const filter=page.getByRole('textbox',{name:'Filter verification tests'});await filter.fill('@pending');assert.equal(await page.locator('.test-row:visible').count(),1);assert.match(await page.locator('.test-row:visible').innerText(),/openGoal/);await filter.fill('');
        const before=await page.evaluate(()=>solidityIDE.state.timing.length);const rect=await page.locator('#editor').boundingBox();const line=await page.evaluate(()=>solidityIDE.editor.getScrolledVisiblePosition({lineNumber:18,column:1}));await page.mouse.click(rect.x+10,rect.y+line.top+10);
        await page.waitForFunction(before=>solidityIDE.state.timing.length>before,before);const latest=await page.evaluate(()=>solidityIDE.state.timing.at(-1));assert.deepEqual(latest.results,[{function:'one()',status:'proved'}]);
        assert.equal(await page.evaluate(()=>solidityIDE.state.reports.get('Counter.sol').results.find(r=>r.function==='openGoal').status),'pending');
      });
      await check('editing clears every dependent proof immediately',async()=>{
        const clear=await page.evaluate(()=>{solidityIDE.editor.setValue(solidityIDE.editor.getValue()+'// invalidate\n');return {reports:solidityIDE.state.reports.size,decorations:[...solidityIDE.state.statuses].length};});assert.equal(clear.reports,0);assert.equal(clear.decorations,0);
      });
    }
    await check('first visit caches Monaco dependencies; fully disconnected reload still edits',async()=>{
      // A brand-new profile with exactly one initial page load catches missing
      // first-load AMD chunks that a warm profile would hide.
      const offlineContext=await browser.newContext({viewport:{width:1440,height:900}});const offlinePage=await offlineContext.newPage();offlinePage.on('pageerror',error=>report.pageErrors.push(error.message));
      await offlinePage.goto(url+'/?backend=native');await offlinePage.waitForFunction(()=>window.solidityIDE?.ready);
      await offlinePage.evaluate(()=>navigator.serviceWorker.ready);await offlinePage.waitForTimeout(500);
      await offlineContext.setOffline(true);await offlinePage.reload();await offlinePage.waitForFunction(()=>window.solidityIDE?.ready,{timeout:30000});
      await offlinePage.evaluate(()=>solidityIDE.editor.setValue(solidityIDE.editor.getValue()+'\n// edited while fully disconnected\n'));
      assert.match(await offlinePage.evaluate(()=>solidityIDE.editor.getValue()),/fully disconnected/);
      assert.equal(await offlinePage.evaluate(()=>solidityIDE.state.reports.size),0);
      await offlinePage.screenshot({path:path.join(artifacts,'web-disconnected.png')});await offlinePage.waitForTimeout(200);
      await offlineContext.setOffline(false);await offlinePage.reload();await offlinePage.waitForFunction(()=>window.solidityIDE?.ready);assert.match(await offlinePage.evaluate(()=>solidityIDE.editor.getValue()),/fully disconnected/);
      await offlineContext.close();
    });
    await check('responsive layout and command palette remain usable at 768px',async()=>{await page.setViewportSize({width:768,height:900});await page.keyboard.press('F1');await page.screenshot({path:path.join(artifacts,'web-narrow.png')});await page.keyboard.press('Escape');await page.setViewportSize({width:1440,height:900});});
    assert.deepEqual(report.externalRequests,[]);assert.deepEqual(report.pageErrors,[]);report.passed=true;
  }finally{await context.close();await browser.close();await app.close();fs.writeFileSync(path.join(artifacts,'browser-report.json'),JSON.stringify(report,null,2)+'\n');}
}
main().catch(error=>{console.error(error);process.exitCode=1;});
