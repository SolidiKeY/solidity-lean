'use strict';
// Capture a fresh, real browser-only proof state matching the isolated extension.
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {chromium}=require('playwright');
require(path.join(path.dirname(require.resolve('playwright-core/package.json')),'lib/coreBundle.js')).server.setMaxDispatchersForTest(100);
const {createStaticServer}=require('../tools/serve-static.cjs');
const artifacts=path.resolve(__dirname,'../artifacts');
async function main(){
  const app=createStaticServer({port:0}),url=await app.listen();
  const profiles=path.join(artifacts,'browser-profiles');fs.mkdirSync(profiles,{recursive:true});
  const profile=fs.mkdtempSync(path.join(profiles,'reference-'));
  const context=await chromium.launchPersistentContext(profile,{executablePath:process.env.CHROMIUM_PATH||'/usr/bin/chromium',args:['--no-sandbox'],viewport:{width:1440,height:900},deviceScaleFactor:1,colorScheme:'dark'});
  await context.addInitScript(()=>{globalThis.WebSocket=class{constructor(){throw new Error('No backend connection is permitted');}};});
  const page=await context.newPage(),errors=[],external=[];
  page.on('pageerror',error=>errors.push(error.message));
  context.on('request',request=>{if(new URL(request.url()).origin!==url)external.push(request.url());});
  const result={startedAt:new Date().toISOString(),trials:[]};
  try{
    const start=performance.now();await page.goto(url);
    await page.waitForFunction(()=>window.solidityIDE?.state.connected&&(solidityIDE.state.runtime.proofReady||solidityIDE.state.runtime.error),{timeout:600000});
    assert.equal(await page.evaluate(()=>solidityIDE.state.runtime.proofReady),true,await page.evaluate(()=>solidityIDE.state.runtime.error));
    result.runtime=await page.evaluate(()=>solidityIDE.state.runtime);result.assetBuild=JSON.parse(fs.readFileSync(path.join(__dirname,'../dist/asset-manifest.json'),'utf8')).build;
    await page.evaluate(()=>solidityIDE.language('textDocument/documentSymbol',solidityIDE.editor.getModel()));
    result.startupMs=+(performance.now()-start).toFixed(1);
    result.source=await page.evaluate(()=>solidityIDE.editor.getValue());
    const reference=JSON.parse(fs.readFileSync(path.join(artifacts,'native-report.json'),'utf8'));
    assert.equal(result.source,reference.source);
    for(let trial=0;trial<2;trial++){
      const then=performance.now();const report=await page.evaluate(()=>solidityIDE.rpc('verify',{name:'Counter.sol',version:solidityIDE.editor.getModel().getVersionId()}));
      assert.deepEqual(report.errors,[]);assert.deepEqual(report.results.map(row=>[row.function,row.status]),reference.trials[0].report.results.map(row=>[row.function,row.status]));
      result.trials.push({elapsedMs:+(performance.now()-then).toFixed(1),report});
    }
    result.hover=await page.evaluate(()=>solidityIDE.language('textDocument/hover',solidityIDE.editor.getModel(),{position:{line:17,character:14}}));
    assert.match(result.hover.contents.value,/Counter\.one\(\): proved/);
    result.diagnostics=await page.evaluate(()=>solidityIDE.state.diagnostics.get('Counter.sol'));
    await page.evaluate(()=>{solidityIDE.setView('testing');solidityIDE.showPanel('problems');solidityIDE.editor.setPosition({lineNumber:1,column:1});});
    await page.mouse.move(1300,650);await page.waitForTimeout(250);
    await page.screenshot({path:path.join(artifacts,'website-problems.png')});
    assert.deepEqual(external,[]);assert.deepEqual(errors,[]);result.passed=true;
    console.log(JSON.stringify({passed:true,startupMs:result.startupMs,trialMs:result.trials.map(t=>t.elapsedMs)}));
  }catch(error){result.error=error.stack;result.logs=await page.evaluate(()=>solidityIDE.state.logs);console.error(JSON.stringify(result.logs,null,2));throw error;}finally{
    fs.writeFileSync(path.join(artifacts,'website-reference-report.json'),JSON.stringify({...result,errors,external},null,2)+'\n');
    await context.close();fs.rmSync(profile,{recursive:true,force:true});await app.close();
  }
}
main().catch(error=>{console.error(error);process.exitCode=1;});
