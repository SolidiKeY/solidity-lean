'use strict';
// Fresh-profile, real edited-source measurements. Cached retrieval is a
// separate control and must never be reported as proof execution throughput.
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {chromium}=require('playwright');
const {createHash}=require('node:crypto');
require(path.join(path.dirname(require.resolve('playwright-core/package.json')),'lib/coreBundle.js')).server.setMaxDispatchersForTest(100);
const {createStaticServer}=require('../tools/serve-static.cjs');
const single=process.argv.includes('--single'),artifacts=path.resolve(__dirname,'../artifacts');
const calldataProofs=process.argv.includes('--calldata-proofs');
async function main(){
  const app=createStaticServer({port:0,...(single?{root:path.resolve(__dirname,'../single-file')}:{} )}),url=await app.listen();
  fs.mkdirSync(path.join(artifacts,'browser-profiles'),{recursive:true});
  const profile=fs.mkdtempSync(path.join(artifacts,'browser-profiles/performance-'));
  let context,page;
  const report={startedAt:new Date().toISOString(),singleFile:single,calldataProofs,trials:[],errors:[],external:[]};
  try{
    context=await chromium.launchPersistentContext(profile,{executablePath:process.env.CHROMIUM_PATH||'/usr/bin/chromium',args:['--no-sandbox'],viewport:{width:1440,height:900}});
    await context.addInitScript(()=>{globalThis.WebSocket=class{constructor(){throw new Error('No proof backend is permitted');}};});
    context.on('request',request=>{if(!/^(blob:|data:)/.test(request.url())&&new URL(request.url()).origin!==url)report.external.push(request.url());});
    page=await context.newPage();page.on('pageerror',e=>report.errors.push(e.message));
    const start=performance.now();await page.goto(url,{timeout:300000});
    await page.waitForFunction(()=>window.solidityIDE?.state.connected&&(solidityIDE.state.runtime.proofReady||solidityIDE.state.runtime.error),null,{timeout:600000});
    assert.equal(await page.evaluate(()=>solidityIDE.state.runtime.proofReady),true);
    report.runtime=await page.evaluate(()=>solidityIDE.state.runtime);
    report.startupMs=performance.now()-start;
    if(single)report.embedded=await page.evaluate(()=>({build:singleFileIDE.build,preparationMs:singleFileIDE.preparationMs,reused:singleFileIDE.reused}));
    await page.evaluate(()=>solidityIDE.language('textDocument/documentSymbol',solidityIDE.editor.getModel()));
    const expected=[['increment','proved'],['reset','proved'],['one','proved'],['openGoal','pending']];
    async function verify(label,expected,options={}){
      const start=performance.now();const result=await page.evaluate(options=>solidityIDE.rpc('verify',{name:'Counter.sol',version:solidityIDE.editor.getModel().getVersionId(),...options}),options);
      assert.deepEqual(result.errors,[]);const statuses=result.results.map(r=>[r.function,r.status]);assert.deepEqual(statuses,expected);
      const elapsedMs=performance.now()-start;
      const sourceHash=createHash('sha256').update(await page.evaluate(()=>solidityIDE.editor.getValue())).digest('hex');
      for(const row of result.results)assert.equal(row.sourceHash,sourceHash,'each result must belong to the exact edited source');
      const trial={label,elapsedMs,statuses,timings:result.timings};report.trials.push(trial);console.log(JSON.stringify(trial));
    }
    await verify('cold proof including library preparation',expected);
    report.firstResultMs=performance.now()-start;
    const libraries=await page.evaluate(async()=>(await(await fetch('/lean/manifest.json')).json()).libraries);
    report.serializedLibraryBytes=libraries.reduce((sum,entry)=>sum+entry.size,0);
    assert.ok(report.serializedLibraryBytes<2500000000,'the browser library footprint must stay below the old broad-import build');
    for(const check of report.trials[0].timings.kernelChecks){
      assert.ok(check.libraries.inflatedBytes<=report.serializedLibraryBytes*1.01,'a cold import must not reinflate the environment in its IR pass');
      if(single){assert.equal(check.libraries.prefetchedBytes,0);assert.equal(check.libraries.fallbacks,0);assert.ok(check.libraries.directReads>0);}
    }
    await verify('unchanged cached result',expected);
    await page.evaluate(async()=>{solidityIDE.editor.setValue(solidityIDE.editor.getValue()+'\n// new source: measure a real recheck\n');await solidityIDE.language('textDocument/documentSymbol',solidityIDE.editor.getModel());});
    await verify('real proof after comment edit',expected);
    await page.evaluate(async()=>{solidityIDE.editor.setValue(solidityIDE.editor.getValue().replace('return 1;','return 2;'));await solidityIDE.language('textDocument/documentSymbol',solidityIDE.editor.getModel());});
    await verify('real proof after false-result edit',[['increment','proved'],['reset','proved'],['one','pending'],['openGoal','pending']]);
    await page.evaluate(async()=>{solidityIDE.editor.setValue(solidityIDE.editor.getValue().replace('ensures \\result == 1','ensures \\result == 2'));await solidityIDE.language('textDocument/documentSymbol',solidityIDE.editor.getModel());});
    await verify('real proof after updating the changed result specification',expected);
    // Exercise admission in the actual interpreter. Listing does not claim a
    // proof. --calldata-proofs additionally reproduces the known deep-simp
    // browser stack limit, and must succeed before claiming proof parity here.
    await page.evaluate(async()=>{
      solidityIDE.editor.setValue(`// SPDX-License-Identifier: MIT
pragma solidity ^0.8.34;
contract CalldataViews {
  /// @custom:key box
  function localAlias(uint[] calldata xs) external pure {
    uint[] calldata ys = xs;
    require(ys.length > 0);
    assert(ys[0] == xs[0]);
  }
  /// @custom:key box
  function sliceRead(uint[] calldata xs, uint k) external pure {
    uint[] calldata t = xs[1:];
    assert(t[k] == xs[1 + k]);
  }
  function writesCopy(uint[] calldata xs) external pure {
    uint[] memory m = xs;
    m[0] = 1;
  }
}`);
      await solidityIDE.language('textDocument/documentSymbol',solidityIDE.editor.getModel());
    });
    await verify(calldataProofs?'calldata proof-search regression':'calldata admission only (listing, no proof execution)',[['localAlias',calldataProofs?'proved':'ready'],['sliceRead',calldataProofs?'proved':'ready'],['writesCopy','unsupported']],{listing:!calldataProofs});
    assert.deepEqual(report.errors,[]);assert.deepEqual(report.external,[]);report.passed=true;
  }catch(error){
    report.failure=error.stack;
    report.runtimeLogs=await page?.evaluate(()=>window.solidityIDE?.state.logs).catch(()=>[]);
    throw error;
  }finally{
    await context?.close();await app.close();fs.rmSync(profile,{recursive:true,force:true});
    fs.writeFileSync(path.join(artifacts,single?'performance-single-report.json':'performance-report.json'),JSON.stringify(report,null,2)+'\n');
  }
}
main().catch(error=>{console.error(error);process.exitCode=1;});
