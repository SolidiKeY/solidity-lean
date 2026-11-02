'use strict';
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {createHash}=require('node:crypto');
const {chromium}=require('playwright');
const {createStaticServer}=require('../tools/serve-static.cjs');
const cases=require('./simple-programs.cjs');
const args=process.argv.slice(2),single=args.includes('--single');
const repeats=Number(process.env.BENCH_REPEATS||3);
assert.ok(Number.isSafeInteger(repeats)&&repeats>0);
const output=path.resolve(process.env.BENCH_REPORT||path.join(__dirname,'../artifacts/simple-browser-report.json'));
async function main(){
  const app=createStaticServer({port:0,...(single?{root:path.resolve(__dirname,'../single-file')}:{} )}),url=await app.listen();
  fs.mkdirSync(path.dirname(output),{recursive:true});
  fs.mkdirSync(path.join(__dirname,'../artifacts/browser-profiles'),{recursive:true});
  const profile=fs.mkdtempSync(path.join(__dirname,'../artifacts/browser-profiles/simple-'));
  const report={startedAt:new Date().toISOString(),singleFile:single,repeats,trials:[],errors:[],external:[]};
  let context,page;
  try{
    context=await chromium.launchPersistentContext(profile,{executablePath:process.env.CHROMIUM_PATH||'/usr/bin/chromium',args:['--no-sandbox'],viewport:{width:1440,height:900}});
    await context.addInitScript(()=>{globalThis.WebSocket=class{constructor(){throw new Error('No proof backend is permitted');}};});
    context.on('request',request=>{if(!/^(blob:|data:)/.test(request.url())&&new URL(request.url()).origin!==url)report.external.push(request.url());});
    page=context.pages()[0];page.on('pageerror',e=>report.errors.push(e.message));
    const startup=performance.now();await page.goto(url,{timeout:300000});
    await page.waitForFunction(()=>window.solidityIDE?.state.runtime.proofReady||window.solidityIDE?.state.runtime.error,null,{timeout:600000});
    assert.equal(await page.evaluate(()=>solidityIDE.state.runtime.proofReady),true);
    report.startupMs=performance.now()-startup;report.runtime=await page.evaluate(()=>solidityIDE.state.runtime);
    report.artifact=single?JSON.parse(fs.readFileSync(path.join(__dirname,'../single-file/build.json'),'utf8')):null;
    for(let repeat=0;repeat<repeats;repeat++)for(const example of cases){
      // Every run has different source bytes and a new editor version. A warm
      // process must still import the model, search and check a fresh proof.
      const source=example.source+`\n// measurement repetition ${repeat}\n`;
      const start=performance.now();
      await page.evaluate(source=>solidityIDE.editor.setValue(source),source);
      await page.evaluate(()=>solidityIDE.language('textDocument/documentSymbol',solidityIDE.editor.getModel()));
      const compilationMs=performance.now()-start,proofStart=performance.now();
      const result=await page.evaluate(()=>solidityIDE.rpc('verify',{name:'Counter.sol',version:solidityIDE.editor.getModel().getVersionId(),benchmark:true}));
      assert.deepEqual(result.errors,[]);
      assert.deepEqual(result.results.map(row=>[row.function,row.status]),[['run',example.status]]);
      const sourceHash=createHash('sha256').update(source).digest('hex');
      assert.ok(result.results.every(row=>row.sourceHash===sourceHash));
      assert.equal(result.timings.kernelChecks.length,1);
      assert.ok(result.timings.kernelChecks[0].phases.some(phase=>phase.phase==='search'),'must execute a real search');
      const trial={name:example.name,repeat,sourceHash,compilationMs,proofMs:performance.now()-proofStart,totalMs:performance.now()-start,results:result.results,timings:result.timings};
      report.trials.push(trial);console.log(JSON.stringify(trial));
    }
    await page.screenshot({path:output.replace(/\.json$/,'.png')});
    assert.deepEqual(report.errors,[]);assert.deepEqual(report.external,[]);report.passed=true;
  }catch(error){report.failure=error.stack;report.logs=await page?.evaluate(()=>solidityIDE.state.logs).catch(()=>[]);throw error;}
  finally{await context?.close();await app.close();fs.rmSync(profile,{recursive:true,force:true});fs.writeFileSync(output,JSON.stringify(report,null,2)+'\n');}
}
main().catch(error=>{console.error(error);process.exitCode=1;});
