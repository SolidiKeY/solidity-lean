'use strict';
// Real compiler and compiled verifier in a fresh Chromium profile. Every
// submission changes the live editor; result-cache hits are excluded.
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {chromium}=require('playwright');
const {createStaticServer}=require('../tools/serve-static.cjs');
const root=path.resolve(__dirname,'../..'),directory=path.join(root,'.lake/testsuite-performance');
const inputs=JSON.parse(fs.readFileSync(path.join(directory,'inputs.json'),'utf8'));
const single=!process.argv.includes('--static');
async function main(){
 const {validateInputs}=await import('../../scripts/testsuite-performance.mjs');validateInputs(inputs);
 const app=createStaticServer({port:0,...(single?{root:path.join(root,'web/single-file')}:{})}),url=await app.listen();
 const profile=fs.mkdtempSync(path.join(directory,'chromium-'));
 const report={...(single?{assetBuild:JSON.parse(fs.readFileSync(path.join(root,'web/single-file/build.json'),'utf8')).build}:{}),startedAt:new Date().toISOString(),inventorySha256:inputs.inventorySha256,single,trials:[],errors:[],external:[]};
 let context;
 try{
  context=await chromium.launchPersistentContext(profile,{executablePath:process.env.CHROMIUM_PATH||'/usr/bin/chromium',args:['--no-sandbox'],viewport:{width:1440,height:900}});
  context.on('request',r=>{if(!/^(blob:|data:)/.test(r.url())&&!r.url().startsWith(url))report.external.push(r.url());});
  const page=context.pages()[0]||await context.newPage();page.on('pageerror',e=>report.errors.push(e.message));
  const start=performance.now();await page.goto(url,{timeout:120000});
  await page.waitForFunction(()=>window.solidityIDE?.state.connected&&(solidityIDE.state.runtime.proofReady||solidityIDE.state.runtime.error),null,{timeout:120000});
  report.startupMs=performance.now()-start;if(single)assert.equal(await page.evaluate(()=>singleFileIDE.build),report.assetBuild);report.runtime=await page.evaluate(()=>solidityIDE.state.runtime);
  assert.equal(report.runtime.proofReady,true,report.runtime.error);assert.equal(report.runtime.verifier,'generated-c-wasm');
  await page.evaluate(()=>solidityIDE.rpc('configure',{automaticVerification:'never'}));
  for(let round=0;round<Number(process.env.TESTSUITE_REPEATS||3);round++)for(const input of inputs.trials){
   const text=fs.readFileSync(input.source,'utf8'),before=performance.now();
   const result=await page.evaluate(async({text,name})=>{
    solidityIDE.editor.setValue(text);
    return solidityIDE.rpc('verify',{name:'Counter.sol',version:solidityIDE.editor.getModel().getVersionId(),function:name});
   },{text,name:input.name});
   assert.deepEqual(result.errors,[]);assert.equal(result.results.length,1);
   assert.equal(result.results[0].status,'proved',input.name);assert.equal(result.results[0].function,input.name);assert.equal(result.results[0].sourceHash,input.sourceHash);
   assert.deepEqual(result.timings.kernelChecks,[]);assert.equal(result.timings.directChecks.length,1);
   assert.equal(result.timings.directChecks[0].environmentImports,0);
   report.trials.push({name:input.name,round,sourceHash:input.sourceHash,wallMs:performance.now()-before,...result});
  }
  assert.deepEqual(report.trials.map(t=>t.timings.directChecks[0].checkSequence),report.trials.map((_,i)=>i+1));
  assert.deepEqual(report.errors,[]);assert.deepEqual(report.external,[]);report.passed=true;
 }finally{
  await context?.close();await app.close();fs.rmSync(profile,{recursive:true,force:true});
  fs.writeFileSync(path.join(directory,'browser.json'),JSON.stringify(report,null,2)+'\n');
 }
 console.log(JSON.stringify({passed:report.passed,startupMs:report.startupMs,trials:report.trials.length}));
}
main().catch(error=>{console.error(error);process.exitCode=1;});
