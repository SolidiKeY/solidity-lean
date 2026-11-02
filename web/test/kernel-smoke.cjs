'use strict';
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict');
const {chromium}=require('playwright');
const {createStaticServer}=require('../tools/serve-static.cjs');
async function main(){
  const app=createStaticServer({port:0}),url=await app.listen();
  const browser=await chromium.launch({executablePath:process.env.CHROMIUM_PATH||'/usr/bin/chromium',args:['--no-sandbox']});
  const page=await browser.newPage();page.on('console',message=>console.log(new Date().toISOString(),message.text()));const report={startedAt:new Date().toISOString()};
  try{
    await page.goto(url+'/bootstrap.json');const start=performance.now();
    report.boot=await page.evaluate(()=>{
      const kernel=new Worker('/kernel-worker.js');window.kernel=kernel;window.kernelTasks=new Map();window.kernelLogs=[];
      kernel.onmessage=event=>{const message=event.data;if(message.method==='log'){kernelLogs.push(message.message);console.log('KERNEL',message.message);return;}if(message.method==='progress'){window.kernelProgress=message;if(message.loaded%200===0||message.loaded===message.total)console.log('LIBRARIES',message.loaded,message.total);return;}const task=kernelTasks.get(message.id);if(!task)return;kernelTasks.delete(message.id);if(message.error)task.reject(new Error(message.error.message+'\n'+(message.error.stderr||[]).join('\n')+'\n'+(message.error.stack||'')));else task.resolve(message.result);};
      window.kernelRequest=(id,method,params={})=>new Promise((resolve,reject)=>{const timer=setTimeout(()=>{kernel.terminate();reject(new Error('Kernel smoke check timed out'));},600000);kernelTasks.set(id,{resolve:value=>{clearTimeout(timer);resolve(value);},reject:error=>{clearTimeout(timer);reject(error);}});kernel.postMessage({id,method,params});});
      kernel.onerror=error=>{for(const task of kernelTasks.values())task.reject(new Error(error.message));kernelTasks.clear();};
      return kernelRequest(1,'boot');
    });
    report.startupMs=+(performance.now()-start).toFixed(1);console.log('PASS pinned Lean kernel startup',report.startupMs,'ms');
    if(process.argv.includes('--boot-only')){report.passed=true;return;}
    const header=process.argv.includes('--solidity')?'import Solidity.Frontend.Testing\n':process.argv.includes('--init-only')?'':'import Lean\n';
    report.trueProof=await page.evaluate(header=>kernelRequest(2,'check',{source:header+'example : (1 : Nat) + 1 = 2 := by decide\n'}),header);
    assert.equal(report.trueProof.code,0,JSON.stringify(report.trueProof));console.log('PASS real arithmetic proof');
    report.falseProof=await page.evaluate(header=>kernelRequest(3,'check',{source:header+'example : False := by trivial\n'}),header);
    assert.notEqual(report.falseProof.code,0);assert.ok(report.falseProof.diagnostics.some(d=>d.severity==='error'));console.log('PASS false theorem rejected');
    report.passed=true;
  }catch(error){report.error=error.stack;report.progress=await page.evaluate(()=>window.kernelProgress);report.logs=await page.evaluate(()=>window.kernelLogs);throw error;
  }finally{
    fs.writeFileSync(path.resolve(__dirname,'../artifacts/kernel-smoke-report.json'),JSON.stringify(report,null,2)+'\n');
    await browser.close();await app.close();
  }
}
main().catch(error=>{console.error(error);process.exitCode=1;});
