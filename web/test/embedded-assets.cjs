'use strict';
// Exercise the real broker with nested workers in an opaque origin. Revoking
// the parent's URLs forces workers to own their assets independently.
const fs=require('node:fs'),path=require('node:path'),http=require('node:http'),assert=require('node:assert/strict');
const {chromium}=require('playwright');
const artifacts=path.resolve(__dirname,'../artifacts');
const localFile=process.argv.includes('--file');
async function main(){
  fs.mkdirSync(path.join(artifacts,'browser-profiles'),{recursive:true});
  const fixture=fs.mkdtempSync(path.join(artifacts,'browser-profiles/fixture-'));
  const html='<!doctype html><link rel="icon" href="data:,"><body></body>';
  fs.writeFileSync(path.join(fixture,'index.html'),html);
  const server=localFile?null:http.createServer((_req,res)=>{res.setHeader('Content-Type','text/html');res.end(html);});
  if(server)await new Promise(resolve=>server.listen(0,'127.0.0.1',resolve));
  const url=localFile?require('node:url').pathToFileURL(path.join(fixture,'index.html')).href:'http://127.0.0.1:'+server.address().port;
  const profile=fs.mkdtempSync(path.join(artifacts,'browser-profiles/embedded-'));
  let context;const report={localFile,errors:[],external:[]};
  try{
    context=await chromium.launchPersistentContext(profile,{executablePath:process.env.CHROMIUM_PATH||'/usr/bin/chromium',args:['--no-sandbox']});
    if(localFile)await context.setOffline(true);
    context.on('request',request=>{if(!/^(blob:|data:)/.test(request.url())&&new URL(request.url()).origin!==new URL(url).origin)report.external.push(request.url());});
    const page=await context.newPage();page.on('pageerror',e=>report.errors.push(e.message));await page.goto(url);
    report.result=await page.evaluate(async({source,localFile})=>new Promise((resolve,reject)=>{
      const iframe=document.createElement('iframe');iframe.sandbox='allow-scripts';const token=Date.now()+':'+Math.random();
      const timer=setTimeout(()=>reject(new Error('Embedded worker ownership test timed out')),15000);
      window.addEventListener('message',function receive(event){if(event.data?.token!==token)return;clearTimeout(timer);window.removeEventListener('message',receive);resolve(event.data);});
      function run(token){
        const assets={
          '/data':new Blob(['offline bytes']),
          '/dependency.js':new Blob(["self.dependency='imported';"],{type:'text/javascript'}),
          '/child.js':new Blob(["onmessage=async event=>{try{const request=new XMLHttpRequest();request.open('GET','/data',false);request.send();postMessage({sequence:event.data.sequence,xhr:request.responseText,status:request.status,fetch:await(await fetch('/data')).text()});}catch(error){postMessage({error:error.message});}};"],{type:'text/javascript'}),
          '/main.js':new Blob(["importScripts('/dependency.js');const child=new Worker('/child.js');child.onmessage=event=>postMessage({dependency,...event.data});child.onerror=event=>postMessage({error:event.message});onmessage=event=>child.postMessage(event.data);"],{type:'text/javascript'})
        };
        try{
          const resolveAsset=installEmbeddedAssets(assets),worker=new Worker('/main.js'),results=[];
          worker.onerror=event=>parent.postMessage({token,error:event.message},'*');
          worker.onmessage=event=>{if(event.data.error){parent.postMessage({token,...event.data},'*');return;}results.push(event.data);if(results.length===2)parent.postMessage({token,origin:location.origin,protocol:location.protocol,results},'*');};
          worker.postMessage({sequence:1});worker.postMessage({sequence:2});
          for(const key of Object.keys(assets))URL.revokeObjectURL(resolveAsset(key));
        }catch(error){parent.postMessage({token,error:error.message},'*');}
      }
      const code=source+'\n('+run.toString()+')('+JSON.stringify(token)+');';
      if(localFile)(0,eval)(code);else{iframe.srcdoc='<script>'+code+'</script>';document.body.append(iframe);}
    }),{source:fs.readFileSync(path.resolve(__dirname,'../browser/single-file.js'),'utf8'),localFile});
    assert.equal(report.result.error,undefined,report.result.error);if(localFile)assert.equal(report.result.protocol,'file:');else assert.equal(report.result.origin,'null');
    assert.deepEqual(report.result.results.map(r=>r.sequence).sort(),[1,2]);
    for(const row of report.result.results){assert.equal(row.dependency,'imported');assert.equal(row.xhr,'offline bytes');assert.equal(row.fetch,'offline bytes');assert.equal(row.status,200);}
    if(localFile)await page.reload();
    report.failureCleanup=await page.evaluate(async({source,connection,localFile})=>new Promise((resolve,reject)=>{
      const iframe=document.createElement('iframe');iframe.sandbox='allow-scripts';const token=Date.now()+':'+Math.random();
      const timer=setTimeout(()=>reject(new Error('Partial worker shutdown test timed out')),15000);
      window.addEventListener('message',function receive(event){if(event.data?.token!==token)return;clearTimeout(timer);window.removeEventListener('message',receive);resolve(event.data);});
      function run(token){
        installEmbeddedAssets({'/browser-worker.js':new Blob(["setInterval(()=>postMessage({method:'heartbeat'}),5);setTimeout(()=>{throw new Error('partial startup fixture');},30);"],{type:'text/javascript'})});
        const client=new BrowserConnection();let heartbeats=0;
        client.onmessage=()=>heartbeats++;client.onerror=event=>event.preventDefault();
        client.onclose=()=>setTimeout(()=>{const stopped=heartbeats;setTimeout(()=>parent.postMessage({token,stopped,after:heartbeats,state:client.readyState},'*'),100);},50);
      }
      const code=source+'\n'+connection+'\n('+run.toString()+')('+JSON.stringify(token)+');';
      if(localFile)(0,eval)(code);else{iframe.srcdoc='<script>'+code+'</script>';document.body.append(iframe);}
    }),{source:fs.readFileSync(path.resolve(__dirname,'../browser/single-file.js'),'utf8'),connection:fs.readFileSync(path.resolve(__dirname,'../browser/connection.js'),'utf8'),localFile});
    assert.ok(report.failureCleanup.stopped>0,'fixture must partially initialize before throwing');assert.equal(report.failureCleanup.after,report.failureCleanup.stopped,'a failed owned worker must stop before reconnecting');assert.equal(report.failureCleanup.state,3);
    assert.deepEqual(report.external,[]);assert.deepEqual(report.errors,[]);report.passed=true;
    console.log('PASS nested workers own Blob handles, preserve queued messages, import scripts, fetch and synchronous XHR after parent URL revocation');
    console.log('PASS a partially initialized compiler worker is terminated before reconnecting');
  }finally{await context?.close();fs.rmSync(profile,{recursive:true,force:true});fs.rmSync(fixture,{recursive:true,force:true});if(server)await new Promise(resolve=>server.close(resolve));fs.writeFileSync(path.join(artifacts,localFile?'embedded-assets-file-report.json':'embedded-assets-report.json'),JSON.stringify(report,null,2)+'\n');}
}
main().catch(error=>{console.error(error);process.exitCode=1;});
