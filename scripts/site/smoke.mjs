// Real Chromium UI/worker smoke; the verifier transport is explicitly a stub.
// PLAYWRIGHT_MODULE may point at a preinstalled Playwright module.
import {createServer} from 'node:http';
import {readFile} from 'node:fs/promises';
import {resolve,extname} from 'node:path';
import assert from 'node:assert/strict';
const {chromium}=await import(process.env.PLAYWRIGHT_MODULE || 'playwright');
const root=resolve('site');
const stub=`postMessage({method:'runtime',params:{proofReady:true}}); onmessage=({data:m})=>{if(m.method==='open'){if(!m.params.text.includes('contract Identity'))throw Error('Example source missing');postMessage({id:m.id,result:{}});}else if(m.method==='verify')postMessage({id:m.id,result:{results:[{contract:'Identity',function:'identity',status:'proved',range:{start:{line:5,character:4},end:{line:7,character:5}}}],errors:[]}});};`;
const server=createServer(async(req,res)=>{try{if(req.url==='/browser-worker.js'){res.setHeader('Content-Type','text/javascript');res.end(stub);return;}const name=req.url.split('?')[0]==='/'?'/index.html':req.url.split('?')[0];const path=resolve(root,'.'+name);if(!path.startsWith(root+'/'))throw Error('Invalid path');res.setHeader('Content-Type',({'.mjs':'text/javascript','.js':'text/javascript','.css':'text/css','.html':'text/html','.json':'application/json'})[extname(path)]||'text/plain');res.end(await readFile(path));}catch{res.statusCode=404;res.end();}});
await new Promise(r=>server.listen(0,'127.0.0.1',r));let browser;
try{browser=await chromium.launch({headless:true,...(process.env.CHROMIUM_PATH?{executablePath:process.env.CHROMIUM_PATH}:{}),args:['--no-sandbox']});const context=await browser.newContext();const page=await context.newPage();const errors=[];page.on('pageerror',e=>errors.push(e.message));const url='http://127.0.0.1:'+server.address().port;
await page.goto(url);await page.waitForFunction(()=>document.querySelector('#source').value.includes('contract Identity'));
await page.click('#verify');await page.waitForSelector('.result.proved');assert.match(await page.locator('#results').innerText(),/Identity.identity: proved/);await page.click('.result');assert.ok(await page.locator('.marked').count()>0);
await page.click('#share');await page.waitForFunction(()=>location.hash.startsWith('#source='));const share=page.url();await page.reload();await page.waitForFunction(()=>document.querySelector('#source').value.includes('contract Identity'));assert.equal(page.url(),share);
await page.evaluate(async()=>{await navigator.serviceWorker.ready;});await page.waitForFunction(()=>!!navigator.serviceWorker.controller);await context.setOffline(true);await page.reload();await page.waitForFunction(()=>document.querySelector('#source').value.includes('contract Identity'));assert.deepEqual(errors,[]);console.log('PASS Chromium: picker, stub worker verification, positions, share round trip, offline reload');
}finally{await browser?.close();await new Promise(r=>server.close(r));}
