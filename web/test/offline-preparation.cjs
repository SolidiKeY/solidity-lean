'use strict';
// An incomplete first download must not announce offline readiness or hang.
const assert=require('node:assert/strict');
const {chromium}=require('playwright');
const {createStaticServer}=require('../tools/serve-static.cjs');
async function main(){
  const browser=await chromium.launch({executablePath:process.env.CHROMIUM_PATH||'/usr/bin/chromium',args:['--no-sandbox']});
  try{
    for(const missing of ['/asset-manifest.json','/browser-worker.js']){
      const app=createStaticServer({port:0}),serve=app.server.listeners('request')[0];
      app.server.removeAllListeners('request');app.server.on('request',(req,res)=>{if(req.url===missing){res.writeHead(404);res.end('Missing test asset');}else serve(req,res);});
      const context=await browser.newContext(),page=await context.newPage();
      try{
        await page.goto(await app.listen());
        await page.waitForFunction(()=>document.querySelector('#editor')?.textContent.includes('Offline preparation failed'),{timeout:60000});
        assert.equal(await page.evaluate(()=>!!window.solidityIDE),false);
        assert.equal(await page.evaluate(()=>!!navigator.serviceWorker.controller),false);
        console.log('PASS failed offline preparation is reported:',missing);
      }finally{await context.close();await app.close();}
    }
  }finally{await browser.close();}
}
main().catch(error=>{console.error(error);process.exitCode=1;});
