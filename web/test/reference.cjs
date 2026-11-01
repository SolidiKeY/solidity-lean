'use strict';
// An actual Code-compatible host must already be running with the production
// extension and the reference probe installed. No imitation reference is drawn.
const {chromium}=require('playwright');
const fs=require('node:fs');
const path=require('node:path');
const assert=require('node:assert/strict');
const artifacts=path.resolve(__dirname,'../artifacts');
const url=process.env.REFERENCE_URL || 'http://127.0.0.1:4180/?folder=/tmp/solidity-web-reference/workspace';
const reportPath=process.env.SOLIDITY_LEAN_REFERENCE_REPORT || path.join(artifacts,'native-report.json');
async function main(){
  fs.mkdirSync(artifacts,{recursive:true});if(fs.existsSync(reportPath))fs.unlinkSync(reportPath);
  const browser=await chromium.launch({executablePath:process.env.CHROMIUM_PATH || (fs.existsSync('/usr/bin/chromium')?'/usr/bin/chromium':undefined),headless:true,args:['--no-sandbox','--disable-dev-shm-usage']});
  const page=await browser.newPage({viewport:{width:1440,height:900},deviceScaleFactor:1,colorScheme:'dark'});
  async function command(label){await page.keyboard.press('F1');const input=page.locator('.quick-input-widget input');await input.fill('>'+label);await page.waitForTimeout(200);const results=await page.locator('.quick-input-widget').innerText();assert.ok(!results.includes('No matching results'),`Native command unavailable: ${label}`);await page.keyboard.press('Enter');await page.waitForTimeout(350);}
  try{
    const start=performance.now();await page.goto(url);await page.waitForSelector('.monaco-workbench',{timeout:60000});await page.waitForTimeout(1500);
    if(await page.locator('.part.auxiliarybar').isVisible())await command('View: Toggle Secondary Side Bar Visibility');
    await command('View: Close All Editors');await page.keyboard.press('Control+Shift+e');await page.getByText('Counter.sol',{exact:true}).first().dblclick();
    await page.waitForSelector('.view-lines .view-line');const nativeStartupMs=+(performance.now()-start).toFixed(1);
    await command('Solidity Lean Parity: Capture');
    const deadline=Date.now()+180000;
    while(!fs.existsSync(reportPath)){assert.ok(Date.now()<deadline,'Native proof capture timed out');await page.waitForTimeout(200);}
    const report=JSON.parse(fs.readFileSync(reportPath,'utf8'));assert.equal(report.passed,true,report.error);report.editorStartupMs=nativeStartupMs;report.referenceHost='OpenVSCode Server 1.105.1';
    fs.writeFileSync(reportPath,JSON.stringify(report,null,2)+'\n');
    await page.locator('.activitybar .codicon-test-view-icon').click();await page.waitForTimeout(300);
    // Opening Testing resolves the native controller with listing requests.
    // Let that finish, then republish real proofs so the screenshot does not
    // accidentally compare discovery's "ready" state with checked results.
    await page.waitForFunction(()=>document.querySelector('.part.sidebar')?.textContent.includes('Identity.sol'));
    await command('Solidity Lean: Verify File');
    const rows=page.locator('.part.sidebar .monaco-list-row');console.log('Testing rows:',await rows.allTextContents());
    // Expand the real file item through its tree affordance when needed.
    const fileRow=rows.filter({hasText:'Counter.sol'}).first();
    if(await fileRow.count()){
      const twistie=fileRow.locator('.monaco-tl-twistie');if((await twistie.getAttribute('class')||'').includes('collapsed'))await twistie.click();
    }
    await page.waitForFunction(()=>{const text=document.querySelector('.part.sidebar')?.textContent;return text?.includes('proved')&&text.includes('pending');});
    await page.keyboard.press('Control+Shift+m');await page.waitForTimeout(350);
    const panel=await page.locator('.part.panel').boundingBox();if(panel&&Math.abs(panel.y-663)>3){await page.mouse.move(900,panel.y);await page.mouse.down();await page.mouse.move(900,663,{steps:12});await page.mouse.up();}
    await page.keyboard.press('Escape');await page.mouse.move(1300,650);await page.waitForTimeout(250);
    await page.screenshot({path:path.join(artifacts,'native-problems.png')});
    console.log(JSON.stringify({passed:report.passed,editorStartupMs:nativeStartupMs,trialMs:report.trials.map(t=>t.elapsedMs),results:report.trials[0].report.results.map(r=>({function:r.signature||r.function,status:r.status}))},null,2));
    const webPath=path.join(artifacts,'browser-report.json');if(fs.existsSync(webPath)){
      const web=JSON.parse(fs.readFileSync(webPath));if(web.proofs&&web.passed){const expected=report.trials[0].report.results.map(r=>[r.signature||r.function,r.status]);assert.deepEqual(web.proofTimings[0].results.map(r=>[r.function,r.status]),expected);if(web.proofDiagnostics)assert.deepEqual(web.proofDiagnostics.map(d=>({code:d.code,message:d.message,severity:d.severity-1})),report.diagnostics.map(d=>({code:d.code,message:d.message,severity:d.severity})));console.log('Native and web function statuses and proof diagnostics match exactly.');}
    }
  }catch(error){console.log((await page.locator('body').innerText()).slice(-5000));await page.screenshot({path:path.join(artifacts,'native-failure.png')});throw error;}finally{await browser.close();}
}
main().catch(error=>{console.error(error);process.exitCode=1;});
