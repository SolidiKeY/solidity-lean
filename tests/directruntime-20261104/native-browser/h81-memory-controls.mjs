// Guard positive Identity diamond, paired memory controls and exact B journal replay.
// Exact producer sources, fresh compilation, both real backends; no translator.
import fs from 'node:fs';import path from 'node:path';import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';import {spawnSync} from 'node:child_process';import {createRequire} from 'node:module';
import {compileFixture} from '../../../scripts/solc-ast.mjs';
const require=createRequire(import.meta.url),root=path.resolve('.'),out=path.resolve(process.env.NATIVE_BROWSER_CONTROL_OUTPUT||'/workspace/scratch/browser-chain/h81-memory');
const sha=b=>createHash('sha256').update(b).digest('hex');fs.mkdirSync(out,{recursive:true});
const destination=path.join(out,'control-inventory-with-guard.json');assert.ok(!fs.existsSync(destination));
for(const name of ['control-native-with-guard.strace','native-replies-with-guard.jsonl','browser-attempts-with-guard.jsonl'])assert.ok(!fs.existsSync(path.join(out,name)),'Refusing raw output overwrite');
const dir=path.join(out,'fresh-fixtures');assert.ok(!fs.existsSync(dir));fs.mkdirSync(dir);
const owner=process.env.NATIVE_BROWSER_MEMORY_PRODUCER||'tests/directruntime-20261104/memory-references',manifestPath=path.join(owner,'manifest.json'),producer=JSON.parse(fs.readFileSync(manifestPath));assert.equal(producer.cases.length,84);
const box=fs.readFileSync(path.join(owner,'sources/identity.box.sol'),'utf8'),diamond=fs.readFileSync(path.join(owner,'sources/identity.diamond.sol'),'utf8');assert.equal(box.replace(' /// @custom:key box',''),diamond,'exact unannotated positive twin');
const replayDir=process.env.NATIVE_BROWSER_ORIGINAL_JOURNAL;
let replay;
if(replayDir){
 const handoffBytes=fs.readFileSync(path.join(replayDir,'browser-handoff.json')),journal=fs.readFileSync(path.join(replayDir,'requests.jsonl'));
 assert.equal(sha(handoffBytes),'53c9438eb30010736432d9bcde121ef94272efcfa243c25acfc034cb79c4879f');
 assert.equal(sha(journal),'ae658ff7ea04b163a9d3939f58fc4b30acc15cf4cbe5487ca4abf5baddbb7f1d');
 const handoff=JSON.parse(handoffBytes),lines=journal.toString('utf8').trimEnd().split('\n');assert.equal(lines.length,84);assert.equal(handoff.cases.length,84);assert.equal(handoff.compilerPin,producer.compilerSha256);
 replay={lines,cases:handoff.cases,journalSha256:sha(journal),handoffSha256:sha(handoffBytes)};
}
const trials=[];
for(const row of producer.cases){
 const caseKey=row.id+'.'+row.modality+'.'+(row.viaIR?'ir':'non-ir'),original=path.join(owner,row.source),bytes=fs.readFileSync(original);assert.equal(sha(bytes),row.sourceSha256);
 const source=path.join(dir,caseKey+'.sol'),fixture=path.join(dir,caseKey+'.ast.json');assert.ok(!fs.existsSync(source)&&!fs.existsSync(fixture));fs.copyFileSync(original,source);
 const compiled=compileFixture({args:['--source',source,'--out',fixture,'--no-wrapper',...(row.viaIR?['--via-ir']:[])],quiet:true});assert.equal(compiled.fixture.header.sourceSha256,row.sourceSha256);assert.equal(compiled.fixture.header.settings.viaIR,row.viaIR);assert.equal(compiled.fixture.header.compilerSha256,producer.compilerSha256);
 const contract=(compiled.primaryAst??compiled.fixture.ast).nodes.find(n=>n.nodeType==='ContractDefinition'&&n.name==='Identity');assert.ok(contract);
 let request={contract,function:'identity'},wire=JSON.stringify(request);
 if(replay){
  const i=trials.length,c=replay.cases[i];assert.equal(c.id,row.id);assert.equal(c.modality,row.modality);assert.equal(c.viaIR,row.viaIR);assert.equal(c.sourceSha256,row.sourceSha256);
  wire=replay.lines[i];request=JSON.parse(wire);assert.equal(JSON.stringify(request),wire,'exact compact journal line');assert.equal(request.function,'identity');
  const selected=request.contract.nodes.filter(n=>n.nodeType==='FunctionDefinition'&&n.name===request.function);assert.equal(selected.length,1);assert.equal(selected[0].id,request.sourceId);
 }
 trials.push({caseKey,id:row.id,modality:row.modality,viaIR:row.viaIR,name:'identity',original,sourceHash:row.sourceSha256,fixture,fixtureSha256:sha(fs.readFileSync(fixture)),compilerHeader:compiled.fixture.header,modelHalt:row.modelHalt,request,wire,wireSha256:sha(Buffer.from(wire))});
}
const nativeDir=process.env.NATIVE_BROWSER_NATIVE_OUTPUT||'.lake/native-browser-cold-native',wasmDir=process.env.NATIVE_BROWSER_DIRECT||'.lake/native-browser-hardening/direct';
const binaries={native:path.join(nativeDir,'direct-check'),wasm:path.join(wasmDir,'direct.wasm')};
const manifests={native:JSON.parse(fs.readFileSync(path.join(nativeDir,'build.json'))),wasm:JSON.parse(fs.readFileSync(path.join(wasmDir,'build.json')))};
const freshness={};for(const mode of ['native','wasm']){const m=manifests[mode];for(const e of m.sourceFiles)assert.equal(sha(fs.readFileSync(e.module.replaceAll('.','/')+'.lean')),e.sourceSha256,e.module);assert.equal(sha(fs.readFileSync('web/browser/direct-bridge.c')),m.bridgeSha256);assert.equal(sha(fs.readFileSync('scripts/direct-runtime-closure.py')),m.closureScriptSha256);assert.equal(sha(fs.readFileSync(binaries[mode])),mode==='native'?m.executable:m.wasm);freshness[mode]={sourceFiles:m.sourceFiles.length,binarySha256:sha(fs.readFileSync(binaries[mode])),manifestSha256:sha(fs.readFileSync(path.join(mode==='native'?nativeDir:wasmDir,'build.json')))};}
const report={producerDirectory:path.resolve(owner),requestMode:replay?'exact-delivered-B-journal':'fresh-normalized',originalJournal:replay?{journalSha256:replay.journalSha256,handoffSha256:replay.handoffSha256}:null,producerManifestSha256:sha(fs.readFileSync(manifestPath)),expectedRequestsPerBackend:trials.length,freshness,requests:trials.map(({request,wire,...meta})=>meta),native:[],browser:[],assetRequests:[],errors:[],semanticAcceptanceComplete:false,identityNonVacuityComplete:false,boundary:replay?'Exact delivered original B requests replayed through revalidated H81 native/browser builds; no new runtime build or benchmark. Fresh companion fixtures bind source/compiler provenance but are not submitted payloads. Trusted compiled-checker observations are not source-preservation proofs or Lean certificates.':'Fresh compiler inputs from exact published B sources and real freshly built native/browser binaries. Required Diamond and paired controls checked explicitly. Trusted compiled-checker observations are not source-preservation proofs or Lean certificates.'};
const trace=path.join(out,'control-native-with-guard.strace'),input=trials.map(t=>t.wire+'\n').join('');
const run=spawnSync('strace',['-f','-qq','-e','trace=%file,%process,%network','-o',trace,path.resolve(binaries.native)],{input,encoding:'utf8',timeout:600000,maxBuffer:16*1024*1024});
fs.writeFileSync(path.join(out,'native-replies-with-guard.jsonl'),run.stdout||'');assert.equal(run.status,0,run.stderr);const lines=run.stdout.trim().split('\n').map(line=>JSON.parse(line));assert.deepEqual(lines.shift(),{ready:true});assert.equal(lines.length,trials.length);
for(const [i,reply]of lines.entries()){assert.equal(reply.results?.length,1);assert.equal(reply.results[0].function,trials[i].name);report.native.push({name:trials[i].name,caseKey:trials[i].caseKey,wireSha256:trials[i].wireSha256,reply});}
report.forbiddenNativeLoads=fs.readFileSync(trace,'utf8').split('\n').filter(s=>/\.(olean|ilean)(\W|$)|execve\("[^"]*\/(lean|lake)"/.test(s));assert.equal(report.forbiddenNativeLoads.length,0);
const {chromium}=require(path.join(root,'web/node_modules/playwright')),{createStaticServer}=require(path.join(root,'web/tools/serve-static.cjs'));
const app=createStaticServer({root:path.join(root,'web/dist'),port:0}),url=await app.listen(),profile=fs.mkdtempSync(path.join(root,'.lake/native-browser-published-controls-'));
let context;try{
 context=await chromium.launchPersistentContext(profile,{executablePath:process.env.CHROMIUM_PATH||'/usr/bin/chromium',args:['--no-sandbox']});context.on('request',r=>report.assetRequests.push(r.url()));const page=context.pages()[0]||await context.newPage();page.on('pageerror',e=>report.errors.push(e.message));await page.goto(url+'/bootstrap.json');
 for(const t of trials){
  fs.appendFileSync(path.join(out,'browser-attempts-with-guard.jsonl'),JSON.stringify({name:t.name,wireSha256:t.wireSha256,wire:t.wire})+'\n');
  const actual=await page.evaluate(async wire=>{const worker=new Worker('/direct-worker.js');let sequence=0;const pending=new Map();worker.onmessage=({data})=>{const p=pending.get(data.id);if(p){pending.delete(data.id);p(data.error?{workerError:data.error}:data.result);}};const call=(method,params)=>new Promise(resolve=>{const id=++sequence;pending.set(id,resolve);worker.postMessage({id,method,params});});try{const boot=await call('boot',{}),params=JSON.parse(wire),serialized=JSON.stringify(params),hash=await crypto.subtle.digest('SHA-256',new TextEncoder().encode(serialized));return {boot,wireSha256:[...new Uint8Array(hash)].map(x=>x.toString(16).padStart(2,'0')).join(''),reply:await call('check',params)};}finally{worker.terminate();}},t.wire);
  report.browser.push({name:t.name,caseKey:t.caseKey,...actual});assert.equal(actual.boot.kind,'generated-c-wasm');assert.equal(actual.boot.build,manifests.wasm.wasm);assert.equal(actual.wireSha256,t.wireSha256);assert.equal(actual.reply.timings?.backend,'generated-c-wasm');assert.equal(actual.reply.timings?.checkSequence,1);assert.equal(actual.reply.results?.length,1);assert.equal(actual.reply.results[0].function,t.name);
 }
 report.forbiddenBrowserAssets=report.assetRequests.filter(s=>/\.(olean|ilean)(\W|$)|kernel-worker|\/lean\//.test(s));report.externalRequests=report.assetRequests.filter(s=>!s.startsWith(url)&&!/^(blob:|data:)/.test(s));assert.equal(report.errors.length,0);assert.equal(report.forbiddenBrowserAssets.length,0);assert.equal(report.externalRequests.length,0);
 report.inventoryCompleted=report.native.length===trials.length&&report.browser.length===trials.length;
 const required=new Set(['identity','false','default','alias','zeroRead','zeroWrite','oobRead','oobWrite','emptySuccess']);
 report.requiredControlFailures=[];
 for(const backend of ['native','browser'])for(const row of report[backend]){
  const input=trials.find(t=>t.caseKey===row.caseKey),expected=input.id==='false'?'refuted':['zeroRead','zeroWrite','oobRead','oobWrite'].includes(input.id)?(input.modality==='box'?'proved':'refuted'):'proved';
  if(required.has(input.id)&&row.reply.results[0].status!==expected)report.requiredControlFailures.push({backend,caseKey:row.caseKey,expected,actual:row.reply.results[0]});
 }
 report.identityNonVacuityComplete=['native','browser'].every(backend=>report[backend].filter(row=>trials.find(t=>t.caseKey===row.caseKey).id==='identity'&&trials.find(t=>t.caseKey===row.caseKey).modality==='diamond').length===2&&report[backend].filter(row=>trials.find(t=>t.caseKey===row.caseKey).id==='identity'&&trials.find(t=>t.caseKey===row.caseKey).modality==='diamond').every(row=>row.reply.results[0].status==='proved'));
 report.supportGaps=Object.fromEntries(['native','browser'].map(backend=>[backend,report[backend].filter(row=>['unsupported','pending'].includes(row.reply.results[0].status)).map(row=>({caseKey:row.caseKey,reply:row.reply}))]));

}catch(error){report.failure=error.stack;throw error;}finally{await context?.close();await app.close();fs.rmSync(profile,{recursive:true,force:true});fs.writeFileSync(destination,JSON.stringify(report,null,2)+'\n');}
console.log(JSON.stringify({inventoryCompleted:report.inventoryCompleted,identityNonVacuityComplete:report.identityNonVacuityComplete,requiredControlFailures:report.requiredControlFailures?.length,supportGaps:Object.fromEntries(Object.entries(report.supportGaps||{}).map(([k,v])=>[k,v.length]))}));
assert.equal(report.requiredControlFailures.length,0,'mandatory memory controls failed');
