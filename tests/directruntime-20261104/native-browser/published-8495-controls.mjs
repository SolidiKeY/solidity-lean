// Guard fixture outcomes and compiler function IDs in requests/replies on both backends.
// Fresh fixture and baseline backend inventory, not source-preservation acceptance.
import fs from 'node:fs';import path from 'node:path';import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';import {spawnSync} from 'node:child_process';import {createRequire} from 'node:module';
import {compileFixture} from '../../../scripts/solc-ast.mjs';
const require=createRequire(import.meta.url),root=path.resolve('.'),out=path.resolve(process.env.NATIVE_BROWSER_CONTROL_OUTPUT||'docs/benchmarks/directruntime-2026-11-04/published-8495');
const sha=b=>createHash('sha256').update(b).digest('hex');
fs.mkdirSync(out,{recursive:true});
const destination=path.join(out,'control-inventory-with-guard.json');assert.ok(!fs.existsSync(destination));
for(const name of ['control-native-with-guard.strace','native-replies-with-guard.jsonl','browser-attempts-with-guard.jsonl'])assert.ok(!fs.existsSync(path.join(out,name)),'Refusing raw output overwrite');
const dir=path.join(out,'controls-with-guard');assert.ok(!fs.existsSync(dir));fs.mkdirSync(dir);
const suitePath=process.env.NATIVE_BROWSER_CONTROL_SUITE||null,suiteBytes=suitePath?fs.readFileSync(suitePath):null,suite=suiteBytes?JSON.parse(suiteBytes):null;
const original=suite?.source||'tests/directruntime-20261104/control-tuples/Controls.sol',source=path.join(dir,'Controls.sol'),fixture=path.join(dir,'Controls.ast.json');
fs.copyFileSync(original,source);const bytes=fs.readFileSync(source);if(suite)assert.equal(sha(bytes),suite.sourceSha256);
const compiled=compileFixture({args:['--source',source,'--out',fixture,'--no-wrapper'],quiet:true});assert.equal(compiled.fixture.header.sourceSha256,sha(bytes));
const ast=compiled.primaryAst??compiled.fixture.ast,contract=ast.nodes.find(n=>n.nodeType==='ContractDefinition');assert.equal(contract.name,suite?.contract||'ControlTuples');
const selectedFunctions=contract.nodes.filter(n=>n.nodeType==='FunctionDefinition'&&n.kind==='function'&&['public','external'].includes(n.visibility)),names=selectedFunctions.map(n=>n.name);assert.ok(selectedFunctions.every(n=>Number.isSafeInteger(n.id)&&n.id>0),'positive compiler function identities');assert.equal(new Set(selectedFunctions.map(n=>n.id)).size,selectedFunctions.length,'unique compiler function identities');assert.equal(names.length,suite?.expected.length||13);if(suite){assert.deepEqual([...names].sort(),suite.expected.map(x=>x.name).sort());assert.equal(compiled.fixture.header.compilerSha256,suite.compilerSha256);}
let trials=selectedFunctions.map(n=>{const name=n.name,sourceId=n.id,request={contract,function:name,sourceId},wire=JSON.stringify(request);return {name,sourceId,request,wire,wireSha256:sha(Buffer.from(wire))};});
const baseline=JSON.parse(fs.readFileSync('docs/benchmarks/directruntime-2026-11-04/before/inputs/inputs.json'));
const known=baseline.trials.find(t=>t.name==='additionSimple');assert.ok(known);
const wheatSource=path.join(dir,'Wheat.sol'),wheatFixture=path.join(dir,'Wheat.ast.json');fs.copyFileSync(known.source,wheatSource);
const wheatCompiled=compileFixture({args:['--source',wheatSource,'--out',wheatFixture,'--no-wrapper'],quiet:true});assert.equal(wheatCompiled.fixture.header.sourceSha256,sha(fs.readFileSync(wheatSource)));
const wheatContract=(wheatCompiled.primaryAst??wheatCompiled.fixture.ast).nodes.find(n=>n.nodeType==='ContractDefinition');
const wheatFunction=wheatContract.nodes.find(n=>n.nodeType==='FunctionDefinition'&&n.name==='additionSimple');assert.ok(Number.isSafeInteger(wheatFunction?.id)&&wheatFunction.id>0);const wheatRequest={contract:wheatContract,function:'additionSimple',sourceId:wheatFunction.id},wheatWire=JSON.stringify(wheatRequest);
trials=[{name:'additionSimple',sourceId:wheatFunction.id,request:wheatRequest,wire:wheatWire,wireSha256:sha(Buffer.from(wheatWire)),positiveHarnessGuard:true},...trials];
const nativeDir=process.env.NATIVE_BROWSER_NATIVE_OUTPUT||'.lake/native-browser-cold-native',wasmDir=process.env.NATIVE_BROWSER_DIRECT||'.lake/native-browser-hardening/direct';
const binaries={native:path.join(nativeDir,'direct-check'),wasm:path.join(wasmDir,'direct.wasm')};
const manifests={native:JSON.parse(fs.readFileSync(path.join(nativeDir,'build.json'))),wasm:JSON.parse(fs.readFileSync(path.join(wasmDir,'build.json')))};
const freshness={};for(const mode of ['native','wasm']){const m=manifests[mode];for(const e of m.sourceFiles)assert.equal(sha(fs.readFileSync(e.module.replaceAll('.','/')+'.lean')),e.sourceSha256,e.module);assert.equal(sha(fs.readFileSync('web/browser/direct-bridge.c')),m.bridgeSha256);assert.equal(sha(fs.readFileSync('scripts/direct-runtime-closure.py')),m.closureScriptSha256);assert.equal(sha(fs.readFileSync(binaries[mode])),mode==='native'?m.executable:m.wasm);freshness[mode]={sourceFiles:m.sourceFiles.length,binarySha256:sha(fs.readFileSync(binaries[mode])),manifestSha256:sha(fs.readFileSync(path.join(mode==='native'?nativeDir:wasmDir,'build.json')))};}
const report={suite:suite?{path:path.resolve(suitePath),sha256:sha(suiteBytes),spec:suite}:null,original,sourceSha256:sha(bytes),fixtureSha256:sha(fs.readFileSync(fixture)),compilerHeader:compiled.fixture.header,names,sourceIds:trials.map(t=>({name:t.name,sourceId:t.sourceId})),expectedControlRequests:names.length,expectedRequestsPerBackend:trials.length,positiveHarnessGuard:{name:"additionSimple",sourceSha256:sha(fs.readFileSync(wheatSource)),fixtureSha256:sha(fs.readFileSync(wheatFixture)),compilerHeader:wheatCompiled.fixture.header},freshness,native:[],browser:[],assetRequests:[],errors:[],semanticAcceptanceComplete:false,identityNonVacuityComplete:false,boundary:'Freshly compiled selected fixture, real pinned native/WASM requests. Pinned runtime bindings are verified; build freshness is evidenced separately by build receipts. Completion of this inventory is not admission/proof/backend acceptance, and no Identity substitute is used.'};
const trace=path.join(out,'control-native-with-guard.strace'),input=trials.map(t=>t.wire+'\n').join('');
const run=spawnSync('strace',['-f','-qq','-e','trace=%file,%process,%network','-o',trace,path.resolve(binaries.native)],{input,encoding:'utf8',timeout:120000,maxBuffer:16*1024*1024});
fs.writeFileSync(path.join(out,'native-replies-with-guard.jsonl'),run.stdout||'');assert.equal(run.status,0,run.stderr);const lines=run.stdout.trim().split('\n').map(line=>JSON.parse(line));assert.deepEqual(lines.shift(),{ready:true});assert.equal(lines.length,trials.length);
for(const [i,reply]of lines.entries()){assert.equal(reply.results?.length,1);assert.equal(reply.results[0].function,trials[i].name);assert.equal(reply.results[0].sourceId,trials[i].sourceId,'native source identity');report.native.push({name:trials[i].name,wireSha256:trials[i].wireSha256,reply});}
report.forbiddenNativeLoads=fs.readFileSync(trace,'utf8').split('\n').filter(s=>/\.(olean|ilean)(\W|$)|execve\("[^"]*\/(lean|lake)"/.test(s));assert.equal(report.forbiddenNativeLoads.length,0);
const {chromium}=require(path.join(root,'web/node_modules/playwright')),{createStaticServer}=require(path.join(root,'web/tools/serve-static.cjs'));
const app=createStaticServer({root:path.join(root,'web/dist'),port:0}),url=await app.listen(),profile=fs.mkdtempSync(path.join(root,'.lake/native-browser-published-controls-'));
let context;try{
 context=await chromium.launchPersistentContext(profile,{executablePath:process.env.CHROMIUM_PATH||'/usr/bin/chromium',args:['--no-sandbox']});context.on('request',r=>report.assetRequests.push(r.url()));const page=context.pages()[0]||await context.newPage();page.on('pageerror',e=>report.errors.push(e.message));await page.goto(url+'/bootstrap.json');
 for(const t of trials){
  fs.appendFileSync(path.join(out,'browser-attempts-with-guard.jsonl'),JSON.stringify({name:t.name,wireSha256:t.wireSha256,wire:t.wire})+'\n');
  const actual=await page.evaluate(async wire=>{const worker=new Worker('/direct-worker.js');let sequence=0;const pending=new Map();worker.onmessage=({data})=>{const p=pending.get(data.id);if(p){pending.delete(data.id);p(data.error?{workerError:data.error}:data.result);}};const call=(method,params)=>new Promise(resolve=>{const id=++sequence;pending.set(id,resolve);worker.postMessage({id,method,params});});try{const boot=await call('boot',{}),params=JSON.parse(wire),serialized=JSON.stringify(params),hash=await crypto.subtle.digest('SHA-256',new TextEncoder().encode(serialized));return {boot,wireSha256:[...new Uint8Array(hash)].map(x=>x.toString(16).padStart(2,'0')).join(''),reply:await call('check',params)};}finally{worker.terminate();}},t.wire);
  report.browser.push({name:t.name,...actual});assert.equal(actual.boot.kind,'generated-c-wasm');assert.equal(actual.boot.build,manifests.wasm.wasm);assert.equal(actual.wireSha256,t.wireSha256);assert.equal(actual.reply.timings?.backend,'generated-c-wasm');assert.equal(actual.reply.timings?.checkSequence,1);assert.equal(actual.reply.results?.length,1);assert.equal(actual.reply.results[0].function,t.name);assert.equal(actual.reply.results[0].sourceId,t.sourceId,'browser source identity');
 }
 report.forbiddenBrowserAssets=report.assetRequests.filter(s=>/\.(olean|ilean)(\W|$)|kernel-worker|\/lean\//.test(s));report.externalRequests=report.assetRequests.filter(s=>!s.startsWith(url)&&!/^(blob:|data:)/.test(s));assert.equal(report.errors.length,0);assert.equal(report.forbiddenBrowserAssets.length,0);assert.equal(report.externalRequests.length,0);
 assert.equal(report.native[0].reply.results[0].status,'proved','native positive harness guard');assert.equal(report.browser[0].reply.results[0].status,'proved','browser positive harness guard');
 if(suite)for(let i=1;i<trials.length;i++){
  const expected=suite.expected.find(x=>x.name===trials[i].name);assert.ok(expected);
  assert.deepEqual(report.native[i].reply.results,report.browser[i].reply.results,'backend result parity');
  for(const backend of ['native','browser']){const actual=report[backend][i].reply.results[0];assert.equal(actual.status,expected.status,trials[i].name);if(suite.expectedTag!==undefined)assert.equal(actual.tag,suite.expectedTag,trials[i].name);if(expected.reason!==undefined)assert.equal(actual.reason||'',expected.reason,trials[i].name);}
 }
 report.expectedObservationChecks=suite?names.length:null;
 report.positiveHarnessGuard.passed=true;report.inventoryCompleted=report.native.length===trials.length&&report.browser.length===trials.length;
}catch(error){report.failure=error.stack;throw error;}finally{await context?.close();await app.close();fs.rmSync(profile,{recursive:true,force:true});fs.writeFileSync(destination,JSON.stringify(report,null,2)+'\n');}
console.log(JSON.stringify({inventoryCompleted:report.inventoryCompleted,native:report.native.map(r=>[r.name,r.reply.results[0].status]),browser:report.browser.map(r=>[r.name,r.reply.results[0].status]),semanticAcceptanceComplete:false}));
