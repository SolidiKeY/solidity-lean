'use strict';
const fs=require('node:fs'),path=require('node:path'),assert=require('node:assert/strict'),{createHash}=require('node:crypto');
const root=path.resolve('.'),out=path.join(root,'docs/benchmarks/directruntime-2026-11-04/before');
const {chromium}=require(path.join(root,'web/node_modules/playwright'));
const {createStaticServer}=require(path.join(root,'web/tools/serve-static.cjs'));
const sha=b=>createHash('sha256').update(b).digest('hex');
async function main(){
 const destination=path.join(out,'browser-wire-audit.json');
 assert.ok(!fs.existsSync(destination),'Refusing audit overwrite');
 const {compileFixture}=await import(path.join(root,'scripts/solc-ast.mjs'));
 const inputs=JSON.parse(fs.readFileSync(path.join(out,'inputs/inputs.json'),'utf8'));
 const manifest=JSON.parse(fs.readFileSync('.lake/native-browser-wasm/direct/build.json','utf8'));
 const bytes=fs.readFileSync('.lake/native-browser-wasm/direct/direct.wasm');
 assert.equal(sha(bytes),manifest.wasm);assert.notEqual(manifest.closure.full,true);
 const module=await WebAssembly.compile(bytes);
 const report={binarySha256:manifest.wasm,imports:WebAssembly.Module.imports(module),exports:WebAssembly.Module.exports(module),requests:[],assetRequests:[],workers:[],errors:[],failures:[],boundary:'Untimed real browser worker, exact serialized AST requests. Source hashes identify freshly compiled inputs; the binary does not attest source hashes. Independent from IDE latency and not a general semantic equivalence proof.'};
 const packageBuild=JSON.parse(fs.readFileSync('web/single-file/build.json','utf8'));
 const html=fs.readFileSync('web/single-file/index.html','utf8');
 report.packageBuild=packageBuild;report.embeddedAssets=[...html.matchAll(/data-asset="([^"]+)"/g)].map(m=>m[1]);
 assert.equal(packageBuild.compiledOnly,true);assert.equal(packageBuild.kernelBuild,null);
 assert.ok(!report.embeddedAssets.some(s=>/\.olean|\.ilean|\/lean\/|kernel-worker/.test(s)));
 const trials=[];
 for(let round=0;round<3;round++)for(const t of inputs.trials){
  assert.equal(sha(fs.readFileSync(t.source)),t.sourceHash);
  const wire=JSON.stringify(t.request);assert.equal(sha(Buffer.from(wire)),t.requestSha256);
  trials.push({name:t.name,round,sourceHash:t.sourceHash,wire,wireSha256:t.requestSha256,expected:[[t.name,['proved']]]});
 }
 const dir=path.join(out,'browser-wire-inputs');assert.ok(!fs.existsSync(dir));fs.mkdirSync(dir);
 const six=[['additionSimple',['pending','refuted']],['storageRootReadWrite',['pending','refuted']],['storageIndexRootMapping',['pending','refuted']],['whileCountsUp',['pending','refuted']],['invariantCountsToBound',['pending','refuted']],['requireFalseLiteral',['proved']]];
 const controls=six.map(([name,statuses])=>({name,text:fs.readFileSync(path.join(out,'existing-controls',name+'.sol'),'utf8'),expected:[[name,statuses]],selected:name}));
 controls.push({name:'fresh eight specifications',text:fs.readFileSync('tests/automation/ClosedSpecs.sol','utf8'),expected:[['maximum',['proved']],['falseMaximum',['refuted']],['storeMaximum',['proved']],['twoChoices',['proved']],['constantOne',['proved']],['falseConstant',['refuted']],['store',['proved']],['falseStore',['refuted']]]});
 for(const [i,c]of controls.entries()){
  const source=path.join(dir,'control-'+i+'.sol'),fixture=path.join(dir,'control-'+i+'.ast.json');fs.writeFileSync(source,c.text);
  const compiled=compileFixture({args:['--source',source,'--out',fixture,'--no-wrapper'],quiet:true});
  const sourceHash=sha(Buffer.from(c.text));assert.equal(compiled.fixture.header.sourceSha256,sourceHash);
  const ast=compiled.primaryAst??compiled.fixture.ast,contract=ast.nodes.find(n=>n.nodeType==='ContractDefinition');
  const request={contract,...(c.selected?{function:c.selected}:{})},wire=JSON.stringify(request);
  trials.push({name:c.name,sourceHash,wire,wireSha256:sha(Buffer.from(wire)),expected:c.expected,compilerHeader:compiled.fixture.header,fixtureSha256:sha(fs.readFileSync(fixture))});
 }
 const app=createStaticServer({root:path.join(root,'web/dist'),port:0}),url=await app.listen();
 const profile=fs.mkdtempSync(path.join(root,'.lake/native-browser-wire-'));
 let context;
 try{
  context=await chromium.launchPersistentContext(profile,{executablePath:process.env.CHROMIUM_PATH||'/usr/bin/chromium',args:['--no-sandbox'],viewport:{width:1440,height:900}});
  context.on('request',r=>report.assetRequests.push(r.url()));
  const page=context.pages()[0]||await context.newPage();page.on('pageerror',e=>report.errors.push(e.message));page.on('worker',w=>report.workers.push(w.url()));
  await page.goto(url+'/bootstrap.json');
  report.boot=await page.evaluate(async()=>{
   window.auditWorker=new Worker('/direct-worker.js');window.auditPending=new Map();window.auditSequence=0;
   auditWorker.onmessage=({data})=>{const p=auditPending.get(data.id);if(p){auditPending.delete(data.id);data.error?p.reject(new Error(data.error.message)):p.resolve(data.result);}};
   window.auditCall=(method,params)=>new Promise((resolve,reject)=>{const id=++auditSequence;auditPending.set(id,{resolve,reject});auditWorker.postMessage({id,method,params});});
   return auditCall('boot',{});
  });
  assert.equal(report.boot.kind,'generated-c-wasm');assert.equal(report.boot.build,manifest.wasm);
  for(const [i,t]of trials.entries()){
   const actual=await page.evaluate(async wire=>{
    const params=JSON.parse(wire),serialized=JSON.stringify(params);
    const digest=await crypto.subtle.digest('SHA-256',new TextEncoder().encode(serialized));
    const wireSha256=[...new Uint8Array(digest)].map(n=>n.toString(16).padStart(2,'0')).join('');
    return {wireSha256,result:await auditCall('check',params)};
   },t.wire);
   const record={name:t.name,round:t.round,sourceHash:t.sourceHash,expected:t.expected,wireSha256:t.wireSha256,observedSerializedParamsSha256:actual.wireSha256,...(t.compilerHeader?{compilerHeader:t.compilerHeader,fixtureSha256:t.fixtureSha256}:{}),reply:actual.result};
   report.requests.push(record);
   const rows=actual.result.results||[];
   if(actual.wireSha256!==t.wireSha256||actual.result.timings?.backend!=='generated-c-wasm'||actual.result.timings?.checkSequence!==i+1||rows.length!==t.expected.length||rows.some((r,j)=>r.function!==t.expected[j][0]||!t.expected[j][1].includes(r.status)))
    report.failures.push({index:i,record});
  }
  report.forbiddenAssetRequests=report.assetRequests.filter(s=>/\.olean|\.ilean|\/lean\/|kernel-worker/.test(s));
  report.externalRequests=report.assetRequests.filter(s=>!s.startsWith(url)&&!/^(blob:|data:)/.test(s));
  report.passed=report.requests.length===256&&!report.failures.length&&!report.errors.length&&!report.forbiddenAssetRequests.length&&!report.externalRequests.length;
 }catch(error){report.failure=error.stack;throw error;}
 finally{await context?.close();await app.close();fs.rmSync(profile,{recursive:true,force:true});fs.writeFileSync(destination,JSON.stringify(report,null,2)+'\n');}
 console.log(JSON.stringify({passed:report.passed,requests:report.requests.length,suiteReplies:249,freshControlRows:14,failures:report.failures.length,forbiddenAssetRequests:report.forbiddenAssetRequests}));
 assert.equal(report.passed,true);
}
main().catch(e=>{console.error(e);process.exitCode=1;});
