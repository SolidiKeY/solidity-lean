'use strict';
const {test}=require('node:test');
const assert=require('node:assert/strict');
const {mkdtempSync,writeFileSync,rmSync}=require('node:fs');
const {join}=require('node:path');
const {tmpdir}=require('node:os');
const {parse,trial}=require('../parity/stdio.cjs');

test('stdio runner rejects invalid targets, limits and unsupported local worker counts',()=>{
  const base=['--output','/tmp/new-report','--targets','local'];
  for(const args of [['--workers','5'],['--trials','0'],['--memory-reserve-mib','0'],['--scope','pretend'],['--workers','1,1']])assert.throws(()=>parse([...base,...args]));
  assert.equal(parse([...base,'--memory-reserve-mib','2048']).memoryReserveMiB,2048);
});

for(const failure of ['nonzero-exit','ignored-shutdown'])test(`stdio provider successes cannot hide ${failure}`,async()=>{
  if(process.platform==='win32')return;
  const dir=mkdtempSync(join(tmpdir(),'parity-stdio-life-'));
  try{
    const code=join(dir,'fake-dafny');
    const rpc=require.resolve('../src/rpc.cjs'),language=require.resolve('../src/language-services.cjs'),workloads=require.resolve('../parity/workloads.cjs');
    // A deliberately cooperative protocol fixture whose only defect is its
    // shutdown. All provider assertions must pass before lifecycle failure.
    writeFileSync(code,`#!${process.execPath}
const {RpcPeer}=require(${JSON.stringify(rpc)}),{applyChanges,position}=require(${JSON.stringify(language)}),{servicesWorkload,hoverWorkload}=require(${JSON.stringify(workloads)});
const peer=new RpcPeer(process.stdin,process.stdout),fixture=servicesWorkload('dafny');let uri,text;const documents=new Map();
peer.onRequest('initialize',()=>({capabilities:{}}));
peer.onNotification('textDocument/didOpen',p=>{uri=p.textDocument.uri;text=p.textDocument.text;documents.set(uri,text);});
peer.onNotification('textDocument/didChange',p=>{text=applyChanges(documents.get(p.textDocument.uri),p.contentChanges);documents.set(p.textDocument.uri,text);});
peer.onRequest('textDocument/documentSymbol',p=>{const source=documents.get(p.textDocument.uri);return[{name:source.includes('newest')?'newest':source.includes('reopened')?'reopened':source.includes('isolated')?'isolated':'helper'}];});
// Oracle protocol fixture for lifecycle-negative tests only, never native evidence.
const lexical=p=>{const source=documents.get(p.textDocument.uri);return source.includes('class HoverCases')?hoverWorkload('dafny',source).cases.find(c=>JSON.stringify(c.position)===JSON.stringify(p.position)):null;};
const foreign=p=>{const source=documents.get(p.textDocument.uri);if(!source.includes('include \"HoverLib.dfy\"'))return null;const dependency=p.textDocument.uri.replace('hover-user.dfy','HoverLib.dfy'),text=documents.get(dependency),start=text.indexOf('value');return{uri:dependency,range:{start:position(text,start),end:position(text,start+5)},type:text.includes('a: bool')?'bool':'int'};};
peer.onRequest('textDocument/definition',p=>{const f=foreign(p);if(f)return{uri:f.uri,range:f.range};const c=lexical(p);return{uri:p.textDocument.uri,range:c?.declarationRange||fixture.declarationRange};});
peer.onRequest('textDocument/references',()=>[fixture.declarationRange,fixture.callRange].map(range=>({uri,range})));
peer.onRequest('textDocument/hover',p=>{const source=documents.get(p.textDocument.uri);if(source.includes('Missing()'))return null;if(source.endsWith('\\n/'))return{contents:{kind:'markdown',value:'No hover information available due to program error'}};const f=foreign(p);if(f)return{contents:{kind:'markdown',value:'\x60\x60\x60dafny\\nfunction HoverLib.value(a: '+f.type+'): '+f.type+'\\n\x60\x60\x60'}};return{contents:{kind:'markdown',value:lexical(p)?.expected.text||fixture.hoverExpected.text}};});
peer.onRequest('textDocument/signatureHelp',()=>({activeParameter:1,signatures:[{label:'helper'}]}));
peer.onRequest('textDocument/rename',()=>({changes:{[uri]:[fixture.callRange,fixture.declarationRange].map(range=>({range,newText:'renamed'}))}}));
peer.onRequest('textDocument/completion',()=>[{label:'helper'}]);
peer.onRequest('workspace/symbol',()=>[{name:'helper'}]);peer.onRequest('textDocument/formatting',()=>[]);
peer.onRequest('shutdown',()=>${failure==='ignored-shutdown'?'new Promise(()=>{})':'null'});
peer.onNotification('exit',()=>process.exit(17));
`,{mode:0o700});
    const result=await trial('dafny',1,{dafny:code,scope:'services',timeoutMs:1000,memoryReserveMiB:1,memoryMaxMiB:512},join(dir,'trial'));
    assert.equal(result.status,'broken');
    assert.equal(result.result.scenarios.find(s=>s.id==='server-lifecycle').status,'broken');
    assert.ok(result.result.scenarios.filter(s=>s.id!=='server-lifecycle').every(s=>['passed','partial'].includes(s.status)));
    assert.deepEqual(result.resources.cleanup.remaining,[]);
  }finally{rmSync(dir,{recursive:true,force:true});}
});

test('symbol lifecycle assertions reject metadata decoys and stale nested labels',()=>{
  const {assertServiceSymbols}=require('../parity/workloads.cjs');
  assert.throws(()=>assertServiceSymbols([{name:'obsolete',detail:'reopened'}],'reopened',['obsolete']));
  assert.throws(()=>assertServiceSymbols([{name:'reopened',children:[{name:'isolated'}]}],'reopened',['isolated']));
  assert.deepEqual(assertServiceSymbols([{name:'Services',children:[{name:'reopened'}]}],'reopened',['newest']),['Services','reopened']);
});

// Regression: malformed retained evidence must not replace a real request failure.
// Owned Node protocol fixture only; no native Dafny, Lean or proof observation.
test('stdio failure reporting preserves request error when partial JSON is malformed',async()=>{
 if(process.platform==='win32')return;
 const fs=require('node:fs'),dir=mkdtempSync(join(tmpdir(),'stdio-evidence-failure-')),trialDir=join(dir,'trial'),file=join(trialDir,'configuration-observations.json'),code=join(dir,'fixture-server'),rpc=require.resolve('../src/rpc.cjs'),originalWrite=fs.writeFileSync;
 writeFileSync(code,`#!${process.execPath}
const {RpcPeer}=require(${JSON.stringify(rpc)});const peer=new RpcPeer(process.stdin,process.stdout);
peer.onRequest('initialize',()=>({capabilities:{}}));
peer.onRequest('textDocument/documentSymbol',()=>{throw Object.assign(Error('owned original request failure'),{code:-32077});});
peer.onRequest('shutdown',()=>null);peer.onNotification('exit',()=>process.exit(0));
`,{mode:0o700});
 fs.writeFileSync=function(name,...args){return originalWrite.call(this,name,...(String(name)===file?['{malformed-partial']:args));};
 try{const result=await trial('dafny',1,{dafny:code,scope:'configuration',configurationMode:'never',timeoutMs:1000,memoryReserveMiB:12288,memoryMaxMiB:4096},trialDir,{configurationSchema:()=>({default:'onchange',enum:['never','onchange','onsave']})});
  const row=result.result.scenarios.find(s=>s.id==='automatic-configuration-lifecycle');assert.ok(row,'Original failed scenario must remain in aggregate');assert.equal(row.status,'broken');assert.match(row.error,/owned original request failure/);assert.ok(row.failedPartialEvidence.error);assert.equal(row.failedPartialEvidence.bytes,18);assert.match(row.failedPartialEvidence.sha256,/^[a-f0-9]{64}$/);assert.deepEqual(result.resources.cleanup.remaining,[]);assert.equal(result.status,'broken');
 }finally{fs.writeFileSync=originalWrite;rmSync(dir,{recursive:true,force:true});}
});

test('stdio failed evidence roundtrip retains complete ordered observation without accepting its status',()=>{
 const {failedScenario}=require('../parity/stdio.cjs'),{createHash}=require('node:crypto'),observation={status:'passed',rows:[{phase:'open',uri:'file:///owned.dfy',version:1,sourceHash:'a'.repeat(64)},{phase:'edit',uri:'file:///owned.dfy',version:2,sourceHash:'b'.repeat(64)},{phase:'closed',uri:'file:///owned.dfy',version:2}],restoration:{confirmed:false}},bytes=Buffer.from(JSON.stringify(observation)+'\n'),original=Error('actual scenario refusal');let reads=0;
 const row=failedScenario('configuration',23,original,'configuration','/owned',{readFileSync(){reads++;return bytes;}}),copy=JSON.parse(JSON.stringify(row));
 assert.equal(reads,1);assert.equal(copy.status,'broken');assert.equal(copy.error,original.stack);assert.deepEqual(copy.failedPartialObservation,observation);assert.equal(copy.failedPartialEvidence.sha256,createHash('sha256').update(bytes).digest('hex'));assert.equal(copy.failedPartialEvidence.bytes,bytes.length);
});
test('missing unreadable and malformed evidence preserve timeout/missing/error classifications',()=>{
 const {failedScenario}=require('../parity/stdio.cjs');for(const scope of ['configuration','ghost'])for(const code of ['ENOENT','EACCES','MALFORMED']){
  const original=Object.assign(Error('owned timed out'),{code:'TIMEOUT'}),row=failedScenario('failed',1,original,scope,'/owned',{readFileSync(){if(code==='MALFORMED')return Buffer.from('{broken');throw Object.assign(Error('evidence unavailable'),{code});}});
  assert.equal(row.status,'timeout');assert.equal(row.error,original.stack);assert.equal(row.failedPartialObservation,undefined);assert.ok(row.failedPartialEvidence.error);if(code==='MALFORMED')assert.match(row.failedPartialEvidence.sha256,/^[a-f0-9]{64}$/);else assert.equal(row.failedPartialEvidence.code,code);
 }
 const missing=failedScenario('missing',1,Object.assign(Error('unsupported request'),{code:-32601}),'services','/owned',{readFileSync(){throw Error('must not read');}});assert.equal(missing.status,'missing');assert.equal(missing.failedPartialEvidence,undefined);
});
