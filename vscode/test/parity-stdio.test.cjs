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
