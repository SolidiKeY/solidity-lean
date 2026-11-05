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
const {RpcPeer}=require(${JSON.stringify(rpc)}),{applyChanges}=require(${JSON.stringify(language)}),{servicesWorkload}=require(${JSON.stringify(workloads)});
const peer=new RpcPeer(process.stdin,process.stdout),fixture=servicesWorkload('dafny');let uri,text;
peer.onRequest('initialize',()=>({capabilities:{}}));
peer.onNotification('textDocument/didOpen',p=>{uri=p.textDocument.uri;text=p.textDocument.text;});
peer.onNotification('textDocument/didChange',p=>{text=applyChanges(text,p.contentChanges);});
peer.onRequest('textDocument/documentSymbol',()=>[{name:text.includes('newest')?'newest':'helper'}]);
peer.onRequest('textDocument/definition',()=>({uri,range:fixture.declarationRange}));
peer.onRequest('textDocument/references',()=>[fixture.declarationRange,fixture.callRange].map(range=>({uri,range})));
peer.onRequest('textDocument/hover',()=>({contents:'helper'}));
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
