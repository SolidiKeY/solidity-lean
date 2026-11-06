/* Gate-integrity regressions: acceptance of fabricated discovery and stale judgments is consequential. */
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),os=require('node:os');
const {traceRows}=require('../parity/mechanical.cjs'),{verdictValid,prompt,evidencePaths,inside}=require('../parity/parity-gate.cjs');
function trace(){
  const records=[],send=(direction,message)=>records.push({direction,message});
  send('client',{id:1,method:'initialize'});send('server',{id:1,result:{capabilities:{hoverProvider:true}}});
  send('server',{id:9,method:'client/registerCapability',params:{registrations:[{id:'rename',method:'textDocument/rename',registerOptions:{prepareProvider:true}}]}});
  const uri='file:///fixture.dfy';
  for(let v=1;v<=4;v++){
    const doc={uri,version:v,text:'method Check() {} // '+v};
    send('client',{method:v===1?'textDocument/didOpen':'textDocument/didChange',params:v===1?{textDocument:doc}:{textDocument:{uri,version:v},contentChanges:[{text:doc.text}]}});
    if(v===3)send('server',{method:'textDocument/publishDiagnostics',params:{uri,version:v,diagnostics:[{severity:1,source:'Verifier'}]}});
    send('server',{method:'dafny/textDocument/symbolStatus',params:{uri,version:v,namedVerifiables:[{status:v===3?4:5}]}});
  }
  send('client',{method:'textDocument/didSave',params:{textDocument:{uri}}});send('client',{method:'textDocument/didClose',params:{textDocument:{uri}}});
  send('client',{id:2,method:'shutdown'});send('server',{id:2,result:null});send('client',{method:'exit'});
  records.push({direction:'client',framingFinalized:true},{direction:'server',framingFinalized:true});return records;
}
function scan(records){
  const dir=fs.mkdtempSync(path.join(os.tmpdir(),'parity-trace-test-')),file=path.join(dir,'lsp.jsonl');
  try{fs.writeFileSync(file,records.map(r=>JSON.stringify(r)).join('\n')+'\n');return traceRows(file,'fixture.jsonl');}finally{fs.rmSync(dir,{recursive:true,force:true});}
}
test('live discovery includes initialization and dynamic capabilities',()=>{
  const rows=scan(trace());assert(rows.some(r=>r.id==='capability:/hoverProvider'));assert(rows.some(r=>r.id.startsWith('dynamic-capability:textDocument/rename:')));assert(rows.some(r=>r.id==='live-method:dafny/textDocument/symbolStatus'));
});
test('three edits without verifier failure cannot certify break/fix discovery',()=>{
  const r=trace().filter(r=>r.message?.method!=='textDocument/publishDiagnostics');assert.throws(()=>scan(r),/missing ordered event/);
});
test('stale and foreign-document proof feedback cannot certify lifecycle',()=>{
  for(const change of [p=>p.version=99,p=>p.uri='file:///other.dfy']){
    const r=trace();change(r.find(r=>r.message?.method==='dafny/textDocument/symbolStatus'&&r.message.params.version===3).message.params);assert.throws(()=>scan(r),/missing ordered event/);
  }
});
test('missing request IDs and invalid finalization directions fail closed',()=>{
  const r=trace();delete r[0].message.id;delete r[1].message.id;assert.throws(()=>scan(r));
  const invalid=trace();invalid.at(-1).direction='elsewhere';assert.throws(()=>scan(invalid),/finalization/);
});
test('fix feedback must precede save and close',()=>{
  const r=trace(),i=r.findIndex(r=>r.message?.method==='dafny/textDocument/symbolStatus'&&r.message.params.version===4);r.push(r.splice(i,1)[0]);assert.throws(()=>scan(r),/missing ordered event/);
});
test('invalid, inconsistent and unevidenced yes judgments cannot pass',()=>{
  assert.equal(verdictValid({verdict:'yes',aspects:['hover'],differences:[],missing_evidence:[]}),true);
  for(const value of [{verdict:'yes',aspects:[],differences:[],missing_evidence:[]},{verdict:'yes',aspects:['hover'],differences:['colour'],missing_evidence:[]},{verdict:'yes',aspects:['hover'],differences:[],missing_evidence:['screenshot']},{verdict:'maybe',aspects:['hover'],differences:[],missing_evidence:[]}])assert.equal(verdictValid(value),false);
});
test('judge prompt requires evidence for every aspect and treats prose as claims',()=>{
  const p=prompt({id:'fixture'},['upstream.ts'],['proof.png'],'assume it is not done');
  for(const required of ['You did not write','Open and read','inspect images as images','ANY aspect','claims, not proof','assume it is not done'])assert(p.includes(required));
});
test('escaping and absent evidence cannot reach the judge',()=>{
  for(const file of ['/etc/passwd','../outside','tests/editor-parity/nonexistent'])assert.throws(()=>inside(file));
  assert.deepEqual(evidencePaths({assessment:{evidenceFiles:['b','a'],testEvidence:[{artifact:'a'}]}}),['a','b']);
});

test('successful markers cannot hide a still-broken proof in fixed feedback',()=>{
  const r=trace(),fixed=r.find(r=>r.message?.method==='dafny/textDocument/symbolStatus'&&r.message.params.version===4);
  fixed.message.params.namedVerifiables=[{status:4},{status:5}];assert.throws(()=>scan(r),/missing ordered event/);
});
test('noninteger document versions cannot certify a phase',()=>{
  const r=trace();for(const e of r){const p=e.message?.params;if(p?.textDocument?.version===2)p.textDocument.version='2';if(p?.version===2)p.version='2';}
  assert.throws(()=>scan(r),/versioned/);
});
