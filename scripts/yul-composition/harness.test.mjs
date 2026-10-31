import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,mkdtempSync,rmSync} from 'node:fs';
import {join} from 'node:path';
import {ROOT,PIN,VERSION,COMPILER_SHA,sha,inputFor,compileRecord,validateProvenance,compare,policyScan,checkLedger,controlFailures,checkException,diagnosticsMatch,localMatrixFailures,checkProofControls} from './harness.mjs';
const read=p=>JSON.parse(readFileSync(join(ROOT,p),'utf8'));
const fixture=()=>read('tests/yul-composition/fixtures.json');
const ledger=()=>read('tests/yul-composition/ledger.json');
const ast={nodeType:'SourceUnit',nodes:[]};
const raw=JSON.stringify({sources:{'a.sol':{ast}}});
const input=inputFor({'a.sol':{content:'contract C {}'}},'legacy');
function fresh() {return compileRecord(()=>raw,input);}
test('compiler mocks retain explicit reference provenance, never proof coverage',()=>{
 const r=fresh();validateProvenance(r.record,input,raw);assert.equal(r.record.pipeline,'legacy');
 assert.equal(r.record.commit,PIN);assert.equal(r.record.compiler,VERSION);assert.equal(r.record.compilerSha256,COMPILER_SHA);
 assert.equal(inputFor({},'viaIR').settings.viaIR,true);
 assert.equal(inputFor({},'viaIR',true).settings.optimizer.enabled,true);
 assert.throws(()=>inputFor({},'made-up'));
});
for(const field of ['compiler','compilerSha256','commit','pipeline','inputSha256','outputSha256','settings','sources'])
 test('reject stale '+field,()=>{const r=fresh().record;r[field]='drift';assert.throws(()=>validateProvenance(r,input,raw));});
test('raw malformed compiler output retained before parse failure',()=>{
 const tmp=mkdtempSync('/workspace/vy5-composition/mock-');try{
  assert.throws(()=>compileRecord(()=>'{malformed',input,join(tmp,'case')));
  assert.equal(readFileSync(join(tmp,'case.output.json'),'utf8'),'{malformed');
  assert.equal(JSON.parse(readFileSync(join(tmp,'case.provenance.json'))).outputSha256,sha('{malformed'));
 }finally{rmSync(tmp,{recursive:true});}
});
test('observations compare exact failure/bytes/logs/storage/world/memory fields',()=>{
 const expected={failed:false,returnData:'0x1234',logs:[],storage:{'0':'0x01'},memory:'0xaa',world:{balance:'1'}};
 assert.equal(compare(expected,structuredClone(expected)).status,'match');
 for(const field of Object.keys(expected)) {
  const actual=structuredClone(expected);delete actual[field];assert.equal(compare(expected,actual).status,'blocked');
  actual[field]=null;assert.equal(compare(expected,actual).status,'mismatch');
 }
 assert.equal(compare(null,{}).status,'pending');assert.equal(compare({failed:false},{failed:false}).status,'blocked');
 assert.equal(compare({failed:false,returnData:'0x',logs:[]},{failed:false,returnData:'0x',logs:[{data:'0x'}]}).status,'mismatch');
});
test('advisory refusal scans actual AST; malformed inputs fail closed',()=>{
 const source=names=>({nodeType:'SourceUnit',nodes:[{nodeType:'InlineAssembly',flags:['memory-safe'],AST:{nodeType:'YulBlock',statements:names.map(name=>({nodeType:'YulFunctionCall',functionName:{name}}))}}]});
 for(const name of ['gas','msize','pc','codesize','codecopy','callcode']) assert.deepEqual(policyScan(source([name])).refusals,[name]);
 const unsafe=source(['add']);delete unsafe.nodes[0].flags;
 assert.deepEqual(policyScan(unsafe).refusals,['non-memory-safe']);
 assert.deepEqual(policyScan(source(['add'])).refusals,[]);
 assert.throws(()=>policyScan({}));const malformed=source([]);delete malformed.nodes[0].AST;assert.throws(()=>policyScan(malformed));
});
test('ledger accounts for all children and six combinations with zero closure',()=>{
 const result=checkLedger(ledger(),fixture());assert.equal(result.closed,0);assert.equal(result.combinations,6);assert.equal(result.obligations,24);
});
for(const mutation of ['missing','duplicate','proof','status','dependency','owner','combination','fixture'])
 test('ledger rejects '+mutation,()=>{
  const l=ledger(),fs=fixture();
  if(mutation==='missing')l.obligations.pop();
  if(mutation==='duplicate')l.obligations.push(l.obligations[0]);
  if(mutation==='proof')l.obligations[0].proof={symbol:'fake',sha256:'stale'};
  if(mutation==='status')l.obligations[0].status='done';
  if(mutation==='dependency')l.obligations[9].dependencies=['typo'];
  if(mutation==='owner')l.obligations[9].owner='VY5';
  if(mutation==='combination')l.combinations[0].dependencies=['Y03'];
  if(mutation==='fixture')fs.splice(fs.findIndex(f=>f.id==='loops'),1);
  assert.throws(()=>checkLedger(l,fs));
 });
test('negative and upstream mismatch controls fail closed',()=>{
 const r={id:'incorrect-opcode',pipeline:'legacy',status:'mismatch',negativeControl:'must-mismatch',comparison:{differences:['returnData']}};
 const via={...r,pipeline:'viaIR'};
 assert.deepEqual(controlFailures([r,via],true),[]);
 assert.equal(controlFailures([],true).length,2);
 for(const status of ['match','blocked','pending']) assert.equal(controlFailures([{...r,status},{...r,pipeline:'viaIR'}],true).length,1);
 assert.equal(controlFailures([{...r,comparison:{differences:['logs']}},{...r,pipeline:'viaIR'}],true).length,1);
 assert.equal(controlFailures([{id:'upstream',reference:{status:'broken'}}]).length,1);
 assert.equal(controlFailures([{id:'ordinary',status:'mismatch'}]).length,1);
});
test('prerequisite graph has no completion cycles',()=>{
 const rows=ledger().obligations,byId=new Map(rows.map(r=>[r.id,r]));
 function visit(id,path=new Set()) {assert(!path.has(id),'dependency cycle at '+id);const r=byId.get(id);if(!r)return;const next=new Set([...path,id]);for(const d of r.dependencies)visit(d,next);}
 for(const r of rows)visit(r.id);
});

test('log object key order is irrelevant but emitter identity is observed',()=>{
 const expected={failed:false,returnData:'0x',logs:[{topics:['0x01'],data:'0xaa',emitter:'self'}]};
 const actual={failed:false,returnData:'0x',logs:[{emitter:'self',data:'0xaa',topics:['0x01']}]};
 assert.equal(compare(expected,actual).status,'match');
 actual.logs[0].emitter='0x1234';assert.equal(compare(expected,actual).status,'mismatch');
});

test('deployment and runtime unsupported exceptions remain blocked',()=>{
 for(const stage of ['deployment','runtime']) {
  for(const e of [null,'revert','out of gas','stack overflow']) assert.equal(checkException(e,stage),e);
  for(const e of ['invalid opcode','host limit','timeout']) assert.throws(()=>checkException(e,stage));
 }
});
test('malformed-import requires the independent precise diagnostic',()=>{
 const expected=fixture().find(f=>f.id==='malformed-import').expectedDiagnostics;
 const errors=expected.map(e=>({type:e.type,errorCode:e.code,message:e.message}));
 assert(diagnosticsMatch(errors,expected));assert(!diagnosticsMatch([],expected));
 for(const k of ['type','errorCode','message']) {const bad=structuredClone(errors);bad[0][k]='wrong';assert(!diagnosticsMatch(bad,expected));}
});

test('owned local controls fail closed in every requested profile',()=>{
 const profiles=['legacy','viaIR'].flatMap(pipeline=>[false,true].map(optimized=>({pipeline,optimized})));
 const rows=profiles.flatMap(profile=>fixture().map(f=>({kind:'combination',id:f.id,...profile,status:f.negativeControl?'mismatch':'match',comparison:{differences:f.negativeControl==='must-reject-always-revert'?['failed','returnData','exception']:f.negativeControl?['returnData']:[]},compilerStatus:f.compilerError?'rejected':'compiled',compilerControl:'match',policyCheck:'match',layoutSanity:true,targetMutation:{mutantRuntime:f.id==='incorrect-opcode'?'0x60016029035f5260205ff3':'0x5f5ffd'},observed:{failed:false,exception:f.id==='always-revert-target'?'revert':null,logs:[],returnData:'0x'+'0'.repeat(62)+'80'}})));
 assert.deepEqual(localMatrixFailures(rows,profiles),[]);
 for(let i=0;i<rows.length;i++) {
  const missing=rows.filter((_,j)=>j!==i);assert(localMatrixFailures(missing,profiles).length>0,rows[i].id);
  const bad=structuredClone(rows);bad[i].status='blocked';bad[i].compilerStatus='blocked';bad[i].layoutSanity=false;
  assert(localMatrixFailures(bad,profiles).length>0,rows[i].id);
 }
 assert(localMatrixFailures([...rows,rows[0]],profiles).length>0);
 assert(localMatrixFailures(rows.filter(r=>!r.optimized),profiles).length>0);
});
test('revert controls cannot match out-of-gas or stack overflow',()=>{
 for(const id of ['always-revert','constructor-failure']) {
  const expected=fixture().find(f=>f.id===id).expected;
  assert.equal(expected.exception,'revert');
  for(const exception of ['out of gas','stack overflow']) assert.equal(compare(expected,{...expected,exception}).status,'mismatch');
 }
});

test('proof controls reject stale/missing source-bound registrations',()=>{
 const registration=read('tests/yul-composition/proof-controls.json');
 assert.equal(checkProofControls(registration).finiteProofs,3);
 for(const field of ['sourceSha256','proofs','dependency','runtimeGuards','assemblyObligationsClosed']) {
  const bad=structuredClone(registration);
  if(field==='proofs')bad.proofs.pop();else if(field==='dependency')bad.dependency.sha256='stale';else if(field==='runtimeGuards')bad.runtimeGuards=0;else if(field==='assemblyObligationsClosed')bad.assemblyObligationsClosed=['Y10'];else bad[field]='stale';
  assert.throws(()=>checkProofControls(bad));
 }
 const missing=structuredClone(registration);missing.proofs[0].declaration='invented';assert.throws(()=>checkProofControls(missing));
});

test('mutated always-revert target control cannot be an ordinary mismatch',()=>{
 const fixtureRow=fixture().find(f=>f.id==='always-revert-target');
 assert.equal(fixtureRow.expected.failed,false);assert.equal(fixtureRow.expected.exception,null);
 const report={id:fixtureRow.id,kind:'combination',pipeline:'legacy',optimized:false,status:'mismatch',comparison:{differences:['failed','returnData','exception']},targetMutation:{mutantRuntime:'0x5f5ffd'},observed:{exception:'revert'}};
 const profile=[{pipeline:'legacy',optimized:false}];
 const ownedFailures=rows=>localMatrixFailures(rows,profile).filter(s=>s.startsWith(fixtureRow.id+'/'));
 assert.deepEqual(ownedFailures([report]),[]);
 for(const exception of ['out of gas','stack overflow',null]) assert(ownedFailures([{...report,observed:{exception}}]).length);
 assert(ownedFailures([{...report,comparison:{differences:['returnData']}}]).length);
 assert(ownedFailures([{...report,targetMutation:null}]).length);
});

test('malformed nested reference evidence fails the aggregate gate',()=>{
 assert(controlFailures([{id:'bad',reference:{status:'working',validationFailure:'changed pinned oracle'}}]).length);
});
