import test from 'node:test';
import assert from 'node:assert/strict';
import fs,{readFileSync} from 'node:fs';
import {syncBuiltinESMExports} from 'node:module';
import {join,resolve} from 'node:path';
import {isDeepStrictEqual as eq} from 'node:util';
import {sha} from './harness.mjs';
import {verifyNativeRethrowInputs,validateNativeRethrowCall,validateNativeRethrowReport} from './pipeline-rethrow.mjs';
import {validateNativeRethrowCall as originalCall,validateNativeRethrowReport as originalReport} from './native-rethrow.mjs';
const BASE='/workspace/vy5-composition/native-rethrow-20261101',DIR='/workspace/vy5-composition/pipeline-contract-20261102/native-v2';
const report=JSON.parse(readFileSync(join(DIR,'report.json'))),oracle=JSON.parse(readFileSync('tests/yul-composition/native-rethrow-expectations.json'));
const word=n=>'0x'+BigInt(n).toString(16).padStart(64,'0');
const validate=(r=report)=>validateNativeRethrowReport(r,DIR);
const call=(c,index=0)=>validateNativeRethrowCall(c,oracle.plan[index],index,report.rows[0].address,report.rows[0].deployment.actual.returnData,{pipeline:report.rows[0].pipeline,optimized:report.rows[0].optimized});
test('fresh pinned per-pipeline36calls/4profiles/20Sourcebyte projections/eight executed negatives; no adequacy',()=>{
 validate();assert.equal(report.validation,'pass');assert.equal(report.fullProofGate,'pending');assert.equal(report.nativeExecution,'fresh-pinned-solc-evm');assert.equal(report.rows.length,4);assert.equal(report.rows.reduce((n,r)=>n+r.calls.length,0),36);assert.equal(report.rows.flatMap(r=>r.links).filter(l=>l.expectedMatch).length,20);assert.equal(report.rows.flatMap(r=>r.links).filter(l=>!l.expectedMatch).length,8);
 const l=JSON.parse(readFileSync('tests/yul-composition/pipeline-rethrow-ledger.json'));assert.equal(l.fullCoverage,false);assert.equal(l.obligations.length,24);assert.equal(l.combinations.length,6);
});
test('original immutable unaudited fixture remains STRICT FAILURE: all36calls retained, five optimized journal mismatches',()=>{
 const original=JSON.parse(readFileSync(join(BASE,'original-v3/report.json'))),plan=JSON.parse(readFileSync('tests/yul-composition/native-rethrow-expectations.json')).plan,freeze=JSON.parse(readFileSync(join(BASE,'pre-execution-freeze.json')));
 for(const[file,hash]of Object.entries(freeze.hashes))assert.equal(sha(readFileSync(file)),hash);
 assert.equal(original.validation,'mismatch');assert.equal(original.rows.length,4);assert.equal(original.rows.reduce((n,r)=>n+r.calls.length,0),36);assert.deepEqual(original.rows.map(r=>r.errors.length),[0,0,0,5]);
 assert.throws(()=>originalReport(original,join(BASE,'original-v3')));
 for(const row of original.rows)for(let i=0;i<plan.length;i++)if(row.pipeline==='viaIR'&&row.optimized&&[0,1,2,3,6].includes(i))assert.throws(()=>originalCall(row.calls[i],plan[i],i,row.address,row.deployment.actual.returnData),/ordered persistent write journal/);else originalCall(row.calls[i],plan[i],i,row.address,row.deployment.actual.returnData);
});
test('unchanged original source/settings produce identical pinned runtime in each profile',()=>{
 const old=JSON.parse(readFileSync(join(BASE,'original-v3/report.json')));
 assert.deepEqual(report.rows.map(r=>[r.pipeline,r.optimized,r.runtimeSha256]),old.rows.map(r=>[r.pipeline,r.optimized,r.runtimeSha256]));
 assert.equal(report.traceContract.id,'VY5-H3-pinned-rethrow-trace-v1');
});
for(const key of ['actual','capture','index','signature'])test('missing native evidence '+key,()=>{const c=structuredClone(report.rows[0].calls[0]);delete c[key];assert.throws(()=>call(c));});
const mutations={
 'wrong call selector':c=>c.capture.request.input='0x00000000',
 'wrong request ordinal':c=>c.capture.transaction++,
 'wrong caller':c=>c.capture.request.caller=c.capture.request.to,
 'missing child frame':c=>c.capture.frames.pop(),
 'missing actual catch bytes':c=>delete c.capture.frames[0].lastCallReturnData,
 'missing rollback operation':c=>{const a=c.capture.operations.find(o=>o.kind==='revert');a.kind='commit';},
 'child rollback swapped with outer':c=>{for(const o of c.capture.operations)if(o.kind==='revert')o.frame=o.frame===0?1:0;},
 'wrong persistent write despite same returndata':c=>{const a=c.capture.operations.find(o=>o.kind==='putStorage'&&o.frame===1);a.value=word(98);},
 'wrong transient write despite same returndata':c=>{const a=c.capture.operations.find(o=>o.kind==='transient.put'&&o.frame===1);a.value=word(50);},
 'wrong final storage despite same returndata':c=>{c.capture.post[c.capture.request.to].persistent[word(0)]=word(8);},
 'wrong final transient despite same returndata':c=>{c.capture.post[c.capture.request.to].transient[word(0)]=word(17);},
 'wrong child post-prefix restoration':c=>c.capture.frames[1].post[c.capture.request.to].persistent[word(0)]=word(99),
 'native balance drift with same bytes':c=>c.capture.post[c.capture.request.to].balance='1',
 'native caller nonce drift with same bytes':c=>c.capture.post[c.capture.request.caller].nonce='99',
 'native runtime code lost':c=>c.capture.post[c.capture.request.to].code='0x',
 'lost root memory':c=>delete c.capture.frames[0].memory,
 'rethrow final buffer confused with captured data':c=>{c.capture.frames[0].lastCallReturnData.bytes='0xaabb';c.capture.frames[0].lastCallReturnData.length=2;},
 'wrong full semantic REVERT window':c=>{const a=c.capture.frames[0].regions.find(r=>r.opcode==='REVERT'),b=Buffer.from(a.bytes.slice(2),'hex');b[Number(a.offset)]^=1;a.bytes='0x'+b.toString('hex');},
 'lost child log77 memory':c=>{const a=c.capture.frames[1].regions.find(r=>r.opcode==='LOG0'),b=Buffer.from(a.bytes.slice(2),'hex');b[Number(a.offset)]=0x78;a.bytes='0x'+b.toString('hex');},
 'wrong storage slot domain':c=>{const a=c.capture.domain.find(d=>d.address===c.capture.request.to);a.persistent=[];},
 'reordered frame events':c=>c.capture.events.reverse()
};
for(const[name,change]of Object.entries(mutations))test(name,()=>{const c=structuredClone(report.rows[0].calls[0]);change(c);assert.throws(()=>call(c));});
test('same-length AABB cannot replace DEAD even with coherent root/child output bytes',()=>{
 const c=structuredClone(report.rows[0].calls[0]);c.actual.returnData='0xaabb';c.capture.frames[0].output.bytes='0xaabb';c.capture.frames[1].output.bytes='0xaabb';assert.throws(()=>call(c),/full failure\/bytes\/log mismatch/);
});
test('always-revert cannot replace successful try output',()=>{
 const c=structuredClone(report.rows[0].calls[4]);c.actual.failed=true;c.actual.exception='revert';c.actual.returnData='0xdead';c.actual.logs=[];c.capture.frames[0].output.exception='revert';c.capture.frames[0].output.bytes='0xdead';c.capture.frames[0].output.logs=[];assert.throws(()=>call(c,4),/full failure\/bytes\/log mismatch/);
});
test('full panic tail is not a selector/length-only comparison',()=>{
 const c=structuredClone(report.rows[0].calls[2]),bytes=c.actual.returnData.slice(0,-2)+'11';c.actual.returnData=bytes;c.capture.frames[0].output.bytes=bytes;c.capture.frames[1].output.bytes=bytes;assert.throws(()=>call(c,2),/full failure\/bytes\/log mismatch/);
});
for(const[name,change]of Object.entries({
 'missing required pipeline':r=>r.rows.pop(),
 'pipeline ordering':r=>r.rows.reverse(),
 'missing optimizer profile':r=>r.rows[0].optimized=true,
 'missing ordered call':r=>r.rows[0].calls.pop(),
 'reordered calls':r=>r.rows[0].calls.reverse(),
 'passing report has failed diagnostics':r=>r.rows[0].errors.push({call:0,message:'failure'}),
 'passing report lacks error evidence':r=>delete r.rows[0].errors,
 'fake kernel full gate':r=>r.fullProofGate='pass',
 'fake historical native run':r=>r.nativeExecution='historical-replay-only',
 'wrong runtime code hash':r=>r.rows[0].runtimeSha256='0'.repeat(64),
 'wrong compiler settings':r=>r.rows[0].receipt.settings.optimizer.enabled=!r.rows[0].receipt.settings.optimizer.enabled,
 'wrong source/compiler hash':r=>r.rows[0].receipt.compilerSha256='0'.repeat(64),
 'stale runner':r=>r.binding.runnerSha256='0'.repeat(64),
 'fake source model hash':r=>r.binding.sourceReportSha256='0'.repeat(64),
 'wrong Source case order':r=>r.rows[0].links.reverse(),
 'zero timeout falsely linked to native success':r=>r.rows[0].links[0].sourceCase=0,
 'wrong same-length negative falsely match':r=>r.rows[0].links.find(l=>l.call===3).status='match',
 'always-revert falsely match success':r=>r.rows[0].links.find(l=>l.call===8).expectedMatch=true,
 'missing full panic Source link':r=>r.rows[0].links.splice(2,1)
}))test(name,()=>{const r=structuredClone(report);change(r);assert.throws(()=>validate(r));});
function spoof(path,replace,action){const original=fs.readFileSync;try{fs.readFileSync=function(file,...args){const v=original.call(this,file,...args);return String(file)===path?replace(v):v;};syncBuiltinESMExports();assert.throws(action);}finally{fs.readFileSync=original;syncBuiltinESMExports();}}
for(const file of Object.keys(report.binding.inputHashes))test('stale real own/engine/input bytes '+file,()=>spoof(resolve(file),v=>Buffer.concat([Buffer.isBuffer(v)?v:Buffer.from(v),Buffer.from('\n')]),()=>verifyNativeRethrowInputs()));
for(const file of ['legacy.input.json','legacy.output.json','legacy.provenance.json','legacy.capture.json','native.execution.json','report.json'])test('missing/malformed retained native evidence '+file,()=>spoof(join(DIR,file),()=>Buffer.from('{}'),()=>validate()));
for(const file of ['/workspace/vy5-composition/rethrow-20261101/readback-v1/report.json','/workspace/vy5-composition/attempt-20261101/native-v2/report.json'])test('sealed Source/historical24call evidence cannot drift '+file,()=>spoof(file,()=>Buffer.from('{}'),()=>validate()));
test('selected native registration cannot disappear',()=>spoof(resolve('tests/yul-composition/ledger.json'),v=>{const o=JSON.parse(v);delete o.pipelineRethrowEvidence;return Buffer.from(JSON.stringify(o));},()=>validate()));
test('review finding: pass requires exact empty row errors',()=>{const r=structuredClone(report);r.rows[0].errors=[{call:0,message:'failure'}];assert.throws(()=>validate(r),/passing report has missing\/nonempty native errors/);});

const optimized=report.rows[3],profile={pipeline:'viaIR',optimized:true};
const optCall=c=>validateNativeRethrowCall(c,oracle.plan[0],0,optimized.address,optimized.deployment.actual.returnData,profile);
test('H3 optimized trace exact, not arbitrary subset: only persistent7 remains',()=>{
 optCall(optimized.calls[0]);
 assert.deepEqual(optimized.calls[0].capture.operations.filter(o=>o.kind==='putStorage').map(o=>[o.frame,o.value]),[[0,word(7)]]);
 assert.deepEqual(optimized.calls[0].capture.operations.filter(o=>o.kind==='transient.put').map(o=>[o.frame,o.value]),[[0,word(17)],[1,word(51)],[0,word(34)]]);
});
for(const p of [undefined,null,{}, {pipeline:'viaIR',optimized:'true'}, {pipeline:'unknown',optimized:true},{pipeline:'viaIR',optimized:true,extra:true}])test('missing/malformed explicit profile '+JSON.stringify(p),()=>assert.throws(()=>validateNativeRethrowCall(optimized.calls[0],oracle.plan[0],0,optimized.address,optimized.deployment.actual.returnData,p)));
test('optimized call cannot use unoptimized profile',()=>assert.throws(()=>validateNativeRethrowCall(optimized.calls[0],oracle.plan[0],0,optimized.address,optimized.deployment.actual.returnData,{pipeline:'viaIR',optimized:false}),/persistent write journal/));
for(const[frame,value]of [[1,99],[0,8]])test('optimized trace rejects extra removed write '+value,()=>{
 const c=structuredClone(optimized.calls[0]),o=structuredClone(c.capture.operations.find(o=>o.kind==='putStorage'));o.frame=frame;o.value=word(value);c.capture.operations.push(o);assert.throws(()=>optCall(c));
});
for(const[row,name]of [[report.rows[0],'legacyoff'],[report.rows[1],'legacyon'],[report.rows[2],'IRoff']])test('other profile cannot drop reverted stores '+name,()=>{
 const c=structuredClone(row.calls[0]);c.capture.operations=c.capture.operations.filter(o=>o.kind!=='putStorage'||o.frame===0&&o.value===word(7));
 assert.throws(()=>validateNativeRethrowCall(c,oracle.plan[0],0,row.address,row.deployment.actual.returnData,{pipeline:row.pipeline,optimized:row.optimized}));
});
for(const[name,mutate]of Object.entries({
 'missing retained persistent7':c=>c.capture.operations=c.capture.operations.filter(o=>o.kind!=='putStorage'),
 'wrong retained persistent7':c=>c.capture.operations.find(o=>o.kind==='putStorage').value=word(8),
 'wrong optimized transient child51':c=>c.capture.operations.find(o=>o.kind==='transient.put'&&o.frame===1).value=word(50),
 'wrong optimized final world with equal bytes':c=>c.capture.post[c.capture.request.to].persistent[word(0)]=word(99),
 'wrong optimized child restore':c=>c.capture.frames[1].post[c.capture.request.to].persistent[word(0)]=word(8),
 'missing optimized rollback':c=>c.capture.operations=c.capture.operations.filter(o=>o.kind!=='revert'),
 'wrong optimized memory':c=>delete c.capture.frames[0].memory,
 'unvalidated extra call field':c=>c.extra=true
}))test(name,()=>{const c=structuredClone(optimized.calls[0]);mutate(c);assert.throws(()=>optCall(c));});
for(const[name,mutate]of Object.entries({
 'missing contract identity':r=>delete r.traceContract,
 'stale contract hash':r=>r.traceContract.sha256='0'.repeat(64),
 'unapproved generic contract':r=>r.traceContract.id='any-compiler',
 'wrong authorization':r=>r.traceContract.authorization='unapproved',
 'extra report field':r=>r.extra=true,
 'extra profile field':r=>r.rows[0].extra=true
}))test(name,()=>{const r=structuredClone(report);mutate(r);assert.throws(()=>validate(r));});

test('direct call helper rejects stale contract even when trace values still agree',()=>spoof(resolve('tests/yul-composition/rethrow-trace-contract.json'),v=>{const o=JSON.parse(v);o.id='unapproved-but-same-operations';return Buffer.from(JSON.stringify(o));},()=>optCall(optimized.calls[0])));
