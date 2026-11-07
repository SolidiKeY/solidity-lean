import test from 'node:test';
import assert from 'node:assert/strict';
import fs,{readFileSync} from 'node:fs';
import {syncBuiltinESMExports} from 'node:module';
import {join,resolve} from 'node:path';
import {isDeepStrictEqual as eq} from 'node:util';
import {sha} from './harness.mjs';
import {verifyNativeRethrowInputs,validateNativeRethrowCall,validateNativeRethrowReport} from './observed-native-rethrow.mjs';
import {validateNativeRethrowCall as originalCall,validateNativeRethrowReport as originalReport} from './native-rethrow.mjs';
const BASE='/workspace/vy5-composition/native-rethrow-20261101',DIR=join(BASE,'observed-v2');
const report=JSON.parse(readFileSync(join(DIR,'report.json'))),oracle=JSON.parse(readFileSync('tests/yul-composition/observed-native-rethrow-expectations.json'));
const word=n=>'0x'+BigInt(n).toString(16).padStart(64,'0');
const validate=(r=report)=>validateNativeRethrowReport(r,DIR);
const call=(c,index=0)=>validateNativeRethrowCall(c,oracle.plan[index],index,report.rows[0].address,report.rows[0].deployment.actual.returnData);
test('fresh pinned audited36calls/4profiles/20Sourcebyte projections/eight executed negatives; no adequacy',()=>{
 validate();assert.equal(report.validation,'pass');assert.equal(report.fullProofGate,'pending');assert.equal(report.nativeExecution,'fresh-pinned-solc-evm');assert.equal(report.rows.length,4);assert.equal(report.rows.reduce((n,r)=>n+r.calls.length,0),36);assert.equal(report.rows.flatMap(r=>r.links).filter(l=>l.expectedMatch).length,20);assert.equal(report.rows.flatMap(r=>r.links).filter(l=>!l.expectedMatch).length,8);
 const l=JSON.parse(readFileSync('tests/yul-composition/observed-native-rethrow-ledger.json'));assert.equal(l.fullCoverage,false);assert.equal(l.obligations.length,24);assert.equal(l.combinations.length,6);
});
test('original immutable unaudited fixture remains STRICT FAILURE: all36calls retained, five optimized journal mismatches',()=>{
 const original=JSON.parse(readFileSync(join(BASE,'original-v3/report.json'))),plan=JSON.parse(readFileSync('tests/yul-composition/native-rethrow-expectations.json')).plan,freeze=JSON.parse(readFileSync(join(BASE,'pre-execution-freeze.json')));
 for(const[file,hash]of Object.entries(freeze.hashes))assert.equal(sha(readFileSync(file)),hash);
 assert.equal(original.validation,'mismatch');assert.equal(original.rows.length,4);assert.equal(original.rows.reduce((n,r)=>n+r.calls.length,0),36);assert.deepEqual(original.rows.map(r=>r.errors.length),[0,0,0,5]);
 assert.throws(()=>originalReport(original,join(BASE,'original-v3')));
 for(const row of original.rows)for(let i=0;i<plan.length;i++)if(row.pipeline==='viaIR'&&row.optimized&&[0,1,2,3,6].includes(i))assert.throws(()=>originalCall(row.calls[i],plan[i],i,row.address,row.deployment.actual.returnData),/ordered persistent write journal/);else originalCall(row.calls[i],plan[i],i,row.address,row.deployment.actual.returnData);
});
test('initial partial-frame API failure is fixed by a COMPLETE independent four-frame oracle',()=>{
 const c=report.rows[0].calls[0];assert.equal(c.capture.frames.length,4);call(c);
 const f=JSON.parse(readFileSync(join(BASE,'native-v1/legacy.capture.json'))),plan=JSON.parse(readFileSync('tests/yul-composition/native-rethrow-expectations.json')).plan;
 assert.equal(f.calls[0].capture.frames.length,2);originalCall(f.calls[0],plan[0],0,f.address,f.deployment.actual.returnData);
});
for(const key of ['actual','capture','index','signature'])test('missing native evidence '+key,()=>{const c=structuredClone(report.rows[0].calls[0]);delete c[key];assert.throws(()=>call(c));});
const mutations={
 'wrong call selector':c=>c.capture.request.input='0x00000000',
 'wrong request ordinal':c=>c.capture.transaction++,
 'wrong caller':c=>c.capture.request.caller=c.capture.request.to,
 'missing child frame':c=>c.capture.frames.pop(),
 'missing actual catch bytes':c=>delete c.capture.frames[0].lastCallReturnData,
 'wrong audit owner':c=>c.capture.frames[2].codeAddress=c.capture.request.caller,
 'wrong audit argument':c=>c.capture.frames[2].input='0x00000000',
 'missing rollback operation':c=>{const a=c.capture.operations.find(o=>o.kind==='revert');a.kind='commit';},
 'child rollback swapped with outer':c=>{for(const o of c.capture.operations)if(o.kind==='revert')o.frame=o.frame===0?1:0;},
 'wrong persistent write despite same returndata':c=>{const a=c.capture.operations.find(o=>o.kind==='putStorage'&&o.frame===1);a.value=word(98);},
 'wrong transient write despite same returndata':c=>{const a=c.capture.operations.find(o=>o.kind==='transient.put'&&o.frame===1);a.value=word(50);},
 'wrong final storage despite same returndata':c=>{c.capture.post[c.capture.request.to].persistent[word(0)]=word(8);},
 'wrong final transient despite same returndata':c=>{c.capture.post[c.capture.request.to].transient[word(0)]=word(17);},
 'wrong child post-prefix restoration':c=>c.capture.frames[1].post[c.capture.request.to].persistent[word(0)]=word(99),
 'wrong observable audit99 value':c=>c.capture.frames[2].pre[c.capture.request.to].persistent[word(0)]=word(98),
 'wrong observable audit8 value':c=>c.capture.frames[3].post[c.capture.request.to].persistent[word(0)]=word(9),
 'native balance drift with same bytes':c=>c.capture.post[c.capture.request.to].balance='1',
 'native caller nonce drift with same bytes':c=>c.capture.post[c.capture.request.caller].nonce='99',
 'native runtime code lost':c=>c.capture.post[c.capture.request.to].code='0x',
 'lost root memory':c=>delete c.capture.frames[0].memory,
 'rethrow final buffer confused with captured data':c=>{c.capture.frames[0].lastCallReturnData.bytes='0xdead';c.capture.frames[0].lastCallReturnData.length=2;},
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
test('selected native registration cannot disappear',()=>spoof(resolve('tests/yul-composition/ledger.json'),v=>{const o=JSON.parse(v);delete o.observedNativeRethrowEvidence;return Buffer.from(JSON.stringify(o));},()=>validate()));
test('review finding: pass requires exact empty row errors',()=>{const r=structuredClone(report);r.rows[0].errors=[{call:0,message:'failure'}];assert.throws(()=>validate(r),/passing report has missing\/nonempty native errors/);});
