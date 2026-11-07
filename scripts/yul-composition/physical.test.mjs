/** Real pinned compiler/EVM controls; expected state and byte windows were
 * derived before execution in physical-20261031/before-execution-pinned.json. */
import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,mkdtempSync,chmodSync}from'node:fs';
import {checkedCompiler,compileRecord}from'./harness.mjs';
import {runFixture,validateFixtureEvidence,HOST}from'./upstream.mjs';
import {compareUpstreamState,predictedAliases,checkUpstreamOracles}from'./oracles.mjs';
const out=mkdtempSync('/workspace/vy5-composition/remaining-20261031/tests-');chmodSync(out,0o755);console.log('physical oracle evidence: '+out);
const compiler=checkedCompiler('/workspace/vy5-composition/soljson-v0.8.38+commit.1835d247.js');let counter=0;
const compile=i=>compileRecord(compiler,i,out+'/compile-'+counter++).output;
const rows=checkUpstreamOracles(readFileSync('tests/yul-composition/upstream-state-oracles.json','utf8')),names=rows.slice(5).map(r=>r.path),cases=new Map(),word=n=>'0x'+BigInt(n).toString(16).padStart(64,'0');
for(const path of names)test('source-derived physical oracle complete runtime profiles: '+path.split('/').at(-1),async()=>{
 const result=await runFixture(path,'/workspace/vy5-composition/corpus',compile);cases.set(path.split('/').at(-1),result);writeFileSync(out+'/'+path.split('/').at(-1)+'.json',JSON.stringify(result,null,2));
 assert.equal(result.status,'working',JSON.stringify(result.variants.map(v=>v.reason)));validateFixtureEvidence(result,'/workspace/vy5-composition/corpus');
 for(const v of result.variants){assert.equal(v.stateComparison.status,'match',JSON.stringify(v.stateComparison));assert.equal(v.observed.length,result.plan.calls.length);}
});
function reject(name,mutate){const f=cases.get(name),v=structuredClone(f.variants[0]);mutate(v);const result=compareUpstreamState(f,v,HOST.sender);assert(['mismatch','blocked'].includes(result.status),JSON.stringify(result));return result;}
function changeWorld(c,slot,value,kind='persistent',address=predictedAliases(HOST.sender).self){c.post[address][kind][slot]=value;c.frames[0].post=structuredClone(c.post);}
test('wrong physical slot/value/offset/pointer cannot hide behind equal return bytes',()=>{
 for(const name of ['inline_assembly_storage_access.sol','inline_assembly_storage_access_inside_function.sol','inline_assembly_storage_access_local_var.sol','inline_assembly_storage_access_via_pointer.sol'])reject(name,v=>{
  const c=v.observed[0].capture,key=Object.keys(c.post[predictedAliases(HOST.sender).self].persistent)[0];changeWorld(c,key,word(8));
 });
 reject('inline_assembly_storage_access_via_pointer.sol',v=>changeWorld(v.observed[2].capture,word(0),word(7)));
 reject('slot_access_via_mapping_pointer.sol',v=>{const r=v.observed[1].capture.frames[0].regions.find(r=>r.opcode==='RETURN'),bytes=Buffer.from(r.bytes.slice(2),'hex');bytes.set(Buffer.from(word(2).slice(2),'hex'),Number(r.offset));r.bytes='0x'+bytes.toString('hex');});
});
test('MCOPY overlap/direction/zero-length/byte-window mutants preserve actual output but fail state oracle',()=>{
 const data=Buffer.concat(Array.from({length:12},(_,i)=>Buffer.alloc(8,0x22+0x11*i))),wrong=Buffer.from(data);for(let i=0;i<48;i++)wrong[32+i]=wrong[16+i];
 reject('mcopy_overlap.sol',v=>{const r=v.observed[0].capture.frames[0].regions.find(r=>r.opcode==='RETURN'),b=Buffer.from(r.bytes.slice(2),'hex');b.set(wrong,Number(r.offset)+64);r.bytes='0x'+b.toString('hex');});
 for(const name of ['mcopy.sol','mcopy_empty.sol'])reject(name,v=>{const r=v.observed[0].capture.frames[0].regions.find(r=>r.opcode==='RETURN'),b=Buffer.from(r.bytes.slice(2),'hex');b[Number(r.offset)+64]^=255;r.bytes='0x'+b.toString('hex');});
 reject('mcopy_overlap.sol',v=>delete v.observed[0].capture.frames[0].regions);
});
test('ordered transient self-call identity and reset evidence cannot be lost/reordered/stale',()=>{
 const name='transient_storage_multiple_calls_different_transactions.sol';
 reject(name,v=>{v.observed[0].capture.frames[1].input=v.observed[0].capture.frames[2].input;});
 reject(name,v=>v.observed[0].capture.frames.reverse());
 reject(name,v=>changeWorld(v.observed[1].capture,word(42),word(131),'transient'));
 reject(name,v=>{const c=v.observed[0].capture;c.operations=c.operations.filter(o=>o.kind!=='transient.clear').map((o,i)=>({...o,sequence:i}));});
 reject('transient_storage_multiple_transactions.sol',v=>changeWorld(v.observed[2].capture,word(0),word(42),'transient'));
 reject('transient_storage_reset_between_creation_runtime.sol',v=>v.observed[1].capture.transaction=1);
 reject('inline_assembly_transient_storage_access_inside_function.sol',v=>changeWorld(v.observed[0].capture,word(1),word(7),'transient'));
});
test('CREATE child pointer and low-level delegate-owner expectations use no observed address oracle',()=>{
 const a=predictedAliases(HOST.sender);reject('transient_storage_selfdestruct.sol',v=>changeWorld(v.observed[2].capture,word(0),word(BigInt(a.child))));
 reject('transient_storage_low_level_calls.sol',v=>{const c=v.observed[0].capture,o=c.operations.find(o=>o.kind==='transient.put'&&o.address===a.self&&o.value===word(6));o.address=a.caller;});
 const row=rows.find(r=>r.path.endsWith('/transient_storage_low_level_calls.sol'));assert(row.premises.some(s=>s.includes('CREATE2 targets independently')));assert(!row.pendingDomains.some(s=>s.includes('target identity')));
});
test('full source-plan, stale source, missing selected oracle and reordered identical-signature calls fail closed',()=>{
 const f=cases.get('slot_access_via_mapping_pointer.sol'),v=f.variants[0],bad=structuredClone(f);bad.plan.calls.reverse();assert.equal(compareUpstreamState(bad,v,HOST.sender).status,'blocked');
 reject('slot_access_via_mapping_pointer.sol',v=>{[v.observed[0],v.observed[1]]=[v.observed[1],v.observed[0]];});
 const stale=structuredClone(f);stale.sourceSha256='wrong';assert.equal(compareUpstreamState(stale,v,HOST.sender).status,'blocked');
 const missing=structuredClone(f);delete missing.variants[0].stateComparison;assert.throws(()=>validateFixtureEvidence(missing,'/workspace/vy5-composition/corpus'));
 const mismatch=reject('inline_assembly_storage_access.sol',v=>{changeWorld(v.observed[0].capture,word(1),word(99));delete v.observed[1].capture;});assert.equal(mismatch.status,'mismatch');
});

test('coordinated root selector/argument and deployment initcode mutations cannot forge request identity',()=>{
 const name='inline_assembly_storage_access.sol',source=cases.get(name);
 reject(name,v=>{const o=v.observed[0];o.requestData='0xdeadbeef';o.capture.request.input=o.requestData;o.capture.frames[0].input=o.requestData;});
 reject('slot_access_via_mapping_pointer.sol',v=>{const o=v.observed[1];o.requestData=o.requestData.slice(0,10)+word(99).slice(2);o.capture.request.input=o.requestData;o.capture.frames[0].input=o.requestData;});
 const bad=structuredClone(source),d=bad.variants[0].deployment;d.requestData='0xdeadbeef';d.capture.request.input=d.requestData;d.capture.frames[0].input=d.requestData;assert.throws(()=>validateFixtureEvidence(bad,'/workspace/vy5-composition/corpus'),/initcode/);
 const ctor=structuredClone(cases.get('transient_storage_reset_between_creation_runtime.sol')),v=ctor.variants[0],o=v.observed[0];o.requestData='0xdeadbeef';o.capture.request.input=o.requestData;o.capture.frames[0].input=o.requestData;assert.throws(()=>validateFixtureEvidence(ctor,'/workspace/vy5-composition/corpus'));
});
