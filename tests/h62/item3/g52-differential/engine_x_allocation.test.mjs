/** Guarded regression: wrong Engine-X preallocation membership, altered archived
 * bytes or inconsistent environment must not manufacture native payload matches.
 * Synthetic mutations below are controls, never extra fixture conformance cases.
 */
import test from 'node:test';import assert from 'node:assert/strict';
import {createReadStream,readFileSync,openSync,readSync,closeSync} from 'node:fs';
import {createGunzip} from 'node:zlib';import {createInterface} from 'node:readline';
import {createHash} from 'node:crypto';import {createRequire} from 'node:module';
import {pathToFileURL,fileURLToPath} from 'node:url';import {fork} from 'node:child_process';
import {bindEngineXAllocation,EngineXAllocations} from '../../../../scripts/h62/item3/g52-differential/engine_x_allocation.mjs';
import {convertEngineFixture} from '../../../../scripts/h62/item3/g52-differential/engine_payload_reference.mjs';
const bulk=process.env.G52_BULK;if(!bulk)throw new Error('G52_BULK required; never skip');
const source=createReadStream(bulk+'/engine-x-inputs.jsonl.gz').pipe(createGunzip());const lines=createInterface({input:source,crlfDelay:Infinity});let record;for await(const line of lines){record=JSON.parse(line);break;}lines.close();source.destroy();
const index=JSON.parse(readFileSync(bulk+'/engine-x-allocations-index.json','utf8'));const entry=index[record.fixture.preHash];const raw=Buffer.alloc(entry.length);const fd=openSync(bulk+'/engine-x-allocations.jsonl','r');let got=0;while(got<raw.length){const n=readSync(fd,raw,got,raw.length-got,entry.offset+got);if(!n)throw new Error('truncated control allocation');got+=n;}closeSync(fd);
test('actual archived allocation binds exact case/pre/genesis with no final account map claim',()=>{
 const bound=bindEngineXAllocation(record,entry,raw),decoded=JSON.parse(raw).allocation;
 assert.deepEqual(bound.record.fixture.pre,decoded.pre);assert.deepEqual(bound.record.fixture.genesisBlockHeader,decoded.genesis);assert.deepEqual(bound.record.fixture.postState,{});assert.equal(bound.binding.final_account_map_present,false);assert.equal(bound.binding.exact_case_membership,true);
 const reader=new EngineXAllocations(bulk+'/engine-x-allocations.jsonl',index);try{assert.deepEqual(reader.bind(record).binding,bound.binding);assert.deepEqual(reader.bind(record).binding,bound.binding);assert.equal(reader.reads,1);assert.equal(reader.hits,1);}finally{reader.close();}
});
test('wrong descriptor, case, fork, mixed schema and altered allocation bytes refuse',()=>{
 for(const mutate of [r=>{r.fixture.preHash='missing';},r=>{r.allocation_ref.length--;},r=>{r.case='not-an-archived-member';},r=>{r.fixture.network='Prague';},r=>{r.fixture.postState={};}]){const changed=structuredClone(record);mutate(changed);assert.throws(()=>bindEngineXAllocation(changed,entry,raw));}
 const changed=Buffer.from(raw);changed[0]^=1;assert.throws(()=>bindEngineXAllocation(record,entry,changed),/record digest mismatch/);
 const reader=new EngineXAllocations(bulk+'/engine-x-allocations.jsonl',{[record.fixture.preHash]:{...entry,offset:Number.MAX_SAFE_INTEGER}});try{assert.throws(()=>reader.bind(record),/bounds mismatch/);}finally{reader.close();}
});
test('self-consistent control descriptors still cannot hide environment/genesis disagreement',()=>{
 for(const mutate of [g=>{g.environment.currentGasLimit='0x01';},g=>{g.environment.blockHashes={'0x00':'0x01'};},g=>{g.preAccountCount++;}]){
  const decoded=JSON.parse(raw);mutate(decoded.allocation);const bytes=Buffer.from(JSON.stringify(decoded)+'\n');const changedEntry={...entry,length:bytes.length,record_sha256:createHash('sha256').update(bytes).digest('hex')};const changedRecord=structuredClone(record);changedRecord.allocation_ref={pre_hash:record.fixture.preHash,stream:'engine-x-allocations.jsonl',...changedEntry};assert.throws(()=>bindEngineXAllocation(changedRecord,changedEntry,bytes));
 }
});
test('real native validator rejects a wrong allocation pre-state root',{timeout:65000},async()=>{
 const bound=bindEngineXAllocation(record,entry,raw);const wrong=structuredClone(bound.record);const address=Object.keys(wrong.fixture.pre)[0];wrong.fixture.pre[address].nonce='0x123456';
 const require=createRequire(bulk+'/reference/package.json');const loaded=[];for(const name of ['@ethereumjs/common','@ethereumjs/block','@ethereumjs/util','micro-eth-signer/kzg.js','@paulmillr/trusted-setups/fast-peerdas.js'])loaded.push(await import(pathToFileURL(require.resolve(name)).href));const m={...loaded[0],...loaded[1],...loaded[2],kzg:new loaded[3].KZG(loaded[4].trustedSetup)};const converted=await convertEngineFixture(wrong,m);assert.equal(converted.status,'converted');
 const child=fork(fileURLToPath(new URL('../../../../scripts/h62/item3/g52-differential/eest_reference.mjs',import.meta.url)),['--worker',bulk],{execArgv:['--max-old-space-size=4096'],stdio:['ignore','ignore','inherit','ipc']});
 try{const result=await new Promise((resolve,reject)=>{const timer=setTimeout(()=>reject(new Error('native allocation control timeout')),60000);child.once('message',r=>{clearTimeout(timer);resolve(r);});child.once('error',reject);child.send(converted.record);});assert.equal(result.status,'reference_mismatch');assert.deepEqual(result.fields,['genesis_pre_state_root']);}finally{if(child.exitCode===null)await new Promise(done=>{child.once('close',done);child.kill('SIGKILL');});}
});
