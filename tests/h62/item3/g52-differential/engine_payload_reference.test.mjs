/** Guarded regression: wrong Engine domains, bad hashes/parameters or resource
 * refusals must not manufacture payload matches or complete RPC/source claims. */
import test from 'node:test';import assert from 'node:assert/strict';
import {createReadStream,mkdtempSync,mkdirSync,symlinkSync,writeFileSync,readFileSync,rmSync} from 'node:fs';import {createGunzip,gzipSync} from 'node:zlib';import {createHash} from 'node:crypto';import {createInterface} from 'node:readline';import {createRequire} from 'node:module';import {pathToFileURL,fileURLToPath} from 'node:url';import {fork,spawnSync} from 'node:child_process';
import {convertEngineFixture,selectionRange,executeEngineFixture,engineExitCode} from '../../../../scripts/h62/item3/g52-differential/engine_payload_reference.mjs';
test('wrong fork/format and negative/version RPC profiles refuse before native conversion',async()=>{
 for(const f of [{network:'Prague'},{network:'Osaka',_info:{'fixture-format':'blockchain_test_sync'}},{network:'Osaka',_info:{'fixture-format':'blockchain_test_engine'},pre:{},postState:{},genesisBlockHeader:{},engineNewPayloads:[{params:[],newPayloadVersion:5,forkchoiceUpdatedVersion:3}]}])assert.equal((await convertEngineFixture({fixture:f},{})).status,'unsupported');
});
test('real constructors reject bad payload hash/blob parameters and native worker detects wrong post-state',{timeout:65000},async()=>{
 const bulk=process.env.G52_BULK;if(!bulk)throw new Error('G52_BULK required; never skip');const require=createRequire(bulk+'/reference/package.json');const loaded=[];for(const name of ['@ethereumjs/common','@ethereumjs/block','@ethereumjs/util','micro-eth-signer/kzg.js','@paulmillr/trusted-setups/fast-peerdas.js'])loaded.push(await import(pathToFileURL(require.resolve(name)).href));const m={...loaded[0],...loaded[1],...loaded[2],kzg:new loaded[3].KZG(loaded[4].trustedSetup)};
 const source=createReadStream(bulk+'/engine-inputs.jsonl.gz').pipe(createGunzip()),lines=createInterface({input:source,crlfDelay:Infinity});let record;for await(const line of lines){record=JSON.parse(line);break;}lines.close();source.destroy();
 const badHash=structuredClone(record);badHash.fixture.engineNewPayloads[0].params[0].blockHash='0x'+'00'.repeat(32);await assert.rejects(()=>convertEngineFixture(badHash,m),/Invalid blockHash/);
 const badGenesis=structuredClone(record);badGenesis.fixture.genesisBlockHeader.hash='0x'+'00'.repeat(32);
 for(const bad of [badGenesis,badHash]) {
  const result=await executeEngineFixture(bad,m,async()=>{throw new Error('unexpected native execution after conversion failure');});
  assert.equal(result.status,'engine_error');assert.equal(result.reason,'engine-conversion-validation-failed');
  assert.equal(engineExitCode({[result.status]:1}),1);
  const root=mkdtempSync(bulk+'/runner-hash-control-');
  try {
   mkdirSync(root+'/evidence');mkdirSync(root+'/reference');
   for(const name of ['package.json','package-lock.json','node_modules'])symlinkSync(bulk+'/reference/'+name,root+'/reference/'+name);
   const sha=b=>createHash('sha256').update(b).digest('hex');
   const input=gzipSync(JSON.stringify(bad)+'\n'),inventory=gzipSync(JSON.stringify({role:'fixture',selection:'exact-osaka',format:'blockchain_test_engine',path:bad.path,case:bad.case})+'\n');
   writeFileSync(root+'/engine-inputs.jsonl.gz',input);writeFileSync(root+'/archive-inventory.jsonl.gz',inventory);
   const census=JSON.stringify({inventory_sha256:sha(inventory)});writeFileSync(root+'/evidence/archive-census.json',census);
   writeFileSync(root+'/evidence/engine-export.json',JSON.stringify({cases:1,archive_sha256:'5dd08fee0fb41bc2a59bc4ab1dc75b19723fc71fe6af2f855454d3283fba09b9',stream_sha256:sha(input),census_sha256:sha(census)}));
   const run=spawnSync(process.execPath,['--max-old-space-size=4096',fileURLToPath(new URL('../../../../scripts/h62/item3/g52-differential/engine_payload_reference.mjs',import.meta.url)),root,'1','conversion-failure'],{encoding:'utf8',timeout:20000});
   assert.equal(run.status,1,run.stderr);
   const row=JSON.parse(readFileSync(root+'/evidence/conversion-failure.jsonl','utf8'));
   assert.equal(row.status,'engine_error');assert.equal(row.reason,'engine-conversion-validation-failed');
  } finally {rmSync(root,{recursive:true,force:true});}

 }
 const blobs=structuredClone(record);blobs.fixture.engineNewPayloads[0].params[1]=['0x'+'00'.repeat(32)];assert.equal((await convertEngineFixture(blobs,m)).reason,'engine-blob-parameter-disagreement');
 const wrongState=structuredClone(record);const address=Object.keys(wrongState.fixture.postState)[0];wrongState.fixture.postState[address].nonce='0x1234';const converted=await convertEngineFixture(wrongState,m);assert.equal(converted.status,'converted');
 const child=fork(fileURLToPath(new URL('../../../../scripts/h62/item3/g52-differential/eest_reference.mjs',import.meta.url)),['--worker',bulk],{execArgv:['--max-old-space-size=4096'],stdio:['ignore','ignore','inherit','ipc']});
 try{const result=await new Promise((resolve,reject)=>{const timer=setTimeout(()=>reject(new Error('native control timeout')),60000);child.once('message',r=>{clearTimeout(timer);resolve(r);});child.once('error',reject);child.send(converted.record);});assert.equal(result.status,'reference_mismatch');assert.ok(result.fields.includes('post-account:'+address));}finally{if(child.exitCode===null)await new Promise(done=>{child.once('close',done);child.kill('SIGKILL');});}
});
test('oversized parent heap is refused before any payload can run',()=>{
 const bulk=process.env.G52_BULK;if(!bulk)throw new Error('G52_BULK required');const result=spawnSync(process.execPath,['--max-old-space-size=8192',fileURLToPath(new URL('../../../../scripts/h62/item3/g52-differential/engine_payload_reference.mjs',import.meta.url)),bulk,'1','heap-refusal-control'],{encoding:'utf8',timeout:10000});assert.notEqual(result.status,0);assert.match(result.stderr,/parent heap prerequisite/);
});

test('resumed selections are nonempty bounded ranges without rounding or wrap',()=>{
 assert.deepEqual(selectionRange(21124,20),{start:0,end:20});
 assert.deepEqual(selectionRange(21124,20,20),{start:20,end:40});
 assert.deepEqual(selectionRange(21124,20,21120),{start:21120,end:21124});
 assert.deepEqual(selectionRange(Number.MAX_SAFE_INTEGER,Number.MAX_SAFE_INTEGER,1),{start:1,end:Number.MAX_SAFE_INTEGER});
 for(const args of [[0,20,0],[10,0,0],[10,2,-1],[10,2,10],[10,1.5,0],[10,1,NaN],[10,Infinity,0],[10,1,Number.MAX_SAFE_INTEGER+1]])assert.throws(()=>selectionRange(...args),/invalid Engine selection range/);
});
