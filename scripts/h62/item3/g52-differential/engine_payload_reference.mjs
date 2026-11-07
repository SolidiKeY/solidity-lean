/** Guarded regression: Engine payload conversion must preserve declared hashes,
 * blob/request parameters and full native header/state validation. Native payload
 * observations do not establish Engine RPC/fork-choice or source conformance.
 */
import {createReadStream,createWriteStream,readFileSync,writeFileSync,renameSync} from 'node:fs';
import {createGunzip} from 'node:zlib';import {createInterface} from 'node:readline';
import {createRequire} from 'node:module';import {fork} from 'node:child_process';
import {createHash} from 'node:crypto';import {resolve} from 'node:path';
import {once} from 'node:events';import {hostResourceGuard} from './host_resource_guard.mjs';
import {fileURLToPath,pathToFileURL} from 'node:url';
export async function convertEngineFixture(record,m) {
 const f=record.fixture;
 if(f?.network!=='Osaka'||f?._info?.['fixture-format']!=='blockchain_test_engine')return {status:'unsupported',reason:'engine-format-fork'};
 if(!f.pre||!f.postState||!f.genesisBlockHeader||!Array.isArray(f.engineNewPayloads))return {status:'unsupported',reason:'engine-world-data-pending'};
 const allowed=['forkchoiceUpdatedVersion','newPayloadVersion','params'];
 if(f.engineNewPayloads.some(p=>Object.keys(p).some(k=>!allowed.includes(k))||![4,'4'].includes(p.newPayloadVersion)||![3,'3'].includes(p.forkchoiceUpdatedVersion)||!Array.isArray(p.params)||p.params.length!==4))return {status:'unsupported',reason:'engine-rpc-negative-or-version-profile-pending'};
 const common=new m.Common({chain:m.Mainnet,hardfork:m.Hardfork.Osaka,customCrypto:{kzg:m.kzg}});
 const header={...f.genesisBlockHeader,logsBloom:f.genesisBlockHeader.bloom};delete header.hash;delete header.bloom;
 const genesis=m.createBlock({header,transactions:[],withdrawals:[]},{common});
 if(m.bytesToHex(genesis.hash())!==f.genesisBlockHeader.hash)throw new Error('Engine genesis hash conversion mismatch');
 const blocks=[];const hashes=[];
 for(const item of f.engineNewPayloads) {
  const [payload,blobHashes,parentBeaconBlockRoot,requests]=item.params;
  if(!Array.isArray(blobHashes)||!Array.isArray(requests)||!/^0x[0-9a-f]{64}$/.test(parentBeaconBlockRoot))return {status:'unsupported',reason:'engine-parameter-shape'};
  let last=-1;const requestHashes=[];
  for(const request of requests){if(typeof request!=='string'||!/^0x(?:[0-9a-f]{2})+$/.test(request))return {status:'unsupported',reason:'engine-request-encoding'};const bytes=m.hexToBytes(request);if(bytes.length<2||bytes[0]>2||bytes[0]<=last)return {status:'unsupported',reason:'engine-request-order-or-empty'};last=bytes[0];requestHashes.push(createHash('sha256').update(bytes).digest());}
  const requestsHash='0x'+createHash('sha256').update(Buffer.concat(requestHashes)).digest('hex');
  const block=await m.createBlockFromExecutionPayload({...payload,parentBeaconBlockRoot,requestsHash},{common});
  const actualBlobHashes=block.transactions.flatMap(tx=>(tx.blobVersionedHashes??[]));
  if(JSON.stringify(blobHashes)!==JSON.stringify(actualBlobHashes))return {status:'unsupported',reason:'engine-blob-parameter-disagreement'};
  hashes.push(m.bytesToHex(block.hash()));blocks.push({rlp:m.bytesToHex(block.serialize())});
 }
 return {status:'converted',record:{fixture:{...f,_info:{...f._info,'fixture-format':'blockchain_test','original-fixture-format':'blockchain_test_engine'},sealEngine:'NoProof',genesisRLP:m.bytesToHex(genesis.serialize()),blocks}},binding:{original_format:'blockchain_test_engine',payload_versions:4,forkchoice_version:3,genesis_hash:m.bytesToHex(genesis.hash()),payload_block_hashes:hashes,blob_parameters_checked:true,request_hashes_derived_from_exact_parameters:true}};
}
async function digest(path){const hash=createHash('sha256');for await(const b of createReadStream(path))hash.update(b);return hash.digest('hex');}
export async function main(bulk,limit=20,label='engine-payload-pilot') {
 if(!bulk||!Number.isInteger(limit)||limit<1||!/^[a-z0-9-]+$/.test(label))throw new Error('usage: engine_payload_reference.mjs H44_BULK LIMIT LABEL');bulk=resolve(bulk);
 let child;const guard=hostResourceGuard(()=>{if(child)child.kill('SIGKILL');});
 try {
 const json=p=>JSON.parse(readFileSync(bulk+'/'+p,'utf8'));const receipt=json('evidence/engine-export.json'),census=json('evidence/archive-census.json');
 if(receipt.archive_sha256!=='5dd08fee0fb41bc2a59bc4ab1dc75b19723fc71fe6af2f855454d3283fba09b9'||receipt.stream_sha256!==await digest(bulk+'/engine-inputs.jsonl.gz')||receipt.census_sha256!==await digest(bulk+'/evidence/archive-census.json')||census.inventory_sha256!==await digest(bulk+'/archive-inventory.jsonl.gz'))throw new Error('Engine provenance mismatch');
 if(!readFileSync(bulk+'/reference/package-lock.json').equals(readFileSync(new URL('../../../../tests/h62/item3/g52-differential/package-lock.json',import.meta.url))))throw new Error('native lock mismatch');
 const inventory=[];const input=createInterface({input:createReadStream(bulk+'/archive-inventory.jsonl.gz').pipe(createGunzip()),crlfDelay:Infinity});for await(const line of input){const r=JSON.parse(line);if(r.role==='fixture'&&r.selection==='exact-osaka'&&r.format==='blockchain_test_engine')inventory.push([r.path,r.case]);}if(inventory.length!==receipt.cases)throw new Error('Engine inventory count mismatch');
 const require=createRequire(bulk+'/reference/package.json');const loaded=[];for(const name of ['@ethereumjs/common','@ethereumjs/block','@ethereumjs/util','micro-eth-signer/kzg.js','@paulmillr/trusted-setups/fast-peerdas.js'])loaded.push(await import(pathToFileURL(require.resolve(name)).href));const m={...loaded[0],...loaded[1],...loaded[2],kzg:new loaded[3].KZG(loaded[4].trustedSetup)};
 const worker=()=>{if(!child){child=fork(fileURLToPath(new URL('./eest_reference.mjs',import.meta.url)),['--worker',bulk],{execArgv:['--max-old-space-size=4096'],stdio:['ignore','ignore','inherit','ipc']});const c=child;c.on('error',()=>{});c.once('close',()=>{if(child===c)child=undefined;});}return child;};
 async function execute(record){guard.check();const c=worker();return new Promise(resolveResult=>{let done=false,stopped=false,failure=null;const finish=r=>{if(done)return;done=true;clearTimeout(timer);c.removeListener('message',message);c.removeListener('close',closed);c.removeListener('error',error);resolveResult(r);};const message=r=>{if(!stopped)finish(r);};const closed=()=>finish({status:'unsupported',reason:failure??(stopped?'native-worker-timeout':'native-worker-exited')});const error=()=>{if(done)return;stopped=true;failure='native-worker-error';c.kill('SIGKILL');};const timer=setTimeout(()=>{stopped=true;c.kill('SIGKILL');},60000);c.once('message',message);c.once('close',closed);c.once('error',error);c.send(record,e=>{if(e)error(e);});});}
 const counts={};let selected=0;const path=bulk+'/evidence/'+label+'.jsonl';const output=createWriteStream(path+'.partial');const resultHash=createHash('sha256');const source=createReadStream(bulk+'/engine-inputs.jsonl.gz').pipe(createGunzip());const lines=createInterface({input:source,crlfDelay:Infinity});
 try{for await(const line of lines){guard.check();if(selected>=limit)break;const record=JSON.parse(line);if(record.index!==selected||JSON.stringify([record.path,record.case])!==JSON.stringify(inventory[record.index])||record.status!=='input-only-not-executed')throw new Error('Engine identity mismatch');let result;
 try{const converted=await convertEngineFixture(record,m);if(converted.status!=='converted')result=converted;else{const native=await execute(converted.record);result={...native,status:native.status==='reference_match'?'payload_reference_match':native.status==='reference_mismatch'?'payload_reference_mismatch':native.status,binding:converted.binding};}}catch(error){result={status:'unsupported',reason:'engine-conversion-unclassified',conversion_error:String(error)};}
 guard.check();const row={index:record.index,path:record.path,case:record.case,...result,engine_rpc_complete:false,forkchoice_executed:false,source_semantics:'unsupported-adapter-pending'};const text=JSON.stringify(row)+'\n';resultHash.update(text);if(!output.write(text))await once(output,'drain');selected++;counts[row.status]=(counts[row.status]??0)+1;if(selected%100===0)console.log(JSON.stringify({cases:selected,counts}));}}
 finally{lines.close();source.destroy();if(child)await new Promise(done=>{child.once('close',done);child.kill('SIGKILL');});output.end();await once(output,'finish');}
 guard.check();if(selected!==Math.min(limit,receipt.cases))throw new Error('Incomplete Engine payload selection');renameSync(path+'.partial',path);
 const summary={selected,expected:receipt.cases,counts,payload_execution_only:true,engine_fixture_conformance_complete:false,engine_rpc_complete:false,differential_complete:false,source_semantics_unsupported:receipt.cases,export_sha256:await digest(bulk+'/evidence/engine-export.json'),input_sha256:receipt.stream_sha256,inventory_sha256:census.inventory_sha256,reference_lock_sha256:await digest(bulk+'/reference/package-lock.json'),adapter_sha256:await digest(fileURLToPath(import.meta.url)),resource_guard_sha256:await digest(fileURLToPath(new URL('./host_resource_guard.mjs',import.meta.url))),native_worker_sha256:await digest(fileURLToPath(new URL('./eest_reference.mjs',import.meta.url))),native_block_adapter_sha256:await digest(fileURLToPath(new URL('./blockchain_adapter.mjs',import.meta.url))),rejection_adapter_sha256:await digest(fileURLToPath(new URL('./eest_rejection.mjs',import.meta.url))),peak_aggregate_rss:guard.peakAggregateRss,results_sha256:resultHash.digest('hex')};guard.check();writeFileSync(bulk+'/evidence/'+label+'-summary.json.partial',JSON.stringify(summary,null,2)+'\n');renameSync(bulk+'/evidence/'+label+'-summary.json.partial',bulk+'/evidence/'+label+'-summary.json');console.log(JSON.stringify(summary));return counts.payload_reference_mismatch||counts.engine_error?1:2;
 } finally {guard.stop();if(child)await new Promise(done=>{child.once('close',done);child.kill('SIGKILL');});}
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url))process.exitCode=await main(process.argv[2],Number(process.argv[3]??20),process.argv[4]??'engine-payload-pilot');
