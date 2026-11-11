/** Guarded regression: a rejection label or mutable receipt must not certify
 * substituted inputs, RPC errors or worker failures as successful execution.
 * At most four exact Engine-X indices per job; caller MUST use the existing
 * external serial process-group/time/AS/RSS guard. Internal guard is additional.
 * Results remain separate, unqualified reference observations, never Source,
 * positive payload, Engine RPC/forkchoice or full conformance credit.
 */
import {createReadStream,openSync,closeSync,readFileSync,writeFileSync,renameSync,existsSync,realpathSync} from 'node:fs';
import {createHash} from 'node:crypto';import {createGunzip} from 'node:zlib';
import {createInterface} from 'node:readline';import {createRequire} from 'node:module';
import {execFile,fork} from 'node:child_process';
import {resolve,sep} from 'node:path';import {fileURLToPath,pathToFileURL} from 'node:url';
import {EngineXAllocations} from './engine_x_allocation.mjs';
import {executeNativeWorker} from './engine_payload_reference.mjs';
import {executeExpectedInvalidEngineFixture,rejectionExitCode} from './engine_rejection_reference.mjs';
import {hostResourceGuard} from './host_resource_guard.mjs';

export function selectionIndices(values) {
 if(!Array.isArray(values)||values.length<1||values.length>4||values.some((n,i)=>!Number.isSafeInteger(n)||n<0||(i>0&&n<=values[i-1])))throw new Error('require one to four strictly increasing safe integer case indices');
 return [...values];
}
export function cliIndices(values) {
 if(values.some(value=>typeof value!=='string'||! /^(0|[1-9][0-9]*)$/.test(value)))throw new Error('noncanonical CLI case index');
 return selectionIndices(values.map(Number));
}
/** Metadata selection only; main independently archive-binds this file first.
 * Own both streams so early selection and parse errors cannot leak input fds. */
export async function* selectedRecords(path,indices) {
 indices=selectionIndices(indices);const wanted=new Set(indices);let scanned=0,selected=0;
 const file=createReadStream(path),source=file.pipe(createGunzip());
 file.on('error',error=>source.destroy(error));
 const lines=createInterface({input:source,crlfDelay:Infinity});
 try {
  for await(const line of lines) {
   const record=JSON.parse(line);
   if(record.index!==scanned++||record.status!=='input-only-not-executed'||typeof record.path!=='string'||typeof record.case!=='string')throw new Error('noncanonical archived case identity/order');
   if(!wanted.has(record.index))continue;
   yield record;
   if(++selected===indices.length)break;
  }
  if(selected!==indices.length)throw new Error('incomplete archived selection');
 } finally {lines.close();source.destroy();file.destroy();}
}
async function digest(path) {const hash=createHash('sha256');for await(const chunk of createReadStream(path))hash.update(chunk);return hash.digest('hex');}
async function stop(child) {
 if(!child||child.exitCode!==null||child.signalCode!==null)return;
 await new Promise(done=>{const finish=()=>{child.removeListener('exit',finish);child.removeListener('close',finish);done();};child.once('exit',finish);child.once('close',finish);child.kill('SIGKILL');});
}
export async function main(bulk,label,indices) {
 indices=selectionIndices(indices);
 if(typeof label!=='string'||!/^[a-z0-9-]+$/.test(label))throw new Error('invalid fresh rejection output label');
 bulk=realpathSync(bulk);const repo=realpathSync(fileURLToPath(new URL('../../../../',import.meta.url))),evidence=realpathSync(bulk+'/evidence');
 if([bulk,evidence].some(path=>path===repo||path.startsWith(repo+sep)))throw new Error('bulk/evidence must stay outside repository');
 const path=evidence+'/'+label;
 for(const suffix of ['.jsonl','.jsonl.partial','-summary.json','-summary.json.partial'])if(existsSync(path+suffix))throw new Error('rejection output label already exists');
 let verifier,worker,allocations,output;
 const guard=hostResourceGuard(()=>{verifier?.kill('SIGKILL');worker?.kill('SIGKILL');});
 try {
  const names=['engine_rejection_runner.mjs','engine_rejection_reference.mjs','engine_payload_reference.mjs','engine_payload_encoding.mjs','engine_x_allocation.mjs','eest_reference.mjs','eest_observation.mjs','blockchain_adapter.mjs','eest_rejection.mjs','host_resource_guard.mjs','serial_semantics.py','eest_export.py','archive_census.py','pipeline.py'];const sources={};
  for(const name of names)sources[name]=await digest(fileURLToPath(new URL('./'+name,import.meta.url)));
  // Run the existing independent archive regeneration, not receipt agreement.
  const binding=await new Promise((accept,reject)=>{
   verifier=execFile('python3',[fileURLToPath(new URL('./eest_export.py',import.meta.url)),'--verify','--format','blockchain_test_engine_x','--bulk',bulk],{maxBuffer:16*1024*1024,timeout:300000,killSignal:'SIGKILL',env:{...process.env,LEAN_NUM_THREADS:'1'}},(error,stdout,stderr)=>{
    verifier=undefined;if(error){reject(new Error('archive-derived rejection input verification failed: '+stderr));return;}
    try{accept(JSON.parse(stdout));}catch(error){reject(error);}
   });
  });
  guard.check();
  const files=['archive-inventory.jsonl.gz','engine-x-inputs.jsonl.gz','engine-x-allocations.jsonl','engine-x-allocations-index.json','evidence/archive-census.json'];
  const checkFiles=async()=>{for(const name of files)if(typeof binding.files?.[name]!=='string'||await digest(bulk+'/'+name)!==binding.files[name])throw new Error('archive-bound input changed: '+name);};
  if(binding.format!=='blockchain_test_engine_x'||!Number.isSafeInteger(binding.cases)||binding.cases<1||indices.at(-1)>=binding.cases)throw new Error('archive selection bound mismatch');
  await checkFiles();
  const lock=readFileSync(bulk+'/reference/package-lock.json');
  if(!lock.equals(readFileSync(new URL('../../../../tests/h62/item3/g52-differential/package-lock.json',import.meta.url))))throw new Error('native lock mismatch');
  const lockSha=await digest(bulk+'/reference/package-lock.json');
  allocations=new EngineXAllocations(bulk+'/engine-x-allocations.jsonl',JSON.parse(readFileSync(bulk+'/engine-x-allocations-index.json','utf8')));
  const require=createRequire(bulk+'/reference/package.json'),loaded=[];
  for(const name of ['@ethereumjs/common','@ethereumjs/block','@ethereumjs/util','micro-eth-signer/kzg.js','@paulmillr/trusted-setups/fast-peerdas.js','@ethereumjs/rlp'])loaded.push(await import(pathToFileURL(require.resolve(name)).href));
  const m={...loaded[0],...loaded[1],...loaded[2],...loaded[5],kzg:new loaded[3].KZG(loaded[4].trustedSetup)};
  const getWorker=()=>{
   if(!worker){worker=fork(fileURLToPath(new URL('./eest_reference.mjs',import.meta.url)),['--worker',bulk],{execArgv:['--max-old-space-size=4096'],stdio:['ignore','ignore','inherit','ipc']});const child=worker;child.on('error',()=>{});const clear=()=>{if(worker===child)worker=undefined;};child.once('exit',clear);child.once('close',clear);}
   return worker;
  };
  let nativeCalls=0,selected=0;const counts={},hash=createHash('sha256');
  output=openSync(path+'.jsonl.partial','wx');
  try {
   for await(const record of selectedRecords(bulk+'/engine-x-inputs.jsonl.gz',indices)) {
    guard.check();
    const bound=allocations.bind(record);
    const result=await executeExpectedInvalidEngineFixture(bound.record,m,r=>{nativeCalls++;return executeNativeWorker(getWorker,r,()=>guard.check());});
    const row={index:record.index,path:record.path,case:record.case,...result,allocation_binding:bound.binding,coverage_admitted:false,source_matches:0};
    const text=JSON.stringify(row)+'\n';hash.update(text);writeFileSync(output,text);selected++;counts[result.status]=(counts[result.status]??0)+1;
   }
  } finally {closeSync(output);output=undefined;}
  guard.check();if(selected!==indices.length)throw new Error('incomplete rejection selection');
  await checkFiles();if(await digest(bulk+'/reference/package-lock.json')!==lockSha)throw new Error('native lock changed during execution');
  for(const name of names)if(await digest(fileURLToPath(new URL('./'+name,import.meta.url)))!==sources[name])throw new Error('validator changed during execution: '+name);
  const summary={schema:1,original_format:'blockchain_test_engine_x',indices,selected,native_worker_calls:nativeCalls,counts,archive_binding:binding,reference_lock_sha256:lockSha,validator_sha256:sources,results_sha256:hash.digest('hex'),peak_aggregate_rss:guard.peakAggregateRss,coverage_admitted:false,source_matches:0,engine_rpc_complete:false,forkchoice_executed:false,differential_complete:false,full_conformance:false,final_account_map_present:false};
  guard.check();writeFileSync(path+'-summary.json.partial',JSON.stringify(summary,null,2)+'\n',{flag:'wx'});renameSync(path+'.jsonl.partial',path+'.jsonl');renameSync(path+'-summary.json.partial',path+'-summary.json');console.log(JSON.stringify({indices,counts,native_worker_calls:nativeCalls,coverage_admitted:false,source_matches:0}));return rejectionExitCode(counts);
 } finally {if(output!==undefined)closeSync(output);guard.stop();allocations?.close();await stop(verifier);await stop(worker);}
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url))process.exitCode=await main(process.argv[2],process.argv[3],cliIndices(process.argv.slice(4)));
