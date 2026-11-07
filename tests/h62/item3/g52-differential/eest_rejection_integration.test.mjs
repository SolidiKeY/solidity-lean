/** Guarded regression: an accepted transaction must fail an expected-invalid fixture; no acceptance is inferred from its label. Synthetic control only. */
import test from 'node:test';import assert from 'node:assert/strict';
import {createReadStream} from 'node:fs';import {createGunzip} from 'node:zlib';import {createInterface} from 'node:readline';
import {fork} from 'node:child_process';import {fileURLToPath} from 'node:url';
test('real EVM acceptance contradicts an injected expected-invalid label',{timeout:65000},async()=>{
 const bulk=process.env.G52_BULK;if(!bulk)throw new Error('G52_BULK required; never skip this integration control');
 const source=createReadStream(bulk+'/eest-inputs.jsonl.gz').pipe(createGunzip());const lines=createInterface({input:source,crlfDelay:Infinity});
 let record;for await(const line of lines){record=JSON.parse(line);break;}lines.close();source.destroy();
 assert.equal(record.index,0);assert.equal(record.post.expectException,undefined);
 record.post.expectException='TransactionException.NONCE_IS_MAX';
 const child=fork(fileURLToPath(new URL('../../../../scripts/h62/item3/g52-differential/eest_reference.mjs',import.meta.url)),['--worker',bulk],{execArgv:['--max-old-space-size=4096'],stdio:['ignore','ignore','inherit','ipc']});
 try{
  const response=await new Promise((resolve,reject)=>{const timer=setTimeout(()=>reject(new Error('control worker timeout')),60000);child.once('message',r=>{clearTimeout(timer);resolve(r);});child.once('error',e=>{clearTimeout(timer);reject(e);});child.once('exit',()=>{clearTimeout(timer);reject(new Error('worker exited before result'));});child.send(record);});
  assert.equal(response.status,'reference_mismatch');assert.deepEqual(response.fields,['transaction_admission']);
 }finally{if(child.exitCode===null)await new Promise(done=>{child.once('exit',done);child.kill('SIGKILL');});}
});
