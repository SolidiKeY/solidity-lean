/** Guarded regression: noncanonical selections and coordinated mutable fixture
 * receipts cannot bypass the runner's independent archive check or earn matches.
 */
import test from 'node:test';import assert from 'node:assert/strict';
import {mkdtempSync,mkdirSync,writeFileSync,rmSync,existsSync,readdirSync,readlinkSync} from 'node:fs';
import {tmpdir} from 'node:os';import {join} from 'node:path';import {spawnSync} from 'node:child_process';import {fileURLToPath} from 'node:url';import {createHash,randomBytes} from 'node:crypto';import {gzipSync} from 'node:zlib';
import {selectionIndices,cliIndices,selectedRecords} from '../../../../scripts/h62/item3/g52-differential/engine_rejection_runner.mjs';

test('bounded exact selections preserve identity without coercion or duplicate work',()=>{
 const values=[0,3,8,Number.MAX_SAFE_INTEGER],out=selectionIndices(values);assert.deepEqual(out,values);assert.notEqual(out,values);
 assert.deepEqual(cliIndices(['0','2618']),[0,2618]);
 for(const bad of [[],[1,1],[2,1],[-1],[0.5],[NaN],[Infinity],[true],['1'],[Number.MAX_SAFE_INTEGER+1],[0,1,2,3,4],null])assert.throws(()=>selectionIndices(bad));
 for(const bad of [['01'],['+1'],['1.0'],['1e2'],[' 1'],['1 '],['-0'],['9007199254740992']])assert.throws(()=>cliIndices(bad));
});

test('runner refuses coordinated substituted inputs and receipts before SDK/native loading',{timeout:20000},()=>{
 const bulk=mkdtempSync(join(tmpdir(),'engine-rejection-substitution-'));
 try {
  mkdirSync(bulk+'/evidence');mkdirSync(bulk+'/upstream');
  const sha=b=>createHash('sha256').update(b).digest('hex');
  const fixture={index:0,path:'substituted',case:'substituted',status:'input-only-not-executed',fixture:{network:'Osaka',_info:{'fixture-format':'blockchain_test_engine_x'},engineNewPayloads:[{validationError:'TransactionException.INTRINSIC_GAS_TOO_LOW'}]}};
  const input=gzipSync(JSON.stringify(fixture)+'\n'),inventory=gzipSync(JSON.stringify({path:fixture.path,case:fixture.case,role:'fixture',selection:'exact-osaka',format:'blockchain_test_engine_x'})+'\n');
  writeFileSync(bulk+'/engine-x-inputs.jsonl.gz',input);writeFileSync(bulk+'/archive-inventory.jsonl.gz',inventory);
  const census=JSON.stringify({inventory_sha256:sha(inventory)});writeFileSync(bulk+'/evidence/archive-census.json',census);
  writeFileSync(bulk+'/evidence/engine-x-export.json',JSON.stringify({cases:1,archive_sha256:'5dd08fee0fb41bc2a59bc4ab1dc75b19723fc71fe6af2f855454d3283fba09b9',stream_sha256:sha(input),census_sha256:sha(census)}));
  writeFileSync(bulk+'/upstream/fixtures_develop-v5.3.0.tar.gz','substituted archive');
  const result=spawnSync(process.execPath,['--max-old-space-size=4096',fileURLToPath(new URL('../../../../scripts/h62/item3/g52-differential/engine_rejection_runner.mjs',import.meta.url)),bulk,'refusal-control','0'],{encoding:'utf8',timeout:15000});
  assert.equal(result.status,1,result.stderr);assert.match(result.stderr,/archive-derived rejection input verification failed/);assert.match(result.stderr,/archive/);
  for(const suffix of ['.jsonl','.jsonl.partial','-summary.json','-summary.json.partial'])assert.equal(existsSync(bulk+'/evidence/refusal-control'+suffix),false);
 } finally {rmSync(bulk,{recursive:true,force:true});}
});

// A compressed tail larger than the read buffer keeps the original file open
// at the first selected row, so this checks actual early-close behavior.
test('selection closes compressed input on early completion and parse failure',async()=>{
 const bulk=mkdtempSync(join(tmpdir(),'engine-rejection-stream-'));
 try {
  const path=bulk+'/input.gz',row=n=>({index:n,path:'fixture',case:'case'+n,status:'input-only-not-executed'});
  const tail=JSON.stringify({...row(1),padding:randomBytes(256*1024).toString('hex')})+'\n';
  const open=()=>readdirSync('/proc/self/fd').some(fd=>{try{return readlinkSync('/proc/self/fd/'+fd)===path;}catch{return false;}});
  for(const malformed of [false,true]) {
   writeFileSync(path,gzipSync((malformed?'invalid-json':JSON.stringify(row(0)))+'\n'+tail));
   const read=async()=>{const rows=[];for await(const value of selectedRecords(path,[0]))rows.push(value);return rows;};
   if(malformed)await assert.rejects(read,SyntaxError);else assert.deepEqual(await read(),[row(0)]);
   for(let tries=0;open()&&tries<100;tries++)await new Promise(done=>setTimeout(done,5));
   assert.equal(open(),false,'compressed input file descriptor leaked');
  }
 }finally{rmSync(bulk,{recursive:true,force:true});}
});
