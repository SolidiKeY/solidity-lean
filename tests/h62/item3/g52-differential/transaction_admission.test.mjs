/** Guarded regression: expected labels, host errors and unlocated RLP failures
 * cannot become serialized-transaction conformance; authority bounds need the
 * native type/stage and ambiguous fields need actual validator provenance. */
import {createReadStream,mkdtempSync,mkdirSync,symlinkSync,writeFileSync,readFileSync,existsSync,rmSync} from 'node:fs';import {createGunzip,gzipSync} from 'node:zlib';import {createInterface} from 'node:readline';import {createHash} from 'node:crypto';import {spawnSync} from 'node:child_process';import {fileURLToPath} from 'node:url';
import test from 'node:test';import assert from 'node:assert/strict';
import {admissionCategories,classifyAdmission,envelopeRepairFacts} from '../../../../scripts/h62/item3/g52-differential/transaction_admission.mjs';
const facts={stage:'decode',transaction_type:4,authorization_validator:true};
test('known native authorization categories bind observed errors',()=>{
 const format='TransactionException.TYPE_4_INVALID_AUTHORIZATION_FORMAT',sig='TransactionException.TYPE_4_INVALID_AUTHORITY_SIGNATURE';
 assert.equal(classifyAdmission(format,'Invalid EIP-7702 transaction: nonce exceeds 2^64 - 1',facts).status,'reference_match');
 assert.equal(classifyAdmission(sig+'|TransactionException.TYPE_4_INVALID_AUTHORITY_SIGNATURE_S_TOO_HIGH','Invalid EIP-7702 transaction: s exceeds 2^256 - 1',facts).status,'reference_match');
 assert.equal(classifyAdmission(format,'Invalid EIP-7702 transaction: s exceeds 2^256 - 1',facts).status,'reference_mismatch');
});
test('host errors and generic RLP errors remain unsupported',()=>{
 for(const message of ['RangeError: memory exhausted','invalid RLP: remainder must be zero','invalid RLP: total length is larger than the data'])assert.equal(classifyAdmission('TransactionException.TYPE_4_INVALID_AUTHORIZATION_FORMAT',message,facts).status,'unsupported');
});
test('stage/type and validator provenance cannot be inferred from expected category',()=>{
 const message='nonce cannot have leading zeroes, received: 0x0000';
 assert.deepEqual(admissionCategories(message),[]);assert.deepEqual(admissionCategories(message,{...facts,authorization_validator:false}),[]);
 for(const f of [{...facts,stage:'sender'},{...facts,transaction_type:2}])assert.deepEqual(admissionCategories('Invalid EIP-7702 transaction: authorization list is empty',f),[]);
 assert.deepEqual(admissionCategories(message,facts),['TransactionException.TYPE_4_INVALID_AUTHORIZATION_FORMAT']);
});

test('only exact type4 envelope mutations with a validated canonical repair classify',()=>{
 const error='invalid RLP: remainder must be zero';let observed;
 const repair=envelopeRepairFacts(Uint8Array.of(4,1,0),error,candidate=>{observed=[...candidate];return true;});assert.deepEqual(observed,[4,1]);
 assert.equal(classifyAdmission('TransactionException.TYPE_4_INVALID_AUTHORIZATION_FORMAT',error,{...facts,envelope_repair:repair}).status,'reference_match');
 for(const validation of [()=>false,()=>{throw new Error('native rejection');}])assert.deepEqual(envelopeRepairFacts(Uint8Array.of(4,1,0),error,validation),{});
 assert.deepEqual(envelopeRepairFacts(Uint8Array.of(2,1,0),error,()=>true),{});assert.deepEqual(envelopeRepairFacts(Uint8Array.of(4,1,9),error,()=>true),{});
 assert.deepEqual(envelopeRepairFacts(Uint8Array.of(4,1,0),'RangeError',()=>true),{});
});
test('one-byte truncation witness is diagnostic-specific, not an arbitrary expected-label override',()=>{
 const message='invalid RLP: total length is larger than the data';let observed;
 const repair=envelopeRepairFacts(Uint8Array.of(4,1),message,candidate=>{observed=[...candidate];return true;});assert.deepEqual(observed,[4,1,0]);
 assert.equal(classifyAdmission('TransactionException.TYPE_4_EMPTY_AUTHORIZATION_LIST',message,{...facts,envelope_repair:repair}).status,'reference_mismatch');
 assert.equal(classifyAdmission('TransactionException.TYPE_4_INVALID_AUTHORIZATION_FORMAT','invalid RLP: remainder must be zero',{...facts,envelope_repair:repair}).status,'unsupported');
});

test('coordinated transaction, expectation, inventory and receipt substitution cannot certify a corpus',{timeout:280000},async()=>{
 const bulk=process.env.G52_BULK;if(!bulk)throw new Error('G52_BULK required; missing private corpus is never a pass');
 const source=createReadStream(bulk+'/transaction-inputs.jsonl.gz').pipe(createGunzip()),lines=createInterface({input:source,crlfDelay:Infinity});let record;for await(const line of lines){record=JSON.parse(line);break;}lines.close();source.destroy();
 record.expected={...record.expected,intrinsicGas:'0x0'};record.fixture.result.Osaka=record.expected;
 const root=mkdtempSync(bulk+'/transaction-substitution-control-');
 try{
  for(const name of ['evidence','reference','upstream'])mkdirSync(root+'/'+name);
  for(const name of ['package.json','package-lock.json','node_modules'])symlinkSync(bulk+'/reference/'+name,root+'/reference/'+name);
  symlinkSync(bulk+'/upstream/fixtures_develop-v5.3.0.tar.gz',root+'/upstream/fixtures_develop-v5.3.0.tar.gz');
  const sha=b=>createHash('sha256').update(b).digest('hex'),input=gzipSync(JSON.stringify(record)+'\n'),inventory=gzipSync(JSON.stringify({role:'fixture',selection:'exact-osaka',format:'transaction_test',path:record.path,case:record.case,variants:1})+'\n');
  writeFileSync(root+'/transaction-inputs.jsonl.gz',input);writeFileSync(root+'/archive-inventory.jsonl.gz',inventory);
  const census={...JSON.parse(readFileSync(bulk+'/evidence/archive-census.json','utf8')),inventory_sha256:sha(inventory)};const censusBytes=JSON.stringify(census);writeFileSync(root+'/evidence/archive-census.json',censusBytes);
  const receipt={...JSON.parse(readFileSync(bulk+'/evidence/transaction-export.json','utf8')),cases:1,stream_sha256:sha(input),census_sha256:sha(censusBytes)};writeFileSync(root+'/evidence/transaction-export.json',JSON.stringify(receipt));
  const result=spawnSync(process.execPath,['--max-old-space-size=4096',fileURLToPath(new URL('../../../../scripts/h62/item3/g52-differential/transaction_admission.mjs',import.meta.url)),root],{encoding:'utf8',timeout:250000});
  assert.equal(result.status,1,result.stderr);assert.match(result.stderr,/input differs from pinned archive: (transaction-inputs\.jsonl\.gz|archive-inventory\.jsonl\.gz|evidence\/archive-census\.json)/);assert.equal(existsSync(root+'/evidence/transaction-admission-summary.json'),false);
 }finally{rmSync(root,{recursive:true,force:true});}
});
