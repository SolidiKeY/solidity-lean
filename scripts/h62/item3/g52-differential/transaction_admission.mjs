/** Guarded regression: arbitrary host errors and expected fixture labels must
 * never manufacture transaction admission matches. Pinned Osaka serialized
 * transaction decoding/validation only: no world execution or source agreement.
 */
import {createRequire} from 'node:module';
import {createReadStream,readFileSync,writeFileSync,renameSync} from 'node:fs';
import {createGunzip} from 'node:zlib';
import {createInterface} from 'node:readline';
import {createHash} from 'node:crypto';
import {resolve,dirname} from 'node:path';
import {fileURLToPath,pathToFileURL} from 'node:url';
export function admissionCategories(message,facts={}) {
 if(facts.stage!=='decode'||facts.transaction_type!==4)return [];
 const formatMessages=new Set([
  'Invalid EIP-7702 transaction: chainId exceeds 2^256 - 1',
  'Invalid EIP-7702 transaction: nonce exceeds 2^64 - 1',
  'Invalid EIP-7702 transaction: authorization list item should have 6 elements',
  'Invalid EIP-7702 transaction: authority list element is a list, not bytes',
  'Invalid EIP-7702 transaction: address length should be 20 bytes',
  'EIP-7702 authorization list invalid: chainId is not defined'
 ]);
 if(formatMessages.has(message))return ['TransactionException.TYPE_4_INVALID_AUTHORIZATION_FORMAT'];
 if(facts.authorization_validator && /^(chainId|nonce) cannot have leading zeroes, received: 0x[0-9a-f]+$/.test(message))return ['TransactionException.TYPE_4_INVALID_AUTHORIZATION_FORMAT'];
 if(['Invalid EIP-7702 transaction: r exceeds 2^256 - 1','Invalid EIP-7702 transaction: s exceeds 2^256 - 1','Invalid EIP-7702 transaction: yParity should be fit within 1 byte (0 - 255)'].includes(message))return ['TransactionException.TYPE_4_INVALID_AUTHORITY_SIGNATURE'];
 if(message==='Invalid EIP-7702 transaction: authorization list is empty')return ['TransactionException.TYPE_4_EMPTY_AUTHORIZATION_LIST'];
 // Generic RLP decoder diagnostics do not locate an authorization failure.
 // They stay unsupported until an independent structural binding exists.
 return [];
}
export function classifyAdmission(expected,message,facts={}) {
 const categories=admissionCategories(message,facts);
 if(!categories.length)return {status:'unsupported',reason:'unclassified-serialized-transaction-rejection',actual_categories:[]};
 const matched=categories.filter(c=>expected.split('|').includes(c));
 return {status:matched.length?'reference_match':'reference_mismatch',fields:matched.length?[]:['rejection_category'],actual_categories:categories,matched_categories:matched};
}
async function digest(path){const h=createHash('sha256');for await(const b of createReadStream(path))h.update(b);return h.digest('hex');}
export async function main(bulk) {
 if(!bulk)throw new Error('usage: node transaction_admission.mjs H44_BULK');bulk=resolve(bulk);
 const json=name=>JSON.parse(readFileSync(resolve(bulk,name),'utf8'));
 const receipt=json('evidence/transaction-export.json'),census=json('evidence/archive-census.json');
 if(receipt.archive_sha256!=='5dd08fee0fb41bc2a59bc4ab1dc75b19723fc71fe6af2f855454d3283fba09b9'||receipt.stream_sha256!==await digest(bulk+'/transaction-inputs.jsonl.gz')||receipt.census_sha256!==await digest(bulk+'/evidence/archive-census.json')||census.inventory_sha256!==await digest(bulk+'/archive-inventory.jsonl.gz'))throw new Error('transaction export provenance mismatch');
 const lock=readFileSync(bulk+'/reference/package-lock.json');if(!lock.equals(readFileSync(new URL('../../../../tests/h62/item3/g52-differential/package-lock.json',import.meta.url))))throw new Error('installed/committed lock mismatch');
 const require=createRequire(bulk+'/reference/package.json');const loaded=[];
 for(const name of ['@ethereumjs/tx','@ethereumjs/common','@ethereumjs/util'])loaded.push(await import(pathToFileURL(require.resolve(name)).href));
 const nativeVersions={},nativeSources={};
 for(const name of ['@ethereumjs/tx','@ethereumjs/common','@ethereumjs/util']){const packageRoot=resolve(dirname(require.resolve(name)),'../..');const version=JSON.parse(readFileSync(packageRoot+'/package.json','utf8')).version;if(version!=='10.1.3')throw new Error('native package version mismatch');nativeVersions[name]=version;}
 for(const name of ['7702/tx.js','7702/constructors.js','capabilities/eip7702.js'])nativeSources[name]=await digest(resolve(dirname(require.resolve('@ethereumjs/tx')),name));
 const [txModule,commonModule,util]=loaded;const {Common,Mainnet,Hardfork}=commonModule;
 const expectedIds=[];const inventory=createInterface({input:createReadStream(bulk+'/archive-inventory.jsonl.gz').pipe(createGunzip()),crlfDelay:Infinity});
 for await(const l of inventory){const r=JSON.parse(l);if(r.role==='fixture'&&r.selection==='exact-osaka'&&r.format==='transaction_test')expectedIds.push([r.path,r.case]);}
 if(expectedIds.length!==receipt.cases)throw new Error('transaction inventory count mismatch');
 const rows=[],counts={},seen=new Set();const lines=createInterface({input:createReadStream(bulk+'/transaction-inputs.jsonl.gz').pipe(createGunzip()),crlfDelay:Infinity});
 for await(const line of lines) {
  const record=JSON.parse(line),f=record.fixture;
  if(record.index!==rows.length||seen.has(record.index)||JSON.stringify(expectedIds[record.index])!==JSON.stringify([record.path,record.case])||record.variant!==0||record.selected_fork!=='Osaka'||f._info?.['fixture-format']!=='transaction_test'||JSON.stringify(record.expected)!==JSON.stringify(f.result?.Osaka))throw new Error('transaction record identity/fork/expectation mismatch');
  seen.add(record.index);let outcome;let tx;let error;let stage='decode';
  try{tx=txModule.createTxFromRLP(util.hexToBytes(f.txbytes),{common:new Common({chain:Mainnet,hardfork:Hardfork.Osaka})});stage='validation';const errors=tx.getValidationErrors();if(errors.length)error=new Error(errors.join('\n'));else {stage='sender';tx.getSenderAddress();}}
  catch(e){error=e;}
  const expected=record.expected.exception;
  const facts={stage,transaction_type:Number.parseInt(f.txbytes.slice(2,4),16),authorization_validator:/verifyAuthorizationList.*\/capabilities\/eip7702\.js/.test(error?.stack??'')};
  if(error){outcome=expected?classifyAdmission(expected,error.message,facts):{status:'unsupported',reason:'valid-fixture-native-error-unclassified'};outcome.engine_reason=error.message;outcome.engine_error_name=error.name;outcome.engine_stack=error.stack?.slice(0,5000);}
  else if(expected)outcome={status:'reference_mismatch',fields:['serialized_transaction_admission'],reason:'expected-invalid serialized transaction accepted'};
  else outcome={status:'unsupported',reason:'valid-transaction-fixture-profile-pending'};
  rows.push({index:record.index,path:record.path,case:record.case,fixture_sha256:record.fixture_sha256,expected_exception:expected??null,expected_intrinsic_gas:record.expected.intrinsicGas??null,native_admission:error?'rejected':'accepted',validation_facts:facts,...outcome,scope:'serialized transaction validation only; no world execution',source_semantics:'unsupported-adapter-pending'});counts[outcome.status]=(counts[outcome.status]??0)+1;
 }
 if(rows.length!==receipt.cases)throw new Error('incomplete transaction coverage');
 const output=rows.map(r=>JSON.stringify(r)+'\n').join('');writeFileSync(bulk+'/evidence/transaction-admission.jsonl.partial',output);renameSync(bulk+'/evidence/transaction-admission.jsonl.partial',bulk+'/evidence/transaction-admission.jsonl');
 const summary={native_versions:nativeVersions,native_source_sha256:nativeSources,cases:rows.length,counts,native_rejected:rows.filter(r=>r.native_admission==='rejected').length,fixture_admission_complete:counts.reference_match===rows.length,execution_complete:false,differential_complete:false,source_semantics_unsupported:rows.length,export_sha256:await digest(bulk+'/evidence/transaction-export.json'),reference_lock_sha256:createHash('sha256').update(lock).digest('hex'),adapter_sha256:await digest(fileURLToPath(import.meta.url)),results_sha256:createHash('sha256').update(output).digest('hex')};
 writeFileSync(bulk+'/evidence/transaction-admission-summary.json.partial',JSON.stringify(summary,null,2)+'\n');renameSync(bulk+'/evidence/transaction-admission-summary.json.partial',bulk+'/evidence/transaction-admission-summary.json');console.log(JSON.stringify(summary));
 return counts.reference_mismatch?1:summary.fixture_admission_complete?0:2;
}
if(process.argv[1]&&resolve(process.argv[1])===fileURLToPath(import.meta.url))process.exitCode=await main(process.argv[2]);
