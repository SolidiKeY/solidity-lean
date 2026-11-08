/** Guarded regression: Engine-X preHash names and case labels must never substitute
 * for exact archived allocation bytes, membership and genesis/world binding.
 * A missing final account map is not a successful final storage comparison.
 */
import {openSync,readSync,closeSync,fstatSync} from 'node:fs';
import {createHash} from 'node:crypto';
const canonical=value=>JSON.stringify(Object.entries(value).sort(([a],[b])=>a.localeCompare(b)));
const headerFields={currentBaseFee:'baseFeePerGas',currentBlobGasUsed:'blobGasUsed',
 currentCoinbase:'coinbase',currentDifficulty:'difficulty',currentExcessBlobGas:'excessBlobGas',
 currentGasLimit:'gasLimit',currentNumber:'number',currentRandom:'mixHash',
 currentTimestamp:'timestamp',parentBeaconBlockRoot:'parentBeaconBlockRoot',parentUncleHash:'uncleHash'};
export function bindEngineXAllocation(record,entry,raw) {
 const f=record.fixture,ref=record.allocation_ref;
 if(f?.network!=='Osaka'||f?._info?.['fixture-format']!=='blockchain_test_engine_x')throw new Error('Engine-X format/fork mismatch');
 if(Object.keys(f).sort().join(',')!==['_info','config','engineNewPayloads','lastblockhash','network','preHash'].sort().join(','))throw new Error('Engine-X fixture shape mismatch');
 if(!entry||!ref||canonical(ref)!==canonical({pre_hash:f.preHash,stream:'engine-x-allocations.jsonl',...entry}))throw new Error('Engine-X allocation descriptor mismatch');
 if(raw.length!==entry.length||createHash('sha256').update(raw).digest('hex')!==entry.record_sha256)throw new Error('Engine-X allocation record digest mismatch');
 const decoded=JSON.parse(raw),g=decoded.allocation;
 if(decoded.path!==entry.path||decoded.source_sha256!==entry.source_sha256)throw new Error('Engine-X allocation provenance mismatch');
 if(g?.network!==f.network||!Array.isArray(g.testIds)||g.testCount!==g.testIds.length||new Set(g.testIds).size!==g.testIds.length||!g.testIds.includes(record.case))throw new Error('Engine-X allocation case membership mismatch');
 if(!g.pre||typeof g.pre!=='object'||Array.isArray(g.pre)||g.preAccountCount!==Object.keys(g.pre).length)throw new Error('Engine-X allocation pre-state shape mismatch');
 const e=g.environment,h=g.genesis;
 if(!e||!h||Object.keys(e).sort().join(',')!==[...Object.keys(headerFields),'blockHashes','ommers','withdrawals'].sort().join(','))throw new Error('Engine-X environment shape mismatch');
 if(!e.blockHashes||Array.isArray(e.blockHashes)||Object.keys(e.blockHashes).length||!Array.isArray(e.ommers)||e.ommers.length||!Array.isArray(e.withdrawals)||e.withdrawals.length)throw new Error('Engine-X earlier history or genesis body unsupported');
 for(const [field,header] of Object.entries(headerFields))if(typeof e[field]!=='string'||typeof h[header]!=='string'||BigInt(e[field])!==BigInt(h[header]))throw new Error('Engine-X environment/genesis disagreement: '+field);
 return {record:{...record,fixture:{...f,_info:{...f._info,'fixture-format':'blockchain_test_engine'},pre:g.pre,genesisBlockHeader:h,postState:{}}},
  binding:{original_format:'blockchain_test_engine_x',pre_hash:f.preHash,allocation_path:entry.path,
   allocation_source_sha256:entry.source_sha256,allocation_record_sha256:entry.record_sha256,
   exact_case_membership:true,environment_genesis_checked:true,final_account_map_present:false}};
}
/** Caller verifies full stream/index hashes against the pinned export receipt first.
 * One cached raw record bounds retention; each case still rechecks its membership.
 */
export class EngineXAllocations {
 constructor(path,index){this.fd=openSync(path,'r');this.bytes=fstatSync(this.fd).size;this.index=index;this.cached=null;this.cacheKey=null;this.reads=0;this.hits=0;}
 bind(record){
  const key=record.fixture?.preHash;const entry=Object.hasOwn(this.index,key)?this.index[key]:null;
  if(!entry||!Number.isSafeInteger(entry.offset)||!Number.isSafeInteger(entry.length)||entry.offset<0||entry.length<1||entry.offset+entry.length>this.bytes)throw new Error('Engine-X allocation bounds mismatch');
  if(this.cacheKey!==key){const raw=Buffer.alloc(entry.length);let got=0;while(got<raw.length){const n=readSync(this.fd,raw,got,raw.length-got,entry.offset+got);if(!n)throw new Error('Engine-X truncated allocation record');got+=n;}this.cached=raw;this.cacheKey=key;this.reads++;}else this.hits++;
  return bindEngineXAllocation(record,entry,this.cached);
 }
 close(){if(this.fd!==null){closeSync(this.fd);this.fd=null;}}
}
