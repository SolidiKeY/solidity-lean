/** Guarded regression: semantically invalid transactions must retain their
 * original bytes when transported to a native block decoder. Encoding is not
 * transaction admission, block execution, rollback evidence or a fixture pass.
 * Partial Osaka V4/V3 profile: legacy and types1/2/4, empty blob parameters.
 * Caller must independently archive-bind inputs and apply existing host bounds.
 */
import {createHash} from 'node:crypto';
const hex=/^0x(?:[0-9a-f]{2})*$/;
const hash=/^0x[0-9a-f]{64}$/;
const requireCondition=(condition,message)=>{if(!condition)throw new Error(message);};

export async function encodePayloadForNativeDecode(item,m) {
 requireCondition(item&&typeof item==='object'&&!Array.isArray(item),'payload request object required');
 requireCondition(Object.keys(item).every(key=>['params','newPayloadVersion','forkchoiceUpdatedVersion','validationError'].includes(key)),'unknown request/RPC error profile');
 requireCondition([4,'4'].includes(item.newPayloadVersion)&&[3,'3'].includes(item.forkchoiceUpdatedVersion)&&Array.isArray(item.params)&&item.params.length===4,'Osaka V4/V3 four-parameter profile required');
 const parameters=structuredClone(item.params),parametersSha256=createHash('sha256').update(JSON.stringify(parameters)).digest('hex');
 const [payload,blobHashes,parentBeaconBlockRoot,requests]=parameters;
 requireCondition(payload&&typeof payload==='object'&&!Array.isArray(payload)&&hash.test(payload.blockHash),'declared payload hash required');
 requireCondition(Array.isArray(blobHashes)&&blobHashes.length===0,'raw blob payload encoding pending');
 requireCondition(hash.test(parentBeaconBlockRoot)&&Array.isArray(requests),'beacon/request parameter shape');
 requireCondition(Array.isArray(payload.transactions)&&Array.isArray(payload.withdrawals),'transaction and withdrawal arrays required');
 const rawTransactions=[],body=[];
 for(const raw of payload.transactions) {
  requireCondition(typeof raw==='string'&&hex.test(raw)&&raw.length>2,'canonical transaction hex required');
  const bytes=m.hexToBytes(raw),typed=bytes[0]<0x80;
  requireCondition(!typed||[1,2,4].includes(bytes[0]),'raw typed transaction profile pending');
  const encoded=typed?bytes.slice(1):bytes,decoded=m.RLP.decode(encoded);
  requireCondition(Array.isArray(decoded)&&m.bytesToHex(m.RLP.encode(decoded))===m.bytesToHex(encoded),'canonical transaction RLP list required');
  rawTransactions.push(bytes);body.push(typed?bytes:decoded);
 }
 let last=-1;const requestHashes=[];
 for(const request of requests) {
  requireCondition(typeof request==='string'&&hex.test(request)&&request.length>=6,'canonical nonempty request encoding required');
  const bytes=m.hexToBytes(request);requireCondition(bytes[0]<=2&&bytes[0]>last,'request type/order pending');last=bytes[0];
  requestHashes.push(createHash('sha256').update(bytes).digest());
 }
 const requestsHash='0x'+createHash('sha256').update(Buffer.concat(requestHashes)).digest('hex');
 const common=new m.Common({chain:m.Mainnet,hardfork:m.Hardfork.Osaka,customCrypto:{kzg:m.kzg}});
 // The SDK trie helper reads serialize() only. These byte providers carry no
 // transaction validity assertion and are never passed to a block executor.
 const transactionsTrie=await m.genTransactionsTrieRoot(rawTransactions.map(bytes=>({serialize:()=>bytes})));
 const withdrawals=payload.withdrawals.map(data=>m.createWithdrawal(data));
 const withdrawalsRoot=await m.genWithdrawalsTrieRoot(withdrawals);
 const header=m.createBlockHeader({...payload,number:payload.blockNumber,receiptTrie:payload.receiptsRoot,mixHash:payload.prevRandao,coinbase:payload.feeRecipient,transactionsTrie,withdrawalsRoot,parentBeaconBlockRoot,requestsHash},{common});
 const blockHash=m.bytesToHex(header.hash());
 requireCondition(blockHash===payload.blockHash,'raw payload header hash disagreement');
 const rlp=m.bytesToHex(m.RLP.encode([header.raw(),body,[],withdrawals.map(w=>w.raw())]));
 return {role:'payload-byte-encoding-only',rlp,block_hash:blockHash,parameters_sha256:parametersSha256,transactions_validated:false,native_execution_evidence:false,source_matches:0};
}
