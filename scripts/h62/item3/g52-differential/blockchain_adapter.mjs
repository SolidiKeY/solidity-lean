import {createHash} from 'node:crypto';
/** Guarded regression: prepared blockchain inputs must never become matches by
 * skipping header validation, trusting generated roots, or swallowing block errors.
 * Exact-Osaka only; unknown rejection diagnostics stay unsupported.
 */
import {classifyBlockRejection} from './eest_rejection.mjs';

// Retain native transaction outcomes without tracing or re-executing the engine.
export function transactionObservations(block, result, bytesToHex) {
  if(result.results?.length!==block.transactions.length || result.receipts?.length!==block.transactions.length) throw new Error('incomplete native block transaction results');
  const logs=xs=>xs.map(([address,topics,data])=>({address:bytesToHex(address),topics:topics.map(t=>bytesToHex(t)),data:bytesToHex(data)}));
  return result.results.map((r,index)=>{
    const tx=block.transactions[index], e=r.execResult, receipt=result.receipts[index];
    if(!e || !(e.returnValue instanceof Uint8Array) || typeof e.executionGasUsed!=='bigint' || typeof r.totalGasSpent!=='bigint' || typeof receipt.cumulativeBlockGasUsed!=='bigint') throw new Error('missing native transaction observation');
    const observedLogs=logs(e.logs??[]), receiptLogs=logs(receipt.logs);
    if(JSON.stringify(observedLogs)!==JSON.stringify(receiptLogs) || receipt.status!==(e.exceptionError?0:1)) throw new Error('native receipt/execution outcome disagreement');
    return {index,hash:bytesToHex(tx.hash()),type:tx.type,output:bytesToHex(e.returnValue),execution_exception:e.exceptionError?.error??null,logs:observedLogs,receipt_status:receipt.status,receipt_cumulative_gas_used:receipt.cumulativeBlockGasUsed.toString(),total_gas_spent:r.totalGasSpent.toString(),execution_gas_used:e.executionGasUsed.toString(),native_gas_refund_counter:r.gasRefund.toString(),gas_limit:tx.gasLimit.toString()};
  });
}

/** Guarded regression: a gas-cap decoder label alone cannot bind a rejection
 * to an input transaction. Reproduce the first SDK transaction constructor
 * refusal and derive canonical gas/type/index/digest from exact block RLP.
 * This helper supplies facts only; callers still observe native root/head.
 */
export function gasLimitDecodeFacts(rlp,message,m,common) {
 const diagnostic=/^Transaction gas limit (0|[1-9][0-9]*) exceeds the maximum allowed by EIP-7825 \((0|[1-9][0-9]*)\)$/.exec(message);
 if(!diagnostic)return undefined;
 const requireCondition=(ok,why)=>{if(!ok)throw new Error(why);};
 requireCondition(common.isActivatedEIP(7825)&&!common.isActivatedEIP(8037),'gas-cap fork not active');
 const txCommon=common.copy();txCommon.updateParams(m.paramsTx);
 const cap=txCommon.param('maxTransactionGasLimit');
 const bytes=m.hexToBytes(rlp),decoded=m.RLP.decode(bytes);
 requireCondition(Array.isArray(decoded)&&Array.isArray(decoded[1])&&m.bytesToHex(m.RLP.encode(decoded))===rlp,'noncanonical decoder input block');
 for(const [index,entry] of decoded[1].entries()) {
  const raw=entry instanceof Uint8Array?entry:m.RLP.encode(entry);
  let failure;
  try {m.createTxFromRLP(raw,{common});}catch(error){failure=error;}
  if(!failure)continue;
  requireCondition(failure.message===message,'gas-cap error is not first input constructor refusal');
  const typed=raw[0]<0x80,type=typed?raw[0]:0;
  requireCondition([0,1,2,4].includes(type),'gas-cap raw type pending');
  const encoded=typed?raw.slice(1):raw,fields=m.RLP.decode(encoded),gasIndex=type===0?2:type===1?3:4;
  requireCondition(Array.isArray(fields)&&m.bytesToHex(m.RLP.encode(fields))===m.bytesToHex(encoded),'noncanonical gas-cap transaction');
  const gasBytes=fields[gasIndex];requireCondition(gasBytes instanceof Uint8Array&&gasBytes.length<=8&&(gasBytes.length===0||gasBytes[0]!==0),'noncanonical gas-cap integer');
  const gas=gasBytes.length?BigInt(m.bytesToHex(gasBytes)):0n;
  requireCondition(gas>cap&&gas.toString()===diagnostic[1]&&cap.toString()===diagnostic[2],'gas-cap diagnostic differs from input/fork');
  return {stage:'decode',transaction_index:index,transactionType:type,gasLimit:gas.toString(),maximumGasLimit:cap.toString(),transaction_sha256:createHash('sha256').update(raw).digest('hex')};
 }
 throw new Error('gas-cap diagnostic without an input constructor refusal');
}

export async function executeBlockchain(record, m, budget) {
  const f = record.fixture;
  if (f?.network !== 'Osaka' || f?._info?.['fixture-format'] !== 'blockchain_test' || f.sealEngine !== 'NoProof') return {status:'unsupported',reason:'blockchain-format-fork-seal'};
  if (!Array.isArray(f.blocks) || f.blocks.some(b => !b.rlp)) return {status:'unsupported',reason:'missing-block-rlp'};
  const {Common,createCustomCommon,Mainnet,Hardfork,createBlockFromRLP,createBlockchain,createVM,runBlock,Account,createAddressFromString,hexToBytes,bytesToHex,RLP,keccak256,kzg}=m;
  // Constant-fork EEST networks activate Osaka at genesis. The real chain DB
  // re-derives hardforks when reading historical headers, so Mainnet activation
  // heights cannot describe these fixtures even with current hardfork=Osaka.
  const lastFork=Mainnet.hardforks.findIndex(h=>h.name===Hardfork.Osaka);
  if(lastFork<0) throw new Error('Osaka fork parameters unavailable');
  const hardforks=Mainnet.hardforks.slice(0,lastFork+1).map(h=>({name:h.name,block:0}));
  const common=createCustomCommon({chainId:1,hardforks},Mainnet,{hardfork:Hardfork.Osaka,eips:[7934],params:{7934:{maxRlpBlockSize:8388608}},customCrypto:{kzg}});
  // EEST v5.3.0 commit6824474 pins EIP7934 at 8MiB (10MiB minus
  // 2MiB safety margin). The reference's Osaka defaults omit its activation.
  if(!common.isActivatedEIP(7934) || common.param('maxRlpBlockSize')!==8388608n) throw new Error('pinned block-size rule inactive');
  const genesis=createBlockFromRLP(hexToBytes(f.genesisRLP),{common});
  if(bytesToHex(genesis.hash())!==f.genesisBlockHeader.hash) return {status:'reference_mismatch',fields:['genesis_hash']};
  const chain=await createBlockchain({common,genesisBlock:genesis,validateBlocks:true,validateConsensus:true,hardforkByHeadBlockNumber:false});
  if(typeof chain.validateHeader!=='function') throw new Error('real header validator unavailable');
  const vm=await createVM({common,blockchain:chain});
  if(vm.evm.DEBUG) return {status:'unsupported',reason:'debug-tracer-enabled'};
  const word=n=>hexToBytes('0x'+BigInt(n).toString(16).padStart(64,'0'));
  for(const [address,a] of Object.entries(f.pre)) {
    const key=createAddressFromString(address);
    await vm.stateManager.putAccount(key,new Account(BigInt(a.nonce),BigInt(a.balance)));
    if(a.code!=='0x') await vm.stateManager.putCode(key,hexToBytes(a.code));
    for(const [slot,value] of Object.entries(a.storage)) await vm.stateManager.putStorage(key,word(slot),word(value));
  }
  const initialRoot=bytesToHex(await vm.stateManager.getStateRoot());
  if(initialRoot!==bytesToHex(genesis.header.stateRoot)) return {status:'reference_mismatch',fields:['genesis_pre_state_root'],initialRoot};
  const blocks=[],rejections=[];let last=genesis,currentTx;
  vm.events.on('beforeTx', tx=>{currentTx=tx;});
  for(const [blockIndex,item] of f.blocks.entries()) {
    const expectedException=item.expectException??item.expectExceptionALL;
    const beforeRoot=bytesToHex(await vm.stateManager.getStateRoot());
    const beforeHead=bytesToHex((await chain.getCanonicalHeadHeader()).hash());
    let block,result;currentTx=undefined;let stage='decode';
    try {
      block=createBlockFromRLP(hexToBytes(item.rlp),{common});
      if (bytesToHex(block.header.parentHash) !== bytesToHex(last.hash())) return {status:'unsupported',reason:'nonlinear-history-adapter-pending'};
      stage='provider-validation';
      await chain.validateBlock(block);
      stage='runBlock';
      // No generated commitments or validation skips. Native block errors revert
      // the VM checkpoint; observe that rollback instead of repairing the state.
      result=await runBlock(vm,{block,generate:false,skipBlockValidation:false,skipHeaderValidation:false,validateBlockSize:true,setHardfork:false});
    } catch(error) {
      if(!expectedException) throw error;
      if(error.message.includes('H44_HOST_STEP_LIMIT')) throw error;
      const afterRoot=bytesToHex(await vm.stateManager.getStateRoot());
      const afterHead=bytesToHex((await chain.getCanonicalHeadHeader()).hash());
      const facts=stage==='decode'?(gasLimitDecodeFacts(item.rlp,error.message,m,common)??{stage}):{stage};
      const errorTxIndex=/^invalid transactions: errors at tx ([0-9]+):/.exec(error.message);
      const diagnosticTx=errorTxIndex?block?.transactions[Number(errorTxIndex[1])]:currentTx;
      if(diagnosticTx) {
        currentTx=diagnosticTx;
        facts.transactionType=currentTx.type;
        if(error.message.startsWith('INTRINSIC_GAS_TOO_LOW:') || /^invalid transactions: errors at tx [0-9]+: gasLimit is too low\./.test(error.message)) {
          facts.gasLimit=currentTx.gasLimit.toString();facts.intrinsicGas=currentTx.getIntrinsicGas().toString();
          facts.floorGas=m.getCalldataFloorGas(currentTx,currentTx.getSenderAddress()).toString();
        }
      }
      const classified=classifyBlockRejection(expectedException,error.message,facts,beforeRoot,afterRoot,beforeHead,afterHead);
      const rejection={...classified,block_index:blockIndex,expected_exception:expectedException,engine_reason:error.message,validation_facts:facts,before_state_root:beforeRoot,after_state_root:afterRoot,before_head:beforeHead,after_head:afterHead};
      if(classified.status!=='reference_match')return {...rejection,blocks,rejections,source_semantics:'unsupported-adapter-pending'};
      rejections.push(rejection);continue;
    }
    if(expectedException) return {status:'reference_mismatch',fields:['block_admission'],reason:'expected-invalid block accepted',block_index:blockIndex,expected_exception:expectedException,native_block_hash:bytesToHex(block.hash()),validation_stages:['decode','provider-validation','runBlock'],observed:{state_root:bytesToHex(await vm.stateManager.getStateRoot()),gas_used:result.gasUsed.toString(),transactions:transactionObservations(block,result,bytesToHex)},source_semantics:'unsupported-adapter-pending'};
    await chain.putBlock(block);
    blocks.push({number:block.header.number.toString(),hash:bytesToHex(block.hash()),state_root:bytesToHex(await vm.stateManager.getStateRoot()),gas_used:result.gasUsed?.toString()??null,transactions:transactionObservations(block,result,bytesToHex)});
    last=block;
  }
  const fields=[];
  if(bytesToHex(last.hash())!==f.lastblockhash) fields.push('lastblockhash');
  const expectedKeys=['balance','code','nonce','storage'];
  for(const [address,a] of Object.entries(f.postState)) {
    if(!a || Object.keys(a).sort().join(',')!==expectedKeys.join(',')) return {status:'unsupported',reason:'partial-post-state-shape'};
    const key=createAddressFromString(address);const actual=await vm.stateManager.getAccount(key);
    if((actual?.nonce??0n)!==BigInt(a.nonce) || (actual?.balance??0n)!==BigInt(a.balance)) fields.push('post-account:'+address);
    if(bytesToHex(await vm.stateManager.getCode(key))!==a.code) fields.push('post-code:'+address);
    const expectedStore={};
    for(const [slot,value] of Object.entries(a.storage)) {
      if(BigInt(value)===0n) continue;
      let v=BigInt(value).toString(16);if(v.length%2)v='0'+v;
      expectedStore[keccak256(word(slot))]=bytesToHex(RLP.encode(hexToBytes('0x'+v)));
    }
    const actualStore=actual?await vm.stateManager.dumpStorage(key):{};
    const canonical=x=>JSON.stringify(Object.entries(x).sort());
    if(canonical(expectedStore)!==canonical(actualStore)) fields.push('post-storage:'+address);
  }
  return {status:fields.length?'reference_mismatch':'reference_match',fields,blocks,rejections,steps:budget.steps,
    observation_limits:['native transaction outputs/logs/gas retained; fixture commits receipts/state but has no direct return/revert-byte expectation','source executable semantics not connected; no isolated per-transaction storage snapshot claim','native_gas_refund_counter is the engine counter, not necessarily the capped applied refund'],
    header_validation:true,block_validation:true,block_size_validation:true,max_rlp_block_size:8388608,provider_consensus_validation_enabled:true,
    consensus_scope:'NoProof execution/header checks; no beacon consensus, signatures or fork-choice proof',
    post_state_scope:'fixture-declared accounts plus validated complete block header commitments',
    source_semantics:'unsupported-adapter-pending'};
}
