/** Guarded regression: prepared blockchain inputs must never become matches by
 * skipping header validation, trusting generated roots, or swallowing block errors.
 * Positive exact-Osaka fixture path only; expected-invalid blocks stay unsupported.
 */
export async function executeBlockchain(record, m, budget) {
  const f = record.fixture;
  if (f?.network !== 'Osaka' || f?._info?.['fixture-format'] !== 'blockchain_test' || f.sealEngine !== 'NoProof') return {status:'unsupported',reason:'blockchain-format-fork-seal'};
  if (!Array.isArray(f.blocks) || f.blocks.some(b => b.expectException || b.expectExceptionALL || !b.rlp)) return {status:'unsupported',reason:'expected-block-rejection-adapter-pending'};
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
  const blocks=[];let last=genesis;
  for(const item of f.blocks) {
    const block=createBlockFromRLP(hexToBytes(item.rlp),{common});
    if (bytesToHex(block.header.parentHash) !== bytesToHex(last.hash())) return {status:'unsupported',reason:'nonlinear-history-adapter-pending'};
    // No skip flags or generated commitments: the pinned VM validates all
    // supplied header roots and delegates header/history checks to the provider.
    const result=await runBlock(vm,{block,generate:false,skipBlockValidation:false,skipHeaderValidation:false,validateBlockSize:true,setHardfork:false});
    await chain.putBlock(block);
    blocks.push({number:block.header.number.toString(),hash:bytesToHex(block.hash()),state_root:bytesToHex(await vm.stateManager.getStateRoot()),gas_used:result.gasUsed?.toString()??null});
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
  return {status:fields.length?'reference_mismatch':'reference_match',fields,blocks,steps:budget.steps,
    header_validation:true,block_validation:true,block_size_validation:true,max_rlp_block_size:8388608,provider_consensus_validation_enabled:true,
    consensus_scope:'NoProof execution/header checks; no beacon consensus, signatures or fork-choice proof',
    post_state_scope:'fixture-declared accounts plus validated complete block header commitments',
    source_semantics:'unsupported-adapter-pending'};
}
