/** Guarded regression: arbitrary host errors, wrong rejection categories and
 * mutated state must never satisfy an EEST expected-invalid transaction.
 * Classify only pinned EthereumJS validation diagnostics; never infer a reason
 * from the expected fixture label. Gas facts come from the actual engine tx.
 */
export function rejectionCategories(message, facts = {}) {
  const prefix = 'TransactionException.';
  const result = [];
  const add = name => result.push(prefix + name);
  if (/^INTRINSIC_GAS_TOO_LOW: tx gas limit [0-9]+ is lower than the minimum gas limit of [0-9]+(?: |$)/.test(message)) {
    if (facts.gasLimit !== undefined && facts.intrinsicGas !== undefined && BigInt(facts.gasLimit) < BigInt(facts.intrinsicGas)) add('INTRINSIC_GAS_TOO_LOW');
    if (facts.gasLimit !== undefined && facts.floorGas !== undefined && BigInt(facts.gasLimit) < BigInt(facts.floorGas)) add('INTRINSIC_GAS_BELOW_FLOOR_GAS_COST');
    return result;
  }
  const rules = [
    [/^Transaction gas limit [0-9]+ exceeds the maximum allowed by EIP-7825 \([0-9]+\)/, 'GAS_LIMIT_EXCEEDS_MAXIMUM'],
    [/^tx causes total blob gas of [0-9]+ to exceed maximum blob gas per block of [0-9]+/, 'TYPE_3_TX_MAX_BLOB_GAS_ALLOWANCE_EXCEEDED'],
    [/^[0-9]+ blobs exceeds max [0-9]+ blobs per tx \(EIP-7594\)/, 'TYPE_3_TX_BLOB_COUNT_EXCEEDED'],
    [/^the initcode size of this transaction is too large:/, 'INITCODE_SIZE_EXCEEDED'],
    [/^Transaction's (maxFeePerGas|gasPrice) \([0-9]+\) is less than the block's baseFeePerGas/, 'INSUFFICIENT_MAX_FEE_PER_GAS'],
    [/^versioned hash does not start with KZG commitment version(?: |$)/, 'TYPE_3_TX_INVALID_BLOB_VERSIONED_HASH'],
    [/^tx should contain at least one blob(?: |$)/, 'TYPE_3_TX_ZERO_BLOBS'],
    [/^Transaction's maxFeePerBlobGas [0-9]+\) is less than block blobGasPrice/, 'INSUFFICIENT_MAX_FEE_PER_BLOB_GAS'],
    [/^sender doesn't have enough funds to send tx\. The (max|upfront) cost is:/, 'INSUFFICIENT_ACCOUNT_FUNDS'],
    [/^nonce cannot equal or exceed MAX_UINT64(?: |$)/, 'NONCE_IS_MAX'],
    [/^gas limit \* gasPrice cannot exceed MAX_INTEGER/, 'GASLIMIT_PRICE_PRODUCT_OVERFLOW'],
    [/^tx has a higher gas limit than the block(?: |$)/, 'GAS_ALLOWANCE_EXCEEDED'],
    [/^maxFeePerGas cannot be less than maxPriorityFeePerGas/, 'PRIORITY_GREATER_THAN_MAX_FEE_PER_GAS'],
    [/^invalid sender address, address is not EOA \(EIP-3607\)/, 'SENDER_NOT_EOA'],
    [/^Invalid EIP-7702 transaction: authorization list is empty(?: |$)/, 'TYPE_4_EMPTY_AUTHORIZATION_LIST'],
  ];
  for (const [pattern, category] of rules) if (pattern.test(message)) add(category);
  if (/^tx should have a "to" field and cannot be used to create contracts(?: |$)/.test(message)) {
    if (facts.transactionType === 3) add('TYPE_3_TX_CONTRACT_CREATION');
    if (facts.transactionType === 4) add('TYPE_4_TX_CONTRACT_CREATION');
  }
  return result;
}
export function classifyRejection(expected, message, facts, before, after, expectedRoot, expectedLogs, emptyLogsHash) {
  const categories = rejectionCategories(message, facts);
  if (!categories.length) return {status:'unsupported',reason:'unclassified-transaction-rejection',actual_categories:[]};
  const alternatives = expected.split('|');
  const matched = categories.filter(category => alternatives.includes(category));
  const fields = [];
  if (!matched.length) fields.push('rejection_category');
  if (before !== after) fields.push('rejection_rollback');
  if (after !== expectedRoot) fields.push('state_root');
  if (emptyLogsHash !== expectedLogs) fields.push('logs_hash');
  return {status:fields.length?'reference_mismatch':'reference_match',fields,actual_categories:categories,matched_categories:matched};
}


// Block rejection mapping uses the observed native diagnostic, never the fixture
// label as evidence. Unknown errors are not conformance; chain/state rollback is
// mandatory even for a recognized category. Native runBlock results only.
export function blockRejectionCategories(message, facts = {}) {
  // validateData reports tx errors in a fixed wrapper before runTx's beforeTx
  // event. The adapter binds any referenced index to the actual decoded tx.
  const wrapped=/^invalid transactions: errors at tx [0-9]+: (.*)$/.exec(message);
  const diagnostic=wrapped?wrapped[1]:message;
  const categories=rejectionCategories(diagnostic,facts);
  if(/^gasLimit is too low\. The gasLimit is lower than the minimum gas limit of [0-9]+ \((?:intrinsic gas [0-9]+|calldata floor [0-9]+ \(intrinsic [0-9]+\))\), the gas limit is: [0-9]+ \(block number=/.test(diagnostic)) {
    if(facts.gasLimit!==undefined && facts.intrinsicGas!==undefined && BigInt(facts.gasLimit)<BigInt(facts.intrinsicGas))categories.push('TransactionException.INTRINSIC_GAS_TOO_LOW');
    if(facts.gasLimit!==undefined && facts.floorGas!==undefined && BigInt(facts.gasLimit)<BigInt(facts.floorGas))categories.push('TransactionException.INTRINSIC_GAS_BELOW_FLOOR_GAS_COST');
  }
  const rules=[
    [/^Block size exceeds maximum RLP block size limit: [0-9]+ bytes > [0-9]+ bytes(?: |$)/,'BlockException.RLP_BLOCK_LIMIT_EXCEEDED'],
    [/^Block size exceeds limit: [0-9]+ > [0-9]+$/,'BlockException.RLP_BLOCK_LIMIT_EXCEEDED'],
    [/^expected blob gas: [0-9]+, got: [0-9]+$/,'BlockException.INCORRECT_EXCESS_BLOB_GAS'],
    [/^block excessBlobGas mismatch: have [0-9]+, want [0-9]+$/,'BlockException.INCORRECT_EXCESS_BLOB_GAS'],
    [/^block blobGasUsed mismatch: have [0-9]+, want [0-9]+$/,'BlockException.INCORRECT_BLOB_GAS_USED'],
    [/^invalid transactions: invalid blobGasUsed expected=[0-9]+ actual=[0-9]+ \(block number=/,'BlockException.INCORRECT_BLOB_GAS_USED'],
    [/^blob transaction maxFeePerBlobGas [0-9]+ < than block blob gas price [0-9]+ - /,'TransactionException.INSUFFICIENT_MAX_FEE_PER_BLOB_GAS'],
    [/^invalid requestsHash \(vm hf=osaka -> block number=/,'BlockException.INVALID_REQUESTS'],
    [/^invalid deposit log: unsupported data layout$/,'BlockException.INVALID_DEPOSIT_EVENT_LAYOUT'],
    [/^Invalid EIP-4844 transaction\. Only expecting 11 values \(for unsigned tx\) or 14 values \(for signed tx\)\.$/,'BlockException.RLP_STRUCTURES_ENCODING']
  ];
  for(const [pattern,category] of rules)if(pattern.test(message))categories.push(category);
  if(/^tx unable to pay base fee \((?:non )?EIP-1559 tx\) \(block number=/.test(diagnostic))categories.push('TransactionException.INSUFFICIENT_MAX_FEE_PER_GAS');
  const creation=/^tx should have a "to" field and cannot be used to create contracts \(tx type=([34]) hash=/.exec(message);
  if(creation)categories.push('TransactionException.TYPE_'+creation[1]+'_TX_CONTRACT_CREATION');
  const nonce=/^the tx doesn't have the correct nonce\. account has nonce of: ([0-9]+) tx has nonce of: ([0-9]+) \(vm hf=osaka ->/.exec(message);
  if(nonce && BigInt(nonce[1])>BigInt(nonce[2]))categories.push('TransactionException.NONCE_MISMATCH_TOO_LOW');
  return [...new Set(categories)];
}
export function classifyBlockRejection(expected,message,facts,beforeRoot,afterRoot,beforeHead,afterHead) {
  const actual_categories=blockRejectionCategories(message,facts);
  if(!actual_categories.length)return {status:'unsupported',reason:'unclassified-block-rejection',actual_categories};
  const matched_categories=actual_categories.filter(c=>expected.split('|').includes(c));
  const fields=[];
  if(!matched_categories.length)fields.push('rejection_category');
  if(beforeRoot!==afterRoot)fields.push('rejection_rollback');
  if(beforeHead!==afterHead)fields.push('rejection_chain_head');
  return {status:fields.length?'reference_mismatch':'reference_match',fields,actual_categories,matched_categories};
}
