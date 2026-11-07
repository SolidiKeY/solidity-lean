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
