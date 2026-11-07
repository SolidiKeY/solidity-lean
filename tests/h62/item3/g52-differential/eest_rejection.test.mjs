/** Guarded regression: a host exception or wrong/ambiguous invalid-tx reason must not count as fixture conformance. */
import test from 'node:test';import assert from 'node:assert/strict';
import {rejectionCategories as cats,classifyRejection as classify} from '../../../../scripts/h62/item3/g52-differential/eest_rejection.mjs';
test('arbitrary host error stays unsupported',()=>{assert.deepEqual(cats('RangeError: bad allocation'),[]);assert.equal(classify('TransactionException.NONCE_IS_MAX','RangeError',{},'a','a','a','l','l').status,'unsupported');});
test('observed category and unchanged state are both required',()=>{
 const expected='TransactionException.NONCE_IS_MAX', message='nonce cannot equal or exceed MAX_UINT64 (2^64-1)';
 assert.equal(classify(expected,message,{},'a','a','a','l','l').status,'reference_match');
 assert.equal(classify('TransactionException.SENDER_NOT_EOA',message,{},'a','a','a','l','l').status,'reference_mismatch');
 assert.equal(classify(expected,message,{},'a','b','a','l','l').status,'reference_mismatch');
 assert.equal(classify(expected,message,{},'a','a','a','l','bad').status,'reference_mismatch');
});
test('gas-floor distinction requires actual computed facts',()=>{
 const message='INTRINSIC_GAS_TOO_LOW: tx gas limit 100 is lower than the minimum gas limit of 120';
 assert.deepEqual(cats(message),[]);
 assert.deepEqual(cats(message,{gasLimit:'100',intrinsicGas:'90',floorGas:'120'}),['TransactionException.INTRINSIC_GAS_BELOW_FLOOR_GAS_COST']);
 assert.deepEqual(cats(message,{gasLimit:'100',intrinsicGas:'120',floorGas:'90'}),['TransactionException.INTRINSIC_GAS_TOO_LOW']);
});
test('creation refusal uses actual transaction type',()=>{
 const message='tx should have a "to" field and cannot be used to create contracts';
 assert.deepEqual(cats(message,{}),[]);assert.deepEqual(cats(message,{transactionType:4}),['TransactionException.TYPE_4_TX_CONTRACT_CREATION']);
});

test('unchanged state is insufficient when the fixture expects a different root',()=>{
 assert.deepEqual(classify('TransactionException.NONCE_IS_MAX','nonce cannot equal or exceed MAX_UINT64',{},'a','a','wrong','l','l').fields,['state_root']);
});
test('overlapping gas predicates preserve actual alternatives',()=>{
 const message='INTRINSIC_GAS_TOO_LOW: tx gas limit 100 is lower than the minimum gas limit of 130';
 assert.deepEqual(cats(message,{gasLimit:'100',intrinsicGas:'120',floorGas:'130'}),['TransactionException.INTRINSIC_GAS_TOO_LOW','TransactionException.INTRINSIC_GAS_BELOW_FLOOR_GAS_COST']);
});
