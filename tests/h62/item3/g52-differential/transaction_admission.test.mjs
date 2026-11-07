/** Guarded regression: expected labels, host errors and unlocated RLP failures
 * cannot become serialized-transaction conformance; authority bounds need the
 * native type/stage and ambiguous fields need actual validator provenance. */
import test from 'node:test';import assert from 'node:assert/strict';
import {admissionCategories,classifyAdmission} from '../../../../scripts/h62/item3/g52-differential/transaction_admission.mjs';
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
