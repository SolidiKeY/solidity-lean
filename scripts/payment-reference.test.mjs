import {test} from 'node:test';
import assert from 'node:assert/strict';
import {discardedSelfPaymentReference} from './solidity-upstream.mjs';
import {runSolidityTests} from './test-solidity.mjs';
import {solkeyTestOptions} from './test-compiler.mjs';
const compilerOptions=solkeyTestOptions();
const self={nodeType:'Identifier',name:'this'};
const receiver={nodeType:'FunctionCall',kind:'typeConversion',
  expression:{nodeType:'ElementaryTypeNameExpression',typeName:{name:'address'}},arguments:[self]};
function reference(name='transfer',expression=receiver) {
  return {nodeType:'ExpressionStatement',expression:{nodeType:'MemberAccess',memberName:name,
    typeDescriptions:{typeIdentifier:`t_function_${name}_nonpayable`},expression}};
}
test('host exemption is only a discarded native reference with total self receiver',()=>{
  assert.equal(discardedSelfPaymentReference(reference()),true);
  assert.equal(discardedSelfPaymentReference(reference('send')),true);
  assert.equal(discardedSelfPaymentReference({nodeType:'ExpressionStatement',expression:{
    nodeType:'FunctionCall',expression:reference().expression,arguments:[]}}),false);
  assert.equal(discardedSelfPaymentReference(reference('transfer',{
    nodeType:'FunctionCall',kind:'functionCall',expression:{nodeType:'Identifier',name:'effect'},arguments:[]})),false);
  const user=reference();user.expression.referencedDeclaration=12;
  assert.equal(discardedSelfPaymentReference(user),false);
  const unknown=reference();unknown.expression.typeDescriptions={};
  assert.equal(discardedSelfPaymentReference(unknown),false);
});
test('source member discard retains receiver writes, reverts, and state frame',()=>{
  const report=runSolidityTests(['tests/solc/PaymentReferences.sol'],{...compilerOptions,build:false,contract:'PaymentReferences'});
  assert.deepEqual(report.errors,[]);
  for(const name of ['discardedEffects','discardedFailure','discardedSelf']) {
    const row=report.results.find(r=>r.function===name);
    assert.equal(row?.status,'proved',`${name}: ${row?.reason}`);
  }
});
test('actual unsupported self transfer retains dispatch refusal',()=>{
  const report=runSolidityTests(['tests/solc/PaymentReferences.sol'],{
    ...compilerOptions,build:false,contract:'ActualPaymentDispatch',list:true});
  assert.deepEqual(report.errors,[]);
  for (const name of ['actual','parenthesized','conditional']) {
    const row=report.results.find(r=>r.function===name);
    assert.equal(row?.status,'unsupported',`${name}: ${row?.reason}`);
    assert.match(row.reason,/selfPayment/);
  }
});

test('native payment members do not become mobile conditional function values',()=>{
  const report=runSolidityTests(['tests/solc/PaymentInvalidCallee.sol'],{...compilerOptions,build:false});
  assert.equal(report.results.length,0);
  assert.equal(report.errors.length,1);
  assert.equal(report.errors[0].stage,'compile');
  assert.match(report.errors[0].reason,/Invalid mobile type/);
});
