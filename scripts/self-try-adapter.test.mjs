import {test} from 'node:test';
import assert from 'node:assert/strict';
import {directSelfTryContext,SELF_TRY_ADDRESS} from './self-try-adapter.mjs';
const scalar = typeString => ({typeDescriptions:{typeString}});
function control() {
  const target = {nodeType:'FunctionDefinition',id:2,visibility:'public',body:{},
    parameters:{parameters:[scalar('bool')]},returnParameters:{parameters:[scalar('uint256')]}};
  const call = {nodeType:'FunctionCall',expression:{nodeType:'MemberAccess',referencedDeclaration:2,
    expression:{nodeType:'Identifier',name:'this'}},arguments:[]};
  const clause = {nodeType:'TryStatement',externalCall:call,clauses:[{}]};
  const contract = {nodes:[target,clause]};
  return {target,call,clause,contract,ast:{nodes:[contract]}};
}
test('only a resolved direct self try obtains a recorded nonzero 160-bit context',()=>{
  const c=control();assert.deepEqual(directSelfTryContext(c.ast,c.contract),{kind:'direct-self-try',selfAddress:SELF_TRY_ADDRESS});
  assert.ok(BigInt(SELF_TRY_ADDRESS)>0n && BigInt(SELF_TRY_ADDRESS)<2n**160n);
});
for (const [name,mutate] of [
  ['foreign receiver',c=>c.call.expression.expression.name='other'],
  ['foreign declaration',c=>c.call.expression.referencedDeclaration=99],
  ['call options',c=>c.call.expression={nodeType:'FunctionCallOptions',expression:c.call.expression}],
  ['reference return',c=>c.target.returnParameters.parameters=[scalar('string memory')]],
  ['address observation',c=>c.contract.nodes.push({nodeType:'Identifier',name:'this'})],
  ['caller observation',c=>c.target.body={nodeType:'MemberAccess',expression:{name:'msg'},memberName:'sender'}],
  ['assembly',c=>c.target.body={nodeType:'InlineAssembly'}],
  ['creation',c=>c.target.body={nodeType:'NewExpression'}],
  ['ordinary self call',c=>c.contract.nodes.push(c.call)],
  ['external function value',c=>c.call.expression={nodeType:'Identifier',typeDescriptions:{typeString:'function () external'}}],
  ['constructor helper self try',c=>c.contract.nodes.push({nodeType:'FunctionDefinition',kind:'constructor',body:{nodeType:'FunctionCall',expression:{name:'helper'}}})],
  ['constructor modifier self try',c=>c.contract.nodes.push({nodeType:'FunctionDefinition',kind:'constructor',body:{},modifiers:[{name:'helper'}]})],
  ['initializer helper self try',c=>c.contract.nodes.push({nodeType:'VariableDeclaration',stateVariable:true,value:{nodeType:'FunctionCall',expression:{name:'helper'}}})],
  ['constructor self try',c=>c.contract.nodes.push({nodeType:'FunctionDefinition',kind:'constructor',body:c.clause})],
  ['effectful external argument',c=>c.call.arguments.push({nodeType:'FunctionCall',expression:{typeDescriptions:{typeIdentifier:'t_function_barecall'}}})]
]) test(`refuses ${name}`,()=>{const c=control();mutate(c);assert.equal(directSelfTryContext(c.ast,c.contract),null);});

const yulCall=name=>({nodeType:'YulExpressionStatement',expression:{nodeType:'YulFunctionCall',functionName:{nodeType:'YulIdentifier',name},arguments:[]}});
test('reference-only memory assembly/aggregate ABI cannot obtain a native context',()=>{
  const c=control();c.target.parameters.parameters=[scalar('bytes memory')];
  c.target.body={nodeType:'InlineAssembly',AST:{nodeType:'YulBlock',statements:[yulCall('mstore'),yulCall('revert')]}};
  assert.equal(directSelfTryContext(c.ast,c.contract),null);
  assert.equal(directSelfTryContext(c.ast,c.contract,{referenceOnly:true}).kind,'direct-self-try-reference');
});
for(const op of ['caller','address','origin','callvalue','gas','timestamp','sload','sstore','tload','tstore','balance','extcodecopy','call','delegatecall','staticcall','create','create2','log0','selfdestruct','verbatim_1i_1o','unknown'])
 test(`reference refuses Yul ${op} hidden inside a function/loop`,()=>{
  const c=control();c.target.body={nodeType:'InlineAssembly',AST:{nodeType:'YulBlock',statements:[{nodeType:'YulFunctionDefinition',body:{nodeType:'YulBlock',statements:[{nodeType:'YulForLoop',body:{nodeType:'YulBlock',statements:[yulCall(op)]}}]}}]}};
  assert.equal(directSelfTryContext(c.ast,c.contract,{referenceOnly:true}),null);
 });
for(const AST of [undefined,{}, {nodeType:'YulBlock'}, {nodeType:'UnknownYul',statements:[]}])
 test('missing or unknown Yul AST never becomes a reference admission',()=>{
  const c=control();c.target.body={nodeType:'InlineAssembly',AST};
  assert.equal(directSelfTryContext(c.ast,c.contract,{referenceOnly:true}),null);
 });
