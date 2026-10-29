/** Narrow, structural host admission for direct resolved self-try calls.
 * Address is CREATE(caller=0x12 repeated 20, nonce=0), checked against actual
 * reference deployment. Context observations remain outside this adapter.
 */
export const SELF_TRY_ADDRESS = '457415396813334496268612927368880745799219276745';
const scalar = p => /^(?:bool|u?int(?:[0-9]+)?)$/.test(p.typeDescriptions?.typeString ?? '');
// Return-only function values use the existing packed address/selector model.
// This admits no function inputs, invocation, or general function signature.
const nullaryExternalVoidResult = p => {
  const t=p.typeName;
  return t?.nodeType === 'FunctionTypeName' && t.visibility === 'external' &&
    Array.isArray(t.parameterTypes?.parameters) && t.parameterTypes.parameters.length === 0 &&
    Array.isArray(t.returnParameterTypes?.parameters) && t.returnParameterTypes.parameters.length === 0;
};
const resultValue = p => scalar(p) || nullaryExternalVoidResult(p);
// Reference-only memory assembly: execute compiler bytecode, never model Yul.
// Unknown shapes/instructions and context/world observations remain refused.
const yulKinds = new Set(['YulBlock','YulVariableDeclaration','YulAssignment','YulExpressionStatement',
  'YulFunctionCall','YulIdentifier','YulLiteral','YulIf','YulForLoop','YulSwitch','YulCase',
  'YulFunctionDefinition','YulTypedName','YulBreak','YulContinue','YulLeave']);
const memoryOps = new Set(['mload','mstore','mstore8','add','sub','mul','div','mod',
  'and','or','xor','not','shl','shr','sar','eq','lt','gt','iszero','pop','revert','return']);
function memoryAssembly(node) {
  const ast=node.AST;
  if (ast?.nodeType !== 'YulBlock' || !Array.isArray(ast.statements)) return false;
  function valid(n) {
    if (!n || typeof n !== 'object') return true;
    if (n.nodeType && !yulKinds.has(n.nodeType)) return false;
    if (n.nodeType === 'YulBlock' && !Array.isArray(n.statements)) return false;
    if (n.nodeType === 'YulFunctionCall' && !memoryOps.has(n.functionName?.name)) return false;
    return Object.values(n).every(v=>Array.isArray(v)?v.every(valid):valid(v));
  }
  return valid(ast);
}
export function directSelfTryContext(ast, contract, {referenceOnly = false} = {}) {
  if (!contract) return null;
  const functions = new Map((contract.nodes ?? []).filter(n => n.nodeType === 'FunctionDefinition' && n.body)
    .map(n => [n.id,n]));
  let tries = 0;
  let functionReturnSeen = false;
  const hasCall = n => n && typeof n === 'object' && (n.nodeType === 'FunctionCall' ||
    Object.values(n).some(v => Array.isArray(v) ? v.some(hasCall) : hasCall(v)));
  function visit(node) {
    if (!node || typeof node !== 'object') return true;
    // Runtime code does not exist during deployment. Refuse constructor and
    // initializer dependency closures instead of inlining a predeployment try.
    if (node.nodeType === 'FunctionDefinition' && node.kind === 'constructor') return false;
    if (!referenceOnly && node.nodeType === 'FunctionDefinition' &&
        (node.returnParameters?.parameters ?? []).some(nullaryExternalVoidResult))
      functionReturnSeen = true;
    if (node.nodeType === 'VariableDeclaration' && node.stateVariable && hasCall(node.value)) return false;
    if (node.nodeType === 'TryStatement') {
      const call = node.externalCall, member = call?.expression;
      const callee = functions.get(member?.referencedDeclaration);
      if (call?.nodeType !== 'FunctionCall' || member?.nodeType !== 'MemberAccess' ||
          member.expression?.nodeType !== 'Identifier' || member.expression.name !== 'this' ||
          !callee || !['public','external'].includes(callee.visibility) ||
          (!referenceOnly && (!callee.parameters.parameters.every(scalar) || !callee.returnParameters.parameters.every(resultValue)))) return false;
      tries++;
      if (!referenceOnly && callee.returnParameters.parameters.some(nullaryExternalVoidResult))
        functionReturnSeen = true;
      // The only permitted host nodes are this exact receiver/call. Inspect
      // arguments and every clause, including nested tries, normally.
      return (call.arguments ?? []).every(visit) && (node.clauses ?? []).every(visit);
    }
    if (node.nodeType === 'Identifier' && node.name === 'this') return false;
    if (node.nodeType === 'MemberAccess' && (['msg','block','tx'].includes(node.expression?.name) ||
        ['balance','code','codehash'].includes(node.memberName))) return false;
    if (node.nodeType === 'InlineAssembly') return referenceOnly && memoryAssembly(node);
    if (node.nodeType === 'NewExpression') return false;
    if (node.nodeType === 'FunctionCall' && (['gasleft','blockhash','blobhash'].includes(node.expression?.name) ||
        /external|barecall|send|transfer|delegatecall|staticcall/.test(node.expression?.typeDescriptions?.typeIdentifier ?? '') ||
        /\bexternal\b/.test(node.expression?.typeDescriptions?.typeString ?? ''))) return false;
    return Object.values(node).every(v => Array.isArray(v) ? v.every(visit) : visit(v));
  }
  const scalarEntryInputs = node => {
    if (!node || typeof node !== 'object') return true;
    if (['FunctionDefinition','ModifierDefinition'].includes(node.nodeType) &&
        (!Array.isArray(node.parameters?.parameters) || !node.parameters.parameters.every(scalar))) return false;
    return Object.values(node).every(v=>Array.isArray(v)?v.every(scalarEntryInputs):scalarEntryInputs(v));
  };
  const valid=visit(ast);
  // The new return-only fragment must not open an indirect route through an
  // outer entry/helper's function-reference inputs. Old scalar-only cases and
  // reference-only EVM admission retain their previous policy.
  return valid && tries > 0 && (!functionReturnSeen || scalarEntryInputs(ast)) ?
    {kind:referenceOnly?'direct-self-try-reference':'direct-self-try',selfAddress:SELF_TRY_ADDRESS} : null;
}
