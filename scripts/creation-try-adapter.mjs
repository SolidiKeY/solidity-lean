import {SELF_TRY_ADDRESS} from './self-try-adapter.mjs';
// Structural host admission only. Lean independently checks whole source
// declarations and compiles actual typed constructor/caller programs.
const ref=n=>n?.referencedDeclaration??n?.pathNode?.referencedDeclaration;
const parameters=(n,key='parameters')=>n?.[key]?.parameters;
const uint=n=>n?.typeDescriptions?.typeString==='uint256';
const string=n=>n?.typeDescriptions?.typeString==='string'&&n.storageLocation==='memory';
const same=(n,d)=>n?.nodeType==='Identifier'&&Number.isInteger(d?.id)&&n.referencedDeclaration===d.id;
const one=xs=>Array.isArray(xs)&&xs.length===1?xs[0]:null;
const assignment=(n,d)=>n?.nodeType==='ExpressionStatement'&&n.expression?.nodeType==='Assignment'&&
 n.expression.operator==='='&&same(n.expression.leftHandSide,d)?n.expression.rightHandSide:null;
const addressArg=n=>n?.nodeType==='FunctionCall'&&n.kind==='typeConversion'&&
 n.expression?.nodeType==='ElementaryTypeNameExpression'&&n.expression.typeName?.name==='address'?one(n.arguments):null;
function closed(target){
 if(target?.contractKind!=='contract'||target.abstract!==false||target.baseContracts?.length)return false;
 const c=one(target.nodes);if(c?.nodeType!=='FunctionDefinition'||c.kind!=='constructor'||c.stateMutability!=='nonpayable'||c.modifiers?.length||
 !uint(one(parameters(c)))||parameters(c,'returnParameters')?.length!==0)return false;
 const ss=c.body?.statements;if(!Array.isArray(ss))return false;if(!ss.length)return true;
 const s=one(ss),call=s?.expression,r=one(call?.arguments);
 return s?.nodeType==='ExpressionStatement'&&call?.nodeType==='FunctionCall'&&call.expression?.nodeType==='Identifier'&&
 call.expression.name==='revert'&&Number.isInteger(call.expression.referencedDeclaration)&&
 (call.expression.referencedDeclaration<0||(call.expression.referencedDeclaration>=2**31&&call.expression.referencedDeclaration<=2**32-1))&&r?.nodeType==='Literal'&&r.kind==='string';
}
export function creationTryContext(ast,owner){
 if(owner?.contractKind!=='contract'||owner.abstract!==false||owner.baseContracts?.length||!owner.nodes?.length)return null;
 const units=ast.nodes?.filter(n=>n.nodeType==='ContractDefinition')??[];const targets=new Set();
 for(const f of owner.nodes){
  if(f.nodeType!=='FunctionDefinition'||f.kind!=='function'||!['public','external'].includes(f.visibility)||f.stateMutability!=='nonpayable'||
   f.modifiers?.length||parameters(f)?.length!==0)return null;
  const rets=parameters(f,'returnParameters');if(rets?.length!==2||rets[0].typeDescriptions?.typeString!=='bool'||!string(rets[1]))return null;
  const ss=f.body?.statements;if(ss?.length!==2)return null;
  const [prefix,t]=ss,arg=one(prefix.declarations),initial=prefix.initialValue;
  if(prefix.nodeType!=='VariableDeclarationStatement'||!uint(arg)||initial?.nodeType!=='Literal'||initial.kind!=='number'||
   !/^(0|[1-9][0-9]*)$/.test(initial.value)||(initial.subdenomination??'')!==''||t.nodeType!=='TryStatement')return null;
  const call=t.externalCall,n=call?.expression;
  if(call?.nodeType!=='FunctionCall'||call.names?.length||!same(one(call.arguments),arg)||n?.nodeType!=='NewExpression')return null;
  const target=units.find(x=>x.id===ref(n.typeName));if(!target||target.id===owner.id||!closed(target))return null;targets.add(target.id);
  if(t.clauses?.length!==2)return null;const [ok,err]=t.clauses,h=one(parameters(ok)),reason=one(parameters(err));
  if(ok.errorName!==''||err.errorName!=='Error'||ref(h?.typeName)!==target.id||!string(reason))return null;
  if(ok.block?.statements?.length!==2||err.block?.statements?.length!==1)return null;
  let cmp=assignment(ok.block.statements[0],rets[0]);
  if(cmp?.nodeType==='TupleExpression'&&cmp.isInlineArray===false)cmp=one(cmp.components);
  const z=addressArg(cmp?.rightExpression),text=assignment(ok.block.statements[1],rets[1]);
  if(cmp?.nodeType!=='BinaryOperation'||cmp.operator!=='!='||!same(addressArg(cmp.leftExpression),h)||
   z?.nodeType!=='Literal'||z.value!=='0'||text?.nodeType!=='Literal'||text.kind!=='string'||
   !same(assignment(err.block.statements[0],rets[1]),reason))return null;
 }
 if(units.some(n=>n.id!==owner.id&&!targets.has(n.id)))return null;
 return {kind:'creation-try-source',selfAddress:SELF_TRY_ADDRESS,
  sender:'103164821458651970696730694074090566093359944210',senderFunds:'1000000000000000000000000000000',
  ownerFunds:'0',value:'0',timestamp:'0',firstCreationNonce:1};
}
