// Closed declaration admission for the original linked-library try family.
// Lean independently resolves these identities and checks its typed programs.
const one=xs=>Array.isArray(xs)&&xs.length===1?xs[0]:null;
const ref=n=>n?.referencedDeclaration??n?.pathNode?.referencedDeclaration;
const ps=(n,k='parameters')=>n?.[k]?.parameters;
const same=(n,d)=>n?.nodeType==='Identifier'&&Number.isInteger(d?.id)&&ref(n)===d.id&&n.name===d.name;
const uint=n=>n?.typeDescriptions?.typeString==='uint256';
const bool=n=>n?.typeDescriptions?.typeString==='bool';
const str=n=>n?.typeDescriptions?.typeString==='string'&&n.storageLocation==='memory';
const number=n=>n?.nodeType==='Literal'&&n.kind==='number'&&/^(0|[1-9][0-9]*)$/.test(n.value)&&(n.subdenomination??'')==='';
const member=(n,r,f)=>n?.nodeType==='MemberAccess'&&ref(n)===f.id&&n.memberName===f.name&&same(n.expression,r);
const returned=b=>{const s=one(b?.statements);return b?.nodeType==='Block'&&s?.nodeType==='Return'?s.expression:null;};
export function libraryTryContext(ast,owner){
 const units=ast?.nodes?.filter(n=>n.nodeType==='ContractDefinition');
 const lib=one(units?.filter(n=>n.contractKind==='library'));
 if(units?.length!==2||!lib||owner?.contractKind!=='contract'||[owner,lib].some(n=>n.abstract!==false||n.baseContracts?.length))return null;
 const structure=one(lib.nodes?.filter(n=>n.nodeType==='StructDefinition')),field=one(structure?.members);
 if(lib.nodes?.length!==3||!uint(field))return null;
 const root=one(owner.nodes?.filter(n=>n.nodeType==='VariableDeclaration'));
 const using=one(owner.nodes?.filter(n=>n.nodeType==='UsingForDirective'));
 if(owner.nodes?.length!==4||!root?.stateVariable||root.constant!==false||root.value||ref(root.typeName)!==structure.id||
  using?.global!==false||ref(using.libraryName)!==lib.id||ref(using.typeName)!==structure.id)return null;
 const fs=owner.nodes.filter(n=>n.nodeType==='FunctionDefinition'),used=new Set();let storageCount=0;
 if(fs.length!==2)return null;
 for(const f of fs){
  const input=one(ps(f)),rets=ps(f,'returnParameters'),ss=f.body?.statements;
  if(f.kind!=='function'||f.visibility!=='public'||f.stateMutability!=='nonpayable'||f.modifiers?.length||!bool(input)||
   rets?.length!==2||!uint(rets[0])||!str(rets[1])||rets.some(x=>x.name!=='')||ss?.length!==2)return null;
  const [prefix,t]=ss,call=t.externalCall,callee=call?.expression;
  if(t.nodeType!=='TryStatement'||call?.nodeType!=='FunctionCall'||call.names?.length||callee?.nodeType!=='MemberAccess')return null;
  const fn=one(lib.nodes.filter(n=>n.nodeType==='FunctionDefinition'&&n.id===ref(callee))),params=ps(fn),output=one(ps(fn,'returnParameters'));
  if(!fn||callee.memberName!==fn.name||fn.kind!=='function'||fn.visibility!=='public'||fn.stateMutability!=='view'||fn.modifiers?.length||params?.length!==2||!bool(params[1])||!uint(output)||output.name!=='')return null;
  used.add(fn.id);const [formal,flag]=params,storage=formal.storageLocation==='storage';
  if(storage){
   storageCount++;const a=prefix.expression;
   if(ref(formal.typeName)!==structure.id||!same(callee.expression,root)||!same(one(call.arguments),input)||prefix.nodeType!=='ExpressionStatement'||
    a?.nodeType!=='Assignment'||a.operator!=='='||!member(a.leftHandSide,root,field)||!number(a.rightHandSide))return null;
  }else{
   const d=one(prefix.declarations);
   if(!uint(formal)||!same(callee.expression,lib)||prefix.nodeType!=='VariableDeclarationStatement'||!uint(d)||!number(prefix.initialValue)||
    call.arguments?.length!==2||!same(call.arguments[0],d)||!same(call.arguments[1],input))return null;
  }
  const branch=one(fn.body?.statements),v=returned(branch?.trueBody),fail=one(branch?.falseBody?.statements),rc=fail?.expression,reason=one(rc?.arguments);
  if(branch?.nodeType!=='IfStatement'||!same(branch.condition,flag)||!(storage?member(v,formal,field):same(v,formal))||
   fail?.nodeType!=='ExpressionStatement'||rc?.nodeType!=='FunctionCall'||rc.expression?.nodeType!=='Identifier'||rc.expression.name!=='revert'||
   !(ref(rc.expression)<0||ref(rc.expression)>=2**31&&ref(rc.expression)<=2**32-1)||reason?.nodeType!=='Literal'||reason.kind!=='string')return null;
  if(t.clauses?.length!==2)return null;
  const [ok,err]=t.clauses,bound=one(ps(ok)),message=one(ps(err)),yes=returned(ok.block),no=returned(err.block);
  if(ok.errorName!==''||!uint(bound)||err.errorName!=='Error'||!str(message)||yes?.nodeType!=='TupleExpression'||yes.isInlineArray!==false||
   yes.components?.length!==2||!same(yes.components[0],bound)||yes.components[1]?.nodeType!=='Literal'||yes.components[1].kind!=='string'||
   no?.nodeType!=='TupleExpression'||no.isInlineArray!==false||no.components?.length!==2||!number(no.components[0])||!same(no.components[1],message))return null;
 }
 if(used.size!==2||storageCount!==1)return null;
 return {kind:'linked-library-try-source',selfAddress:'816484669177263916909924781827997526878516243634',libraryAddress:'457415396813334496268612927368880745799219276745',libraryName:lib.name,libraryDeclaration:lib.id,ownerDeclaration:owner.id,
  sourceMethods:[...used],storageRoot:root.id,storageMember:field.id,
  sender:'103164821458651970696730694074090566093359944210',senderFunds:'1000000000000000000000000000000',ownerFunds:'0',value:'0',timestamp:'0'};
}
/** Consume precisely the validated deployment directive, never ignore unknown observations. */
export function libraryTryVectorsFixture(fixture,context){
 if(context?.kind!=='linked-library-try-source')throw new Error('linked try context required');
 const directive='library: '+context.libraryName;
 if(fixture.expectations.filter(x=>x.trim()===directive).length!==1)throw new Error('exact linked library directive required');
 return {...fixture,expectations:fixture.expectations.filter(x=>x.trim()!==directive)};
}
/** Patch only compiler-resolved twenty-byte addresses; unresolved strings never become truncated bytes. */
export function linkLibraryObject(object,references,file,name,address){
 if(typeof object!=='string'||object.length%2||!/^0x[0-9a-fA-F]{40}$/.test(address)||BigInt(address)===0n)throw new Error('invalid link object/address');
 const positions=[];
 for(const [f,libs] of Object.entries(references??{}))for(const [n,sites] of Object.entries(libs)){
  if(f!==file||n!==name||!Array.isArray(sites))throw new Error('unresolved linked library identity');
  for(const {start,length} of sites){
   if(!Number.isSafeInteger(start)||start<0||length!==20||2*(start+length)>object.length||positions.some(p=>start<p+20&&p<start+20))throw new Error('invalid compiler link range');
   if(!/^__\$[0-9a-fA-F]{34}\$__$/.test(object.slice(start*2,(start+20)*2)))throw new Error('link range does not identify a compiler placeholder');
   positions.push(start);
  }
 }
 if(!positions.length)throw new Error('missing exact compiler link references');
 let linked=object;
 for(const start of positions)linked=linked.slice(0,start*2)+address.slice(2).toLowerCase()+linked.slice((start+20)*2);
 if(!/^(?:[0-9a-fA-F]{2})+$/.test(linked))throw new Error('unresolved/nonhex linked bytecode');
 return {object:linked,positions};
}
