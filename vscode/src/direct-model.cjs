'use strict';
function signature(n,short=false){return n.name+'('+n.parameters.parameters.map(p=>{const t=p.typeDescriptions.typeString;return short?t.replace(/\buint256\b/g,'uint').replace(/\bint256\b/g,'int'):t;}).join(',')+')';}
function requestFor(contract,options){
  if(options.certify===true||options.auditPreconditions)return null;
  let selected;
  if(options.function){
    const candidates=contract.nodes.filter(n=>n.nodeType==='FunctionDefinition'&&(n.name===options.function||signature(n)===options.function||signature(n,true)===options.function));
    if(candidates.length!==1)return null;selected=candidates[0].name;
  }
  return {contract,function:selected,listing:!!options.listing};
}
function decorate(contract,result){
  if(result.gap||!Array.isArray(result.results)||!result.results.length||result.results.some(r=>['pending','unsupported','error'].includes(r.status)))return null;
  const ids=new Set();
  for(const row of result.results){
    const declaration=contract.nodes.find(n=>n.id===row.sourceId&&n.name===row.function&&n.nodeType==='FunctionDefinition');
    if(!declaration||ids.has(row.sourceId))throw new Error('Direct result does not belong to the selected declaration');
    ids.add(row.sourceId);row.signature=signature(declaration,true);
  }
  return result;
}
module.exports={signature,requestFor,decorate};
