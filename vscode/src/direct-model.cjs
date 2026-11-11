'use strict';
function signature(n,short=false){return (n.name||n.kind)+'('+n.parameters.parameters.map(p=>{const t=p.typeDescriptions.typeString;return short?t.replace(/\buint256\b/g,'uint').replace(/\bint256\b/g,'int'):t;}).join(',')+')';}
function requestFor(contract,options){
  // Requested audits and model prestates are certified evidence (Lean path).
  if(options.certify===true||options.auditPreconditions||options.counterexamples)return null;
  let selected,sourceId;
  if(options.function){
    const candidates=contract.nodes.filter(n=>n.nodeType==='FunctionDefinition'&&(n.name===options.function||signature(n)===options.function||signature(n,true)===options.function));
    if(candidates.length!==1)return null;selected=candidates[0].name;sourceId=candidates[0].id;
  }
  return {contract,function:selected,sourceId,listing:!!options.listing};
}
function unknownResult(contract,options,reason,allContracts=[]){
  const lineage=contract.linearizedBaseContracts||[contract.id];
  const members=[contract,...allContracts.filter(c=>c!==contract&&lineage.includes(c.id))].flatMap(c=>c.nodes);
  const declarations=[...new Map(members.filter(n=>n.nodeType==='FunctionDefinition'&&
    (n.kind==='constructor'?contract.nodes.includes(n):['public','external'].includes(n.visibility))).reverse().map(n=>[signature(n),n])).values()];
  let selected=declarations;
  if(options.function){
    selected=declarations.filter(n=>n.name===options.function||signature(n)===options.function||signature(n,true)===options.function);
    if(selected.length!==1)return {results:[],errors:[{stage:'selection',reason:'Select one existing function by its full signature.'}]};
  }
  return {results:selected
    .map(n=>({sourceId:n.id,function:n.name||n.kind,signature:signature(n,true),status:'unsupported',reason,
      verification:'direct',reading:'solc',tag:'specified'}))};
}
function decorate(contract,result){
  if(result.gap||!Array.isArray(result.results)||!result.results.length||result.results.some(r=>!['proved','refuted','ready','pending','unsupported','skipped'].includes(r.status)))return null;
  const ids=new Set();
  for(const row of result.results){
    const declaration=contract.nodes.find(n=>n.id===row.sourceId&&n.name===row.function&&n.nodeType==='FunctionDefinition');
    if(!declaration||ids.has(row.sourceId))throw new Error('Direct result does not belong to the selected declaration');
    ids.add(row.sourceId);row.signature=signature(declaration,true);
  }
  return result;
}
module.exports={signature,requestFor,decorate,unknownResult};
