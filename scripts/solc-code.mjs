/** Static compiler code constants. No account/world-code observations. */
export function compilerCode(compile, sources, settings, ast, provenance) {
  const nodes=[];
  function walk(x) { if (!x || typeof x!=='object') return;
    if (x.nodeType) nodes.push(x);
    for (const v of Object.values(x)) if (Array.isArray(v)) v.forEach(walk); else walk(v);
  }
  walk(ast);
  const requested=new Set(nodes.filter(n=>n.nodeType==='MemberAccess' &&
    ['creationCode','runtimeCode'].includes(n.memberName) &&
    n.expression?.nodeType==='FunctionCall' && n.expression.expression?.name==='type')
    .map(n=>n.expression.arguments?.[0]?.referencedDeclaration));
  if (!requested.size) return undefined;
  const contracts=[...requested].map(id=>{
    const d=nodes.find(n=>n.nodeType==='ContractDefinition' && n.id===id);
    if (!d) throw new Error('compiled-code constant lacks a contract declaration identity');
    return d;
  });
  const unit=Object.keys(sources);
  if (unit.length!==1) throw new Error('compiled-code constants require single-source provenance');
  const selected=Object.fromEntries(contracts.map(d=>[d.name,['evm.bytecode.object','evm.deployedBytecode.object']]));
  const codeSettings={...settings,outputSelection:{[unit[0]]:selected}};
  const output=compile({language:'Solidity',sources,settings:codeSettings});
  const errors=(output.errors??[]).filter(e=>e.severity==='error');
  if (errors.length) throw new Error(errors.map(e=>e.formattedMessage??e.message).join('\n'));
  const hex=(value)=>{
    if (typeof value!=='string' || !/^(?:[0-9a-fA-F]{2})*$/.test(value))
      throw new Error('compiled-code constant is missing or contains unresolved library links');
    if (value.length>262144) throw new Error('compiled-code constant exceeds the materialization bound');
    return value.toLowerCase();
  };
  return {...provenance,settings:codeSettings,contracts:contracts.map(d=>{
    const code=output.contracts?.[unit[0]]?.[d.name]?.evm;
    return {id:d.id,name:d.name,creationCode:hex(code?.bytecode?.object),runtimeCode:hex(code?.deployedBytecode?.object)};
  })};
}
