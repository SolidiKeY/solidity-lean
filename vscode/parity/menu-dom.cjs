// Read-only DOM diagnostics. Legacy menu-item attributes are never repaired or inferred.
'use strict';
function observeMenuItems(nodes,viewport){
  const describe=node=>node?{tag:node.tagName,role:node.getAttribute('role'),className:node.className,ariaDisabled:node.getAttribute('aria-disabled')}:null;
  return nodes.map(e=>{
    const item=e.closest('[role=menuitem]'),role=e.closest('[role]'),r=e.getBoundingClientRect();
    return{label:e.textContent,ariaDisabled:item?.getAttribute('aria-disabled')??null,className:item?.className??null,
      bounds:{left:r.left,top:r.top,right:r.right,bottom:r.bottom},
      withinViewport:r.left>=0&&r.top>=0&&r.right<=viewport.width&&r.bottom<=viewport.height,
      roleContext:{label:describe(e),nearestRole:describe(role),menuItem:describe(item)}};
  });
}
function recorder(directory,context){
  const fs=require('node:fs'),path=require('node:path'),{createHash}=require('node:crypto'),reads=[];
  context=JSON.parse(JSON.stringify(context));
  return snapshot=>{
    const roles=snapshot.items.map(row=>row.roleContext??null);
    const legacy={...snapshot,items:snapshot.items.map(({roleContext,...row})=>row)};
    reads.push({index:reads.length,origin:'CDP Runtime.evaluate',context,
      rendererLifetime:snapshot.rendererLifetime??null,activeUri:snapshot.activeUri??null,
      legacyStateSha256:createHash('sha256').update(JSON.stringify(legacy)).digest('hex'),
      availability:roles.length===0?'empty':roles.every(role=>role!==null)?'present':'unavailable',roles});
    fs.writeFileSync(path.join(directory,'menu-roles.json'),JSON.stringify({version:1,reads},null,2)+'\n');
    return legacy;
  };
}
module.exports={observeMenuItems,recorder};
