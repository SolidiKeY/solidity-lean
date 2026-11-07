// Display-only hierarchy from accepted result identities and current compiler DocumentSymbols.
'use strict';
const model=require('./model.cjs'),{offset}=require('./language-services.cjs');
const items=collection=>{const values=[];collection.forEach(item=>values.push(item));return values;};
const rowId=(uri,row)=>`${uri}#${encodeURIComponent(row.contract)}:${encodeURIComponent(row.signature||row.function)}`;
const contains=(a,b)=>compare(a.start,b.start)<=0&&compare(a.end,b.end)>=0;
const compare=(a,b)=>a.line-b.line||a.character-b.character;
function currentSymbols(symbols,text){
 if(!Array.isArray(symbols))return null;
 const validRange=range=>{if(!model.validRange(range))return false;try{offset(text,range.start);offset(text,range.end);return true;}catch{return false;}};
 const valid=(symbol,parent)=>symbol&&typeof symbol.name==='string'&&Number.isSafeInteger(symbol.kind)&&validRange(symbol.range)&&validRange(symbol.selectionRange)&&contains(symbol.range,symbol.selectionRange)&&(!parent||contains(parent,symbol.range))&&!/^Outdated:/.test(symbol.detail||'')&&Array.isArray(symbol.children)&&symbol.children.every(child=>valid(child,symbol.range));
 return symbols.every(symbol=>valid(symbol))?structuredClone(symbols):null;
}
function install(vscode,controller,metadata){
 const obligationTag=vscode.TestTag?new vscode.TestTag('solidityLean.discoveredObligation'):null;
 const key=uri=>uri.toString(),toRange=range=>new vscode.Range(range.start.line,range.start.character,range.end.line,range.end.character);
 const descendants=item=>[item,...items(item.children).flatMap(descendants)];
 function leaves(uri){const file=controller.items.get(key(uri));return file?descendants(file).filter(item=>metadata.get(item.id)?.row):null;}
 function live(item){let child=item,meta=metadata.get(child.id);if(!meta)return null;const original=meta;
  while(meta.parent){const parentMeta=metadata.get(meta.parent),parent=parentMeta?.item;if(!parent||parent.children.get(child.id)!==child)return null;child=parent;meta=parentMeta;}
  return controller.items.get(child.id)===child?original:null;
 }
 function excluded(item,ids){let meta=metadata.get(item.id);while(meta){if(ids.has(meta.item.id))return true;meta=metadata.get(meta.parent);}return false;}
 function clear(uri){const file=controller.items.get(key(uri));if(file)for(const item of descendants(file))metadata.delete(item.id);controller.items.delete(key(uri));}
 function render(doc,report,symbols){
  const fileId=key(doc.uri),oldFile=controller.items.get(fileId),old=new Map(oldFile?descendants(oldFile).map(item=>[item.id,item]):[]),used=new Set(),children=new Map();
  function item(id,label,parent,range,description,row){const value=old.get(id)||controller.createTestItem(id,label,doc.uri);value.label=label;value.range=range?toRange(range):undefined;value.description=description;value.tags=row&&obligationTag?[obligationTag]:[];used.add(id);children.set(id,[]);metadata.set(id,{item:value,parent,uri:doc.uri,...(row?{row}:{})});if(parent)children.get(parent).push(value);return value;}
  const file=item(fileId,vscode.workspace.asRelativePath(doc.uri),null);controller.items.add(file);
  const paths=[];function visit(nodes,parents=[]){for(const node of nodes){const path=[...parents,node];paths.push(path);visit(node.children,path);}}if(symbols)visit(symbols);
  const grouped=new Map();
  function parentFor(path){let parent=fileId;for(let index=0;index<path.length;index++){const node=path[index],id=fileId+'#symbol:'+JSON.stringify(path.slice(0,index+1).map(value=>[value.name,value.kind,value.selectionRange]));if(!used.has(id))item(id,node.name,parent,node.selectionRange,'Current compiler symbol');parent=id;}return parent;}
  for(const row of report.results){
   const valid=model.validRange(row.range),matches=valid?paths.filter(path=>{const node=path.at(-1);return node.kind===12&&(node.name===row.function||node.name===row.signature)&&contains(node.range,row.range);}):[];
   let parent;
   if(matches.length===1)parent=parentFor(matches[0].slice(0,-1));
   else{const id=fileId+'#contract:'+encodeURIComponent(row.contract);if(!grouped.has(id)){item(id,row.contract,fileId,undefined,'Accepted result grouping; current symbol match unavailable');grouped.set(id,true);}parent=id;}
   const declarationContract=matches.length===1?matches[0].slice(0,-1).findLast(node=>node.kind===5)?.name:null;
   const description=model.status(row)+(declarationContract&&declarationContract!==row.contract?`; declared in ${declarationContract}; verification context ${row.contract}`:'');
   item(rowId(fileId,row),model.label(row),parent,valid?row.range:undefined,description,row);
  }
  for(const id of used)metadata.get(id).item.children.replace(children.get(id));
  for(const id of old.keys())if(!used.has(id))metadata.delete(id);
  return file;
 }
 function renderCompiler(doc,symbols){
  const valid=currentSymbols(symbols,doc.getText());if(!valid)return false;clear(doc.uri);const file=controller.createTestItem(key(doc.uri),vscode.workspace.asRelativePath(doc.uri),doc.uri);file.description='Current compiler declarations; no verification outcomes';controller.items.add(file);metadata.set(file.id,{item:file,parent:null,uri:doc.uri,compilerOnly:true});
  function visit(nodes,parent,path=[]){for(const symbol of nodes){if(![5,12].includes(symbol.kind))continue;const trail=[...path,[symbol.name,symbol.kind,symbol.selectionRange]],id=key(doc.uri)+'#compiler:'+JSON.stringify(trail),item=controller.createTestItem(id,symbol.name,doc.uri);item.range=toRange(symbol.selectionRange);item.description='Current compiler declaration; verification obligation not discovered';item.tags=[];parent.children.add(item);metadata.set(id,{item,parent:parent.id,uri:doc.uri,compilerOnly:true});visit(symbol.children,item,trail);}}
  visit(valid,file);return true;
 }
 return{render,renderCompiler,obligationTag,clear,leaves,live,excluded};
}
module.exports={install,currentSymbols,rowId,items};
