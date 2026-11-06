// Historical read-only lookup data. This module exports no compiler AST, proof input or editing operation.
'use strict';
const language=require('./language-services.cjs'),source=require('./solidity-text.cjs');
const methods=new Set(['textDocument/hover','textDocument/definition','textDocument/documentSymbol','textDocument/references','textDocument/documentHighlight']);
function directives(text){const ts=source.tokens(text).filter(t=>t.kind!=='comment'),result=[];for(let i=0;i<ts.length;i++)if(['import','pragma','using'].includes(ts[i].text)){const item=[];do{item.push(ts[i].text);}while(ts[i].text!==';'&&++i<ts.length);result.push(item);}return JSON.stringify(result);}
function snapshot(index,doc,generation){
  const declarations=new Map(),entries=[],bindingInputs=[];
  const scopes=node=>{const result=[];for(let p=index.parents.get(node);p;p=index.parents.get(p))if(['ContractDefinition','FunctionDefinition','ModifierDefinition','Block','StructDefinition'].includes(p.nodeType)){const range=index.nodeRange(p);if(range)result.push(range);}return result;};
  // Compiler-derived declaration headers include inheritance, receiver/local types,
  // parameters, returns and modifiers; body edits may preserve historical display.
  for(const node of index.nodes.filter(n=>index.declarations.has(n.id))){
    const range=index.nodeRange(node);if(!range)continue;
    const start=language.offset(doc.text,range.start),end=language.offset(doc.text,range.end);
    const container=['ContractDefinition','FunctionDefinition','ModifierDefinition','StructDefinition','EnumDefinition'].includes(node.nodeType);
    const brace=container?source.tokens(doc.text.slice(start,end)).find(t=>t.text==='{'):null;
    bindingInputs.push({start:range.start,end:brace?language.position(doc.text,start+brace.end):range.end});
  }
  for(const [id,node]of index.declarations){const location=index.location(node),name=node.name||node.kind;
    if(!location.range||!name)continue;
    const uri=location.uri||doc.uri,origin=index.origins.get(node),range=location.range;
    declarations.set(id,{id,name,description:`${name}: ${node.typeDescriptions?.typeString||node.nodeType}`,location:{uri,range},whole:uri===doc.uri?index.nodeRange(node):null,nameText:origin.text.slice(language.offset(origin.text,range.start),language.offset(origin.text,range.end)),scopes:uri===doc.uri?scopes(node):[]});
  }
  for(const node of index.nodes){const target=declarations.get(node.referencedDeclaration??node.id),range=index.nameRange(node);if(!target||!range)continue;
    let expression=node;
    while(['MemberAccess','IndexAccess','IndexRangeAccess','FunctionCall','FunctionCallOptions','TupleExpression','BinaryOperation','UnaryOperation','Conditional','Assignment','NewExpression'].includes(index.parents.get(expression)?.nodeType))expression=index.parents.get(expression);
    const whole=declarations.has(node.id)?range:index.nodeRange(expression);if(!whole)continue;
    const names=source.tokens(doc.text.slice(language.offset(doc.text,whole.start),language.offset(doc.text,whole.end))).filter(t=>t.kind==='word').map(t=>t.text);
    entries.push({target:target.id,range,context:whole,names,scopes:scopes(node)});
  }
  const files=doc.compiled?.project?.files||{};
  const dependencies=Object.fromEntries(Object.entries(files).filter(([,file])=>require('node:path').resolve(file.path)!==require('node:path').resolve(doc.path)));
  return {uri:doc.uri,version:doc.version,generation,declarations:[...declarations.values()],entries,symbols:structuredClone(index.symbols),bindingInputs,dependencies:{files:dependencies},outdated:false};
}
// Cached line tables and ranges avoid rescanning the entire text for each lookup record.
function table(text){
  const starts=[0],ends=[];for(const m of text.matchAll(/\r\n|\r|\n/g)){ends.push(m.index);starts.push(m.index+m[0].length);}ends.push(text.length);
  const at=p=>{if(!Number.isSafeInteger(p?.line)||!Number.isSafeInteger(p?.character)||p.line<0||p.line>=starts.length||p.character<0||p.character>ends[p.line]-starts[p.line])throw Error('Position outside document');return starts[p.line]+p.character;};
  const pos=n=>{if(n<0||n>text.length)return null;let lo=0,hi=starts.length;while(lo+1<hi){const mid=(lo+hi)>>1;if(starts[mid]<=n)lo=mid;else hi=mid;}return n<=ends[lo]?{line:lo,character:n-starts[lo]}:null;};
  return {at,pos};
}
function mapper(before,change){
  const after=language.applyChanges(before,[change]),old=table(before),next=table(after),from=old.at(change.range.start),to=old.at(change.range.end),delta=change.text.length-(to-from),memo=new Map();
  const move=r=>{
    const key=JSON.stringify(r);if(memo.has(key))return memo.get(key);
    let a,b;try{a=old.at(r.start);b=old.at(r.end);}catch{memo.set(key,null);return null;}
    let start=a,end=b;
    if(b<a||a===from&&b===to&&to>from)start=null;
    else if(b<=from){}
    else if(a>=to){start+=delta;end+=delta;}
    else if(a<from&&b>to)end+=delta;
    else start=null;
    const mapped=start===null?null:{start:next.pos(start),end:next.pos(end)};
    const result=mapped?.start&&mapped.end?mapped:null;memo.set(key,result);return result;
  };
  const unchanged=r=>{const mapped=move(r);if(!mapped)return null;return before.slice(old.at(r.start),old.at(r.end))===after.slice(next.at(mapped.start),next.at(mapped.end))?mapped:null;};
  const oldTokens=source.tokens(before).filter(t=>t.kind!=='comment'),newTokens=source.tokens(after).filter(t=>t.kind!=='comment');
  const words=new Set(newTokens.filter(t=>t.kind==='word').map(t=>t.start+':'+t.end));
  const stacks=tokens=>{const result=new Map();let stack=null;for(const t of tokens){if(t.text==='}')stack=stack?.parent||null;result.set(t.start,stack);if(t.text==='{')stack={offset:t.start,parent:stack};}return result;};
  const oldStacks=stacks(oldTokens),newStacks=stacks(newTokens);
  const provenance=r=>{
    const mapped=unchanged(r);if(!mapped)return false;
    let a=oldStacks.get(old.at(r.start)),b=newStacks.get(next.at(mapped.start));if(a===undefined||b===undefined)return false;
    while(a&&b){const brace=unchanged({start:old.pos(a.offset),end:old.pos(a.offset+1)});if(!brace||next.at(brace.start)!==b.offset)return false;a=a.parent;b=b.parent;}return !a&&!b;
  };
  const tokensUnchanged=r=>{const mapped=move(r);if(!mapped)return null;
    const signature=(tokens,a,b)=>{let lo=0,hi=tokens.length;while(lo<hi){const mid=(lo+hi)>>1;if(tokens[mid].start<a)lo=mid+1;else hi=mid;}const result=[];for(let i=lo;i<tokens.length&&tokens[i].end<=b;i++)result.push([tokens[i].kind,tokens[i].text]);return JSON.stringify(result);};
    const oldNeighbors=JSON.parse(neighbors(oldTokens,old.at(r.start),old.at(r.end))),newNeighbors=JSON.parse(neighbors(newTokens,next.at(mapped.start),next.at(mapped.end)));
    // A newly inserted namespace/type prefix just outside the old AST span also changes provenance.
    if((newNeighbors[0]?.[0]==='word'||newNeighbors[0]?.[1]==='.')&&JSON.stringify(oldNeighbors[0])!==JSON.stringify(newNeighbors[0]))return null;
    return signature(oldTokens,old.at(r.start),old.at(r.end))===signature(newTokens,next.at(mapped.start),next.at(mapped.end))?mapped:null;
  };
  const neighbors=(tokens,a,b)=>{
    let lo=0,hi=tokens.length;while(lo<hi){const mid=(lo+hi)>>1;if(tokens[mid].end<=a)lo=mid+1;else hi=mid;}const previous=tokens[lo-1];
    lo=0;hi=tokens.length;while(lo<hi){const mid=(lo+hi)>>1;if(tokens[mid].start<b)lo=mid+1;else hi=mid;}const next=tokens[lo];
    return JSON.stringify([previous&&[previous.kind,previous.text],next&&[next.kind,next.text]]);
  };
  const context=r=>{const mapped=unchanged(r);return mapped&&neighbors(oldTokens,old.at(r.start),old.at(r.end))===neighbors(newTokens,next.at(mapped.start),next.at(mapped.end))?mapped:null;};
  const code=range=>!!range&&words.has(next.at(range.start)+':'+next.at(range.end));
  const boundaryChanged=r=>{const a=old.at(r.start),b=old.at(r.end);return /\S/.test(before.slice(from,to)+change.text)&&((from<=a&&to>=a)||(from<=b&&to>=b));};
  return {after,move,unchanged,context,code,provenance,tokensUnchanged,boundaryChanged,removed:before.slice(from,to)};
}
function migrate(previous,text,changes,version){
  if(!previous||!changes.length)return null;
  let state=structuredClone(previous);
  for(const change of changes){
    if(!change.range)return null;
    const map=mapper(text,change);if(directives(text)!==directives(map.after))return null;
    const bindingInputs=(state.bindingInputs||[]).map(map.tokensUnchanged);if(!bindingInputs.every(Boolean))return null;state.bindingInputs=bindingInputs;
    const editedNames=new Set(source.tokens(map.removed+' '+change.text).filter(t=>t.kind==='word').map(t=>t.text));
    const guards=ranges=>{const result=ranges.map(map.move);return result.every(Boolean)?result:null;};
    state.declarations=state.declarations.flatMap(d=>{
      if(editedNames.has(d.name))return [];
      if(d.location.uri!==state.uri)return [d];
      const range=map.unchanged(d.location.range),whole=map.move(d.whole),scopes=guards(d.scopes);return range&&map.code(range)&&map.provenance(d.location.range)&&whole&&scopes?[{...d,location:{...d.location,range},whole,scopes}]:[];
    });
    const ids=new Set(state.declarations.map(d=>d.id));
    state.entries=state.entries.flatMap(e=>{
      if(!ids.has(e.target)||map.boundaryChanged(e.context)||!map.provenance(e.range)||(e.names||[]).some(name=>editedNames.has(name)))return [];
      const range=map.unchanged(e.range),context=map.context(e.context),scopes=guards(e.scopes);return range&&map.code(range)&&context&&scopes?[{...e,range,context,scopes}]:[];
    });
    const symbol=s=>{const selectionRange=map.unchanged(s.selectionRange),range=map.move(s.range);if(!selectionRange||!map.code(selectionRange)||!range||editedNames.has(s.name))return null;return{...s,range,selectionRange,detail:'Outdated: '+s.detail.replace(/^Outdated: /,''),children:s.children.map(symbol).filter(Boolean)};};
    state.symbols=state.symbols.map(symbol).filter(Boolean);text=map.after;
  }
  return {...state,version,outdated:true};
}
function query(state,method,params){
  if(!methods.has(method)||!state?.outdated)return null;
  if(method==='textDocument/documentSymbol')return structuredClone(state.symbols);
  const targetById=new Map(state.declarations.map(d=>[d.id,d]));
  const e=state.entries.find(e=>language.contains(e.range,params.position));if(!e)return method==='textDocument/references'||method==='textDocument/documentHighlight'?[]:null;
  const target=targetById.get(e.target);if(!target)return null;
  if(method==='textDocument/hover')return{contents:{kind:'plaintext',value:'Outdated: '+target.description},range:e.range};
  if(method==='textDocument/definition')return structuredClone(target.location);
  let entries=state.entries.filter(item=>item.target===target.id).map(item=>({uri:state.uri,range:item.range}));
  if(params.context?.includeDeclaration===false)entries=entries.filter(item=>item.uri!==target.location.uri||JSON.stringify(item.range)!==JSON.stringify(target.location.range));
  if(method==='textDocument/references'&&params.context?.includeDeclaration!==false)entries.push(target.location);
  const unique=[...new Map(entries.map(item=>[JSON.stringify(item),item])).values()];
  return method==='textDocument/references'?structuredClone(unique):unique.filter(item=>item.uri===state.uri).map(item=>({range:structuredClone(item.range),kind:1}));
}
module.exports={snapshot,migrate,query,methods};
