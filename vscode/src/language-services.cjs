'use strict';
const keywords=('contract interface library abstract function constructor modifier event error struct enum mapping address bool string bytes uint int public private internal external view pure payable returns return if else for while do break continue require assert revert new delete this super true false storage memory calldata immutable constant virtual override emit try catch unchecked assembly').split(' ');
const reserved=new Set([...keywords,...('import pragma as from layout at after alias apply auto byte case copyof default define final implements in inline let macro match mutable null of partial promise reference relocatable sealed sizeof static supports switch typedef typeof var is using type fixed ufixed receive fallback indexed anonymous transient').split(' ')]);
const validIdentifier=name=>typeof name==='string'&&/^[A-Za-z_$][\w$]*$/.test(name)&&!reserved.has(name)&&! /^(?:u?int\d+|bytes\d+|u?fixed\d+x\d+)$/.test(name);
const contains=(r,p)=>r&&(p.line>r.start.line||p.line===r.start.line&&p.character>=r.start.character)&&(p.line<r.end.line||p.line===r.end.line&&p.character<=r.end.character);
function offset(text,p){
  if(!Number.isSafeInteger(p?.line)||!Number.isSafeInteger(p?.character)||p.line<0||p.character<0)throw new Error('Invalid document position');
  const lines=text.split(/\r\n|\r|\n/);if(p.line>=lines.length||p.character>lines[p.line].length)throw new Error('Position outside document');
  let start=0;const re=/\r\n|\r|\n/g;for(let i=0;i<p.line;i++){re.lastIndex=start;const m=re.exec(text);start=m.index+m[0].length;}return start+p.character;
}
function applyChanges(text,changes){
  for(const change of changes){
    if(typeof change.text!=='string')throw new Error('Invalid document change');
    if(!change.range){text=change.text;continue;}
    const start=offset(text,change.range.start),end=offset(text,change.range.end);if(end<start)throw new Error('Reversed document range');
    text=text.slice(0,start)+change.text+text.slice(end);
  }
  return text;
}
function position(text,n){const lines=text.slice(0,n).split(/\r\n|\r|\n/);return {line:lines.length-1,character:lines.at(-1).length};}
function byteRange(text,src){
  const m=/^(\d+):(\d+):0$/.exec(src??'');if(!m)return null;
  const bytes=Buffer.from(text),start=Number(m[1]),end=start+Number(m[2]);
  if(end>bytes.length)return null;
  return {start:position(text,bytes.subarray(0,start).toString('utf8').length),end:position(text,bytes.subarray(0,end).toString('utf8').length)};
}
const kinds={ContractDefinition:5,FunctionDefinition:12,VariableDeclaration:13,StructDefinition:23,EnumDefinition:10,EnumValue:22,EventDefinition:24,ErrorDefinition:5,ModifierDefinition:6,UserDefinedValueTypeDefinition:26};
function index(text,ast,project){
  const nodes=[],allNodes=[],declarations=new Map(),parents=new Map(),origins=new Map();
  const {pathToFileURL}=require('node:url');
  const mainId=Number(ast?.src?.split(':').at(-1)??0);
  const units=project?.asts?Object.entries(project.asts):[['',ast]];
  for(const [name,unit]of units){
    const file=project?.files?.[name],origin={text:file?.text??text,hash:file?.hash,uri:file?pathToFileURL(file.path).href:project?.uri,version:file?.version,
      sourceId:Number(unit?.src?.split(':').at(-1)??mainId)};
    const visit=(node,parent)=>{
      if(!node||typeof node!=='object')return;
      if(Array.isArray(node)){node.forEach(n=>visit(n,parent));return;}
      if(node.nodeType){allNodes.push(node);if(unit===ast||unit?.id===ast?.id)nodes.push(node);parents.set(node,parent);origins.set(node,origin);
        if(kinds[node.nodeType]&&Number.isSafeInteger(node.id))declarations.set(node.id,node);parent=node;}
      for(const value of Object.values(node))if(value&&typeof value==='object')visit(value,parent);
    };visit(unit,null);
  }
  const nodeRange=(node,src=node.src)=>{
    const origin=origins.get(node);if(!origin)return null;
    const match=/^(\d+):(\d+):(-?\d+)$/.exec(src??'');
    return match&&Number(match[3])===origin.sourceId?byteRange(origin.text,`${match[1]}:${match[2]}:0`):null;
  };
  const nameRange=node=>{
    if(!node)return null;
    let range=nodeRange(node,node.nameLocation||node.memberLocation||node.nameLocations?.at(-1)||node.pathNode?.nameLocations?.at(-1));
    if(range)return range;
    const whole=nodeRange(node);if(!whole)return null;
    const source=origins.get(node).text,start=offset(source,whole.start),end=offset(source,whole.end),name=node.name||node.memberName;
    const at=name?source.slice(start,end).indexOf(name):-1;
    return at>=0?{start:position(source,start+at),end:position(source,start+at+name.length)}:whole;
  };
  const occurrence=point=>{
    const matches=nodes.filter(n=>contains(nameRange(n),point)&&(Number.isSafeInteger(n.referencedDeclaration)||declarations.has(n.id))).sort((a,b)=>{
      const size=n=>{const r=nodeRange(n);return r?offset(text,r.end)-offset(text,r.start):Infinity;};return size(a)-size(b);
    });const node=matches[0];return node?{node,range:nameRange(node),declaration:declarations.get(node.referencedDeclaration??node.id)}:null;
  };
  const location=node=>({uri:origins.get(node)?.uri,range:nameRange(node),version:origins.get(node)?.version,sourceHash:origins.get(node)?.hash});
  const referenceNodes=(declaration,include=true)=>{
    if(!declaration)return [];
    const found=allNodes.filter(n=>n.referencedDeclaration===declaration.id);if(include)found.push(declaration);
    return [...new Map(found.filter(n=>nameRange(n)).map(n=>[JSON.stringify(location(n)),n])).values()];
  };
  function symbol(node){const range=nodeRange(node),selectionRange=nameRange(node);if(!range||!selectionRange)return null;
    return {name:node.name||node.kind||'constructor',detail:node.typeDescriptions?.typeString||'',kind:kinds[node.nodeType],range,selectionRange,
      children:(node.nodes||node.members||[]).filter(n=>kinds[n.nodeType]).map(symbol).filter(Boolean)};}
  const contractAt=point=>nodes.find(n=>n.nodeType==='ContractDefinition'&&contains(nodeRange(n),point));
  return {nodes,allNodes,declarations,parents,origins,nodeRange,nameRange,location,contractAt,occurrence,target:p=>occurrence(p)?.declaration,
    references:(d,include)=>referenceNodes(d,include).map(nameRange),referenceNodes,
    locations:(d,include)=>referenceNodes(d,include).map(location),symbols:((units.find(([,u])=>u?.id===ast?.id)?.[1]??ast)?.nodes||[]).filter(n=>kinds[n.nodeType]).map(symbol).filter(Boolean)};
}
const plainType=s=>(s||'').replace(/ (?:storage|memory|calldata)(?: ref| pointer)?/g,'');
function fallbackMembers(text,point){
  const before=text.slice(0,offset(text,point)),match=/([A-Za-z_$][\w$]*)\s*\.\s*[\w$]*$/.exec(before);if(!match)return [];
  const ts=require('./solidity-text.cjs').tokens(text).filter(t=>t.kind!=='comment'&&t.kind!=='string');
  const scopes=[];for(let i=0;i<ts.length;i++)if(['contract','library','interface','struct','enum'].includes(ts[i].text)&&ts[i+1]?.kind==='word'){
    const kind=ts[i].text,name=ts[i+1].text;let open=i+2;while(open<ts.length&&ts[open].text!=='{')open++;let depth=1,end=open+1;
    for(;end<ts.length&&depth;end++){if(ts[end].text==='{')depth++;if(ts[end].text==='}')depth--;}
    scopes.push({kind,name,start:ts[open]?.start??text.length,end:ts[end-1]?.end??text.length,body:text.slice(ts[open]?.end,ts[end-1]?.start)});
  }
  let type=match[1],storage=false;
  if(type==='this'||type==='super'){const scope=scopes.find(s=>['contract','library','interface'].includes(s.kind)&&s.start<match.index&&s.end>match.index);type=scope?.name;}
  else{
    const declarations=[...before.slice(0,match.index).matchAll(new RegExp('([A-Za-z_$][\\w$]*(?:\\[\\])?)(?:\\s+(storage|memory|calldata))?\\s+'+match[1]+'\\b','g'))];
    const declaration=declarations.at(-1);if(declaration){type=declaration[1];storage=declaration[2]==='storage'||declaration[2]===undefined&&before.slice(0,declaration.index).lastIndexOf('function')<0;}
  }
  if(/\[\]$/.test(type||'')||type==='bytes')return [{name:'length'},...(storage?[{name:'push',nodeType:'FunctionDefinition'},{name:'pop',nodeType:'FunctionDefinition'}]:[])];
  const scope=scopes.find(s=>s.name===type);if(!scope)return [];
  if(scope.kind==='struct')return [...scope.body.matchAll(/\b([A-Za-z_$][\w$]*)\s*;/g)].map(m=>({name:m[1]}));
  if(scope.kind==='enum')return scope.body.split(',').map(name=>({name:name.trim()}));
  return [...scope.body.matchAll(/\bfunction\s+([A-Za-z_$][\w$]*)\s*\([^)]*\)([^{};]*)/g)].filter(m=>/\b(public|external)\b/.test(m[2])).map(m=>({name:m[1],nodeType:'FunctionDefinition'}));
}
function receiverMembers(text,point,analysis){
  const before=text.slice(0,offset(text,point));const match=/([A-Za-z_$][\w$]*)\s*\.\s*[\w$]*$/.exec(before);
  if(!match)return null;
  if(!analysis)return fallbackMembers(text,point);
  const receiver=match[1],contract=analysis?.contractAt(point);
  let declaration=receiver==='this'||receiver==='super'?contract:analysis?.target(position(text,match.index));
  let type=declaration?.typeDescriptions?.typeString||'';
  const typeId=declaration?.typeName?.referencedDeclaration??declaration?.typeName?.pathNode?.referencedDeclaration;
  if(typeId!==undefined)declaration=analysis.declarations.get(typeId);
  if(receiver==='super'){
    const bases=(contract?.linearizedBaseContracts||[]).slice(1).flatMap(id=>analysis.declarations.get(id)?.nodes||[]);
    return bases.filter(n=>n.nodeType==='FunctionDefinition'&&!['private','external'].includes(n.visibility));
  }
  if(declaration?.nodeType==='ContractDefinition'){
    const ids=declaration.linearizedBaseContracts||[declaration.id];
    return ids.flatMap(id=>analysis.declarations.get(id)?.nodes||[]).filter(n=>
      (n.nodeType==='FunctionDefinition'&&(['public','external'].includes(n.visibility)||declaration.contractKind==='library'))||
      n.nodeType==='VariableDeclaration'&&n.visibility==='public'||['StructDefinition','EnumDefinition'].includes(n.nodeType));
  }
  if(declaration?.nodeType==='StructDefinition')return declaration.members||[];
  if(declaration?.nodeType==='EnumDefinition')return declaration.members||[];
  const result=[];
  if(/\[.*\]/.test(type)||/^bytes(?: |$)/.test(type)){
    result.push({name:'length'});if(type.includes('storage')&&/\[\]|^bytes(?: |$)/.test(type))result.push({name:'push',nodeType:'FunctionDefinition'},{name:'pop',nodeType:'FunctionDefinition'});
  }
  if(/^address/.test(type))for(const name of ['balance','code','codehash','call','delegatecall','staticcall'])result.push({name});
  for(const using of analysis?.nodes.filter(n=>n.nodeType==='UsingForDirective')||[]){
    const library=analysis.declarations.get(using.libraryName?.referencedDeclaration);
    const functions=library?.nodes?.filter(n=>n.nodeType==='FunctionDefinition')||[];
    for(const fn of functions)if(plainType(fn.parameters?.parameters?.[0]?.typeDescriptions?.typeString)===plainType(type))result.push(fn);
  }
  return result;
}

function completion(text,point,analysis){
  const before=text.slice(0,offset(text,point)),prefix=/[\w$]*$/.exec(before)[0];
  const member=/\.\s*[\w$]*$/.test(before),items=[];
  if(!member)items.push(...keywords.map(label=>({label,kind:14})));
  if(member){for(const node of receiverMembers(text,point,analysis)||[])if(node.name)items.push({label:node.name,kind:node.nodeType==='FunctionDefinition'?3:6,detail:node.typeDescriptions?.typeString});}
  else {
    const clean=text.replace(/\/\*[\s\S]*?\*\/|\/\/[^\r\n]*|"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*'/g,' ');
    for(const m of clean.matchAll(/\b(contract|interface|library|function|struct|enum|event|error|modifier)\s+([A-Za-z_$][\w$]*)/g))items.push({label:m[2],kind:m[1]==='function'?3:7,detail:'Declared in this document'});
    for(const node of analysis?.declarations.values()||[])if(node.name)items.push({label:node.name,kind:node.nodeType==='FunctionDefinition'?3:6,detail:node.typeDescriptions?.typeString});
  }

  return {isIncomplete:true,items:[...new Map(items.filter(i=>i.label.startsWith(prefix)).map(i=>[i.label,i])).values()]};
}
function signatureHelp(text,point,analysis){
  const before=text.slice(0,offset(text,point));let depth=0,open=-1;
  for(let i=before.length-1;i>=0;i--){if(before[i]===')')depth++;if(before[i]==='('){if(depth===0){open=i;break;}depth--;}}
  if(open<0)return null;
  const name=/([A-Za-z_$][\w$]*)\s*$/.exec(before.slice(0,open))?.[1];if(!name)return null;
  const call=analysis?.nodes.filter(n=>n.nodeType==='FunctionCall'&&contains(analysis.nodeRange(n),point)).sort((a,b)=>(a.src?.length||0)-(b.src?.length||0))[0];
  const resolved=analysis?.declarations.get(call?.expression?.referencedDeclaration);
  const declarations=resolved?.nodeType==='FunctionDefinition'?[resolved]:[...(analysis?.declarations.values()||[])].filter(n=>n.nodeType==='FunctionDefinition'&&n.name===name);
  if(!declarations.length)return null;
  let nested=0,argument=0;for(const char of before.slice(open+1)){if('([{'.includes(char))nested++;if(')]}'.includes(char))nested--;if(char===','&&nested===0)argument++;}
  return {signatures:declarations.map(n=>({label:`${n.name}(${n.parameters.parameters.map(p=>`${p.typeDescriptions?.typeString||''} ${p.name}`).join(', ')})`,
    parameters:n.parameters.parameters.map(p=>({label:p.name||p.typeDescriptions?.typeString||'argument'}))})),activeSignature:0,
    activeParameter:Math.min(argument,Math.max(0,declarations[0].parameters.parameters.length-1))};
}
module.exports={offset,position,applyChanges,byteRange,index,completion,signatureHelp,contains,validIdentifier,receiverMembers};
