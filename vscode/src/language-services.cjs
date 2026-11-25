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
  if(!Number.isSafeInteger(start)||!Number.isSafeInteger(end)||start>bytes.length||end>bytes.length)return null;
  // Compiler offsets are UTF-8 byte boundaries; LSP cannot represent a partial
  // codepoint or the interior of CRLF. Never decode either as a replacement.
  const boundary=n=>(n===bytes.length||(bytes[n]&0xc0)!==0x80)&&!(bytes[n-1]===13&&bytes[n]===10);
  if(!boundary(start)||!boundary(end))return null;
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
    if((node.nameLocations!=null&&!Array.isArray(node.nameLocations))||(node.pathNode?.nameLocations!=null&&!Array.isArray(node.pathNode.nameLocations)))return null;
    const explicit=node.nameLocation??node.memberLocation??node.nameLocations?.at(-1)??node.pathNode?.nameLocations?.at(-1);
    // solc reports this sentinel for genuinely unnamed function forms.
    if(explicit==='-1:-1:-1'&&node.nodeType==='FunctionDefinition'&&node.name===''&&['constructor','receive','fallback'].includes(node.kind))return nodeRange(node);
    // Invalid explicit compiler metadata cannot be replaced by a text guess.
    return explicit!=null?(typeof explicit==='string'?nodeRange(node,explicit):null):nodeRange(node);
  };
  const occurrence=point=>{
    const matches=nodes.filter(n=>contains(nameRange(n),point)&&(Number.isSafeInteger(n.referencedDeclaration)||declarations.has(n.id))).sort((a,b)=>{
      const size=n=>{const r=nodeRange(n);return r?offset(text,r.end)-offset(text,r.start):Infinity;};return size(a)-size(b);
    });const node=matches[0],declaration=node&&declarations.get(node.referencedDeclaration??node.id);return node&&(!declaration||nameRange(declaration))?{node,range:nameRange(node),declaration}:null;
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
  // Mask non-code tokens without moving UTF-16 offsets or line boundaries.
  const all=require('./solidity-text.cjs').tokens(text);let code='',end=0;
  for(const token of all)if(token.kind==='comment'||token.kind==='string'){code+=text.slice(end,token.start)+token.text.replace(/[^\r\n]/g,' ');end=token.end;}
  code+=text.slice(end);
  const before=code.slice(0,offset(text,point)),match=/([A-Za-z_$][\w$]*)\s*\.\s*[\w$]*$/.exec(before);if(!match)return [];
  const ts=all.filter(t=>t.kind!=='comment'&&t.kind!=='string');
  const scopes=[];for(let i=0;i<ts.length;i++)if(['contract','library','interface','struct','enum'].includes(ts[i].text)&&ts[i+1]?.kind==='word'){
    const kind=ts[i].text,name=ts[i+1].text;let open=i+2;while(open<ts.length&&ts[open].text!=='{')open++;let depth=1,end=open+1;
    for(;end<ts.length&&depth;end++){if(ts[end].text==='{')depth++;if(ts[end].text==='}')depth--;}
    scopes.push({kind,name,start:ts[open]?.start??text.length,end:ts[end-1]?.end??text.length,body:code.slice(ts[open]?.end,ts[end-1]?.start)});
  }
  let type=match[1],storage=false;
  if(type==='this'||type==='super'){const scope=scopes.find(s=>['contract','library','interface'].includes(s.kind)&&s.start<match.index&&s.end>match.index);type=scope?.name;}
  else{
    const receiver=match[1].replace(/\$/g,'\\$');
    const declarations=[...before.slice(0,match.index).matchAll(new RegExp('([A-Za-z_$][\\w$]*(?:\\s*\\[\\s*\\])?)(?:\\s+(storage|memory|calldata))?\\s+'+receiver+'(?![\\w$])','g'))];
    const declaration=declarations.at(-1);if(declaration){
      type=declaration[1].replace(/\s+/g,'');
      const ownerAt=position=>scopes.find(s=>['contract','library','interface'].includes(s.kind)&&s.start<position&&s.end>position);
      // This additional fallback requires a directly owned declaration and properly nested delimiters.
      const owner=ownerAt(declaration.index),delimiters=[];let valid=true;
      if(owner&&owner===ownerAt(match.index))for(const token of ts){
        if(token.start<=owner.start||token.start>=declaration.index)continue;
        if(['{','(','['].includes(token.text))delimiters.push(token.text);
        const opening=token.text==='}'?'{':token.text===')'?'(':token.text===']'?'[':null;
        if(opening&&delimiters.pop()!==opening)valid=false;
      }
      const directState=owner&&owner===ownerAt(match.index)&&valid&&delimiters.length===0;
      storage=declaration[2]==='storage'||declaration[2]===undefined&&(before.slice(0,declaration.index).lastIndexOf('function')<0||directState);
    }
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
    const location=declaration?.storageLocation;
    // Declaration ownership is separate from type text; only the outer array can grow.
    const nonstorage=/\s(?:memory|calldata)(?: ref| pointer)?$/.test(type);
    const storage=!nonstorage&&(location==='storage'||location==='default'&&declaration?.stateVariable===true||location===undefined&&declaration?.stateVariable===undefined&&/\bstorage\b/.test(type));
    const arrayType=declaration?.typeName,openOuter=/\[\]$/.test(plainType(type));
    const dynamicOuter=openOuter&&(arrayType?.nodeType!=='ArrayTypeName'||!Object.hasOwn(arrayType,'length')||arrayType.length===null);
    result.push({name:'length'});if(storage&&(dynamicOuter||/^bytes(?: |$)/.test(type)))result.push({name:'push',nodeType:'FunctionDefinition'},{name:'pop',nodeType:'FunctionDefinition'});
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
  const cursor=offset(text,point),token=require('./solidity-text.cjs').tokens(text).find(t=>t.start<cursor&&cursor<=t.end&&(t.kind==='comment'||t.kind==='string'));
  if(token){
    let inside=cursor<token.end;
    if(token.kind==='comment')inside ||= token.text.startsWith('//')||token.text.length<4||!token.text.endsWith('*/');
    else if(!inside){const raw=token.text.replace(/^(?:hex|unicode)(?=["'])/,'');let escapes=0;for(let i=raw.length-2;i>=0&&raw[i]==='\\';i--)escapes++;inside=raw.length<2||raw.at(-1)!==raw[0]||escapes%2===1;}
    if(inside)return {isIncomplete:true,items:[]};
  }
  const before=text.slice(0,cursor),prefix=/[\w$]*$/.exec(before)[0];
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
  const before=text.slice(0,offset(text,point)),ts=require('./solidity-text.cjs').tokens(before).filter(t=>t.kind!=='comment'&&t.kind!=='string');let depth=0,open=-1;
  for(let i=ts.length-1;i>=0;i--){if(ts[i].text===')')depth++;if(ts[i].text==='('){
    if(depth>0){depth--;continue;}
    if(ts[i-1]?.kind==='word'){open=i;break;}
    // Grouping has no callee; expression/index/call-options callees stay unsupported.
    if([')',']','}'].includes(ts[i-1]?.text))return null;
  }}
  if(open<0||ts[open-1]?.kind!=='word')return null;
  // A named function declaration is not an invocation of that function.
  if(ts[open-2]?.text==='function')return null;
  const name=ts[open-1].text;
  const call=analysis?.nodes.filter(n=>n.nodeType==='FunctionCall').map(node=>{const range=analysis.nodeRange(node);return contains(range,point)&&!(range.end.line===point.line&&range.end.character===point.character)?{node,size:offset(text,range.end)-offset(text,range.start)}:null;}).filter(Boolean).sort((a,b)=>a.size-b.size)[0]?.node;
  const resolved=analysis?.declarations.get(call?.expression?.referencedDeclaration);
  const declarations=resolved?.nodeType==='FunctionDefinition'?[resolved]:[...(analysis?.declarations.values()||[])].filter(n=>n.nodeType==='FunctionDefinition'&&n.name===name);
  if(!declarations.length)return null;
  let nested=0,argument=0;for(const token of ts.slice(open+1)){const char=token.text;if('([{'.includes(char))nested++;if(')]}'.includes(char))nested--;if(char===','&&nested===0)argument++;}
  return {signatures:declarations.map(n=>({label:`${n.name}(${n.parameters.parameters.map(p=>`${p.typeDescriptions?.typeString||''} ${p.name}`).join(', ')})`,
    parameters:n.parameters.parameters.map(p=>({label:p.name||p.typeDescriptions?.typeString||'argument'}))})),activeSignature:0,
    activeParameter:Math.min(argument,Math.max(0,declarations[0].parameters.parameters.length-1))};
}
module.exports={offset,position,applyChanges,byteRange,index,completion,signatureHelp,contains,validIdentifier,receiverMembers};

// Display-only compiler provenance; never a proof input or editing authority.
function hoverContent(index,target){
  const origin=index.origins.get(target),range=index.nodeRange(target);let description;
  if(origin&&range&&['FunctionDefinition','ContractDefinition','StructDefinition','EnumDefinition','ModifierDefinition'].includes(target.nodeType)){
    const snippet=origin.text.slice(offset(origin.text,range.start),offset(origin.text,range.end));
    const bodyRange=target.body?.src?index.nodeRange(target,target.body.src):null;
    let bodyStart=bodyRange?offset(origin.text,bodyRange.start)-offset(origin.text,range.start):null;
    if(bodyStart===null){let depth=0;for(const token of require('./solidity-text.cjs').tokens(snippet)){if(token.kind==='comment')continue;if(['(', '['].includes(token.text))depth++;else if([')', ']'].includes(token.text))depth--;else if(token.text==='{'&&depth===0){bodyStart=token.start;break;}}}
    description=(bodyStart===null?snippet:snippet.slice(0,bodyStart)).trim().replace(/;$/,'');
  }
  if(!description)description=`${target.name||target.kind}: ${target.typeDescriptions?.typeString||target.nodeType}`;
  let documentation=typeof target.documentation==='string'?target.documentation:target.documentation?.text;
  const docRange=origin&&target.documentation?.src?index.nodeRange(target,target.documentation.src):null;
  if(docRange){const raw=origin.text.slice(offset(origin.text,docRange.start),offset(origin.text,docRange.end));
    if(raw.startsWith('///'))documentation=raw.split(/\r\n|\r|\n/).map(line=>line.replace(/^\s*\/\/\/ ?/,'')).join('\n');
    else if(raw.startsWith('/**'))documentation=raw.slice(3,-2).split(/\r\n|\r|\n/).map(line=>line.replace(/^\s*\* ?/,'')).join('\n');
  }
  return (documentation?.trim()?documentation.trim()+'\n':'')+'```solidity\n'+description+'\n```';
}
module.exports.hoverContent=hoverContent;
