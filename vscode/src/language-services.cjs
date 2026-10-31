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
function index(text,ast){
  const nodes=[],declarations=new Map(),parents=new Map();
  const visit=(node,parent)=>{
    if(!node||typeof node!=='object')return;
    if(Array.isArray(node)){node.forEach(n=>visit(n,parent));return;}
    if(node.nodeType){nodes.push(node);parents.set(node,parent);if(kinds[node.nodeType]&&Number.isSafeInteger(node.id))declarations.set(node.id,node);parent=node;}
    for(const value of Object.values(node))if(value&&typeof value==='object')visit(value,parent);
  };
  visit(ast,null);
  const nameRange=node=>{
    let range=byteRange(text,node.nameLocation||node.memberLocation||node.nameLocations?.at(-1)||node.pathNode?.nameLocations?.at(-1));
    if(range)return range;
    const whole=byteRange(text,node.src);if(!whole)return null;
    const start=offset(text,whole.start),end=offset(text,whole.end),name=node.name||node.memberName;
    const at=name?text.slice(start,end).indexOf(name):-1;
    return at>=0?{start:position(text,start+at),end:position(text,start+at+name.length)}:whole;
  };
  const occurrence=point=>{
    const matches=nodes.filter(n=>contains(nameRange(n),point)&&
      (Number.isSafeInteger(n.referencedDeclaration)||declarations.has(n.id))).sort((a,b)=>{
      const r=n=>{const x=byteRange(text,n.src);return x?offset(text,x.end)-offset(text,x.start):Infinity;};return r(a)-r(b);
    });
    const node=matches[0];return node?{node,range:nameRange(node),declaration:declarations.get(node.referencedDeclaration??node.id)}:null;
  };
  const target=point=>occurrence(point)?.declaration;
  const references=(declaration,include=true)=>{
    if(!declaration)return [];
    const found=nodes.filter(n=>n.referencedDeclaration===declaration.id).map(nameRange).filter(Boolean);
    if(include)found.push(nameRange(declaration));
    return [...new Map(found.filter(Boolean).map(r=>[JSON.stringify(r),r])).values()];
  };
  function symbol(node){
    const range=byteRange(text,node.src),selectionRange=nameRange(node);if(!range||!selectionRange)return null;
    const children=(node.nodes||node.members||[]).filter(n=>kinds[n.nodeType]).map(symbol).filter(Boolean);
    return {name:node.name||node.kind||'constructor',detail:node.typeDescriptions?.typeString||'',kind:kinds[node.nodeType],range,selectionRange,children};
  }
  return {nodes,declarations,parents,nameRange,target,occurrence,references,symbols:(ast?.nodes||[]).filter(n=>kinds[n.nodeType]).map(symbol).filter(Boolean)};
}
function completion(text,point,analysis){
  const before=text.slice(0,offset(text,point)),prefix=/[\w$]*$/.exec(before)[0];
  const member=/\.\s*[\w$]*$/.test(before),items=[];
  if(!member)items.push(...keywords.map(label=>({label,kind:14})));
  // Live-text fallback works during incomplete edits. Strip strings/comments so
  // declarations inside documentation never become bogus suggestions.
  const clean=text.replace(/\/\*[\s\S]*?\*\/|\/\/[^\r\n]*|"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*'/g,' ');
  for(const m of clean.matchAll(/\b(contract|interface|library|function|struct|enum|event|error|modifier)\s+([A-Za-z_$][\w$]*)/g))
    if(!member||m[1]==='function')items.push({label:m[2],kind:m[1]==='function'?3:7,detail:'Declared in this document'});
  for(const node of analysis?.declarations.values()||[])if(node.name&&(!member||node.nodeType==='FunctionDefinition'))items.push({label:node.name,kind:node.nodeType==='FunctionDefinition'?3:6,detail:node.typeDescriptions?.typeString});
  return {isIncomplete:true,items:[...new Map(items.filter(i=>i.label.startsWith(prefix)).map(i=>[i.label,i])).values()]};
}
function signatureHelp(text,point,analysis){
  const before=text.slice(0,offset(text,point));let depth=0,open=-1;
  for(let i=before.length-1;i>=0;i--){if(before[i]===')')depth++;if(before[i]==='('){if(depth===0){open=i;break;}depth--;}}
  if(open<0)return null;
  const name=/([A-Za-z_$][\w$]*)\s*$/.exec(before.slice(0,open))?.[1];if(!name)return null;
  const declarations=[...(analysis?.declarations.values()||[])].filter(n=>n.nodeType==='FunctionDefinition'&&n.name===name);
  if(!declarations.length)return null;
  let nested=0,argument=0;for(const char of before.slice(open+1)){if('([{'.includes(char))nested++;if(')]}'.includes(char))nested--;if(char===','&&nested===0)argument++;}
  return {signatures:declarations.map(n=>({label:`${n.name}(${n.parameters.parameters.map(p=>`${p.typeDescriptions?.typeString||''} ${p.name}`).join(', ')})`,
    parameters:n.parameters.parameters.map(p=>({label:p.name||p.typeDescriptions?.typeString||'argument'}))})),activeSignature:0,
    activeParameter:Math.min(argument,Math.max(0,declarations[0].parameters.parameters.length-1))};
}
module.exports={offset,position,applyChanges,byteRange,index,completion,signatureHelp,contains,validIdentifier};
