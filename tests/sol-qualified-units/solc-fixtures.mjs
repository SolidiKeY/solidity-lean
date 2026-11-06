import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {dirname, resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
const root=dirname(fileURLToPath(import.meta.url));
const matrix=JSON.parse(readFileSync(resolve(root,'compiler-matrix.json'),'utf8'));
const binary=process.env.SOL_QN_SOLJSON || '/tools/soljson-v0.8.38+commit.1835d247.js';
const sha=b=>createHash('sha256').update(b).digest('hex');
const pins=JSON.parse(readFileSync(resolve(root,'compiler-artifacts.json'),'utf8'));
const artifact=sha(readFileSync(binary));
if(!pins.artifacts.some(a=>a.sha256===artifact))throw Error('compiler SHA256 mismatch');
const solc=createRequire(import.meta.url)(binary);
const version=solc.cwrap('solidity_version','string',[])();
if(version!==matrix.version)throw Error('compiler version mismatch');
const compile=solc.cwrap('solidity_compile','string',['string','number','number']);
const report={version,sha256:artifact,rows:[]};
let failed=false;
for(const row of matrix.rows){
  const sources={}; const hashes={};
  for(const [unit,path] of Object.entries(row.sources)){
    const bytes=readFileSync(resolve(root,path));hashes[unit]=sha(bytes);sources[unit]={content:bytes.toString('utf8')};
  }
  const settings={evmVersion:'osaka',optimizer:{enabled:false,runs:200},viaIR:false,outputSelection:{'*':{'':['ast']}}};
  const output=JSON.parse(compile(JSON.stringify({language:'Solidity',sources,settings}),0,0));
  const errors=(output.errors||[]).filter(e=>e.severity==='error');
  const ids=new Map();const nodes=[];const positions=new Map();
  const graphKinds=new Set(['ContractDefinition','FunctionDefinition','VariableDeclaration','StructDefinition','EnumDefinition','UserDefinedValueTypeDefinition','EventDefinition','ErrorDefinition','ModifierDefinition']);
  for(const [unit,data] of Object.entries(output.sources||{})){
    let index=0;
    for(const node of data.ast?.nodes||[]){
      if(!graphKinds.has(node.nodeType))continue;
      positions.set(node.id,index++);
      if(node.nodeType==='ContractDefinition')for(const member of node.nodes||[])if(graphKinds.has(member.nodeType))positions.set(member.id,index++);
    }
  }
  // Braces are intentional: recursively walk both object and array fields.
  function visit(x,unit){
    if(!x||typeof x!=='object')return;
    if(x.nodeType){nodes.push({unit,node:x});if(typeof x.id==='number')ids.set(x.id,{unit,node:x});}
    for(const value of Object.values(x)){
      if(Array.isArray(value)){for(const item of value)visit(item,unit);}else visit(value,unit);
    }
  }
  for(const [unit,data] of Object.entries(output.sources||{}))visit(data.ast,unit);
  const refs=[];let ok=(errors.length===0)===row.accepted;
  for(const expected of row.references){
    const matching=nodes.filter(({unit,node})=>unit===expected.file&&node.nodeType===expected.nodeType&&node.name===expected.name);
    const resolved=matching.map(({node})=>({reference:node.id,target:ids.get(node.referencedDeclaration)}));
    const good=resolved.some(x=>x.target?.unit===expected.target_unit&&x.target?.node.name===expected.target_name&&positions.get(x.target?.node.id)===expected.target_index);
    refs.push({expected,matched:good,targets:resolved.map(x=>({reference:x.reference,unit:x.target?.unit,name:x.target?.node.name,id:x.target?.node.id,index:positions.get(x.target?.node.id)}))});
    ok&&=good;
  }
  const codes=errors.map(e=>String(e.errorCode)).sort();
  if(row.error_codes!==null)ok&&=JSON.stringify(codes)===JSON.stringify([...row.error_codes].sort());
  const actualTexts=errors.map(e=>e.sourceLocation?sources[e.sourceLocation.file]?.content.slice(e.sourceLocation.start,e.sourceLocation.end):null).sort();
  ok&&=JSON.stringify(actualTexts)===JSON.stringify([...row.error_texts].sort());
  failed||=!ok;
  const declaration_graph=nodes.filter(({node})=>positions.has(node.id)).map(({unit,node})=>({unit,index:positions.get(node.id),name:node.name,nodeType:node.nodeType,solc_id:node.id}));
  report.rows.push({id:row.id,declaration_graph,passed:ok,accepted:errors.length===0,error_codes:codes,errors:errors.map(e=>({code:e.errorCode,message:e.message,sourceLocation:e.sourceLocation,text:e.sourceLocation?sources[e.sourceLocation.file]?.content.slice(e.sourceLocation.start,e.sourceLocation.end):null})),references:refs,source_sha256:hashes,settings,resolution_gap:row.resolution_gap});
}
report.compiler_fixtures_pass=!failed;
report.resolver_acceptance_complete=matrix.rows.every(r=>!r.resolution_gap&&r.kernel_theorems.length>0);
console.log(JSON.stringify(report,null,2));
if(failed)process.exitCode=1;
