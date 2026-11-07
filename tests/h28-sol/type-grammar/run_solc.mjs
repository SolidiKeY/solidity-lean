import {readFileSync,writeFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {resolve,dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
const area=dirname(fileURLToPath(import.meta.url));
const manifest=JSON.parse(readFileSync(resolve(area,'fixtures.json'),'utf8'));
const compiler=process.argv[2];
if(!compiler)throw new Error('explicit pinned compiler path required');
const sha=b=>createHash('sha256').update(b).digest('hex');
if(sha(readFileSync(compiler))!==manifest.compiler.sha256)throw new Error('compiler hash mismatch');
const solc=createRequire(import.meta.url)(resolve(compiler));
const version=solc.cwrap('solidity_version','string',[])();
if(version!==manifest.compiler.version)throw new Error('compiler version mismatch: '+version);
const compile=solc.cwrap('solidity_compile','string',['string','number','number']);
const results=[];const allKinds={};const typeCases=new Map();let failures=0;
for(const fixture of manifest.fixtures){
 const src=readFileSync(resolve(area,fixture.file));
 if(sha(src)!==fixture.sha256)throw new Error('fixture hash mismatch: '+fixture.id);
 const input={language:'Solidity',sources:{'fixture.sol':{content:src.toString()}},settings:{stopAfter:'parsing',outputSelection:{'*':{'':['ast']}}}};
 const encoded=JSON.stringify(input);const started=performance.now();const raw=compile(encoded,0,0);const output=JSON.parse(raw);
 const errors=(output.errors??[]).filter(e=>e.severity==='error');
 const accepted=errors.length===0;const kinds={};const fieldIndices=new Set();let nodes=0;
 function walk(x,parentKind=null){if(!x||typeof x!=='object')return;if(x.nodeType){
 if(fixture.expect_accept&&x.nodeType==='VariableDeclaration'&&parentKind==='ContractDefinition'){
  const match=/^v([0-9]+)$/.exec(x.name);if(!match)throw new Error('unexpected state-variable name');
  const index=Number(match[1]);const text=fixture.type_sources[index];if(typeof text!=='string')throw new Error('missing exact generated type');
  const start=Number(x.src.split(':')[0]);
  if(src.subarray(start,start+Buffer.byteLength(text)).toString()!==text)throw new Error('AST declaration/source mismatch');
  if(fieldIndices.has(index))throw new Error('duplicate state-variable index');fieldIndices.add(index);
  const kind=x.typeName.nodeType;if(!manifest.expected_type_nodes.includes(kind))throw new Error('unexpected type node');
  const old=typeCases.get(text);if(old&&old.root_kind!==kind)throw new Error('inconsistent root kind');
  if(!old)typeCases.set(text,{source:text,expect_accept:true,root_kind:kind,fixtures:[fixture.id]});
  else if(!old.fixtures.includes(fixture.id))old.fixtures.push(fixture.id);
 }
 nodes++;kinds[x.nodeType]=(kinds[x.nodeType]??0)+1;allKinds[x.nodeType]=(allKinds[x.nodeType]??0)+1;}for(const v of Object.values(x)){if(Array.isArray(v))v.forEach(y=>walk(y,x.nodeType??parentKind));else if(v&&typeof v==='object')walk(v,x.nodeType??parentKind);}}
 if(output.sources?.['fixture.sol']?.ast)walk(output.sources['fixture.sol'].ast);
 const phaseCorrect=accepted?(nodes>0&&(!fixture.expect_accept||fieldIndices.size===fixture.type_sources.length)):errors.every(e=>e.type==='ParserError');
 const passed=accepted===fixture.expect_accept&&phaseCorrect;
 if(!passed)failures++;
 results.push({id:fixture.id,file:fixture.file,source_sha256:fixture.sha256,input_sha256:sha(encoded),output_sha256:sha(raw),expected_accept:fixture.expect_accept,accepted,passed,phaseCorrect,elapsed_ms:performance.now()-started,node_count:nodes,node_kinds:kinds,errors:errors.map(e=>({type:e.type,errorCode:e.errorCode,message:e.message,sourceLocation:e.sourceLocation}))});
 console.log((passed?'PASS':'FAIL')+' '+fixture.id+' '+(accepted?'accepted':'rejected')+' '+errors.map(e=>e.message).join(' | '));
}
for(const kind of manifest.expected_type_nodes)if(!allKinds[kind]){failures++;console.log('FAIL absent type constructor '+kind);}
const result={compiler:{...manifest.compiler,observed_version:version},node_version:process.version,phase:'parsing',manifest_sha256:sha(readFileSync(resolve(area,'fixtures.json'))),fixture_count:results.length,failures,all_node_kinds:allKinds,results,proof_boundary:manifest.proof_boundary};
const cases=[...typeCases.values(),...manifest.fixtures.filter(f=>!f.expect_accept).map(f=>({source:f.type_source,expect_accept:false,root_kind:null,fixtures:[f.id]}))];
const encodedCases=JSON.stringify({compiler:result.compiler,phase:'parsing',manifest_sha256:result.manifest_sha256,cases},null,2)+'\n';
writeFileSync(resolve(area,'evidence/solc-type-cases.json'),encodedCases);
result.type_cases_sha256=sha(encodedCases);
writeFileSync(resolve(area,'evidence/solc-results.json'),JSON.stringify(result,null,2)+'\n');
console.log('SOLC_GRAMMAR_FIXTURES '+(failures?'FAIL':'PASS')+' '+results.length+' fixtures; '+failures+' failures');
process.exitCode=failures?1:0;
