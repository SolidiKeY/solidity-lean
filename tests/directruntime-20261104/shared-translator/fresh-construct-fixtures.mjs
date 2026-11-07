import {compileFixture} from '../../../scripts/solc-ast.mjs';
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {createHash} from 'node:crypto';
const owned='tests/directruntime-20261104/shared-translator';
const sha=x=>createHash('sha256').update(x).digest('hex');
const census=JSON.parse(readFileSync(owned+'/fixture-census.json','utf8'));
mkdirSync(owned+'/fresh',{recursive:true});
const receipts=[];
for(const fixture of census.selectedFixturePaths){
 const old=JSON.parse(readFileSync(fixture,'utf8'));const header=old.header;
 const modern=header.solcVersion.startsWith('0.8.38');
 const compiler=modern?owned+'/artifacts/compiler/soljson-v0.8.38+commit.1835d247.js':'/workspace/.setup/soljson/soljson-v0.8.34+commit.80d5c536.js';
 const digest=modern?'6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390':'c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8';
 const args=['--solkey','/workspace/.setup/solkey','--compiler-file',compiler,'--compiler-sha256',digest,'--no-wrapper'];
 const name=fixture.split('/').pop().replace('.ast.json','');
 let source,sourceBytes,project,anchors;
 if(header.provenanceVersion===2){
  const inputPath='tests/solc/source-units/SourceUnits.input.json';
  const input=JSON.parse(readFileSync(inputPath,'utf8'));
  source='app/Main.sol';sourceBytes=Buffer.from(input.sources[source].content);
  project={mainSource:source,sources:input.sources,remappings:input.settings.remappings};
  anchors=Object.entries(input.sources).map(([name,x])=>({name,sourceSha256:sha(x.content),inputFixture:inputPath,inputSha256:sha(readFileSync(inputPath))}));
 }else{
  source=header.source??fixture.replace('.ast.json','.sol');sourceBytes=readFileSync(source);
  anchors=[{name:source.split('/').pop(),source:source,sourceSha256:sha(sourceBytes)}];
 }
 const result=compileFixture({args:[...args,'--source',source,'--out',owned+'/artifacts/h41-normalized/'+name+'.ast.json'],sourceBytes,project,analysisOnly:true,quiet:true});
 const output=owned+'/fresh/'+name+'.raw.json';
 const data={boundary:'Fresh external compiler ASTs, saved without AST rewriting. Producer wrapper/backend gaps are recorded separately; compiler admission is not intrinsic proof or backend correctness.',compiler:result.compiler,originalFixture:fixture,sourceAnchors:anchors,producerWrapperGap:result.proofGap??null,diagnostics:result.diagnostics,compilerAsts:result.rawAsts};
 writeFileSync(output,JSON.stringify(data,null,2)+'\n');
 receipts.push({output,outputSha256:sha(readFileSync(output)),compiler:result.compiler,sourceAnchors:anchors,producerWrapperGap:result.proofGap??null});
 console.log(JSON.stringify(receipts.at(-1)));
}
writeFileSync(owned+'/evidence/h41/fresh-compilation.json',JSON.stringify({fixtures:receipts,boundary:'Actual pinned compiler executions; no source/intrinsic/backend preservation theorem.'},null,2)+'\n');
