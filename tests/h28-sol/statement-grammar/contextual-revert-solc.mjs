import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,mkdirSync,readdirSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {resolve,join,dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
import {execFileSync} from 'node:child_process';
const evidenceRoot='/workspace/h28-statement-grammar-evidence';
const here=dirname(fileURLToPath(import.meta.url)), fixtureDir=join(here,'contextual-revert-fixtures');
const sha=b=>createHash('sha256').update(b).digest('hex');
const compiler=resolve(process.argv[2]??''),requestedOut=resolve(process.argv[3]??'');
const runner=readFileSync(fileURLToPath(import.meta.url));
let out=requestedOut,owned=false,status='fail',failure,manifest;
const header={node:process.version,runnerSha256:sha(runner),requestedOut},results=[];
function walk(x){if(!x||typeof x!=='object')return [];return [x,...Object.values(x).flatMap(v=>Array.isArray(v)?v.flatMap(walk):walk(v))];}
try{
 assert.equal(process.argv.length,4,'usage: node contextual-revert-solc.mjs COMPILER OUTPUT');
 assert(out.startsWith(evidenceRoot+'/'),'fresh owned evidence output required');mkdirSync(out);owned=true;
 manifest=readFileSync(join(fixtureDir,'manifest.json'));const spec=JSON.parse(manifest);
 assert.equal(spec.version,1);assert.equal(spec.cases.length,6);assert.equal(new Set(spec.cases.map(c=>c.id)).size,6);
 assert.deepEqual(readdirSync(fixtureDir).sort(),['manifest.json',...spec.cases.map(c=>c.file)].sort());
 assert.equal(readFileSync('/sys/fs/cgroup/memory.max','utf8').trim(),'12884901888');
 assert.equal(readFileSync('/sys/fs/cgroup/memory.swap.max','utf8').trim(),'0');
 assert.equal(sha(readFileSync(compiler)),spec.compilerSha256,'compiler bytes differ');
 const solc=createRequire(import.meta.url)(compiler),version=solc.cwrap('solidity_version','string',[])();assert.equal(version,spec.compilerVersion);
 const compile=solc.cwrap('solidity_compile','string',['string','number','number']);
 Object.assign(header,{compilerVersion:version,compilerSha256:spec.compilerSha256,manifestSha256:sha(manifest),head:execFileSync('git',['rev-parse','HEAD'],{encoding:'utf8'}).trim(),boundary:spec.boundary});
 for(const c of spec.cases){
  assert(/^[pn][0-9]{2}-[a-z0-9-]+$/.test(c.id));assert.equal(c.file,c.id+'.sol');
  const source=readFileSync(join(fixtureDir,c.file),'utf8');assert.equal(sha(source),c.sha256,c.id+' source drift');
  const input={language:'Solidity',sources:{'case.sol':{content:source}},settings:{outputSelection:{'*':{'':['ast']}}}};
  const output=JSON.parse(compile(JSON.stringify(input),0,0));
  writeFileSync(join(out,c.id+'.input.json'),JSON.stringify(input));writeFileSync(join(out,c.id+'.output.json'),JSON.stringify(output));
  const errors=(output.errors??[]).filter(e=>e.severity==='error').map(e=>({type:e.type,code:e.errorCode,message:e.message}));
  const r={id:c.id,sourceSha256:c.sha256,accepted:errors.length===0,expectedAccept:c.accept,errors};results.push(r);
  assert.equal(r.accepted,c.accept,c.id+' acceptance');assert.deepEqual(errors,c.errors,c.id+' error classification/message');
  if(c.accept){
   const ast=output.sources?.['case.sol']?.ast;assert(ast,c.id+' missing AST');
   const fs=walk(ast).filter(n=>n.nodeType==='FunctionDefinition'&&n.name==='f');assert.equal(fs.length,1);
   const statements=fs[0].body?.statements;assert.equal(statements?.length,1);assert.equal(statements[0].nodeType,c.astStatement);
   r.astStatement=statements[0].nodeType;
   if(c.declPath){assert.equal(statements[0].declarations.length,1);const path=statements[0].declarations[0].typeName?.pathNode?.name;assert.equal(path,c.declPath);r.declPath=path;}
  }
 }
 status='pass';
}catch(e){failure=e.stack??String(e);process.exitCode=1;}
finally{
 if(!owned){out=join(evidenceRoot,'contextual-solc-setup-failed-'+process.hrtime.bigint());mkdirSync(out);owned=true;}
 writeFileSync(join(out,'runner.mjs'),runner);if(manifest)writeFileSync(join(out,'manifest.json'),manifest);
 writeFileSync(join(out,'results.json'),JSON.stringify({status,failure,header,results},null,2));
 writeFileSync(join(out,'SHA256SUMS'),readdirSync(out).filter(n=>n!=='SHA256SUMS').sort().map(n=>sha(readFileSync(join(out,n)))+'  '+n+'\n').join(''));
 console.log(JSON.stringify({status,cases:results.length,evidence:out,failure}));
}
