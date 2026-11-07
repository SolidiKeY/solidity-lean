import assert from 'node:assert/strict';
import {readFileSync,writeFileSync,mkdirSync,readdirSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {resolve,join,dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
import {execFileSync} from 'node:child_process';
const fixtureDir=join(dirname(fileURLToPath(import.meta.url)),'fixtures');
const evidenceRoot='/workspace/h28-statement-grammar-evidence';
const compilerPath=resolve(process.argv[2]??'');
const requestedOut=resolve(process.argv[3]??'');
let out=requestedOut,owned=false,status='fail',failure,manifestBytes;
const sha=b=>createHash('sha256').update(b).digest('hex');
const runnerBytes=readFileSync(fileURLToPath(import.meta.url));
const results=[];
const header={node:process.version,runnerSha256:sha(runnerBytes),requestedOut};
function walk(x){if(!x||typeof x!=='object')return [];return [x,...Object.values(x).flatMap(v=>Array.isArray(v)?v.flatMap(walk):walk(v))];}
try{
 assert(process.argv.length===4,'usage: node solc-fixtures.mjs COMPILER OUTPUT');
 assert(out.startsWith(evidenceRoot+'/'),'output must be a fresh owned evidence directory');
 mkdirSync(out);owned=true;
 manifestBytes=readFileSync(join(fixtureDir,'manifest.json'));
 const spec=JSON.parse(manifestBytes);
 assert.equal(spec.version,1);assert.equal(spec.cases.length,45);assert.equal(spec.requiredCtors.length,40);
 assert.equal(new Set(spec.cases.map(c=>c.id)).size,45);assert.equal(new Set(spec.requiredCtors).size,40);
 assert.deepEqual(readdirSync(fixtureDir).sort(),['manifest.json',...spec.cases.map(c=>c.file)].sort());
 header.manifestSha256=sha(manifestBytes);
 assert.equal(sha(readFileSync(compilerPath)),spec.compilerSha256,'wrong compiler bytes');
 assert.equal(readFileSync('/sys/fs/cgroup/memory.max','utf8').trim(),'12884901888');
 assert.equal(readFileSync('/sys/fs/cgroup/memory.swap.max','utf8').trim(),'0');
 const solc=createRequire(import.meta.url)(compilerPath);
 const version=solc.cwrap('solidity_version','string',[])();assert.equal(version,spec.compilerVersion);
 const compile=solc.cwrap('solidity_compile','string',['string','number','number']);
 Object.assign(header,{compilerVersion:version,compilerSha256:spec.compilerSha256,head:execFileSync('git',['rev-parse','HEAD'],{encoding:'utf8'}).trim(),boundary:spec.boundary});
 for(const c of spec.cases){
  assert(/^[pn][0-9]{2}-[a-z0-9-]+$/.test(c.id));assert.equal(c.file,c.id+'.sol');
  const source=readFileSync(join(fixtureDir,c.file),'utf8');assert.equal(sha(source),c.sha256,c.id+' source drift');
  const input={language:'Solidity',sources:{'case.sol':{content:source}},settings:{outputSelection:{'*':{'':['ast']}}}};
  const output=JSON.parse(compile(JSON.stringify(input),0,0));
  writeFileSync(join(out,c.id+'.input.json'),JSON.stringify(input));
  writeFileSync(join(out,c.id+'.output.json'),JSON.stringify(output));
  const errors=(output.errors??[]).filter(e=>e.severity==='error');
  const result={id:c.id,kind:c.kind,sourceSha256:c.sha256,expectedAccept:c.solcAccept,accepted:errors.length===0,errors:errors.map(e=>({type:e.type,code:e.errorCode,message:e.message})),warnings:(output.errors??[]).filter(e=>e.severity==='warning').map(e=>({code:e.errorCode,message:e.message}))};
  results.push(result);
  assert.equal(result.accepted,c.solcAccept,c.id+' compiler acceptance mismatch');
  if(c.solcErrors)assert.deepEqual(errors.map(e=>({type:e.type,code:e.errorCode})),c.solcErrors,c.id+' error classification');
  if(result.accepted){
   const ast=output.sources?.['case.sol']?.ast;assert(ast,c.id+' missing AST');
   const functions=walk(ast).filter(n=>n.nodeType==='FunctionDefinition'&&n.name==='f');assert.equal(functions.length,1,c.id+' target function');
   const body=functions[0].body;assert(body,c.id+' missing body');
   const nodes=walk(body),types=nodes.map(n=>n.nodeType);
   for(const required of c.astRequired)assert(types.includes(required),c.id+' missing '+required);
   result.bodyNodeTypes=[...new Set(types.filter(Boolean))].sort();
   if(c.id==='p00-block')assert.equal(body.statements[0].nodeType,'Block');
   if(c.id==='p03-tuple-holes'){
    const ds=body.statements[0].declarations;assert.equal(ds.length,5);assert.equal(ds[0],null);assert.equal(ds[2],null);assert.equal(ds[4],null);assert.equal(ds[1].name,'x');assert.equal(ds[3].name,'y');
   }
   if(c.id==='p07-nearest-else'){
    const outer=body.statements[0];assert.equal(outer.nodeType,'IfStatement');assert(outer.falseBody==null);assert.equal(outer.trueBody.nodeType,'IfStatement');assert.equal(outer.trueBody.falseBody.nodeType,'Return');
    result.nearestElse='inner';
   }
   if(c.id==='p20-try-signatures')assert.deepEqual(body.statements[0].clauses.slice(1).map(c=>c.errorName),['Error','Panic','']);
   if(c.id==='p27-yul-constructors')for(const t of ['YulBlock','YulVariableDeclaration','YulAssignment','YulExpressionStatement','YulIf','YulForLoop','YulSwitch','YulCase','YulLeave','YulBreak','YulContinue','YulFunctionDefinition','YulIdentifier','YulFunctionCall','YulLiteral'])assert(types.includes(t),'missing '+t);
  }
 }
 status='pass';
}catch(e){failure=String(e);process.exitCode=1;}
finally{
 if(!owned){out=join(evidenceRoot,'solc-setup-failed-'+process.hrtime.bigint());mkdirSync(out);owned=true;}
 writeFileSync(join(out,'runner.mjs'),runnerBytes);
 if(manifestBytes)writeFileSync(join(out,'manifest-input.json'),manifestBytes);
 writeFileSync(join(out,'header.json'),JSON.stringify(header,null,2));
 writeFileSync(join(out,'results.json'),JSON.stringify({header,status,failure,results},null,2));
 const files=readdirSync(out).sort();writeFileSync(join(out,'SHA256SUMS'),files.map(f=>sha(readFileSync(join(out,f)))+'  '+f+'\n').join(''));
 console.log(JSON.stringify({status,cases:results.length,out,failure}));
}
