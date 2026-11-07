// Fresh compiler -> published reader -> real native compiled verifier controls.
import {compileFixture} from '../../../scripts/solc-ast.mjs';
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {dirname,join,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {spawnSync} from 'node:child_process';
import assert from 'node:assert/strict';
const root=dirname(fileURLToPath(import.meta.url)), repo=resolve(root,'../../..');
const [binaryArg,outArg]=process.argv.slice(2);assert.ok(binaryArg&&outArg,'native-source-controls.mjs BINARY OUTPUT');
const buildRepo=resolve(process.env.MEMORY_NATIVE_REPOSITORY??repo);
const binary=resolve(binaryArg),out=resolve(outArg);mkdirSync(out,{recursive:true});
const sha=b=>createHash('sha256').update(b).digest('hex');
const manifest=JSON.parse(readFileSync(join(dirname(binary),'build.json')));
assert.equal(sha(readFileSync(binary)),manifest.executable);
assert.equal(manifest.leanCommit,'797c613eb9b6d4ec95db23e3e00af9ac6657f24b');
for(const module of ['Solidity.Tools.DirectRuntime','Solidity.Frontend.ExecutableAst.Shared.Compose','Solidity.Frontend.ExecutableAst.Shared.Intrinsic','Solidity.Frontend.ExecutableAst.Memory.Reader'])assert.ok(manifest.sourceFiles.some(r=>r.module===module));
for(const base of [repo,buildRepo])assert.equal(sha(readFileSync(join(base,'web/browser/direct-bridge.c'))),manifest.bridgeSha256);
for(const row of manifest.sourceFiles){
 assert.equal(sha(readFileSync(join(repo,row.module.replaceAll('.','/')+'.lean'))),row.sourceSha256);
 assert.equal(sha(readFileSync(join(buildRepo,'.lake/build/ir',row.module.replaceAll('.','/')+'.c'))),row.cSha256);
 assert.equal(sha(readFileSync(join(buildRepo,row.module.replaceAll('.','/')+'.lean'))),row.sourceSha256);
 const trace=JSON.parse(readFileSync(join(buildRepo,'.lake/build/lib/lean',row.module.replaceAll('.','/')+'.trace')));
 assert.equal(sha(readFileSync(`/workspace/.setup/cache/lake/artifacts/${trace.outputs.c}.c`)),row.cSha256,'generated C must match current Lake cache output');
}
const normalize=x=>Array.isArray(x)?x.map(normalize):x&&typeof x==='object'?Object.fromEntries(Object.entries(x).map(([k,v])=>[k,k==='referencedDeclaration'&&Number.isInteger(v)&&v>=2**31?v-2**32:normalize(v)])):x;
const rows=JSON.parse(readFileSync(join(root,'manifest.json'))).cases,records=[],requests=[];
const env={...process.env};for(const name of ['LEAN_PATH','LEAN_SRC_PATH','LEAN_SYSROOT'])delete env[name];
const empty=join(out,'empty-cwd');mkdirSync(empty,{recursive:true});
for(const [index,row] of rows.entries()){
 const stem=`${row.id}.${row.modality}.${row.viaIR?'ir':'legacy'}`,source=join(root,row.source);
 const args=['--solkey','/workspace/.setup/solkey','--soljson','/workspace/.setup/soljson','--source',source,'--out',join(out,stem+'.trimmed.json'),'--no-wrapper'];
 if(row.viaIR)args.push('--via-ir');
 const compiled=compileFixture({args,quiet:true});
 assert.equal(compiled.sourceHash,sha(readFileSync(source)));
 assert.equal(compiled.sourceHash,row.sourceSha256);
 assert.equal(compiled.compiler.sha256,'c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8');
 const contract=normalize(compiled.rawAst).nodes.find(n=>n.nodeType==='ContractDefinition');assert.ok(contract);
 const fn=contract.nodes.find(n=>n.nodeType==='FunctionDefinition'&&n.name==='identity');assert.ok(fn);
 const request={contract,function:'identity',sourceId:fn.id},payload=JSON.stringify(request)+'\n';requests.push(payload.trimEnd());
 writeFileSync(join(out,stem+'.request.json'),payload);
 const trace=join(out,stem+'.strace');
 const run=spawnSync('/usr/bin/strace',['-f','-e','trace=file,process,network','-o',trace,binary],{input:payload,encoding:'utf8',cwd:empty,env,timeout:30000,maxBuffer:8*1024*1024});
 writeFileSync(join(out,stem+'.stdout'),run.stdout??'');writeFileSync(join(out,stem+'.stderr'),run.stderr??'');
 let result=null,protocolError=null;
 try{assert.equal(run.status,0);const lines=run.stdout.trim().split('\n').map(l=>JSON.parse(l));assert.deepEqual(lines[0],{ready:true});assert.equal(lines.length,2);result=lines[1];if(result.results){assert.equal(result.results.length,1);assert.equal(result.results[0].tag,row.modality);assert.equal(result.results[0].sourceId,fn.id);}}
 catch(error){protocolError=String(error);}
 const text=readFileSync(trace,'utf8');
 assert.ok(!/\.(?:olean|ilean|lean)(?:["/ ]|$)/.test(text),'serialized/source environment access');
 const execs=[...text.matchAll(/execve\("([^"]+)"/g)].map(x=>x[1]);assert.deepEqual(execs,[binary]);assert.ok(!/\bexecveat\(/.test(text),'execveat observed');
 assert.ok(!/\b(?:socket|socketpair|connect|accept|accept4|bind|listen|sendto|recvfrom|sendmsg|recvmsg|sendmmsg|recvmmsg|shutdown|getsockname|getpeername|setsockopt|getsockopt)\(/.test(text),'network observed');
 const status=protocolError?'protocol-error':result?.results?.[0]?.status??(result?.gap?'gap':'protocol-error');
 records.push({id:row.id,modality:row.modality,viaIR:row.viaIR,source:row.source,sourceSha256:compiled.sourceHash,compiler:compiled.compiler,rawAstSha256:sha(JSON.stringify(compiled.rawAst)),requestSha256:sha(payload),requiredProven:row.requiredProven,status,result,protocolError,exit:run.status,signal:run.signal,traceSha256:sha(text),observedSerializedEnvironmentAccess:false,observedExternalExecs:execs});
 console.log(`${index+1}/${rows.length} ${stem}: ${status}`);
}
writeFileSync(join(out,'requests.jsonl'),requests.join('\n')+'\n');
assert.equal(records.length,84);assert.equal(new Set(records.map(r=>`${r.id}.${r.modality}.${r.viaIR}`)).size,84);
assert.equal(records.filter(r=>r.id==='identity'&&r.modality==='diamond').length,2);
const missingPositive=records.filter(r=>r.requiredProven&&r.status!=='proved');
const unsoundPositive=records.filter(r=>!r.requiredProven&&r.status==='proved');
const unresolved=records.filter(r=>!['proved','refuted'].includes(r.status));
const summary={binary,buildRepository:buildRepo,binarySha256:manifest.executable,sourceFresh:true,backend:'native-generated-c',cases:records.length,missingPositive:missingPositive.map(r=>[r.id,r.modality,r.viaIR,r.status]),unsoundPositive:unsoundPositive.map(r=>[r.id,r.modality,r.viaIR]),unresolved:unresolved.length,protocolErrors:records.filter(r=>r.protocolError).length,identityDiamondProved:records.filter(r=>r.id==='identity'&&r.modality==='diamond').every(r=>r.status==='proved'&&!r.protocolError&&r.exit===0&&r.signal===null),allDecisive:missingPositive.length===0&&unsoundPositive.length===0&&unresolved.length===0&&records.every(r=>!r.protocolError&&r.exit===0&&r.signal===null),records,boundary:'External fresh source-to-native controls; no browser result, compiler equivalence or exhaustive linked-function closure proof. Trace observations apply only to these runs.'};
writeFileSync(join(out,'results.json'),JSON.stringify(summary,null,2)+'\n');
writeFileSync(join(out,'browser-handoff.json'),JSON.stringify({requests:join(out,'requests.jsonl'),requestsSha256:sha(readFileSync(join(out,'requests.jsonl'))),compilerPin:'c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8',cases:records.map(({id,modality,viaIR,sourceSha256,requiredProven})=>({id,modality,viaIR,sourceSha256,requiredProven})),required:'Fresh browser direct.js/direct.wasm from this integrated head, real browser worker check; Node-only WASM does not count as browser acceptance.'},null,2)+'\n');
console.log(JSON.stringify({cases:summary.cases,identityDiamondProved:summary.identityDiamondProved,missingPositive:summary.missingPositive,unsoundPositive:summary.unsoundPositive,unresolved:summary.unresolved,allDecisive:summary.allDecisive}));
if(!summary.allDecisive)process.exitCode=1;
