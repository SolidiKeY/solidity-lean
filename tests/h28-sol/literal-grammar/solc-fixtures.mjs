import {readFileSync,writeFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import assert from 'node:assert/strict';
const [compiler,output,mode='check']=process.argv.slice(2);
const root=new URL('./',import.meta.url);
const manifest=JSON.parse(readFileSync(new URL('solc-cases.json',root),'utf8'));
const sha=x=>createHash('sha256').update(x).digest('hex');
assert.equal(sha(readFileSync(compiler)),manifest.compiler.sha256,'compiler bytes');
const solc=createRequire(import.meta.url)(compiler);
assert.equal(solc.cwrap('solidity_version','string',[])(),manifest.compiler.version);
const compile=solc.cwrap('solidity_compile','string',['string','number','number']);
const prefix='// SPDX-License-Identifier: UNLICENSED\npragma solidity 0.8.38; contract C { function f() external pure ';
const observations=[];const failures=[];
for(const row of manifest.cases)for(const viaIR of [false,true]){
 const before=prefix+(row.mode==='sol'?'returns(bytes memory) { return ':row.mode==='yul'?'{ assembly ("memory-safe") { let x := ':'{ assembly (');
 const after=row.mode==='sol'?'; }}':row.mode==='yul'?' } }}':') {} }}';
 const content=before+row.spelling+after;
 const input={language:'Solidity',sources:{'Case.sol':{content}},settings:{viaIR,evmVersion:'osaka',outputSelection:{'*':{'':['ast'],'*':['evm.bytecode.object']}}}};
 const out=JSON.parse(compile(JSON.stringify(input),0,0));
 const errors=(out.errors??[]).filter(e=>e.severity==='error').map(e=>({type:e.type,code:e.errorCode??null,message:e.message,location:e.sourceLocation??null}));
 const nodes=[];function walk(n){if(!n||typeof n!=='object')return;if(n.nodeType)nodes.push(n);for(const v of Object.values(n))if(v&&typeof v==='object')Array.isArray(v)?v.forEach(walk):walk(v);}walk(out.sources?.['Case.sol']?.ast);
 const literals=nodes.filter(n=>n.nodeType===(row.mode==='yul'?'YulLiteral':'Literal')).map(n=>({kind:n.kind,hex:n.hexValue,src:n.src}));
 const flags=nodes.filter(n=>n.nodeType==='InlineAssembly').map(n=>n.flags??[]);
 const code=out.contracts?.['Case.sol']?.C?.evm?.bytecode?.object;
 const actual={id:row.id,viaIR,sourceSha256:sha(content),inputSha256:sha(JSON.stringify(input)),accept:errors.length===0,errors,literals,flags,bytecodeSha256:typeof code==='string'?sha(code):null};
 observations.push(actual);
 try{
  assert.equal(actual.accept,row.compilerAccept,'compiler accept/refuse');
  if(row.checkedModelAccept!==row.compilerAccept)assert.ok(row.difference,'explicit difference record');
  if(row.compilerAccept){assert.equal(typeof code,'string','code generation ran');assert.ok(code.length>0);
   if(row.mode==='asm')assert.deepEqual(flags,[row.expectedFlags]);
   else {assert.equal(literals.length,1);assert.equal(literals[0].hex,row.expectedHex);assert.equal(literals[0].kind,row.expectedKind);
    assert.equal(literals[0].src,`${Buffer.byteLength(before)}:${Buffer.byteLength(row.spelling)}:0`,'exact consumed literal span');}
  }
 }catch(e){failures.push({id:row.id,viaIR,error:e.message,expected:row,actual});}
}
const differences=manifest.cases.filter(r=>r.checkedModelAccept!==r.compilerAccept).map(r=>({id:r.id,checkedModelAccept:r.checkedModelAccept,compilerAccept:r.compilerAccept,explanation:r.difference}));
const result={compiler:manifest.compiler,boundary:manifest.boundary,comparison:'exact observations; model/compiler conformance is not asserted',differences,observations,failures};
writeFileSync(output,JSON.stringify(result,null,2)+'\n');
if(failures.length){console.error(JSON.stringify(failures.map(f=>({id:f.id,viaIR:f.viaIR,error:f.error,accept:f.actual.accept,errors:f.actual.errors})),null,2));process.exitCode=1;}
else if(mode==='check'){
 const expected=JSON.parse(readFileSync(new URL('solc-observations.json',root),'utf8'));
 assert.deepEqual(result,expected,'fixed exact compiler observations');
 console.log(`PASS ${manifest.cases.length} cases x legacy/viaIR: values, Sol/Yul literal spans, error diagnostics, assembly flags and bytecode hashes; explicit differences retained, conformance not asserted`);
}else {assert.equal(mode,'record');console.log(`RECORDED ${observations.length} compiler observations; independent expectations passed`);}
