import {test} from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync,mkdtempSync,writeFileSync,existsSync,rmSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {tmpdir} from 'node:os';
import {createRequire} from 'node:module';
import {execFileSync} from 'node:child_process';
import {createHash} from 'node:crypto';
import {compilationUnitFixture,normaliseUnit,COMPILERS,hasUnitSpecifications} from './solc-unit.mjs';

const input=JSON.parse(readFileSync('tests/solc/source-units/SourceUnits.input.json','utf8'));
const fixture=JSON.parse(readFileSync('tests/solc/source-units/SourceUnits.ast.json','utf8'));
const pin=COMPILERS[1];
const output={sources:Object.fromEntries(fixture.sourceUnits.map(u=>[u.name,{id:u.id,ast:u.ast}]))};
const make=(o=output,sources=input.sources,settings=input.settings)=>compilationUnitFixture({
 output:o,sources,mainSource:'app/Main.sol',settings,pin:{sha256:pin.sha256,file:pin.file,version:pin.version}});
const clone=x=>structuredClone(x);

test('compilation provenance preserves every original source and compiler identity',()=>{
 const result=make();
 assert.equal(result.header.provenanceVersion,2);
 assert.equal(result.ast,undefined);
 assert.equal(result.header.sourceSha256,undefined);
 assert.deepEqual(result.header.settings,input.settings);
 for(const u of result.sourceUnits){
  assert.equal(u.sourceSha256,createHash('sha256').update(input.sources[u.name].content).digest('hex'));
  assert.equal(u.ast.id,output.sources[u.name].ast.id);
  assert.equal(u.id,output.sources[u.name].id);
  assert.deepEqual(u.ast,output.sources[u.name].ast);
 }
 assert.equal(result.sourceUnits.length,3);
});

test('missing, duplicate, foreign and compiler-invalid source metadata fail closed',()=>{
 const missing=clone(output);delete missing.sources['lib/Math.sol'];
 assert.throws(()=>make(missing),/source set/);
 const duplicate=clone(output);duplicate.sources['lib/Errors.sol'].id=duplicate.sources['lib/Math.sol'].id;
 assert.throws(()=>make(duplicate),/duplicate compiler source/);
 const foreign=clone(output);foreign.sources['lib/Math.sol'].ast.absolutePath='other';
 assert.throws(()=>make(foreign),/foreign/);
 const identity=clone(output);delete identity.sources['lib/Math.sol'].ast.id;
 assert.throws(()=>make(identity),/identity/);
 const errors={...output,errors:[{severity:'error'}]};
 assert.throws(()=>make(errors),/analysis failed/);
 const urls=clone(input.sources);urls['lib/Math.sol']={urls:['lib/Math.sol']};
 assert.throws(()=>make(output,urls),/explicit UTF-8/);
});

test('resolved import paths and source-unit identities must both exist',()=>{
 for(const bad of [
   {absolutePath:'missing',sourceUnit:undefined},
   {absolutePath:'missing',sourceUnit:123},
   {absolutePath:'lib/Math.sol',sourceUnit:undefined},
   {absolutePath:'lib/Math.sol',sourceUnit:123}]){
  const o=clone(output);
  const n=o.sources['app/Main.sol'].ast.nodes.find(n=>n.nodeType==='ImportDirective');
  Object.assign(n,bad);
  assert.throws(()=>make(o),/resolved import target/);
 }
});

test('locations retain byte offsets and the source they belong to',()=>{
 const o=clone(output);
 o.sources['lib/Math.sol'].ast.nodes[1].src='0:1:999';
 assert.throws(()=>make(o),/foreign or malformed source location/);
 assert.throws(()=>normaliseUnit({nodeType:'Identifier',src:'0:999:0'},'a',0),/location/);
 assert.equal(normaliseUnit({nodeType:'Identifier',src:'5:1:0'},'//é\nx',0).line,2);
});

test('an unknown compiler is rejected before its JavaScript is evaluated',()=>{
 const dir=mkdtempSync(join(tmpdir(),'source-unit-compiler-'));
 try{
  const marker=join(dir,'executed');
  const compiler=join(dir,'compiler.cjs');
  writeFileSync(compiler,'require("node:fs").writeFileSync('+JSON.stringify(marker)+',"executed");');
  assert.throws(()=>execFileSync('node',['scripts/solc-unit.mjs','--input','unused',
   '--compiler',compiler,'--main-source','main','--out',join(dir,'out')],{stdio:'pipe'}),/Command failed/);
  assert.equal(existsSync(marker),false);
 }finally{rmSync(dir,{recursive:true,force:true});}
});

test('pinned compiler resolves empty targets and equals signs inside targets',()=>{
 const compiler=process.env.SOURCE_UNITS_SOLJSON ??
   '.lake/source-units/soljson-v0.8.38+commit.1835d247.js';
 assert.equal(createHash('sha256').update(readFileSync(compiler)).digest('hex'),pin.sha256);
 const solc=createRequire(import.meta.url)(resolve(compiler));
 const compile=solc.cwrap('solidity_compile','string',['string','number','number']);
 for(const [remap,target] of [['@p/=deps=v1/','deps=v1/X.sol'],['@p/=','X.sol']]){
  const sources={'Main.sol':{content:'pragma solidity ^0.8.0; import "@p/X.sol"; contract Main is X {}'},
   [target]:{content:'pragma solidity ^0.8.0; contract X {}'}};
  const settings={...input.settings,remappings:[remap]};
  const out=JSON.parse(compile(JSON.stringify({language:'Solidity',sources,settings}),0,0));
  const result=compilationUnitFixture({output:out,sources,mainSource:'Main.sol',settings,pin});
  assert.equal(result.header.settings.remappings[0],remap);
  assert.equal(result.sourceUnits[0].ast.nodes.find(n=>n.nodeType==='ImportDirective').absolutePath,target);
 }
 const dir=mkdtempSync(join(tmpdir(),'source-unit-utf8-'));
 try{
  const file=join(dir,'bad.json');writeFileSync(file,Buffer.from([0xff]));
  assert.throws(()=>execFileSync('node',['scripts/solc-unit.mjs','--input',file,
   '--compiler',compiler,'--main-source','Main.sol','--out',join(dir,'out')],{stdio:'pipe'}),/Command failed/);
  assert.equal(existsSync(join(dir,'out')),false);
 }finally{rmSync(dir,{recursive:true,force:true});}
});


test('original loop NatSpec is refused even though solc drops it, while string markers remain data',()=>{
 const compiler=process.env.SOURCE_UNITS_SOLJSON ??
   '.lake/source-units/soljson-v0.8.38+commit.1835d247.js';
 const solc=createRequire(import.meta.url)(resolve(compiler));
 const compile=solc.cwrap('solidity_compile','string',['string','number','number']);
 const sources={'Main.sol':{content:'pragma solidity ^0.8.0; import "Lib.sol"; contract Main { function run() public pure returns(uint) { return f(); } }'},
  'Lib.sol':{content:'pragma solidity ^0.8.0; function f() pure returns(uint) { uint i;\n/// @custom:key invariant i <= 1;\nwhile(i<1) { i++; } return i; }'}};
 const settings={...input.settings,remappings:[]};
 const out=JSON.parse(compile(JSON.stringify({language:'Solidity',sources,settings}),0,0));
 assert.deepEqual((out.errors??[]).filter(e=>e.severity==='error'),[]);
 assert.throws(()=>compilationUnitFixture({output:out,sources,mainSource:'Main.sol',settings,pin}),
  /solidity.compilationUnitSpecifications/);
 assert.equal(hasUnitSpecifications('string memory s = "@custom:key"; // ordinary @custom:key\n'),false);
 assert.equal(hasUnitSpecifications('/** @custom:key ensures false; */'),true);
 assert.equal(hasUnitSpecifications('string memory s = "/// @custom:key";'),false);
});

test('retry provenance cannot mix different compilation-unit producers',async()=>{
 const {compatible}=await import('./merge-solidity-upstream-retries.mjs');
 assert.throws(()=>compatible({compilationUnitAdapterSha256:'a'},{compilationUnitAdapterSha256:'b'}),
  /compilationUnitAdapterSha256/);
 assert.throws(()=>compatible({}, {compilationUnitAdapterSha256:'b'}),/compilationUnitAdapterSha256/);
});
