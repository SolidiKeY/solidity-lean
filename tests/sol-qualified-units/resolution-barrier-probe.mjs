import assert from 'node:assert/strict';
import {createRequire} from 'node:module';
import {readFileSync,writeFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
const pins=JSON.parse(readFileSync(new URL('./compiler-artifacts.json',import.meta.url),'utf8'));
const path=process.env.SOL_QN_SOLJSON || '/tools/soljson-v0.8.38+commit.1835d247.js';
const out=process.env.SOL_QN_EVIDENCE || 'tests/sol-qualified-units/evidence';
const sha=createHash('sha256').update(readFileSync(path)).digest('hex');
if(!pins.artifacts.some(a=>a.sha256===sha))throw Error('pin');
const solc=createRequire(import.meta.url)(path);
const version=solc.cwrap('solidity_version','string',[])();
assert.equal(version,'0.8.38+commit.1835d247.Emscripten.clang');
const compile=solc.cwrap('solidity_compile','string',['string','number','number']);
const sources=[
 ['overload-variable-barrier','contract A { function f(uint) internal virtual pure returns(uint) { return 1; }} contract B is A { bool internal f; } contract D is B { function f(bool) internal pure returns(uint) { return 2; }}'],
 ['getter-override','abstract contract A { function f() external view virtual returns(bool); } contract B is A { bool public override f; }']
];
const rows=sources.map(([id,body])=>{
 const source='pragma solidity 0.8.38; '+body;
 const input={language:'Solidity',sources:{'A.sol':{content:source}},settings:{evmVersion:'osaka',optimizer:{enabled:false},outputSelection:{'*':{'':['ast']}}}};
 const output=JSON.parse(compile(JSON.stringify(input),0,0));
 const errors=(output.errors||[]).filter(e=>e.severity==='error').map(e=>({code:e.errorCode,message:e.message}));
 return {id,source,source_sha256:createHash('sha256').update(source).digest('hex'),accepted:errors.length===0,errors};
});
const expected=[['overload-variable-barrier',false,['9097','9097']],['getter-override',true,[]]];
assert.deepEqual(rows.map(r=>[r.id,r.accepted,r.errors.map(e=>e.code)]),expected);
writeFileSync(out+'/resolution-barrier-probe.json',JSON.stringify({version,sha256:sha,
 script_sha256:createHash('sha256').update(readFileSync(new URL(import.meta.url))).digest('hex'),expected,compiler_fixtures_pass:true,rows},null,2)+'\n');
console.log(rows.map(r=>r.id+': '+r.accepted+' '+r.errors.map(e=>e.code).join(',')).map(s=>s.trimEnd()).join('\n'));
