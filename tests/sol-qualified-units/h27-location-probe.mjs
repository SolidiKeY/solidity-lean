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
const compile=solc.cwrap('solidity_compile','string',['string','number','number']);
const scenarios=[
 ['public-memory-calldata','memory','calldata','public','public',true],
 ['internal-memory-calldata','memory','calldata','internal','internal',true],
 ['external-calldata-public-memory','calldata','memory','external','public',true],
 ['internal-storage-memory-override','storage','memory','internal','internal',true],
 ['internal-storage-memory-overload','storage','memory','internal','internal',false]
];
const rows=scenarios.map(([id,left,right,visLeft,visRight,override])=>{
 const source=`pragma solidity 0.8.38; contract B { function f(bytes ${left}) ${visLeft} virtual pure returns(uint) { return 1; }} contract D is B { function f(bytes ${right}) ${visRight} ${override?'override':''} pure returns(uint) { return 2; }}`;
 const input={language:'Solidity',sources:{'A.sol':{content:source}},settings:{evmVersion:'osaka',optimizer:{enabled:false},outputSelection:{'*':{'':['ast']}}}};
 const output=JSON.parse(compile(JSON.stringify(input),0,0));
 const errors=(output.errors||[]).filter(e=>e.severity==='error').map(e=>({code:e.errorCode,message:e.message}));
 return {id,source,accepted:errors.length===0,errors};
});
assert.equal(version,'0.8.38+commit.1835d247.Emscripten.clang');
const expected=[['public-memory-calldata',false,['7723']],['internal-memory-calldata',false,['7723']],
 ['external-calldata-public-memory',true,[]],['internal-storage-memory-override',false,['7792']],
 ['internal-storage-memory-overload',true,[]]];
assert.deepEqual(rows.map(r=>[r.id,r.accepted,r.errors.map(e=>e.code)]),expected);
const report={version,sha256:sha,script_sha256:createHash('sha256').update(readFileSync(new URL(import.meta.url))).digest('hex'),
 expected,compiler_fixtures_pass:true,rows};
writeFileSync(out+'/h27-location-probe.json',JSON.stringify(report,null,2)+'\n');
console.log(rows.map(r=>`${r.id}: ${r.accepted?'accept':'reject'} ${r.errors.map(e=>e.code).join(',')}`.trimEnd()).join('\n'));
