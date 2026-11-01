// Finite compiler classifications; no EVM/source adequacy theorem.
import assert from 'node:assert/strict';
import {writeFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {compiler} from '../../scripts/evm-reference/generated.mjs';
const [pin,dest]=process.argv.slice(2);if(!pin||!dest)throw Error('pin and output required');
const compile=compiler(pin),rows=[];
const cases=[
 {name:'default',clause:'',fields:'uint256 x;',ok:true,slots:['0']},
 {name:'literal42',clause:'layout at 42',fields:'uint256 x;',ok:true,slots:['42']},
 {name:'decimalIntegral',clause:'layout at 42.0',fields:'uint256 x;',ok:true,slots:['42']},
 {name:'exponentIntegral',clause:'layout at 0.42e2',fields:'uint256 x;',ok:true,slots:['42']},
 {name:'arithmeticCompilerOnly',clause:'layout at 40+2',fields:'uint256 x;',ok:true,slots:['42'],boundary:'existing Source literal profile excludes this expression; compiler success is preserved'},
 {name:'fraction',clause:'layout at 0.5',fields:'uint256 x;',ok:false},
 {name:'negative',clause:'layout at -1',fields:'uint256 x;',ok:false},
 {name:'numericOverflow',clause:'layout at '+(1n<<256n),fields:'uint256 x;',ok:false},
 {name:'spanOverflow',clause:'layout at '+((1n<<256n)-1n),fields:'uint256 x;uint256 y;',ok:false}
];
for(const viaIR of [false,true])for(const x of cases){
 const source='// SPDX-License-Identifier: UNLICENSED\npragma solidity 0.8.38; contract Origin '+x.clause+' { '+x.fields+' }';
 const input={language:'Solidity',sources:{'Origin.sol':{content:source}},settings:{viaIR,evmVersion:'osaka',optimizer:{enabled:false,runs:200},outputSelection:{'*':{'*':['storageLayout','transientStorageLayout']}}}};
 const out=compile(input),errors=(out.errors??[]).filter(e=>e.severity==='error'),a=out.contracts?.['Origin.sol']?.Origin;
 const row={viaIR,name:x.name,source,inputSha256:createHash('sha256').update(JSON.stringify(input)).digest('hex'),expected:x,errors,storageLayout:a?.storageLayout??null,transientStorageLayout:a?.transientStorageLayout??null};rows.push(row);writeFileSync(dest,JSON.stringify(rows,null,2)+'\n');
 assert.equal(errors.length===0,x.ok,x.name);if(x.ok)assert.deepEqual(a.storageLayout.storage.map(v=>v.slot),x.slots);else assert.ok(errors.every(e=>e.formattedMessage.length>0));
}
console.log(JSON.stringify({status:'pass',pipelines:2,classifications:rows.length,arithmeticBoundary:'compiler success, existing source-profile exclusion unchanged'}));
