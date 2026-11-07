import {createRequire} from 'node:module';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
const file=process.env.SOLJSON_FILE??'/workspace/.setup/cache/v14-solc-0.8.38-6c74ffba/soljson.js';
const pin='6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390';
if(createHash('sha256').update(readFileSync(file)).digest('hex')!==pin)throw Error('compiler pin mismatch');
const compiler=createRequire(import.meta.url)(file);
const version=compiler.cwrap('solidity_version','string',[])();
if(version!=='0.8.38+commit.1835d247.Emscripten.clang')throw Error(version);
const compile=compiler.cwrap('solidity_compile','string',['string','number','number']);
const cases=[
 ['nestedBytes','function f(bytes[] calldata a,uint i,uint j) external pure returns(bytes1){return a[i][j];}',null],
 ['nestedUint','function f(uint[][] calldata a,uint i,uint j) external pure returns(uint){return a[i][j];}',null],
 ['stringElement','function f(string[] calldata a,uint i) external pure returns(string memory){return a[i];}',null],
 ['staticReferenceSlice','function f(uint[2][] calldata a,uint s,uint e,uint i,uint j) external pure returns(uint){return a[s:e][i][j];}',null],
 ['stringSlice','function f(string calldata a,uint s,uint e) external pure returns(string memory){return a[s:e];}',null],
 ['dynamicBaseSlice','function f(bytes[] calldata a) external pure returns(bytes memory){return a[0:1][0];}',['2148']],
 ['staticRootSlice','function f(uint[2] calldata a) external pure returns(uint){return a[0:1][0];}',['1227','4802']]
];
for(const [name,body,error] of cases){
 const source=`// SPDX-License-Identifier: UNLICENSED
pragma solidity 0.8.38;contract C{${body}}`;
 const output=JSON.parse(compile(JSON.stringify({language:'Solidity',sources:{'C.sol':{content:source}},settings:{evmVersion:'osaka',outputSelection:{'*':{'*':['abi','evm.bytecode.object']}}}}),0,0));
 const errors=(output.errors??[]).filter(x=>x.severity==='error').map(x=>({code:x.errorCode,message:x.message}));
 const code=output.contracts?.['C.sol']?.C?.evm?.bytecode?.object;
 if(JSON.stringify(errors.map(x=>x.code))!==JSON.stringify(error??[])||(!error&&!code))throw Error(JSON.stringify({name,errors}));
 console.log(JSON.stringify({name,version,pin,errors,bytecode:!!code,status:'pass',boundary:'compiler acceptance/refusal only; no EVM execution'}));
}
