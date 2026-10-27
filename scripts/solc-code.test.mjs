import {test} from 'node:test';
import assert from 'node:assert/strict';
import {compilerCode} from './solc-code.mjs';
const ast={nodeType:'SourceUnit',nodes:[{nodeType:'ContractDefinition',id:1,name:'A'},
 {nodeType:'MemberAccess',memberName:'creationCode',expression:{nodeType:'FunctionCall',expression:{name:'type'},arguments:[{referencedDeclaration:1}]}}]};
const sources={'unit.sol':{content:'contract A {}'}};
const settings={viaIR:true,evmVersion:'osaka',optimizer:{enabled:false,runs:200},libraries:{},remappings:[],outputSelection:{'*':{'':['ast']}}};
test('static code requests preserve exact settings and all bytes',()=>{
 let calls=0;
 const result=compilerCode(input=>{calls++;assert.deepEqual({...input.settings,outputSelection:settings.outputSelection},settings);
  assert.deepEqual(input.sources,sources);return {contracts:{'unit.sol':{A:{evm:{bytecode:{object:'00aB'},deployedBytecode:{object:'ff00'}}}}}};
 },sources,settings,ast,{compilerSha256:'pin',sourceSha256:'source'});
 assert.equal(calls,1);assert.deepEqual(result.contracts,[{id:1,name:'A',creationCode:'00ab',runtimeCode:'ff00'}]);
});
test('ordinary sources do not request code generation',()=>{
 assert.equal(compilerCode(()=>{throw Error('unexpected compile');},sources,settings,{nodeType:'SourceUnit',nodes:[]},{}),undefined);
});
test('missing artifacts, unresolved links and compiler errors fail closed',()=>{
 for (const output of [{}, {errors:[{severity:'error',message:'codegen failed'}]},
  {contracts:{'unit.sol':{A:{evm:{bytecode:{object:'__library__'},deployedBytecode:{object:'00'}}}}}}])
  assert.throws(()=>compilerCode(()=>output,sources,settings,ast,{}));
});
