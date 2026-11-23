// Injected compiler-metadata controls for editor hints, not semantic/proof admission.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),lang=require('../src/language-services.cjs');
function names(declaration){const text='items.';return lang.receiverMembers(text,lang.position(text,text.length),{nodes:[],declarations:new Map(),contractAt:()=>null,target:()=>declaration}).map(n=>n.name);}
const array=(length,storageLocation='default',stateVariable=false)=>({nodeType:'VariableDeclaration',name:'items',typeDescriptions:{typeString:'uint256[]'},typeName:{nodeType:'ArrayTypeName',length},storageLocation,stateVariable});
test('explicit storage ownership enables mutation hints only on dynamic outer arrays',()=>{
 assert.deepEqual(names(array(null,'default',true)),['length','push','pop']);const omitted=array(null,'default',true);delete omitted.typeName.length;assert.deepEqual(names(omitted),['length','push','pop']);assert.deepEqual(names(array(null,'storage')),['length','push','pop']);
 for(const location of ['memory','calldata','default'])assert.deepEqual(names(array(null,location)),['length']);
 for(const length of [{nodeType:'Literal',value:'2'},undefined])assert.deepEqual(names(array(length,'storage')),['length']);
});
test('legacy type-only hints inspect the outer dimension and preserve byte distinctions',()=>{
 const legacy=type=>({typeDescriptions:{typeString:type}});
 assert.deepEqual(names(legacy('uint256[][2] storage ref')),['length']);assert.deepEqual(names(legacy('uint256[2][] storage ref')),['length','push','pop']);
 assert.deepEqual(names(legacy('bytes storage ref')),['length','push','pop']);assert.deepEqual(names(legacy('bytes memory')),['length']);
});

test('contradictory ownership or fixed outer text cannot gain mutating hints',()=>{
 const memory=array(null,'memory',true);memory.typeDescriptions.typeString='uint256[] storage ref';assert.deepEqual(names(memory),['length']);
 const fixed=array(null,'storage');fixed.typeDescriptions.typeString='uint256[][2]';assert.deepEqual(names(fixed),['length']);
 const unknown=array(null,'unknown',true);assert.deepEqual(names(unknown),['length']);
});

test('explicit storage owner cannot override an explicit nonstorage type suffix',()=>{
 for(const location of ['storage','default'])for(const suffix of ['memory','calldata']){const value=array(null,location,location==='default');value.typeDescriptions.typeString='uint256[] '+suffix;assert.deepEqual(names(value),['length'],location+':'+suffix);}
});

test('legacy nested parameter locations do not hide outer array hints',()=>{
 const value={typeDescriptions:{typeString:'function (uint256[] memory) external returns (uint256)[] storage ref'}};assert.deepEqual(names(value),['length','push','pop']);
 const fixed={typeDescriptions:{typeString:'function (uint256[] memory) external returns (uint256)[][2] storage ref'}};assert.deepEqual(names(fixed),['length']);
});
