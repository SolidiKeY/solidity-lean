import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {libraryTryContext,libraryTryVectorsFixture,linkLibraryObject} from './library-try-adapter.mjs';
const original=JSON.parse(readFileSync(new URL('../tests/solc/LibraryTry.ast.json',import.meta.url))).ast;
const parts=a=>{const L=a.nodes.find(n=>n.name==='L'),C=a.nodes.find(n=>n.name==='C');return {L,C,S:L.nodes[0],integer:L.nodes[1],stru:L.nodes[2],root:C.nodes[1],f:C.nodes[2],g:C.nodes[3]};};
test('whole original linked source obtains exact declaration/runtime context',()=>{
 const {C,L,root,S}=parts(original),c=libraryTryContext(original,C);assert.equal(c.libraryName,L.name);assert.equal(c.storageRoot,root.id);assert.equal(c.storageMember,S.members[0].id);
 assert.equal(c.selfAddress,'816484669177263916909924781827997526878516243634');
});
const mutations=[
 ['wrong library role',p=>p.L.contractKind='contract'],
 ['wrong qualifier identity',p=>p.f.body.statements[1].externalCall.expression.expression.referencedDeclaration=p.C.id],
 ['wrong function identity',p=>p.f.body.statements[1].externalCall.expression.referencedDeclaration=p.stru.id],
 ['wrong member spelling',p=>p.f.body.statements[1].externalCall.expression.memberName='stru'],
 ['wrong scalar argument/order',p=>p.f.body.statements[1].externalCall.arguments.reverse()],
 ['wrong Boolean declaration',p=>p.f.body.statements[1].externalCall.arguments[1].referencedDeclaration=999],
 ['wrong Boolean spelling',p=>p.f.body.statements[1].externalCall.arguments[1].name='wrong'],
 ['wrong bound result type',p=>p.f.body.statements[1].clauses[0].parameters.parameters[0].typeDescriptions.typeString='bool'],
 ['wrong library result type',p=>p.integer.returnParameters.parameters[0].typeDescriptions.typeString='bool'],
 ['wrong return receiver',p=>p.f.body.statements[1].clauses[0].block.statements[0].expression.components[0].referencedDeclaration=999],
 ['wrong caught payload',p=>p.f.body.statements[1].clauses[1].block.statements[0].expression.components[1].referencedDeclaration=999],
 ['wrong storage receiver',p=>p.g.body.statements[1].externalCall.expression.expression.referencedDeclaration=999],
 ['wrong storage formal',p=>p.stru.parameters.parameters[0].typeName.referencedDeclaration=999],
 ['wrong storage field',p=>p.stru.body.statements[0].trueBody.statements[0].expression.referencedDeclaration=999],
 ['wrong storage field spelling',p=>p.stru.body.statements[0].trueBody.statements[0].expression.memberName='wrong'],
 ['wrong field type',p=>p.S.members[0].typeDescriptions.typeString='bool'],
 ['wrong caller prefix root',p=>p.g.body.statements[0].expression.leftHandSide.expression.referencedDeclaration=999],
 ['wrong using library',p=>p.C.nodes[0].libraryName.referencedDeclaration=p.C.id],
 ['denominated prefix',p=>p.f.body.statements[0].initialValue.subdenomination='ether'],
 ['unsupported caller tail',p=>p.f.body.statements.push({nodeType:'ExpressionStatement'})],
 ['unsupported library effect',p=>p.integer.body.statements.push({nodeType:'ExpressionStatement'})],
 ['unknown catalog contract',p=>p.ast.nodes.push({...p.C,id:999,name:'Other'})],
];
for(const [name,mutate]of mutations)test('refuses '+name,()=>{const a=structuredClone(original),p=parts(a);mutate({...p,ast:a});assert.equal(libraryTryContext(a,p.C),null);});
test('consumes only one exact validated library directive',()=>{
 const c=libraryTryContext(original,parts(original).C),f={expectations:['library: L','f(bool): true -> 8, 0x40, 0']};
 assert.deepEqual(libraryTryVectorsFixture(f,c).expectations,[f.expectations[1]]);
 for(const expectations of [[],['library: Wrong'],['library: L','library: L']])assert.throws(()=>libraryTryVectorsFixture({expectations},c));
 assert.deepEqual(libraryTryVectorsFixture({expectations:['library: L','unknown observation']},c).expectations,['unknown observation']);
});
const placeholder='__$'+'a'.repeat(34)+'$__',object='6000'+placeholder+'00',refs={'source.sol':{L:[{start:2,length:20}]}},address='0x'+'12'.repeat(20);
test('links only exact compiler identity/placeholder range',()=>{const x=linkLibraryObject(object,refs,'source.sol','L',address);assert.equal(x.object,'6000'+'12'.repeat(20)+'00');assert.deepEqual(x.positions,[2]);});
for(const [name,mutate]of [
 ['wrong FQN',()=>[object,refs,'other.sol','L',address]],
 ['wrong library',()=>[object,refs,'source.sol','Other',address]],
 ['zero address',()=>[object,refs,'source.sol','L','0x'+'00'.repeat(20)]],
 ['missing links',()=>[object,{},'source.sol','L',address]],
 ['non20byte range',()=>[object,{'source.sol':{L:[{start:2,length:19}]}},'source.sol','L',address]],
 ['out of bounds',()=>[object,{'source.sol':{L:[{start:200,length:20}]}},'source.sol','L',address]],
 ['overlapping ranges',()=>[object,{'source.sol':{L:[{start:2,length:20},{start:2,length:20}]}},'source.sol','L',address]],
 ['wrong in-bounds offset',()=>[object,{'source.sol':{L:[{start:1,length:20}]}},'source.sol','L',address]],
 ['unresolved additional placeholder',()=>[object+placeholder,refs,'source.sol','L',address]],
])test('linker refuses '+name,()=>assert.throws(()=>linkLibraryObject(...mutate())));
