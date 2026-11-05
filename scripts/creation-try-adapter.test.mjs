import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {creationTryContext} from './creation-try-adapter.mjs';
const source=JSON.parse(readFileSync(new URL('../tests/solc/CreationTry.ast.json',import.meta.url),'utf8')).ast;
const C=ast=>ast.nodes.find(n=>n.name==='C');
const F=ast=>C(ast).nodes[0];
const T=ast=>F(ast).body.statements[1];
test('complete original creation family obtains an explicit zero-value source context',()=>{
 assert.equal(creationTryContext(source,C(source))?.kind,'creation-try-source');
});
for(const [label,mutate] of [
 ['denominated prefix',a=>F(a).body.statements[0].initialValue.subdenomination='ether'],
 ['wrong argument declaration',a=>T(a).externalCall.arguments[0].referencedDeclaration=-99],
 ['wrong target declaration',a=>T(a).externalCall.expression.typeName.referencedDeclaration=-99],
 ['wrong returned target',a=>T(a).clauses[0].parameters.parameters[0].typeName.referencedDeclaration=-99],
 ['wrong actual handle',a=>T(a).clauses[0].block.statements[0].expression.rightHandSide.components[0].leftExpression.arguments[0].referencedDeclaration=-99],
 ['wrong caught reason',a=>T(a).clauses[1].block.statements[0].expression.rightHandSide.referencedDeclaration=-99],
 ['bare catch',a=>T(a).clauses[1].errorName=''],
 ['constructor effect',a=>a.nodes.find(n=>n.name==='Succeeds').nodes[0].body.statements.push({nodeType:'InlineAssembly'})],
 ['caller tail',a=>F(a).body.statements.push({nodeType:'Return'})],
 ['stateful owner',a=>C(a).nodes.push({nodeType:'VariableDeclaration',stateVariable:true})],
 ['function-valued input',a=>F(a).parameters.parameters.push({typeDescriptions:{typeString:'function () external'}})],
 ['payment option',a=>T(a).externalCall.expression={nodeType:'FunctionCallOptions',expression:T(a).externalCall.expression}],
 ['unknown target kind',a=>a.nodes.find(n=>n.name==='Succeeds').contractKind='library'],
 ['untracked source contract',a=>a.nodes.push({nodeType:'ContractDefinition',id:999,name:'Other'})]
])test(`creation-only admission refuses ${label}`,()=>{
 const ast=structuredClone(source);mutate(ast);assert.equal(creationTryContext(ast,C(ast)),null);
});
