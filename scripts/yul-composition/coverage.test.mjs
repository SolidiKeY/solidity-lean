import test from 'node:test';
import assert from 'node:assert/strict';
import {scan,BUILTIN_FEATURES} from './coverage.mjs';
test('AST presence remains distinct from semantic coverage',()=>{
 const ast={nodeType:'ContractDefinition',contractKind:'library',nodes:[{nodeType:'ModifierDefinition',body:{nodeType:'WhileStatement',body:{nodeType:'InlineAssembly',AST:{nodeType:'YulBlock',statements:[{nodeType:'YulFunctionCall',functionName:{name:'sstore'}}]}}}}]};
 const r=scan(ast);assert.equal(r.blocks,1);assert.deepEqual(r.features,['inlineAssembly','storageLayout']);
 assert.deepEqual(r.contexts,['ModifierDefinition','WhileStatement','library']);assert.equal(r.calls.sstore,1);
 assert.equal(BUILTIN_FEATURES.gas,'gasleft');assert.equal(BUILTIN_FEATURES.log4,'eventLog');
 assert.deepEqual(scan({}).features,[]);
});
