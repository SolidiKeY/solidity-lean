// Real pinned compiler plus local completion; no native UI/kernel/EVM claim.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),os=require('node:os'),lang=require('../src/language-services.cjs');
test('real compiler index does not admit comment or literal completion contexts',async t=>{
 const dir=fs.mkdtempSync(path.join(os.tmpdir(),'completion-lexical-')),source=path.join(dir,'Contexts.sol'),text=['pragma solidity ^0.8.34;','contract Contexts {','// con','/* con */','function control() public pure returns(bytes memory){','string memory a="con"; string memory b=unicode"con"; bytes memory c=hex"ca";','return bytes(a);','}','}'].join('\n');fs.writeFileSync(source,text);
 try{const {compileFixture}=await import('../../scripts/solc-ast.mjs'),compiled=compileFixture({args:['--source',source,'--out',path.join(dir,'out.json'),'--no-wrapper'],sourceBytes:Buffer.from(text),analysisOnly:true,quiet:true}),analysis=lang.index(text,compiled.rawAst);for(const needle of ['// con','/* con','"con','unicode"con','hex"ca']){const point=lang.position(text,text.indexOf(needle)+needle.length);assert.deepEqual(lang.completion(text,point,analysis).items,[],needle);}assert.ok(lang.completion(text,lang.position(text,text.indexOf('control')+3),analysis).items.some(i=>i.label==='control'));t.diagnostic(JSON.stringify({boundary:'compiler/JavaScript only',compiler:compiled.compiler,sourceHash:compiled.sourceHash}));}finally{fs.rmSync(dir,{recursive:true,force:true});}
});

test('pinned compiler admits spaced arrays and dollar names used by live fallback',async t=>{
 const dir=fs.mkdtempSync(path.join(os.tmpdir(),'completion-spacing-')),source=path.join(dir,'Spacing.sol'),text='pragma solidity ^0.8.34; contract Spacing { uint256 [ ] $items; uint256[] items$; function inspect(uint256 [ ] calldata input) external view returns(uint256){uint256 [ ] memory local = new uint256[](1);return $items.length+items$.length+input.length+local.length;} }';fs.writeFileSync(source,text);
 try{const {compileFixture}=await import('../../scripts/solc-ast.mjs'),compiled=compileFixture({args:['--source',source,'--out',path.join(dir,'out.json'),'--no-wrapper'],sourceBytes:Buffer.from(text),analysisOnly:true,quiet:true}),observations=[];
 for(const name of ['$items','items$','input','local']){const point=lang.position(text,text.indexOf(name+'.length')+name.length+1),labels=lang.completion(text,point,null).items.map(i=>i.label);observations.push({name,labels});assert.deepEqual(labels,['$items','items$'].includes(name)?['length','push','pop']:['length'],name);}
 t.diagnostic(JSON.stringify({boundary:'Actual compiler admission plus JavaScript fallback hints; no native UI/kernel/EVM parity',compiler:compiled.compiler,sourceHash:compiled.sourceHash,observations}));
 }finally{fs.rmSync(dir,{recursive:true,force:true});}
});

test('pinned compiler state declaration after a method has storage fallback members',async t=>{
 const dir=fs.mkdtempSync(path.join(os.tmpdir(),'completion-state-scope-')),source=path.join(dir,'StateScope.sol'),text='pragma solidity ^0.8.34; contract StateScope { function before() public pure returns(uint256){return 1;} uint256[] items; function size() public view returns(uint256){return items.length;} }';fs.writeFileSync(source,text);
 try{const {compileFixture}=await import('../../scripts/solc-ast.mjs'),compiled=compileFixture({args:['--source',source,'--out',path.join(dir,'out.json'),'--no-wrapper'],sourceBytes:Buffer.from(text),analysisOnly:true,quiet:true}),point=lang.position(text,text.indexOf('items.length')+'items.'.length),labels=lang.completion(text,point,null).items.map(item=>item.label);assert.deepEqual(labels,['length','push','pop']);
 t.diagnostic(JSON.stringify({boundary:'Actual compiler admission plus controlled fallback hints; no native UI/kernel/EVM parity',compiler:compiled.compiler,sourceHash:compiled.sourceHash,labels}));
 }finally{fs.rmSync(dir,{recursive:true,force:true});}
});
