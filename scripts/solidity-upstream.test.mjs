import {test} from 'node:test';
import assert from 'node:assert/strict';
import {parseFixture,withPreamble,evmCompatible,diagnosticLines,semanticVectors,partition,runtimePipelines,combineVariants} from './solidity-upstream.mjs';
import {mergeRetry,compatible,mergeDirectories} from './merge-solidity-upstream-retries.mjs';
import {mkdtempSync,mkdirSync,writeFileSync,readFileSync,rmSync} from 'node:fs';
import {join} from 'node:path';
import {tmpdir} from 'node:os';

const abi=[{type:'function',name:'f',inputs:[{type:'uint256'},{type:'bool'}],outputs:[{type:'uint256'}]}];
const fixture=expectations=>({expectations});

test('fixture boundaries preserve sources and ignore expectation text as Solidity',()=>{
  const f=parseFixture('==== Source: A.sol ====\ncontract A {}\n==== Source: B.sol ====\ncontract B {}\n// ====\n// compileViaYul: true\n// ----\n// f() -> 7\n');
  assert.deepEqual([...f.sources],[['A.sol','contract A {}\n'],['B.sol','contract B {}\n']]);
  assert.equal(f.mainSource,'B.sol');
  assert.deepEqual(f.settings,{compileViaYul:'true'});
  assert.deepEqual(f.expectations,['f() -> 7']);
});

test('external sources and duplicate source units cannot silently disappear',()=>{
  assert.throws(()=>parseFixture('==== ExternalSource: x.sol ====\n'),/external-source/);
  assert.throws(()=>parseFixture('==== Source: A ====\na\n==== Source: A ====\nb\n'),/duplicate source/);
});

test('preamble follows the native harness without rewriting fixture source',()=>{
  const source='contract C {}\n';
  assert.equal(withPreamble(source,true),'pragma solidity >=0.0;\n// SPDX-License-Identifier: GPL-3.0\npragma abicoder v1;\n'+source);
  assert.equal(withPreamble('pragma abicoder v2;\n'+source,true).match(/pragma abicoder/g).length,1);
});

test('diagnostics retain exact order, messages, source names and byte offsets',()=>{
  const errors=[{type:'TypeError',errorCode:'1234',message:'one\ntwo',sourceLocation:{file:'A.sol',start:60,end:67}},
    {type:'Warning',errorCode:'9999',message:'other'}];
  assert.deepEqual(diagnosticLines(errors,new Map([['A.sol',50]])),
    ['TypeError 1234: (A.sol:10-17): one\\ntwo','Warning 9999: other']);
  assert.deepEqual(diagnosticLines([{type:'ParserError',errorCode:'5333',
    message:'Source file requires different compiler version (current compiler is 0.8.38)'}],new Map()),
    ['ParserError 5333: Source file requires different compiler version (current compiler is ....']);
});

test('EVM constraints are checked rather than ignored or retargeted',()=>{
  assert.equal(evmCompatible('>=cancun'),true);
  assert.equal(evmCompatible('<byzantium'),false);
  assert.equal(evmCompatible('=osaka'),true);
  assert.throws(()=>evmCompatible('unknown'),/unsupported/);
});

test('implicit and explicit upstream pipeline defaults both require two interpreter modes',()=>{
  assert.deepEqual(runtimePipelines({}),['legacy','viaIR']);
  assert.deepEqual(runtimePipelines({compileViaYul:'also'}),runtimePipelines({}));
  assert.deepEqual(runtimePipelines({compileViaYul:'false'}),['legacy']);
  assert.deepEqual(runtimePipelines({compileViaYul:'true'}),['viaIR']);
  const legacy={pipeline:'legacy',status:'working'};
  assert.equal(combineVariants('x',['legacy','viaIR'],[legacy]).status,'blocked');
  assert.equal(combineVariants('x',['legacy','viaIR'],[legacy,{pipeline:'viaIR',status:'working'}]).status,'working');
  assert.equal(combineVariants('x',['legacy','viaIR'],[legacy,{pipeline:'viaIR',status:'broken',reason:'mismatch'}]).status,'broken');
});

test('runtime vectors retain every call and compare ABI words exactly',()=>{
  const vectors=semanticVectors(fixture(['f(uint256,bool): 2, true -> 3','f(uint256,bool): 0xff, false -> 0xff']),abi);
  assert.equal(vectors.length,2);
  assert.deepEqual(vectors[0],{signature:'f(uint256,bool)',args:['2','true'],failure:false,expected:['3']});
  assert.deepEqual(vectors[1].expected,['255']);
});

test('signed words are decoded and encoded with canonical ABI extension',()=>{
  const signed=[{type:'function',name:'g',inputs:[{type:'int256'}],outputs:[{type:'int256'}]}];
  const max=(2n**256n-1n).toString();
  assert.deepEqual(semanticVectors(fixture([`g(int256): ${max} -> -1`]),signed)[0],
    {signature:'g(int256)',args:['-1'],failure:false,expected:[max]});
});

test('malformed ABI data cannot become a normal typed function call',()=>{
  assert.throws(()=>semanticVectors(fixture(['f(uint256,bool): 1, 2 -> 0']),abi),/Boolean/);
  assert.throws(()=>semanticVectors(fixture(['f(uint256,bool): 1 -> 0']),abi),/argument count/);
  const narrow=[{type:'function',name:'g',inputs:[{type:'uint8'}],outputs:[]}];
  assert.throws(()=>semanticVectors(fixture(['g(uint8): 256 ->']),narrow),/noncanonical/);
});

test('unsupported gas, logs, revert data and extra observations prevent success',()=>{
  for (const line of ['gas legacy: 100','~ emit E(uint256): 1','f(uint256,bool): 1, true -> FAILURE, hex"4e487b71", 0x11'])
    assert.throws(()=>semanticVectors(fixture(['f(uint256,bool): 1, true -> 3',line]),abi),/unsupported|not adapted/);
  assert.throws(()=>semanticVectors(fixture([]),abi),/no runtime vectors/);
});

test('a second constructor cannot accidentally retain the first deployment state',()=>{
  const constructors=[{type:'constructor',inputs:[],outputs:[]}];
  assert.throws(()=>semanticVectors(fixture(['constructor() ->','constructor() ->']),constructors),/redeployment/);
});

test('partitions are exhaustive and unknown/notRun results cannot pass',()=>{
  const rows=[{path:'a',status:'working'},{path:'b',status:'broken'},{path:'c',status:'blocked'}];
  const groups=partition(rows);
  assert.deepEqual(Object.values(groups).flat(),rows);
  assert.throws(()=>partition([{path:'d',status:'notRun'}]),/unclassified/);
});

test('isolated retries retain completed modes and cannot change conclusive results',()=>{
  const base={path:'x',stage:'lean-runtime',requiredPipelines:['legacy','viaIR'],
    variants:[{pipeline:'legacy',status:'working'},{pipeline:'viaIR',status:'blocked'}]};
  const retry={...base,variants:[{pipeline:'legacy',status:'blocked'},{pipeline:'viaIR',status:'working'}]};
  assert.equal(mergeRetry(base,retry).status,'working');
  assert.throws(()=>mergeRetry(base,{...retry,variants:[{pipeline:'legacy',status:'broken'}]}),/contradicts/);
  assert.throws(()=>mergeRetry(base,{...retry,path:'other'}),/identity/);
  compatible({modelSha256:'same'},{modelSha256:'same'});
  assert.throws(()=>compatible({modelSha256:'one'},{modelSha256:'two'}),/provenance differs/);
});

test('multiple retries of one fixture preserve every contributing report',()=>{
  const root=mkdtempSync(join(tmpdir(),'upstream-merge-'));
  const base=join(root,'base'),a=join(root,'a'),b=join(root,'b');
  const metadata={version:1,modelSha256:'same',filter:'x'};
  const row={path:'x',stage:'lean-runtime',requiredPipelines:['legacy','viaIR'],
    variants:[{pipeline:'legacy',status:'blocked'},{pipeline:'viaIR',status:'blocked'}]};
  const save=(dir,file,data)=>{mkdirSync(dir,{recursive:true});writeFileSync(join(dir,file),JSON.stringify(data));};
  try {
    save(base,'results.json',{metadata,results:[row]});
    save(base,'summary.json',{complete:true});
    save(base,'file-coverage.json',[{path:'x',status:'blocked'}]);
    save(a,'results.json',{metadata,results:[{...row,variants:[{pipeline:'legacy',status:'working'},{pipeline:'viaIR',status:'blocked'}]}]});
    save(b,'results.json',{metadata,results:[{...row,variants:[{pipeline:'legacy',status:'blocked'},{pipeline:'viaIR',status:'working'}]}]});
    for (const dir of [a,b]) save(dir,'summary.json',{complete:true});
    assert.deepEqual(mergeDirectories([base,a,b]),{working:1,broken:0,blocked:0});
    const merged=JSON.parse(readFileSync(join(base,'results.json'),'utf8'));
    assert.equal(merged.retryReports.length,2);
    const retained=merged.retryReports.map(ref=>readFileSync(join(base,ref.path),'utf8'));
    assert.ok(retained.includes(readFileSync(join(a,'results.json'),'utf8')));
    assert.ok(retained.includes(readFileSync(join(b,'results.json'),'utf8')));
  } finally {rmSync(root,{recursive:true,force:true});}
});
