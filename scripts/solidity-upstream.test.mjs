import {test} from 'node:test';
import assert from 'node:assert/strict';
import {parseFixture,withPreamble,evmCompatible,diagnosticLines,semanticVectors,partition,runtimePipelines,combineVariants,revertBytes,verifySnapshot} from './solidity-upstream.mjs';
import {mergeRetry,compatible,mergeDirectories} from './merge-solidity-upstream-retries.mjs';
import {mkdtempSync,mkdirSync,writeFileSync,readFileSync,rmSync} from 'node:fs';
import {join} from 'node:path';
import {tmpdir} from 'node:os';
import {execFile} from 'node:child_process';
import {promisify} from 'node:util';

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

test('noncanonical and truncated inputs retain raw bytes for typed decoder replay',()=>{
  assert.throws(()=>semanticVectors(fixture(['f(uint256,bool): 010, true -> 0']),abi),/token not adapted/);
  assert.throws(()=>semanticVectors(fixture(['f(uint256,bool): 1, true -> 010']),abi),/token not adapted/);
  for (const line of ['f(uint256,bool): 1, 2 -> 0','f(uint256,bool): 1 -> 0']) {
    const [v]=semanticVectors(fixture([line]),abi);
    assert.ok(v.calldata); assert.equal(v.args,undefined);
    assert.deepEqual(v.inputTypes,['uint256','bool']);
  }
  const narrow=[{type:'function',name:'g',inputs:[{type:'uint8'}],outputs:[]}];
  assert.equal(semanticVectors(fixture(['g(uint8): 256 ->']),narrow)[0].calldata.at(-2),1);
  assert.equal(semanticVectors({...fixture(['g(uint8): 256 ->']),settings:{ABIEncoderV1Only:'true'}},narrow)[0].canonicalOnly,true);
  assert.equal(semanticVectors({...fixture(['g(uint8): 256 ->']),sources:new Map([['a.sol','pragma abicoder /* comment */ v1;']])},narrow)[0].canonicalOnly,true);
  assert.equal(semanticVectors({...fixture(['g(uint8): 256 ->']),abiCoderV1:true},narrow)[0].canonicalOnly,true);
});

test('aggregate vectors retain offsets, lengths, bytes and exact tuple schemas',()=>{
  const aggregate=[{type:'function',name:'f',inputs:[{type:'tuple[]',components:[{type:'uint8'},{type:'bytes'}]}],outputs:[{type:'bytes4'}]}];
  const [v]=semanticVectors(fixture(['f((uint8,bytes)[]): 32, 0 -> hex"6162636400000000000000000000000000000000000000000000000000000000"']),aggregate);
  assert.deepEqual(v.inputTypes,['(uint8,bytes)[]']);
  assert.equal(v.calldata.length,64); assert.equal(v.calldata[31],32);
  assert.deepEqual(v.expectedBytes,[97,98,99,100,...Array(28).fill(0)]);
  const nominal=structuredClone(aggregate);nominal[0].inputs[0].components[0].internalType='enum C.E';
  assert.throws(()=>semanticVectors(fixture(['f((uint8,bytes)[]): 32, 0 ->']),nominal),/nominal enum/);
});

test('unsupported gas, logs, revert data and extra observations prevent success',()=>{
  for (const line of ['gas legacy: 100','~ emit E(uint256): 1'])
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


test('exact failure data retains raw selector bytes and complete signed ABI words',()=>{
  const payload=revertBytes('hex"4e487b71", 0x12');
  assert.deepEqual(payload,[0x4e,0x48,0x7b,0x71,...Array(31).fill(0),0x12]);
  assert.deepEqual(revertBytes('hex"0001", -1'),[0,1,...Array(32).fill(255)]);
  assert.deepEqual(revertBytes('hex""'),[]);
  const [vector]=semanticVectors(fixture(['f(uint256,bool): 1, true -> FAILURE, hex"4e487b71", 0x12']),abi);
  assert.equal(vector.failure,true);
  assert.deepEqual(vector.expected,[]);
  assert.deepEqual(vector.revertBytes,payload);
  for (const invalid of ['hex"a"','hex"zz"','', 'hex"00",', 'left(hex"00")', '"'+'a'.repeat(33)+'"', '010', '-010', '-0x1', (2n**256n).toString()])
    assert.throws(()=>revertBytes(invalid));
});


test('concurrent snapshot publication retains complete bytes; reuse rejects drift',async()=>{
  const root=mkdtempSync(join(tmpdir(),'upstream-snapshot-')),destination=join(root,'tree');
  const script=`import {verifySnapshot} from ${JSON.stringify(new URL('./solidity-upstream.mjs',import.meta.url).href)}; verifySnapshot(process.argv[1]);`;
  try {
    await Promise.all([0,1].map(()=>promisify(execFile)(process.execPath,['--input-type=module','-e',script,destination])));
    const {manifest}=verifySnapshot(destination);
    const file=join(destination,manifest.files[0].path);
    writeFileSync(file,'drift');
    assert.throws(()=>verifySnapshot(destination),/snapshot file drift/);
    assert.equal(readFileSync(file,'utf8'),'drift');
  } finally {rmSync(root,{recursive:true,force:true});}
});


test('native parameter alignment, quoted commas/hash and byte escapes are exact',()=>{
  assert.deepEqual(revertBytes('left(0x0001), right(0x0001), true, false'),
    [0,1,...Array(30).fill(0),...Array(31).fill(0),1,...Array(31).fill(0),1,...Array(32).fill(0)]);
  assert.deepEqual(revertBytes('"a,b#c"'),[97,44,98,35,99,...Array(27).fill(0)]);
  assert.deepEqual(revertBytes(String.raw`"a\n\r\t\0\x41\\"`),[97,10,13,9,0,65,92,...Array(25).fill(0)]);
  assert.deepEqual(revertBytes(String.raw`"\xf"`),[15,...Array(31).fill(0)]);
  assert.throws(()=>revertBytes(String.raw`"\xfg"`),/escape/);
  assert.throws(()=>revertBytes(String.raw`"\q"`),/escape/);
  const noArgs=[{type:'function',name:'g',inputs:[],outputs:[]}];
  const [v]=semanticVectors(fixture(['g() -> FAILURE, "a,b#c" # explanation #']),noArgs);
  assert.deepEqual(v.revertBytes,revertBytes('"a,b#c"'));
  assert.throws(()=>semanticVectors(fixture(['g() -> FAILURE, left(# comment #1)']),noArgs),/comment/);
  assert.throws(()=>semanticVectors(fixture(['g() -> FAILURE, 1# comment #2']),noArgs),/comment/);
});

test('v1 raw vectors require canonical-prefix replay without dropping suffix bytes',()=>{
  const abi=[{type:'function',name:'f',inputs:[{type:'bytes'}],outputs:[{type:'uint256'}]}];
  const line='f(bytes): 32, 0, hex"aabbff" -> 7';
  const [v]=semanticVectors({...fixture([line]),abiCoderV1:true},abi);
  assert.equal(v.canonicalOnly,true);
  assert.deepEqual(v.calldata,revertBytes('32, 0, hex"aabbff"'));
  assert.equal(v.calldata.length,67);
  assert.deepEqual(v.expectedBytes,revertBytes('7'));
  const [v2]=semanticVectors(fixture([line]),abi);
  assert.equal(v2.canonicalOnly,undefined);
  assert.deepEqual(v2.calldata,v.calldata);
});

test('original named-error sequences retain every selector, word and dynamic observation', async()=>{
  const archive=new URL('../tests/upstream/solidity-0.8.38.tar.gz',import.meta.url);
  const extract=async path=>(await promisify(execFile)('tar',['-xOzf',archive.pathname,path],{maxBuffer:1024*1024})).stdout;
  const word=n=>Array.from(Buffer.from(BigInt.asUintN(256,BigInt(n)).toString(16).padStart(64,'0'),'hex'));
  const bytes=hex=>Array.from(Buffer.from(hex,'hex'));
  const a=parseFixture(await extract('test/libsolidity/semanticTests/errors/revert_error_named_parameters.sol'));
  const av=semanticVectors(a,Array.from({length:5},(_,i)=>({type:'function',name:`trigger${i+1}`,inputs:[],outputs:[]})));
  assert.equal(av.length,5);
  assert.deepEqual(av.map(v=>v.signature),['trigger1()','trigger2()','trigger3()','trigger4()','trigger5()']);
  assert.deepEqual(av[0].revertBytes,bytes('59f176a3').concat(word(2),word(7)));
  assert.deepEqual(av[1].revertBytes,av[0].revertBytes);
  assert.deepEqual(av[2].revertBytes,bytes('b912b8d4').concat(word(2),word(7),word(9)));
  assert.deepEqual(av[3].revertBytes,av[4].revertBytes);
  assert.equal(av[3].revertBytes.length,4+6*32);
  const b=parseFixture(await extract('test/libsolidity/semanticTests/errors/revert_error_named_parameters_literal_conversions.sol'));
  const names=['intWidening','twoStringsUnordered','twoStringsOrdered','stringAndUint','bytesAndBool','mixedDynamic','addressConversion','smallInts'];
  const bv=semanticVectors(b,names.map(name=>({type:'function',name,inputs:[],outputs:[]})));
  assert.equal(bv.length,8);assert.deepEqual(bv.map(v=>v.signature),names.map(n=>n+'()'));
  assert.deepEqual(bv[0].revertBytes,bytes('57685228').concat(word(1),word(200)));
  assert.deepEqual(bv[1].revertBytes,bv[2].revertBytes);
  assert.deepEqual(bv[7].revertBytes,bytes('641a758d').concat(word(1),word(200),word(300)));
  for(const v of [...av,...bv])assert.equal(v.failure,true);
});

test('original numeric failure sequences retain exact panic codes and fixed-byte padding', async()=>{
  const archive=new URL('../tests/upstream/solidity-0.8.38.tar.gz',import.meta.url);
  const extract=async path=>(await promisify(execFile)('tar',['-xOzf',archive.pathname,path],{maxBuffer:1024*1024})).stdout;
  const fn=(name,inputs,output)=>({type:'function',name,inputs:inputs.map(type=>({type})),outputs:[{type:output}]});
  const panic=code=>[0x4e,0x48,0x7b,0x71,...Array(31).fill(0),code];
  const m=semanticVectors(parseFixture(await extract('test/libsolidity/semanticTests/arithmetics/addmod_mulmod_zero.sol')),
    [fn('f',['uint256'],'uint256'),fn('g',['uint256'],'uint256'),fn('h',[],'uint256')]);
  assert.deepEqual(m.map(v=>v.signature),['f(uint256)','g(uint256)','h()']);
  for(const v of m.slice(0,2)){assert.equal(v.failure,true);assert.deepEqual(v.revertBytes,panic(0x12));}
  assert.equal(m[2].failure,false);assert.deepEqual(m[2].expected,['2']);
  const p=semanticVectors(parseFixture(await extract('test/libsolidity/semanticTests/viaYul/exp_overflow.sol')),
    [fn('f',['uint8','uint8'],'uint256'),fn('g',['uint256','uint256'],'uint256')]);
  assert.equal(p.length,20);assert.equal(p[8].signature,'f(uint8,uint8)');
  assert.deepEqual(p[8].args,['255','131']);
  assert.equal(p[8].failure,true);assert.deepEqual(p[8].revertBytes,panic(0x11));
  assert.equal(p.slice(9).length,11);
  for(const v of p.filter(v=>v.failure))assert.deepEqual(v.revertBytes,panic(0x11));
  const names=['conv','upcast','downcast','r_b32','r_b25','r_b16','r_b8','r_b4','r_b1','a_b32','a_b25','a_b16','a_b8','a_b4','a_b1'];
  const types=['bytes32','bytes32','bytes12','bytes32','bytes25','bytes16','bytes8','bytes4','bytes1','bytes32','bytes25','bytes16','bytes8','bytes4','bytes1'];
  const b=semanticVectors(parseFixture(await extract('test/libsolidity/semanticTests/viaYul/unary_fixedbytes.sol')),
    names.map((name,i)=>fn(name,i<3?['bytes25']:[],types[i])));
  assert.deepEqual(b.map(v=>v.signature),names.map((n,i)=>n+(i<3?'(bytes25)':'()')));
  // Exact retained word: the numeric upstream hex includes a leading zero
  // byte after word padding. Do not truncate it to the nominal return width.
  const retained=Array.from(Buffer.from('00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff0000000000000000','hex'));
  assert.equal(retained.length,32);assert.equal(b[4].failure,false);
  assert.deepEqual(b[4].expectedBytes,retained);assert.deepEqual(b[10].expectedBytes,retained);
  assert.notDeepEqual(retained,panic(0x11));assert.notDeepEqual(retained,retained.slice(1));
});

test('original aggregate custom errors retain complete arrays, nested offsets and call order',async()=>{
  const archive=new URL('../tests/upstream/solidity-0.8.38.tar.gz',import.meta.url);
  const extract=async path=>(await promisify(execFile)('tar',['-xOzf',archive.pathname,path],{maxBuffer:1024*1024})).stdout;
  const word=n=>Array.from(Buffer.from(BigInt.asUintN(256,BigInt(n)).toString(16).padStart(64,'0'),'hex'));
  const words=xs=>xs.flatMap(word),hex=s=>Array.from(Buffer.from(s,'hex'));
  const a=semanticVectors(parseFixture(await extract('test/libsolidity/semanticTests/errors/revert_conversion.sol')),
    [{type:'function',name:'f',inputs:[],outputs:[]}]);
  assert.equal(a.length,1);assert.equal(a[0].signature,'f()');assert.equal(a[0].failure,true);
  assert.deepEqual(a[0].revertBytes,hex('59e4d4df').concat(words([64,128,3]),[97,98,99],Array(29).fill(0),words([1,7])));
  const b=semanticVectors(parseFixture(await extract('test/libsolidity/semanticTests/errors/using_structs.sol')),
    [{type:'function',name:'f',inputs:[{type:'bool'}],outputs:[]}]);
  assert.equal(b.length,2);assert.deepEqual(b.map(v=>v.args),[['true'],['false']]);
  const expected=hex('e96e07f0').concat(words([2,96,7,9,64,3]),[97,98,99],Array(29).fill(0));
  for(const v of b){assert.equal(v.signature,'f(bool)');assert.equal(v.failure,true);assert.deepEqual(v.revertBytes,expected);}
  assert.notDeepEqual(expected,expected.slice(0,-1));assert.notDeepEqual(expected,expected.concat(0));
  assert.notDeepEqual(expected,hex('e96e07f0').concat(words([2,64,7,9,64,3]),[97,98,99],Array(29).fill(0)));
});

test('compound array decoder vectors retain dimensions, all calls and raw suffixes',async()=>{
  const archive=new URL('../tests/upstream/solidity-0.8.38.tar.gz',import.meta.url);
  const extract=async path=>(await promisify(execFile)('tar',['-xOzf',archive.pathname,path],{maxBuffer:1024*1024})).stdout;
  const fn=(name,inputs,outputs)=>({type:'function',name,inputs:inputs.map(type=>({type})),outputs:outputs.map(type=>({type}))});
  const word=n=>Array.from(Buffer.from(BigInt(n).toString(16).padStart(64,'0'),'hex'));
  const a=semanticVectors(parseFixture(await extract('test/libsolidity/semanticTests/abicoder/calldataDecoding/array/memory_arrays_static.sol')),
    [fn('f',['uint16[3]','uint16[2][3]','uint256','uint256','uint256'],['uint256','uint256'])]);
  assert.equal(a.length,1);assert.deepEqual(a[0].expectedBytes,[2,32].flatMap(word));
  assert.equal(a[0].calldata.length,12*32);
  const b=semanticVectors(parseFixture(await extract('test/libsolidity/semanticTests/array/indexAccess/arrays_complex_memory_index_access.sol')),
    [fn('set',['uint24[3][]','uint256','uint256'],['uint256','uint256'])]);
  assert.equal(b.length,1);assert.equal(b[0].calldata.length,22*32);
  assert.deepEqual(b[0].expectedBytes,[6,12].flatMap(word));
  assert.deepEqual(b[0].calldata.slice(-32),word(18));
  const inputs=['uint8[][][]','uint8[][1][]','uint8[2][][2]','uint16[][]','uint32[][2]','uint32[2][]'];
  const outputs=['uint8[][]','uint8[][1]','uint8[2][]','uint16[][]','uint32[][2]','uint32[2][]'];
  const c=semanticVectors(parseFixture(await extract('test/libsolidity/semanticTests/array/copying/nested_array_element_memory_to_memory.sol')),
    inputs.map((t,i)=>fn('test'+(i+1),[t],[outputs[i]])));
  assert.equal(c.length,6);assert.deepEqual(c.map(v=>v.signature),inputs.map((t,i)=>`test${i+1}(${t})`));
  const expected=[[32,2,64,128,1,7,2,8,9],[32,32,3,12,13,14],[32,1,7,7],
    [32,2,64,128,1,7,2,8,9],[32,64,128,1,7,2,8,9],[32,2,5,6,7,8]];
  for(let i=0;i<c.length;i++){assert.equal(c[i].failure,false);assert.deepEqual(c[i].expectedBytes,expected[i].flatMap(word));}
});
