import test from 'node:test';
import assert from 'node:assert/strict';
import {parseVerify,main} from './verify.mjs';
import {decodeNative} from './verify-native.mjs';
const request={sourceId:7,function:'f'};
const row={sourceId:7,function:'f',reading:'solc',verification:'native',status:'proved'};
const protocol=r=>JSON.stringify({ready:true})+'\n'+JSON.stringify({results:[r]})+'\n';
test('mode parsing preserves signatures and the literal path separator',()=>{
  const parsed=parseVerify(['a.sol','--mode','fast','--function','f(uint256)']);
  assert.equal(parsed.mode,'fast');assert.equal(parsed.options.function,'f(uint256)');
  assert.deepEqual(parseVerify(['--','--help']).paths,['--help']);
  assert.equal(main(['-h']),0);assert.equal(main(['--help']),0);
  assert.throws(()=>parseVerify(['a.sol','--mode','fast','--mode','certified']),/duplicate/);
  assert.throws(()=>parseVerify(['a.sol','--mode','direct']),/fast or certified/);
});
test('only exact native protocol identity becomes a native verdict',()=>{
  assert.equal(decodeNative(protocol(row),[request])[0].verification,'native');
  for(const change of [{sourceId:8},{function:'other'},{reading:'clean'},{verification:'direct'},{status:'refused'}])
    assert.throws(()=>decodeNative(protocol({...row,...change}),[request]),/protocol/);
  assert.throws(()=>decodeNative(protocol({...row,status:'refuted'}),[request]),/witness/);
  assert.throws(()=>decodeNative(protocol({...row,status:'refuted',counterexample:{certified:true}}),[request]),/witness/);
  assert.throws(()=>decodeNative(protocol(row)+protocol(row),[request]),/responses/);
  assert.throws(()=>decodeNative(JSON.stringify({ready:true})+'\n',[request]),/responses/);
  assert.throws(()=>decodeNative(JSON.stringify({ready:true})+'\n'+JSON.stringify({gap:'unknown syntax'}),[request]),/unsupported/);
});

import {differential} from './verify-differential.mjs';
const listed={source:'case.sol',sourceHash:'a'.repeat(64),contract:'C',sourceId:7,function:'f',reading:'solc',status:'ready',compilationSha256:'c'.repeat(64)};
const result=status=>({results:[{...listed,status}],errors:[]});
const nativeResult=status=>({results:[{...listed,status,verification:'native'}],errors:[]});
test('differential catches shared omissions and never changes certified verdicts',()=>{
  const original=result('refuted');
  const before=JSON.stringify(original);
  const output=differential(['case.sol'],{}, {listing:()=>result('ready'),fast:()=>nativeResult('proved'),certified:()=>original});
  assert.equal(output.status,'bug');assert.equal(output.certified.results[0].status,'refuted');assert.equal(JSON.stringify(original),before);
  const missing=differential(['case.sol'],{}, {listing:()=>result('ready'),fast:()=>({results:[],errors:[]}),certified:()=>({results:[],errors:[]})});
  assert.equal(missing.status,'bug');
  const agree=differential(['case.sol'],{}, {listing:()=>result('ready'),fast:()=>nativeResult('proved'),certified:()=>result('proved')});
  assert.equal(agree.status,'agree');
  const stale=differential(['case.sol'],{}, {listing:()=>result('ready'),fast:()=>({results:[{...listed,sourceHash:'b'.repeat(64),status:'proved'}],errors:[]}),certified:()=>result('proved')});
  assert.equal(stale.status,'bug');
});

test('differential never upgrades a missing or wrong mode marker',()=>{
  for(const verification of [undefined,'direct','certified']) {
    const output=differential(['case.sol'],{}, {listing:()=>result('ready'),fast:()=>({results:[{...listed,status:'proved',verification}],errors:[]}),certified:()=>result('proved')});
    assert.equal(output.status,'bug');
  }
  const output=differential(['case.sol'],{}, {listing:()=>result('ready'),fast:()=>nativeResult('proved'),certified:()=>nativeResult('proved')});
  assert.equal(output.status,'bug');
});

import {policyOf,parseAtoms} from './solidity-lean-assumptions.mjs';
import {reportExitCode} from './solidity-lean.mjs';
test('comparison preserves engine agreement while enforcing caller policy',()=>{
  const policy=policyOf(parseAtoms('callback=withCallback'));
  const output=differential(['case.sol'],{policy}, {listing:()=>result('ready'),fast:()=>nativeResult('proved'),certified:()=>result('proved')});
  assert.equal(output.status,'agree');
  assert.equal(output.fast.results[0].status,'refused');assert.equal(output.certified.results[0].status,'refused');
  assert.equal(reportExitCode('verify',output.fast),1);assert.equal(reportExitCode('verify',output.certified),1);
});
test('synthesized constructor stays in the independent comparison',()=>{
  const constructor={...listed,sourceId:-1,function:'constructor'};
  const output=differential(['case.sol'],{}, {listing:()=>({results:[constructor],errors:[]}),
    fast:()=>({results:[{...constructor,status:'proved',verification:'native'}],errors:[]}),
    certified:()=>({results:[{...constructor,status:'proved'}],errors:[]})});
  assert.equal(output.status,'agree');assert.equal(output.obligations,1);
});

import {mkdtempSync,writeFileSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {freezeSources} from './verify-source.mjs';
import {sourceHash} from './source-locations.mjs';
test('full compilation identity rejects a changed dependency even with unchanged main source',()=>{
  const directory=mkdtempSync(join(tmpdir(),'verify-control-'));
  try {
    const main=join(directory,'Main.sol'),dependency=join(directory,'Dep.sol');
    writeFileSync(main,'import "./Dep.sol";');writeFileSync(dependency,'contract Dep {}');
    const hash=text=>sourceHash(Buffer.from(text));
    const compiled={header:{mainSource:'Main.sol'},sourceUnits:[
      {name:'Main.sol',sourceSha256:hash('import "./Dep.sol";')},{name:'Dep.sol',sourceSha256:hash('contract Dep {}')}]};
    const check=freezeSources(compiled,main);
    writeFileSync(dependency,'contract Changed {}');assert.throws(check,/source changed/);
    writeFileSync(dependency,'contract Dep {}');assert.doesNotThrow(check);
  } finally {rmSync(directory,{recursive:true,force:true});}
  const output=differential(['case.sol'],{}, {listing:()=>result('ready'),
    fast:()=>({results:[{...listed,status:'proved',verification:'native',compilationSha256:'d'.repeat(64)}],errors:[]}),certified:()=>result('proved')});
  assert.equal(output.status,'bug');
});

import {nativeBuild} from './verify-native.mjs';
import {readFileSync,mkdirSync} from 'node:fs';
import {resolve,dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
test('a valid executable hash cannot bind a cache to a different generated input',()=>{
  const root=resolve(dirname(fileURLToPath(import.meta.url)),'..');
  const directory=mkdtempSync(join(tmpdir(),'verify-cache-control-'));
  const key='0'.repeat(64),output=join(directory,key),other='1'.repeat(64);
  const hashFile=path=>sourceHash(readFileSync(path));
  try {
    mkdirSync(output);writeFileSync(join(output,'direct-check'),'control bytes, never executed');
    const buildInputs=Object.fromEntries(['scripts/verify-build.py','scripts/direct-runtime-closure.py',
      'web/browser/direct-bridge.c','lean-toolchain','lakefile.toml'].map(p=>[join(root,p),hashFile(join(root,p))]));
    const manifest={version:2,platform:process.platform,arch:process.arch.replace('x64','x86_64'),
      leanCommit:'797c613eb9b6d4ec95db23e3e00af9ac6657f24b',toolchain:readFileSync(join(root,'lean-toolchain'),'utf8').trim(),
      executable:hashFile(join(output,'direct-check')),sourceFiles:[{module:'Solidity.Tools.FastMode.Engine'}],
      bridgeSha256:hashFile(join(root,'web/browser/direct-bridge.c')),
      closureScriptSha256:hashFile(join(root,'scripts/direct-runtime-closure.py')),buildInputs,
      rootModule:'VerifyInput'+other};
    writeFileSync(join(output,'build.json'),JSON.stringify(manifest));
    assert.throws(()=>nativeBuild(output),/different input/);
    manifest.rootModule='VerifyInput'+key;
    manifest.generatedInput={path:join(root,'.lake/verify/inputs',other,'VerifyInput'+key+'.lean'),sha256:'a'.repeat(64)};
    manifest.generatedFixture={path:join(root,'.lake/verify/inputs',other,'source.ast.json'),sha256:'b'.repeat(64)};
    writeFileSync(join(output,'build.json'),JSON.stringify(manifest));
    assert.throws(()=>nativeBuild(output),/different cache/);
  } finally {rmSync(directory,{recursive:true,force:true});}
});

import {sourceCounterexample} from './verify-source.mjs';
test('inherited witness presentation follows exact source IDs across duplicate contract names',()=>{
  const owner=(id,name)=>({nodeType:'ContractDefinition',name:'Base',nodes:[{
    nodeType:'FunctionDefinition',id,parameters:{parameters:[{name,typeDescriptions:{typeString:'uint256'}}]}}]});
  const base=owner(7,'actualParameter'),other=owner(8,'wrongParameter');
  const ast={nodes:[other,base,{nodeType:'ContractDefinition',name:'Derived',nodes:[]}]};
  const row={sourceId:7,contract:'Derived',status:'refuted',counterexample:{certified:false,
    arguments:[{paramIndex:0,modelName:'bound0',value:'42'}]}};
  const before=JSON.stringify(row),witness=sourceCounterexample(ast,row);
  assert.deepEqual(witness,{certified:false,arguments:[{paramIndex:0,modelName:'bound0',value:'42',sourceName:'actualParameter',sourceType:'uint256'}]});
  assert.equal(JSON.stringify(row),before);
  for(const sourceId of [-1,0,99]) assert.equal(sourceCounterexample(ast,{...row,sourceId}),row.counterexample);
  assert.equal(sourceCounterexample({nodes:[base,owner(7,'ambiguous')]},row),row.counterexample);
});
