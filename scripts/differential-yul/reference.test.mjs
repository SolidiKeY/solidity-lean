import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {compileSource,executeArtifact,compareObservations,loadCompiler} from './reference.mjs';
const artifact = () => ({ir:'object "Generated" {}',irOptimized:'object "Generated" {}',
  storageLayout:{storage:[{label:'x',slot:'0',offset:0,type:'t_uint256'},{label:'y',slot:'1',offset:0,type:'t_uint256'}],
    types:{t_uint256:{label:'uint256',encoding:'inplace',numberOfBytes:'32'}}},
  evm:{bytecode:{object:'6000'},deployedBytecode:{object:'00'},methodIdentifiers:{'run()':'12345678'}}});
const result = () => ({failed:false,returnData:'0x',exception:null,storage:['0','0'],slots:['0','1']});

test('both solc IR stages and viaIR bytecode are requested in the same compilation', () => {
  let seen;
  const compiled=compileSource(input=>{seen=input;return {contracts:{'generated.sol':{Generated:artifact()}}};},'contract Generated {}',{optimizer:false});
  assert.equal(seen.settings.viaIR,true);
  assert.equal(seen.settings.optimizer.enabled,false);
  assert.ok(seen.settings.outputSelection['*']['*'].includes('ir'));
  assert.ok(seen.settings.outputSelection['*']['*'].includes('irOptimized'));
  assert.equal(compiled.artifact.ir,artifact().ir);
  assert.throws(()=>compileSource(()=>({errors:[{severity:'error',message:'bad'}]}),'x'),/rejected source/);
  assert.throws(()=>compileSource(()=>({contracts:{}}),'x'),/missing Generated/);
  const bad=artifact();bad.evm.bytecode.object='__$unlinked$__';
  assert.throws(()=>compileSource(()=>({contracts:{'generated.sol':{Generated:bad}}}),'x'),/unlinked/);
});

test('storage admission covers every complete uint256 field at its declared slot', () => {
  for (const change of [a=>delete a.storageLayout, a=>a.storageLayout.storage.pop(),
    a=>a.storageLayout.storage.push({label:'z',slot:'2',offset:0,type:'t_uint256'}),
    a=>a.storageLayout.storage[1].slot='2', a=>a.storageLayout.storage[0].offset=1,
    a=>a.storageLayout.storage[0].label='z', a=>a.storageLayout.types.t_uint256.label='uint128',
    a=>a.storageLayout.types.t_uint256.numberOfBytes='16',
    a=>a.storageLayout.types.t_uint256.encoding='mapping']) {
    const a=artifact();change(a);
    assert.throws(()=>compileSource(()=>({contracts:{'generated.sol':{Generated:a}}}),'source'),/storage layout/);
  }
});

test('comparison covers status, exact return or revert bytes, and every storage slot', () => {
  const base=result();
  assert.equal(compareObservations(base,base),true);
  for (const changed of [{...base,failed:true}, {...base,returnData:'0x00'},
    {...base,storage:['0','1']}, {...base,storage:['1','0']}])
    assert.equal(compareObservations(changed,base),false);
  const revert={...base,failed:true,exception:'revert',returnData:'0xabcdef'};
  assert.equal(compareObservations(revert,revert),true);
  assert.equal(compareObservations({...revert,returnData:'0xabcdee'},revert),false);
  assert.throws(()=>compareObservations(base,{...base,exception:'out of gas',failed:true}),/unadapted/);
  assert.throws(()=>compareObservations(base,{...base,failed:true}),/inconsistent/);
  assert.throws(()=>compareObservations({...base,storage:['-1']},base),/invalid/);
  for (const invalid of [{...base,storage:[],slots:[]}, {...base,storage:['0'],slots:['0']},
    {...base,slots:['1','0']}, {...base,slots:['0','2']}, {...base,slots:undefined}]) {
    assert.throws(()=>compareObservations(invalid,invalid),/invalid/);
    assert.throws(()=>compareObservations(base,invalid),/invalid/);
    assert.throws(()=>compareObservations(invalid,base),/invalid/);
  }
});

function mock({failed=false,exception=null,hash,deployFailed=false}={}) {
  const calls=[],reads=[];
  const address={toString:()=> 'contract'};
  const deps={machine:async()=>({evm:{stateManager:{getStorage:async(a,key)=>{
    assert.equal(a,address);reads.push(Buffer.from(key).toString('hex'));
    return reads.length===1 ? Uint8Array.of(255) : new Uint8Array();
  }}},call:async options=>{
    calls.push(options);return {result:{createdAddress:address,execResult:{}},metrics:{steps:3}};
  }}),creationObservation:()=>({failed:deployFailed,runtimeCodeSha256:hash??createHash('sha256').update(Uint8Array.of(0)).digest('hex')}),
  observation:()=>({failed,exception,returnData:failed?'0xdead':'0x'})};
  return {deps,calls,reads,address};
}

test('execution uses actual deployment, calldata, and post-call physical storage', async () => {
  const m=mock({failed:true,exception:'revert'});
  const r=await executeArtifact(artifact(),{calldata:'0x1234567800'},m.deps);
  assert.equal(m.calls.length,2);
  assert.equal(m.calls[1].to,m.address);
  assert.equal(Buffer.from(m.calls[1].data).toString('hex'),'1234567800');
  assert.deepEqual(m.reads,['0'.repeat(64),'0'.repeat(63)+'1']);
  assert.deepEqual(r.storage,['255','0']);
  assert.equal(r.returnData,'0xdead');
  assert.equal(r.failed,true);
});

test('host failures and invalid inputs cannot become successful observations', async () => {
  await assert.rejects(executeArtifact(artifact(),{},mock({hash:'bad'}).deps),/runtime hash/);
  await assert.rejects(executeArtifact(artifact(),{},mock({deployFailed:true}).deps),/deployment failed/);
  await assert.rejects(executeArtifact(artifact(),{},mock({failed:true,exception:'out of gas'}).deps),/exceptional halt/);
  await assert.rejects(executeArtifact(artifact(),{calldata:'0x1'},mock().deps),/invalid hex/);
  await assert.rejects(executeArtifact(artifact(),{slots:['0','0']},mock().deps),/invalid storage/);
  const a=artifact();a.evm.methodIdentifiers={};
  await assert.rejects(executeArtifact(a,{},mock().deps),/canonical selector/);
});

// Explicit opt-in: unit tests remain usable before the pinned compiler and EVM
// packages are installed. The campaign itself must never skip these dependencies.
test('pinned reference executes storage success and revert rollback', {skip:!process.env.DIFF_YUL_COMPILER}, async () => {
  const compile=await loadCompiler(process.env.DIFF_YUL_COMPILER);
  for (const revert of [false,true]) {
    const source='pragma solidity >=0.8.0; contract Generated { uint256 x; uint256 y; function run() external returns(uint256) { x=7; y=9; '+(revert?'revert();':'return x+y;')+' } }';
    const {artifact}=compileSource(compile,source);
    const actual=await executeArtifact(artifact);
    assert.equal(actual.failed,revert);
    assert.equal(actual.exception,revert?'revert':null);
    assert.equal(actual.returnData,revert?'0x':'0x'+'10'.padStart(64,'0'));
    assert.deepEqual(actual.storage,revert?['0','0']:['7','9']);
  }
});
