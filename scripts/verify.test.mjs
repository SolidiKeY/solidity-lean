import test from 'node:test';
import assert from 'node:assert/strict';
import {parseVerify,main} from './verify.mjs';
import {decodeNative} from './verify-native.mjs';
const request={sourceId:7,function:'f'};
const row={sourceId:7,function:'f',reading:'solc',verification:'direct',status:'proved'};
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
  for(const change of [{sourceId:8},{function:'other'},{reading:'clean'},{verification:'certified'},{status:'refused'}])
    assert.throws(()=>decodeNative(protocol({...row,...change}),[request]),/protocol/);
  assert.throws(()=>decodeNative(protocol({...row,status:'refuted'}),[request]),/witness/);
  assert.throws(()=>decodeNative(protocol({...row,status:'refuted',counterexample:{certified:true}}),[request]),/witness/);
  assert.throws(()=>decodeNative(protocol(row)+protocol(row),[request]),/responses/);
  assert.throws(()=>decodeNative(JSON.stringify({ready:true})+'\n',[request]),/responses/);
  assert.throws(()=>decodeNative(JSON.stringify({ready:true})+'\n'+JSON.stringify({gap:'unknown syntax'}),[request]),/unsupported/);
});

import {differential} from './verify-differential.mjs';
const listed={source:'case.sol',sourceHash:'a'.repeat(64),contract:'C',sourceId:7,function:'f',reading:'solc',status:'ready'};
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
