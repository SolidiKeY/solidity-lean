import test from 'node:test';
import assert from 'node:assert/strict';
import { comparePost, validateConfig, guardedResult } from '../../../../scripts/h62/item3/g52-differential/eest_observation.mjs';
const zero='0x'+'00'.repeat(32), one='0x'+'00'.repeat(31)+'01';
test('post-state and log hash controls reject each changed observation',()=>{
  const expected={state_root:zero,logs_hash:zero};
  assert.deepEqual(comparePost(expected,expected),[]);
  for(const key of ['state_root','logs_hash']) assert.deepEqual(comparePost(expected,{...expected,[key]:one}),[key]);
  assert.throws(()=>comparePost(expected,{...expected,state_root:'0x00'}),/invalid/);
});
test('fork configuration controls preserve all pinned blob parameters',()=>{
  const config={chainid:'0x1',blobSchedule:{Cancun:{target:'0x3',max:'0x6',baseFeeUpdateFraction:'0x32f0ed'},Prague:{target:'0x6',max:'0x9',baseFeeUpdateFraction:'0x4c6964'},Osaka:{target:'0x6',max:'0x9',baseFeeUpdateFraction:'0x4c6964'}}};
  assert.equal(validateConfig(config),true);
  for(const field of ['target','max','baseFeeUpdateFraction']){
    const changed=structuredClone(config);changed.blobSchedule.Osaka[field]='0x0';assert.equal(validateConfig(changed),false);
  }
  assert.equal(validateConfig({...config,chainid:'0x2'}),false);
});

test('queued success cannot override a requested resource stop',()=>{
 const success={status:'reference_match'};
 assert.equal(guardedResult(success,undefined),success);
 for(const reason of ['host-memory-guard','host-timeout-60000ms']) assert.deepEqual(guardedResult(success,reason),{status:'unsupported',reason});
});
