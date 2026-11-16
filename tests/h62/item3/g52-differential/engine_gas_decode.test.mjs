/** Guarded regression: gas-cap labels, forged decode facts and raw transport
 * outside expected-invalid inputs cannot earn rejection credit. Actual SDK
 * construction controls below are not VM executions or production matches.
 */
import test from 'node:test';import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';import {createReadStream,readFileSync} from 'node:fs';import {createRequire} from 'node:module';import {pathToFileURL} from 'node:url';
import {gasLimitDecodeFacts} from '../../../../scripts/h62/item3/g52-differential/blockchain_adapter.mjs';
import {validateDecodeRejection} from '../../../../scripts/h62/item3/g52-differential/engine_rejection_evidence.mjs';
import {classifyBlockRejection} from '../../../../scripts/h62/item3/g52-differential/eest_rejection.mjs';
import {executeEngineFixture} from '../../../../scripts/h62/item3/g52-differential/engine_payload_reference.mjs';
import {convertExpectedInvalidEngineFixture,executeExpectedInvalidEngineFixture} from '../../../../scripts/h62/item3/g52-differential/engine_rejection_reference.mjs';
import {selectedRecords} from '../../../../scripts/h62/item3/g52-differential/engine_rejection_runner.mjs';
import {EngineXAllocations} from '../../../../scripts/h62/item3/g52-differential/engine_x_allocation.mjs';

test('unknown decode families are not supplied gas-cap facts',()=>{
 for(const message of ['host error','Transaction gas limit 1 exceeds the maximum allowed by EIP-7825 (2) extra','Transaction gas limit 01 exceeds the maximum allowed by EIP-7825 (2)'])assert.equal(gasLimitDecodeFacts('0x',message,{},{}),undefined);
});

test('actual SDK decode fact derivation, mutation refusal and negative-only transport',async()=>{
 const bulk=process.env.G52_BULK;if(!bulk)throw new Error('G52_BULK required; never skip');
 const pins={'engine-x-inputs.jsonl.gz':'26117239c2da1b20734ed3f56bac609bc076bdaff535ec69e4e651cb5b4cbdae','engine-x-allocations.jsonl':'452fc176dfd074d9e460887efed298609055e0f2f568728d9edcac69d460a45c','engine-x-allocations-index.json':'7254fcd67e353229b453695e7a353af0633fbffa54938e218cbd65c6c0cbf43b','reference/package-lock.json':'39b1ce55d3978f318323dfbcf1c094b734507d1483e92c586d5e58c8d0e304f4'};
 async function checkPins(){for(const [name,sha] of Object.entries(pins)){const h=createHash('sha256');for await(const c of createReadStream(bulk+'/'+name))h.update(c);assert.equal(h.digest('hex'),sha,name);}}
 await checkPins();
 const require=createRequire(bulk+'/reference/package.json'),loaded=[];
 for(const name of ['@ethereumjs/common','@ethereumjs/block','@ethereumjs/util','@ethereumjs/tx','micro-eth-signer/kzg.js','@paulmillr/trusted-setups/fast-peerdas.js','@ethereumjs/rlp'])loaded.push(await import(pathToFileURL(require.resolve(name))));
 const m={...loaded[0],...loaded[1],...loaded[2],...loaded[3],...loaded[6],kzg:new loaded[4].KZG(loaded[5].trustedSetup)};
 const last=m.Mainnet.hardforks.findIndex(x=>x.name===m.Hardfork.Osaka),hardforks=m.Mainnet.hardforks.slice(0,last+1).map(x=>({name:x.name,block:0}));
 const common=m.createCustomCommon({chainId:1,hardforks},m.Mainnet,{hardfork:m.Hardfork.Osaka,eips:[7934],params:{7934:{maxRlpBlockSize:8388608}},customCrypto:{kzg:m.kzg}});
 const allocations=new EngineXAllocations(bulk+'/engine-x-allocations.jsonl',JSON.parse(readFileSync(bulk+'/engine-x-allocations-index.json','utf8')));
 try {
  let record;for await(const r of selectedRecords(bulk+'/engine-x-inputs.jsonl.gz',[862]))record=allocations.bind(r).record;
  const converted=await convertExpectedInvalidEngineFixture(record,m);assert.deepEqual(converted.binding.raw_payload_indices,[0]);
  const rlp=converted.record.fixture.blocks[0].rlp;let decodeError;try{m.createBlockFromRLP(m.hexToBytes(rlp),{common});}catch(error){decodeError=error;}
  assert.ok(decodeError);const facts=gasLimitDecodeFacts(rlp,decodeError.message,m,common);
  assert.deepEqual(facts,{stage:'decode',transaction_index:0,transactionType:4,gasLimit:'16777217',maximumGasLimit:'16777216',transaction_sha256:createHash('sha256').update(m.hexToBytes(record.fixture.engineNewPayloads[0].params[0].transactions[0])).digest('hex')});
  const root=record.fixture.genesisBlockHeader.stateRoot,head=converted.binding.genesis_hash,expected=record.fixture.engineNewPayloads[0].validationError;
  const r={...classifyBlockRejection(expected,decodeError.message,facts,root,root,head,head),block_index:0,expected_exception:expected,engine_reason:decodeError.message,validation_facts:facts,before_state_root:root,after_state_root:root,before_head:head,after_head:head};
  validateDecodeRejection(r,rlp,decodeError,m,common);
  for(const mutate of [x=>x.validation_facts.transaction_index=1,x=>x.validation_facts.transactionType=0,x=>x.validation_facts.gasLimit='16777216',x=>x.validation_facts.maximumGasLimit='16777217',x=>x.validation_facts.transaction_sha256='0'.repeat(64),x=>x.validation_facts.stage='provider-validation',x=>x.after_head='0x'+'00'.repeat(32),x=>x.actual_categories=[],x=>x.engine_reason='host error']){const bad=structuredClone(r);mutate(bad);assert.throws(()=>validateDecodeRejection(bad,rlp,decodeError,m,common));}
  for(const diagnostic of [decodeError.message.replace('16777217','16777218'),decodeError.message.replace('16777216','16777215')])assert.throws(()=>gasLimitDecodeFacts(rlp,diagnostic,m,common));
  let calls=0;const noWorker=async()=>{calls++;throw new Error('must not execute');};
  const normalized=structuredClone(record);delete normalized.fixture.engineNewPayloads[0].validationError;
  assert.equal((await executeEngineFixture(normalized,m,noWorker)).status,'engine_error');assert.equal(calls,0);
  const other=structuredClone(record);other.fixture.engineNewPayloads[0].validationError='TransactionException.SENDER_NOT_EOA';
  assert.equal((await executeExpectedInvalidEngineFixture(other,m,noWorker)).status,'engine_error');assert.equal(calls,0);
 } finally {allocations.close();}
 await checkPins();
});
