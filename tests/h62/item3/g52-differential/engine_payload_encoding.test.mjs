/** Guarded regression: raw payload encoding must preserve SDK header/body
 * bytes and fail changed commitments. A native constructor refusal does not
 * establish VM execution, rollback, reference qualification or Source agreement.
 */
import test from 'node:test';import assert from 'node:assert/strict';
import {createReadStream,readFileSync} from 'node:fs';import {createHash} from 'node:crypto';import {createRequire} from 'node:module';import {pathToFileURL} from 'node:url';
import {encodePayloadForNativeDecode} from '../../../../scripts/h62/item3/g52-differential/engine_payload_encoding.mjs';
import {selectedRecords} from '../../../../scripts/h62/item3/g52-differential/engine_rejection_runner.mjs';
import {EngineXAllocations} from '../../../../scripts/h62/item3/g52-differential/engine_x_allocation.mjs';
import {convertExpectedInvalidEngineFixture} from '../../../../scripts/h62/item3/g52-differential/engine_rejection_reference.mjs';
const h='0x'+'00'.repeat(32);
const item=()=>({newPayloadVersion:4,forkchoiceUpdatedVersion:3,params:[{blockHash:h,transactions:[],withdrawals:[]},[],h,[]]});

test('unsupported versions, RPC errors, blob parameters and missing payload commitments refuse',async()=>{
 for(const mutate of [x=>x.newPayloadVersion=5,x=>x.errorCode='-32602',x=>x.params[1]=[h],x=>delete x.params[0].blockHash,x=>x.params[2]='0x',x=>delete x.params[0].transactions]) {
  const x=item();mutate(x);await assert.rejects(()=>encodePayloadForNativeDecode(x,{}));
 }
});

test('pinned real SDK byte equivalence, constructor refusal and payload commitment mutations',async()=>{
 const bulk=process.env.G52_BULK;if(!bulk)throw new Error('G52_BULK required; never skip');
 const pins={'engine-x-inputs.jsonl.gz':'26117239c2da1b20734ed3f56bac609bc076bdaff535ec69e4e651cb5b4cbdae','engine-x-allocations.jsonl':'452fc176dfd074d9e460887efed298609055e0f2f568728d9edcac69d460a45c','engine-x-allocations-index.json':'7254fcd67e353229b453695e7a353af0633fbffa54938e218cbd65c6c0cbf43b','reference/package-lock.json':'39b1ce55d3978f318323dfbcf1c094b734507d1483e92c586d5e58c8d0e304f4'};
 async function checkPins(){for(const [name,sha] of Object.entries(pins)){const digest=createHash('sha256');for await(const c of createReadStream(bulk+'/'+name))digest.update(c);assert.equal(digest.digest('hex'),sha,name);}}
 await checkPins();
 const require=createRequire(bulk+'/reference/package.json'),loaded=[];
 for(const name of ['@ethereumjs/common','@ethereumjs/block','@ethereumjs/util','micro-eth-signer/kzg.js','@paulmillr/trusted-setups/fast-peerdas.js','@ethereumjs/rlp'])loaded.push(await import(pathToFileURL(require.resolve(name))));
 const m={...loaded[0],...loaded[1],...loaded[2],...loaded[5],kzg:new loaded[3].KZG(loaded[4].trustedSetup)};
 const allocations=new EngineXAllocations(bulk+'/engine-x-allocations.jsonl',JSON.parse(readFileSync(bulk+'/engine-x-allocations-index.json','utf8')));
 try {
  const records=[];for await(const r of selectedRecords(bulk+'/engine-x-inputs.jsonl.gz',[862,877]))records.push(allocations.bind(r).record);
  const [invalid,ordinary]=records;
  const encoded=await encodePayloadForNativeDecode(ordinary.fixture.engineNewPayloads[0],m),existing=await convertExpectedInvalidEngineFixture(ordinary,m);
  assert.equal(encoded.rlp,existing.record.fixture.blocks[0].rlp);assert.equal(encoded.block_hash,existing.binding.payload_block_hashes[0]);
  const request=invalid.fixture.engineNewPayloads[0],saved=structuredClone(request),raw=await encodePayloadForNativeDecode(request,m);
  assert.deepEqual(request,saved);assert.equal(raw.block_hash,request.params[0].blockHash);assert.equal(raw.transactions_validated,false);assert.equal(raw.native_execution_evidence,false);assert.equal(raw.source_matches,0);
  const decoded=m.RLP.decode(m.hexToBytes(raw.rlp));assert.equal(m.bytesToHex(decoded[1][0]),request.params[0].transactions[0]);
  const common=new m.Common({chain:m.Mainnet,hardfork:m.Hardfork.Osaka,customCrypto:{kzg:m.kzg}});
  assert.throws(()=>m.createBlockFromRLP(m.hexToBytes(raw.rlp),{common}),/Transaction gas limit 16777217 exceeds the maximum allowed by EIP-7825 \(16777216\)/);
  for(const mutate of [x=>x.params[0].stateRoot=h,x=>x.params[0].transactions=[],x=>x.params[0].withdrawals=[{index:'0x0',validatorIndex:'0x0',address:'0x'+'11'.repeat(20),amount:'0x1'}],x=>x.params[3]=['0x0001'],x=>x.params[0].blockHash=h,x=>x.params[0].transactions=['0x04c180'],x=>x.params[0].transactions=['0x03c0']]) {
   const changed=structuredClone(request);mutate(changed);await assert.rejects(()=>encodePayloadForNativeDecode(changed,m));
  }
 } finally {allocations.close();}
 await checkPins();
});
