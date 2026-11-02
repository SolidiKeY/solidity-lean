import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {randomBytes} from 'node:crypto';
import {brotliCompressSync,constants} from 'node:zlib';
import {prepareBrotli,inflateBrotli} from '../browser/brotli.mjs';

const runtime=prepareBrotli(readFileSync(new URL('../node_modules/brotli-dec-wasm/pkg/brotli_dec_wasm_bg.wasm',import.meta.url)));
const compress=raw=>brotliCompressSync(raw,{params:{[constants.BROTLI_PARAM_QUALITY]:5}});
test('streamed decoder matches native Brotli across input/output boundaries',()=>{
  for(const bytes of [Buffer.alloc(0),Buffer.from('Lean proof libraries'),randomBytes(2500000),Buffer.alloc(40*1024*1024,42)]){
    const encoded=compress(bytes);
    assert.deepEqual(Buffer.from(inflateBrotli(encoded,bytes.length)),bytes);
    assert.deepEqual(Buffer.from(inflateBrotli(encoded)),bytes);
  }
  assert.ok(runtime.memory.buffer.byteLength<64*1024*1024,'a large output must not remain in decoder linear memory');
});
test('truncated, trailing and incorrectly sized streams are rejected',()=>{
  const bytes=randomBytes(100000),encoded=compress(bytes);
  assert.throws(()=>inflateBrotli(encoded.subarray(0,-5)),/Truncated|Brotli|decoder/i);
  assert.throws(()=>inflateBrotli(Buffer.concat([encoded,Buffer.from([1])])),/Trailing/);
  assert.throws(()=>inflateBrotli(encoded,bytes.length-1),/declared size/);
  assert.throws(()=>inflateBrotli(encoded,bytes.length+1),/Invalid.*size/);
});
