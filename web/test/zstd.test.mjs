import test from 'node:test';
import assert from 'node:assert/strict';
import {randomBytes} from 'node:crypto';
import {zstdCompressSync} from 'node:zlib';
import {prepareZstd,inflateZstd} from '../browser/zstd.mjs';

const runtime=await prepareZstd();
test('Wasm Zstandard decoder matches native compression and bounds retained memory',()=>{
  for(const raw of [Buffer.alloc(0),Buffer.from('Lean proof libraries'),randomBytes(2500000),Buffer.alloc(40*1024*1024,42)]){
    const compressed=zstdCompressSync(raw);assert.deepEqual(Buffer.from(inflateZstd(compressed,raw.length)),raw);
  }
  assert.ok(runtime.memory.buffer.byteLength<128*1024*1024);
});
test('corrupt, truncated, trailing and wrongly sized Zstandard frames fail closed',()=>{
  const raw=randomBytes(100000),compressed=zstdCompressSync(raw);
  for(const broken of [compressed.subarray(0,-5),Buffer.concat([compressed,Buffer.from([1])]),Buffer.from('invalid')])assert.throws(()=>inflateZstd(broken,raw.length),/Zstandard/);
  assert.throws(()=>inflateZstd(compressed,raw.length-1),/Zstandard/);
  assert.throws(()=>inflateZstd(compressed,raw.length+1),/Zstandard/);
  assert.throws(()=>inflateZstd(Buffer.from('invalid'),0),/Zstandard/);
  assert.throws(()=>inflateZstd(compressed,Number.MAX_SAFE_INTEGER),/Zstandard/);
});
