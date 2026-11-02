import test from 'node:test';
import assert from 'node:assert/strict';
import {createHash,randomBytes} from 'node:crypto';
import vm from 'node:vm';
import {build} from 'esbuild';

test('browser SHA-256 bundle works without Web Crypto, Buffer or external fetches',async()=>{
  const {outputFiles}=await build({stdin:{contents:"import {createSHA256} from 'hash-wasm'; globalThis.ready=createSHA256();",resolveDir:new URL('../',import.meta.url).pathname},bundle:true,write:false,format:'iife',platform:'browser',target:'es2022'});
  const context=vm.createContext({WebAssembly,TextEncoder,Uint8Array,ArrayBuffer});
  vm.runInContext(outputFiles[0].text,context);const hasher=await context.ready;
  for(const bytes of [Buffer.alloc(0),Buffer.from('abc'),randomBytes(1000000),Buffer.alloc(32*1024*1024,42)]){
    const expected=createHash('sha256').update(bytes).digest('hex');
    assert.equal(hasher.init().update(bytes).digest('hex'),expected);
    hasher.init();for(let i=0;i<bytes.length;i+=65537)hasher.update(bytes.subarray(i,i+65537));
    assert.equal(hasher.digest('hex'),expected);
  }
});
