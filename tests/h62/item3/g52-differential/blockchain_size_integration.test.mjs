/** Guarded regression: omitting validateBlockSize must not silently disable Osaka EIP-7934 validation. Synthetic serialization-size probe only; no fixture match count. */
import test from 'node:test';import assert from 'node:assert/strict';import {createReadStream} from 'node:fs';import {createGunzip} from 'node:zlib';import {createInterface} from 'node:readline';import {createRequire} from 'node:module';import {pathToFileURL} from 'node:url';
import {executeBlockchain} from '../../../../scripts/h62/item3/g52-differential/blockchain_adapter.mjs';
test('real block-size validator rejects limit-plus-one serialization',{timeout:65000},async()=>{
 const bulk=process.env.G52_BULK;if(!bulk)throw new Error('G52_BULK required; never skip');
 const require=createRequire(bulk+'/reference/package.json');const loaded=[];
 for(const name of ['@ethereumjs/vm','@ethereumjs/common','@ethereumjs/util','@ethereumjs/tx','@ethereumjs/block','@ethereumjs/rlp','ethers','micro-eth-signer/kzg.js','@paulmillr/trusted-setups/fast-peerdas.js','@ethereumjs/blockchain'])loaded.push(await import(pathToFileURL(require.resolve(name)).href));
 const [vm,common,util,tx,block,rlp,ethers,kzgLibrary,setup,chain]=loaded;
 const modules={...chain,...vm,...common,...util,...tx,...block,RLP:rlp.RLP,keccak256:ethers.keccak256,kzg:new kzgLibrary.KZG(setup.trustedSetup)};
 const source=createReadStream(bulk+'/blockchain-inputs.jsonl.gz').pipe(createGunzip());const lines=createInterface({input:source,crlfDelay:Infinity});let record;for await(const line of lines){record=JSON.parse(line);break;}lines.close();source.destroy();
 const original=block.Block.prototype.serialize;
 block.Block.prototype.serialize=function(){return this.header.number>0n?new Uint8Array(Number(this.common.param('maxRlpBlockSize'))+1):Reflect.apply(original,this,[]);};
 try{await assert.rejects(()=>executeBlockchain(record,modules,{steps:0}),error=>{assert.match(error.message,/Block size exceeds maximum RLP block size limit/);assert.match(error.stack,/Block.validateData/);return true;});}
 finally{block.Block.prototype.serialize=original;}
});
