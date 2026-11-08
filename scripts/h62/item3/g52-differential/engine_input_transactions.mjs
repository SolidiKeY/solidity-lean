/** Guarded regression: transaction observations must identify exact pinned input
 * bytes, not hashes/types/gas limits asserted only by a result artifact.
 * Pure native transaction decoding/hashing; no EVM execution or fixture passes.
 */
import {readFileSync} from 'node:fs';import {createRequire} from 'node:module';
import {pathToFileURL} from 'node:url';import {resolve} from 'node:path';
const bulk=process.argv[2];if(!bulk)throw new Error('bulk required');const require=createRequire(resolve(bulk,'reference/package.json'));
const loaded=[];for(const name of ['@ethereumjs/common','@ethereumjs/tx','@ethereumjs/util','micro-eth-signer/kzg.js','@paulmillr/trusted-setups/fast-peerdas.js'])loaded.push(await import(pathToFileURL(require.resolve(name)).href));
const {Common,Mainnet,Hardfork}=loaded[0],{createTxFromRLP}=loaded[1],{hexToBytes,bytesToHex}=loaded[2];
const kzg=new loaded[3].KZG(loaded[4].trustedSetup);
const inputs=JSON.parse(readFileSync(0,'utf8'));if(!Array.isArray(inputs))throw new Error('transaction input array required');
const output=inputs.map(raw=>{try{
 if(typeof raw!=='string'||!/^0x(?:[0-9a-f]{2})+$/.test(raw))throw new Error('input transaction encoding');
 const common=new Common({chain:Mainnet,hardfork:Hardfork.Osaka,customCrypto:{kzg}});const tx=createTxFromRLP(hexToBytes(raw),{common});
 if(bytesToHex(tx.serialize())!==raw)throw new Error('noncanonical input transaction');
 return {hash:bytesToHex(tx.hash()),type:tx.type,gas_limit:tx.gasLimit.toString()};
 }catch{return null;}});
process.stdout.write(JSON.stringify(output)+'\n');
