import {createSHA256} from 'hash-wasm';
let fallback;
export async function digest(bytes){
  if(globalThis.crypto?.subtle)return Array.from(new Uint8Array(await crypto.subtle.digest('SHA-256',bytes)),b=>b.toString(16).padStart(2,'0')).join('');
  const hash=await(fallback??=createSHA256());
  return hash.init().update(new Uint8Array(bytes)).digest('hex');
}
