// Exact-byte reuse. Every caller must supply a freshly read complete Buffer.
// No state survives an explicitly owned preflight/postflight phase.
import {createHash} from 'node:crypto';
import {readFileSync} from 'node:fs';
import {setFlagsFromString} from 'node:v8';
import {runInNewContext} from 'node:vm';
export function exactByteDigests(limit, maxEntries=4096) {
 if (!Number.isSafeInteger(limit) || limit < 0) throw Error('invalid byte limit');
 if(!Number.isSafeInteger(maxEntries)||maxEntries<1)throw Error('invalid entry limit');
 const entries=new Map(); let retained=0;
 const stats={hits:0,misses:0,compared:0,hashed:0,evictions:0,peak:0};
 return {stats, digest(path,bytes) {
  if(typeof path!=='string'||!Buffer.isBuffer(bytes))throw Error('expected exact path and fresh Buffer');
  const old=entries.get(path);
  if(old){stats.compared+=bytes.length;if(old.bytes.equals(bytes)){stats.hits++;entries.delete(path);entries.set(path,old);return old.digest;}
   retained-=old.bytes.length;entries.delete(path);}
  stats.misses++;stats.hashed+=bytes.length;
  const digest=createHash('sha256').update(bytes).digest('hex');
  if(bytes.length<=limit){
   while(retained+bytes.length>limit || entries.size>=maxEntries){const first=entries.keys().next().value;retained-=entries.get(first).bytes.length;entries.delete(first);stats.evictions++;}
   // Private immutable-by-construction copy, never exposed to the reader.
   const copy=Buffer.from(bytes);entries.set(path,{bytes:copy,digest});retained+=copy.length;stats.peak=Math.max(stats.peak,retained);
  }
  return digest;
 }, clear(){entries.clear();retained=0;}};
}

// Keep the ordinary read point even on a hit. Never memoize toolchain/source,
// config/guard/manifests here; their original byte/read boundaries are unchanged.
export function freshObjectDigest(path, owner=null) {
 const bytes=readFileSync(path);
 return owner ? owner.digest(path,bytes) : createHash('sha256').update(bytes).digest('hex');
}
let collect;
function collectReleasedBytes() {
 // No CLI argument/child flag changes. Synchronous major collection is required
 // before the phase returns, NOT left to memory pressure during the Lean child.
 if(!collect) {
  setFlagsFromString('--expose_gc');
  try { collect=runInNewContext('gc'); } finally { setFlagsFromString('--no-expose_gc'); }
 }
 collect({execution:'sync',type:'major'});
}
export async function withObjectDigests(work, observe=()=>{}) {
 const memo=exactByteDigests(512*1024*1024,4096);let open=true;
 const owner={digest(path,bytes){if(!open)throw Error('closed object digest phase');return memo.digest(path,bytes);}};
 const before=process.memoryUsage();
 try { return await work(owner); }
 finally {
  open=false;memo.clear();collectReleasedBytes();
  observe({closed:true,retained_payload_bytes:0,stats:{...memo.stats},before,after:process.memoryUsage()});
 }
}
