// HOST-ONLY candidate. Never skips a fresh read; no state survives the owner invocation.
import {createHash} from 'node:crypto';
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
