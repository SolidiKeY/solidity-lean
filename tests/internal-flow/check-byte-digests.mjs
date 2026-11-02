// Host-only candidate controls, never authentication receipts.
import * as fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {exactByteDigests} from './exact-byte-digest.mjs';
const sha=b=>createHash('sha256').update(b).digest('hex');
let cases=0;
const check=(memo,path,bytes)=>{assert.equal(memo.digest(path,bytes),sha(bytes));cases++;};
const memo=exactByteDigests(16),a=Buffer.from('old!');
check(memo,'same',a);check(memo,'same',Buffer.from(a));assert.equal(memo.stats.hits,1);
// Mutation of the original buffer cannot mutate the retained private copy.
a.fill(0);check(memo,'same',Buffer.from('old!'));check(memo,'same',a);
// Identical size and nominal timestamp are deliberately irrelevant inputs.
for(const value of ['new!','old!','new!'])check(memo,'same',Buffer.from(value));
check(memo,'other',Buffer.from('old!'));check(memo,'empty',Buffer.alloc(0));
// Oversized objects bypass retention; eviction only causes original hashing.
for(let i=0;i<12;i++)check(memo,'path'+i,Buffer.alloc(8,i));
assert(memo.stats.evictions>0);assert(memo.stats.peak<=16);
check(memo,'large',Buffer.alloc(17,1));check(memo,'large',Buffer.alloc(17,2));
const oldHits=memo.stats.hits;memo.clear();check(memo,'same',Buffer.from('new!'));assert.equal(memo.stats.hits,oldHits);
const fresh=exactByteDigests(16);check(fresh,'same',Buffer.from('new!'));assert.equal(fresh.stats.hits,0);
for(const limit of [-1,NaN,Infinity,1.5])assert.throws(()=>exactByteDigests(limit));
for(const bytes of ['text',null,{},new Uint8Array(4)])assert.throws(()=>memo.digest('path',bytes));
assert.throws(()=>memo.digest(null,Buffer.alloc(1)));
// Malformed bytes are hashed exactly; parsing/report rejection remains external.
for(const bytes of [Buffer.from('{bad'),Buffer.from([0,255,128]),Buffer.alloc(0)])check(memo,'malformed',bytes);
const dir=fs.mkdtempSync(path.join(os.tmpdir(),'v12-byte-control-'));
try {
 const file=path.join(dir,'object'),time=new Date(1700000000000);fs.writeFileSync(file,'aaaa');fs.utimesSync(file,time,time);
 const m=exactByteDigests(16),first=fs.readFileSync(file),old=m.digest(file,first),stamp=fs.statSync(file).mtimeMs;
 fs.writeFileSync(file,'bbbb');fs.utimesSync(file,time,time);assert.equal(fs.statSync(file).mtimeMs,stamp);
 const changed=fs.readFileSync(file);assert.notEqual(m.digest(file,changed),old);check(m,file,changed);
 const independent=exactByteDigests(16);check(independent,file,fs.readFileSync(file));assert.equal(independent.stats.hits,0);
} finally {fs.rmSync(dir,{recursive:true});}
const tiny=exactByteDigests(0,2);for(let i=0;i<8;i++)check(tiny,'zero'+i,Buffer.alloc(0));assert.equal(tiny.stats.evictions,6);
console.log(JSON.stringify({host_only:true,cases,private_copy:true,same_size_mutation:true,eviction:true,invocation_reset:true,malformed_exact_bytes:true,stats:memo.stats}));
