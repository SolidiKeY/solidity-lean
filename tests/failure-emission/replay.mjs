// Optional pinned Osaka replay of actual Backend.encode fixtures. No Lean proof.
import assert from 'node:assert/strict';
import fs from 'node:fs';
import {createHash} from 'node:crypto';
import {fileURLToPath} from 'node:url';
import {createEVM} from '@ethereumjs/evm';
import {Common,Mainnet,Hardfork} from '@ethereumjs/common';
import {keccak_256} from '@noble/hashes/sha3.js';
const sha=b=>createHash('sha256').update(b).digest('hex');
const word=n=>BigInt(n).toString(16).padStart(64,'0');
const hex=b=>Buffer.from(b).toString('hex');
const boom='626f6f6d';
const errorBody=(len,data,pad)=>'08c379a0'+word(32)+word(len)+data+'00'.repeat(pad);
const seq=Array.from({length:65},(_,i)=>i);
const custom=hex(keccak_256(new TextEncoder().encode('Denied(uint256)')).slice(0,4))+word(7);
// These finite expected payloads are independently stated from standard ABI
// layouts; this is emission agreement, not generic ABI coverage or a bridge proof.
const expected=new Map([
 ['empty_revert',{data:'',kind:'revert'}],['empty_return',{data:'',kind:'success'}],
 ['panic01',{data:'4e487b71'+word(1),kind:'revert'}],
 ['panic12',{data:'4e487b71'+word(0x12),kind:'revert'}],
 ['error_boom',{data:errorBody(4,boom,28),kind:'revert'}],
 ['error33',{data:errorBody(33,'78'.repeat(33),31),kind:'revert'}],
 ['custom_denied',{data:custom,kind:'revert'}],
 ['raw_boundary65',{data:hex(seq),kind:'revert'}],
 ['return_boundary65',{data:hex(seq),kind:'success'}],
 ['suffix_ignored',{data:'010203',kind:'success'}],
 ['stack1022',{data:'',kind:'revert'}],['stack1023',{data:'',kind:'stack overflow'}],
]);
const vectorPath=process.argv[2];assert(vectorPath,'vector path required');
const raw=fs.readFileSync(vectorPath);const vectors=JSON.parse(raw);
assert.equal(vectors.length,expected.size);const seen=new Set();const rows=[];
for(const v of vectors){
 const e=expected.get(v.name);assert(e,`unknown vector ${v.name}`);assert(!seen.has(v.name));seen.add(v.name);
 assert.equal(hex(v.payload),e.data,`${v.name}: existing source payload disagrees with finite ABI fixture`);
 assert(v.code.every(b=>Number.isInteger(b)&&b>=0&&b<=255));
 const evm=await createEVM({common:new Common({chain:Mainnet,hardfork:Hardfork.Osaka})});
 let steps=0,maxStack=0;
 evm.events.on('step',s=>{steps++;maxStack=Math.max(maxStack,s.stack.length);if(steps>5_000_000)throw Error('HOST_BUDGET_BLOCKED');});
 const result=await evm.runCode({code:Uint8Array.from(v.code),gasLimit:100_000_000n});
 const exception=result.exceptionError?.error??null;
 const kind=exception??'success';
 assert.equal(kind,e.kind,`${v.name}: outcome kind`);
 assert.equal(hex(result.returnValue),e.data,`${v.name}: exact output bytes`);
 const stack=result.runState.stack.getStack();
 const tail=e.kind==='stack overflow'?1024:v.tailWords;
 assert.equal(stack.length,tail,`${v.name}: retained stack length`);
 assert(stack.every(x=>x===0n),`${v.name}: immutable zero stack tail`);
 assert.equal(maxStack,e.kind==='stack overflow'?1024:v.tailWords+2,`${v.name}: intermediate stack bound`);
 if(v.offset>0)assert.equal(result.runState.memory.read(v.offset-1,1)[0],0x55,`${v.name}: before-memory frame`);
 assert.equal(result.runState.memory.read(v.offset+v.payload.length,1)[0],0x77,`${v.name}: after-memory frame`);
 rows.push({name:v.name,status:'pass',kind,exception,outputHex:hex(result.returnValue),codeSha256:sha(Uint8Array.from(v.code)),codeBytes:v.code.length,steps,maxStack,retainedStackWords:stack.length,frameBefore:v.offset>0?'55':null,frameAfter:'77'});
}
const lock=JSON.parse(fs.readFileSync(new URL('package-lock.json',import.meta.url)));
console.log(JSON.stringify({status:'pass',fork:'Osaka',gasLimit:'100000000',hostStepLimit:5000000,node:process.version,
 versions:Object.fromEntries(['@ethereumjs/evm','@ethereumjs/common','@ethereumjs/util','@noble/hashes'].map(n=>[n,lock.packages['node_modules/'+n].version])),
 vectorSha256:sha(raw),runnerSha256:sha(fs.readFileSync(fileURLToPath(import.meta.url))),lockSha256:sha(fs.readFileSync(new URL('package-lock.json',import.meta.url))),rows}));
