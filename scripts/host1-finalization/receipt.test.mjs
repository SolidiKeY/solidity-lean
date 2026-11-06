import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {resolve} from 'node:path';
import {createFinalizationSession,validateFinalizedMessage,verifyEngine,CALLER} from './index.mjs';
const A='0x'+'00'.repeat(18)+'0abc',B='0x'+'00'.repeat(18)+'beef',W=n=>'0x'+BigInt(n).toString(16).padStart(64,'0');
const seed=(address,code,balance=1n,nonce=1n,storage={})=>({address,code,balance,nonce,storage});
const req={id:'reader',kind:'call',to:A,data:'0x',value:0n};
let original;
test('actual serialized baseline retains all required evidence',async()=>{const s=await createFinalizationSession({seeds:[seed(A,'0x602a5f5500')],watch:[{address:A,persistent:[],transient:[W(99)]}]}),r=await s.execute(req);validateFinalizedMessage(r,req,0);original=JSON.parse(JSON.stringify(r));});
const mutants=[
 ['missing snapshot',r=>delete r.messagePost],['missing frames',r=>r.frames=[]],['reordered enter/exit',r=>r.trace.reverse()],
 ['duplicate frame',r=>r.frames.push(r.frames[0])],['wrong context',r=>r.frames[0].caller=B],['wrong code owner',r=>r.frames[0].codeAddress=B],['wrong delegate flag',r=>r.frames[0].delegatecall=true],
 ['wrong request',r=>r.request.id='other'],['stale ordinal',r=>r.ordinal++],['wrong pin',r=>r.engine.inputSha256='0'.repeat(64)],['false runTx',r=>r.environment.transactionEnvelope=true],['changed fork',r=>r.environment.hardfork='cancun'],['changed step budget',r=>r.environment.stepLimit++],
 ['missing return buffer',r=>delete r.frames[0].lastCallReturnData],['missing full bytes',r=>delete r.message.bytes],['wrong result bytes',r=>r.message.bytes='0xdead'],['false memory',r=>r.frames[0].memory.bytes='0x00'],
 ['unknown final action',r=>r.finalization.actions[0].kind='cleanEverything'],['reordered final actions',r=>r.finalization.actions.reverse()],['missing commit',r=>r.finalization.actions.pop()],['transient retained',r=>r.post[A].transient[W(99)]=W(1)],
 ['unknown API op',r=>r.operations[0].kind='fake.putStorage'],['missing ops',r=>delete r.operations],['impossible stack',r=>r.message.metrics.maxStack=1025],
 ['post-final balance changed',r=>r.post[A].balance='123'],['post-final nonce changed',r=>r.post[A].nonce='7'],['post-final storage changed',r=>r.post[A].persistent[W(0)]=W(9)],
 ['root/frame post disagreement',r=>r.frames[0].post[A].balance='123'],
 ['coordinated erased domain slot',r=>{r.domain.find(d=>d.address===A).persistent=[];for(const w of [r.pre,r.messagePost,r.post,...r.frames.flatMap(f=>[f.pre,f.post])])delete w[A].persistent[W(0)];}],
 ['disowned slot op',r=>{const o=r.operations.find(o=>o.kind==='putStorage');o.address=B;}],
 ['tagless message slot access',r=>{r.operations.find(o=>o.kind==='putStorage').frame=null;}],
 ];
for(const [name,change]of mutants)test(name,()=>{const r=structuredClone(original);change(r);assert.throws(()=>validateFinalizedMessage(r,req,0));});
test('wrong nonempty payload, unchanged length cannot mask byte mismatch',async()=>{const s=await createFinalizationSession({seeds:[seed(A,'0x63deadbeef5f526004601cfd')]}),q={...req,id:'bytes'},r=await s.execute(q);validateFinalizedMessage(r,q,0);const bad=structuredClone(r);bad.frames[0].output.bytes='0xaabbccdd';assert.throws(()=>validateFinalizedMessage(bad,q,0));});
test('coordinated deletion of nested frame account/slot is refused',async()=>{
 const code='0x5f5f5f5f73'+B.slice(2)+'61c350f45000',s=await createFinalizationSession({seeds:[seed(A,code),seed(B,'0x602a5f5500')]}),q={...req,id:'nested'},r=await s.execute(q);validateFinalizedMessage(r,q,0);
 for(const erase of [x=>{delete x.frames[1].pre[A];delete x.frames[1].post[A];},x=>{delete x.frames[1].pre[A].persistent[W(0)];delete x.frames[1].post[A].persistent[W(0)];}]){const bad=structuredClone(r);erase(bad);assert.throws(()=>validateFinalizedMessage(bad,q,0));}
});
test('direct and transitive runtime/source corruption fail the pin guard',()=>{for(const path of ['scripts/evm-reference/replay.mjs','scripts/evm-reference/node_modules/@ethereumjs/evm/dist/esm/opcodes/functions.js','scripts/evm-reference/node_modules/@noble/hashes/sha3.js'])assert.throws(()=>verifyEngine(p=>p===path?Buffer.from('drift'):readFileSync(resolve('/workspace/vy5-help-20261102',p))));});
test('unknown session configuration never changes defaults',async()=>{await assert.rejects(createFinalizationSession({stepLimit:1}));await assert.rejects(createFinalizationSession({gasLimit:1}));});

test('CREATE result cannot be reassigned to another observed account',async()=>{
 const s=await createFinalizationSession({seeds:[seed(B,'0x',1n,0n)]}),q={id:'created-binding',kind:'create',data:'0x60006000f3',value:0n},r=await s.execute(q);validateFinalizedMessage(r,q,0);
 const bad=structuredClone(r);bad.message.createdAddress=B;bad.frames[0].createdAddress=B;assert.throws(()=>validateFinalizedMessage(bad,q,0));
});
test('transient image/value and actual clear API are bound to the captured state',async()=>{
 const s=await createFinalizationSession({seeds:[seed(A,'0x60115f5d00')]}),q={...req,id:'transient-evidence'},r=await s.execute(q);validateFinalizedMessage(r,q,0);
 for(const mutate of [x=>{x.finalization.transientBefore[A]={[W(0)]:'0x11'};},x=>{x.messagePost[A].transient[W(0)]=W(17);x.frames[0].post[A].transient[W(0)]=W(17);x.finalization.transientBefore={};},x=>{x.operations=x.operations.filter(o=>!(o.phase==='finalization'&&o.kind==='transient.clear'));x.operations.forEach((o,i)=>o.ordinal=i);}]){const bad=structuredClone(r);mutate(bad);assert.throws(()=>validateFinalizedMessage(bad,q,0));}
});
