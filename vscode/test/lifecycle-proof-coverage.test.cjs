// Status protocol controls, not a native execution or row judgment.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),{createHash}=require('node:crypto');
const {phaseProof,waitForPhase,waitForMigration}=require('../parity/lifecycle-trace.cjs'),{initial,expectedDeclarations}=require('../parity/configuration-lifecycle.cjs');
function fixture(){const text=initial+'\nmethod Marker2() {}\n',binding={uri:'file:///lifecycle.dfy',version:2,text,sourceHash:createHash('sha256').update(text).digest('hex')};return{binding,packet:{uri:binding.uri,version:2,namedVerifiables:expectedDeclarations(binding).map(d=>({nameRange:d.nameRange,status:5}))}};}
test('baseline lifecycle requires Check and every fixture declaration at exact ranges',()=>{
 const {binding,packet}=fixture();assert.equal(phaseProof([packet],binding,5),true);
 for(const change of [p=>p.namedVerifiables.shift(),p=>p.namedVerifiables.pop(),p=>p.namedVerifiables[0].nameRange.start.character++,p=>p.namedVerifiables.push(structuredClone(p.namedVerifiables[0])),p=>p.uri='file:///foreign.dfy',p=>p.version++,p=>p.sourceHash='foreign']){const p=structuredClone(packet);change(p);assert.equal(phaseProof([p],binding,5),false);}
 const corrupt={...binding,text:binding.text+'// changed'};assert.equal(phaseProof([packet],corrupt,5),false);
});
test('a failed marker cannot replace the expected failed Check declaration',()=>{
 const {binding,packet}=fixture();packet.namedVerifiables[1].status=4;assert.equal(phaseProof([packet],binding,4),false);packet.namedVerifiables[1].status=5;packet.namedVerifiables[0].status=4;assert.equal(phaseProof([packet],binding,4),true);
 assert.equal(phaseProof([],binding,5),false);assert.equal(phaseProof([{uri:binding.uri,version:2,namedVerifiables:[]}],binding,5),false);
});

test('baseline lifecycle rejects late proof and retained proof after server closure',async()=>{
 const {binding,packet}=fixture();
 for(const where of ['predicate','sleep']){let clock=0,reads=0;const states=where==='predicate'?{some(fn){clock=60000;return fn(packet);}}:[];
  await assert.rejects(waitForPhase({states,diagnostics:[],binding,status:5,peer:{closed:false},now:()=>clock,sleep:async()=>{reads++;clock=60000;states.push(packet);}}),e=>e.code==='TIMEOUT');if(where==='sleep')assert.equal(reads,1);
 }
 await assert.rejects(waitForPhase({states:[packet],diagnostics:[],binding,status:5,peer:{closed:true}}),/Server closed/);
});
test('baseline broken-proof diagnostic shares the original proof deadline',async()=>{
 const {binding,packet}=fixture();packet.namedVerifiables[0].status=4;let clock=0,proof=false;const states={some(fn){proof=true;clock=59999;return fn(packet);}},diagnostics=[];
 await assert.rejects(waitForPhase({states,diagnostics,binding,status:4,peer:{closed:false},now:()=>clock,sleep:async()=>{assert.equal(proof,true);clock=60000;diagnostics.push({uri:binding.uri,version:binding.version,diagnostics:[{severity:1}]});}}),e=>e.code==='TIMEOUT');
 clock=0;await waitForPhase({states:[packet],diagnostics,binding,status:4,peer:{closed:false},now:()=>clock,sleep:async()=>{throw Error('No wait expected');}});
});

test('migration wait refuses late predicates, late wakeups and closed peers at the original bound',async()=>{
 for(const mode of ['predicate','wakeup','closed']){let clock=0,ready=mode!=='wakeup',sleeps=0;
  await assert.rejects(waitForMigration(()=>{if(mode==='predicate')clock=60000;return ready;},'migration control',{peer:{closed:mode==='closed'},now:()=>clock,sleep:async()=>{sleeps++;clock=60000;ready=true;}}),e=>mode==='closed'?/Server closed/.test(e.message):e.code==='TIMEOUT');if(mode==='wakeup')assert.equal(sleeps,1);
 }
});
test('migration wait accepts timely predicates and preserves original predicate failures',async()=>{
 const peer={closed:false};await waitForMigration(()=>true,'ready',{peer,now:()=>0,sleep:async()=>{throw Error('Unexpected wait');}});
 const failure=Error('actual source predicate failure');await assert.rejects(waitForMigration(()=>{throw failure;},'failure',{peer,now:()=>0}),e=>e===failure);
});
