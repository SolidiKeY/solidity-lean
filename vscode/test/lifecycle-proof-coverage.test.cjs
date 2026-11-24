// Status protocol controls, not a native execution or row judgment.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),{createHash}=require('node:crypto');
const {phaseProof}=require('../parity/lifecycle-trace.cjs'),{initial,expectedDeclarations}=require('../parity/configuration-lifecycle.cjs');
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
