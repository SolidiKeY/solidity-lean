import {test} from 'node:test';
import assert from 'node:assert/strict';
import {generate,assemble,random} from './generate.mjs';
test('seed replay and differing seeds',()=>{assert.deepEqual(generate(42,20),generate(42,20));assert.notDeepEqual(generate(42,20),generate(43,20));});
test('assembled branches point at actual JUMPDEST bytes',()=>{for(const r of generate(1128,100)){const code=Buffer.from(assemble(r),'hex');let pc=0;while(pc<code.length){const op=code[pc++];if(op>=0x60&&op<=0x7f){const n=op-0x5f;if(op===0x61){const target=code.readUInt16BE(pc);assert.equal(code[target],0x5b);}pc+=n;}}}});
test('invalid generator inputs and unresolved targets fail closed',()=>{assert.throws(()=>random(-1));assert.throws(()=>generate(1,0));assert.throws(()=>assemble({instructions:[{op:'JUMP',target:'absent'}]}));assert.throws(()=>assemble({instructions:[{op:'PUSH',value:'-1'}]}));});

test('choices cover both branches, unary operations and memory overlap',()=>{const branches=new Set(),unary=new Set(),stores=new Set(),loads=new Set();for(const r of generate(1128,1000)){r.instructions.forEach((i,j)=>{if(i.op==='JUMPI')branches.add(r.instructions[j-1].value);if(['NOT','ISZERO'].includes(i.op))unary.add(i.op);if(i.op==='MSTORE')stores.add(r.instructions[j-1].value);if(i.op==='MLOAD')loads.add(r.instructions[j-1].value);});}assert.deepEqual([...branches].sort(),['0','1']);assert.equal(unary.size,2);assert.equal(stores.size,4);assert.equal(loads.size,4);});
test('prototype names are not opcodes',()=>{for(const op of ['constructor','toString','__proto__'])assert.throws(()=>assemble({instructions:[{op}]}));});
