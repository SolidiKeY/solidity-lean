// External adapter controls: guards four-mode execution and refusal of logs.
// Expected values are deliberate fixed controls, not Lean differential results.
import test from 'node:test';
import assert from 'node:assert/strict';
import {compiler,execute,variants} from '../evm-reference/generated.mjs';
import {referenceCompiler} from '../test-compiler.mjs';
import {shrink} from './run.mjs';
const compile=compiler(referenceCompiler());
const source=`pragma solidity 0.8.38; contract Generated {
 uint256 x; uint256 y; event Seen();
 function setUp() external {x=0;y=1;}
 function run() external returns(uint256,uint256) {x=x+y; return(x,y);}
 function observe() external view returns(uint256,uint256) {return(x,y);}
}`;
const record={schema:1,seed:1108,index:0,kind:0,a:'0',b:'1',source,
 expected:{failed:false,storage:['x = 1','y = 1'],revertData:'0x'}};
for(const variant of variants) test(`fixed reference smoke ${JSON.stringify(variant)}`,async()=>{
 assert.equal((await execute(record,variant,compile)).status,'agree');
 const wrong={...record,expected:{...record.expected,storage:['x = 999','y = 1']}};
 assert.equal((await execute(wrong,variant,compile)).status,'mismatch');
 const logs={...record,source:source.replace('x=x+y;','emit Seen(); x=x+y;')};
 const actual=await execute(logs,variant,compile);
 assert.equal(actual.status,'blocked');assert.match(actual.reason,/log/);
});
test('shrinker reexecutes candidates and preserves only disagreements',async()=>{
 const wrong={...record,a:'2',b:'2',expected:{...record.expected,storage:['x = 999','y = 1']}};
 const generated=[];
 const reduced=await shrink(wrong,variants[0],compile,args=>{
  generated.push(args);return [{...wrong,a:String(args[3]),b:String(args[4]),
    source:source.replace('x=0;y=1;',`x=${args[3]};y=${args[4]};`),
    expected:{...wrong.expected,storage:['x = 999',`y = ${args[4]}`]}}];
 });
 assert.ok(generated.length>0);assert.equal(reduced.record.a,'0');assert.equal(reduced.record.b,'0');
 assert.ok(reduced.attempts.every(a=>a.status==='mismatch'));
});
