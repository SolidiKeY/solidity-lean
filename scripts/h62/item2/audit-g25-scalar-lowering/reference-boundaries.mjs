// Finite external tests, not proofs. No source/target IR or core dependency.
import fs from 'node:fs';
import path from 'node:path';
import {pathToFileURL} from 'node:url';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
const root = process.argv[2];
if (!root) throw Error('usage: node reference-boundaries.mjs ARTIFACT_ROOT');
const load = p => import(pathToFileURL(path.join(root, 'evm-reference/node_modules', p)).href);
const {createEVM} = await load('@ethereumjs/evm/dist/esm/index.js');
const {Common, Mainnet, Hardfork} = await load('@ethereumjs/common/dist/esm/index.js');
const pinned = JSON.parse(fs.readFileSync(new URL('../../../evm-reference/package.json',import.meta.url)));
const versions = {};
for (const [name,pin] of Object.entries(pinned.dependencies)) {
 const installed = JSON.parse(fs.readFileSync(path.join(root,'evm-reference/node_modules',name,'package.json'))).version;
 assert.equal(installed,pin,`installed version differs from frozen pin: ${name}`);
 versions[name]=installed;
}
const vectorData = fs.readFileSync(path.join(root,'evidence/boundary-vectors.json'));
const vectorSha256 = createHash('sha256').update(vectorData).digest('hex');
const vectors = JSON.parse(vectorData);
const cases = [
 ['negation-exact-gas','Osaka',vectors.negatedTrue,6n,null,['0']],
 ['negation-one-less-gas','Osaka',vectors.negatedTrue,5n,'out of gas',null],
 ['push0-osaka','Osaka',vectors.metadataPushZero,2n,null,['0']],
 ['push0-shanghai','Shanghai',vectors.metadataPushZero,2n,null,['0']],
 ['push0-paris-refusal','Paris',vectors.metadataPushZero,1000n,'invalid opcode',null],
 ['always-revert-control','Osaka',[0x60,0,0x60,0,0xfd],1000n,'revert',null],
];
const results=[];
function check(actual,error,stack) {
 assert.equal(actual.error,error);
 if(stack!==null) assert.deepEqual(actual.stack,stack);
 assert.equal(actual.returnData,'');
}
for(const [name,fork,code,gas,error,stack] of cases) {
 const evm=await createEVM({common:new Common({chain:Mainnet,hardfork:Hardfork[fork]})});
 let steps=0;
 evm.events.on('step',()=>{if(++steps>16) throw Error('HOST_LIMIT_BLOCKED');});
 const result=await evm.runCode({code:Uint8Array.from(code),gasLimit:gas});
 const actual={error:result.exceptionError?.error??null,
   stack:result.runState?.stack.getStack().map(String)??null,
   returnData:Buffer.from(result.returnValue).toString('hex')};
 check(actual,error,stack);
 results.push({name,fork,code,gas:gas.toString(),gasUsed:result.executionGasUsed.toString(),steps,...actual,status:'pass'});
}
// Harness must refuse wrong value and wrong halt class, not merely run samples.
assert.throws(()=>check(results[0],null,['1']));
assert.throws(()=>check(results[1],null,null));
const report={boundary:'finite reference executions only; gasless Lean slice has no gas/fork parameter',
 reference:versions,vectorSha256,cases:results,negativeHarnessControls:2,status:'pass'};
fs.writeFileSync(path.join(root,'evidence/reference-boundaries.json'),JSON.stringify(report,null,2)+'\n');
console.log(`PASS: ${results.length} actual-byte gas/fork/halt cases; 2 rejecting harness controls`);
