#!/usr/bin/env node
// Sampled scoped-loop upstream executions, separate from kernel-checked model simulation.
import assert from 'node:assert/strict';
import {createRequire} from 'node:module';
import {readFileSync, writeFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {fileURLToPath} from 'node:url';
import {replayBytecode,INITIAL_GAS,STEP_LIMIT} from './evm-reference/replay.mjs';
const sha = x => createHash('sha256').update(x).digest('hex');
const compiler = process.env.MEMORY_LOOP_SOLC ?? '/workspace/.setup/soljson/soljson-v0.8.34+commit.80d5c536.js';
const compilerSha256 = sha(readFileSync(compiler));
assert.equal(compilerSha256, 'c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8');
const solc = createRequire(import.meta.url)(compiler);
const compile = solc.cwrap('solidity_compile', 'string', ['string','number','number']);
const content = readFileSync(fileURLToPath(new URL('../tests/solc/MemoryCompilerLoops.sol',import.meta.url)), 'utf8');
const vectors = [
  {signature:'scopedArrays()',args:[],expected:['4'],failure:false},
  {signature:'scopedRecords()',args:[],expected:['3'],failure:false},
  {signature:'scopedAllocateTurn()',args:[],expected:['0'],failure:false},
  {signature:'scopedAllocationBeforeRevert()',args:[],expected:[],failure:true},
];
const rows = [];
for (const viaIR of [false,true]) for (const optimizer of [false,true]) {
  const settings = {viaIR,optimizer:{enabled:optimizer,runs:200},evmVersion:'osaka',
    outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.deployedBytecode.object','evm.methodIdentifiers']}}};
  const output = JSON.parse(compile(JSON.stringify({language:'Solidity',sources:{'MemoryCompilerLoops.sol':{content}},settings}),0,0));
  assert.deepEqual((output.errors??[]).filter(e=>e.severity==='error'),[]);
  const artifact = output.contracts['MemoryCompilerLoops.sol'].MemoryCompilerLoops;
  const execution = await replayBytecode(artifact,vectors);
  assert.equal(execution.status,'working',JSON.stringify(execution));
  assert.equal(execution.observed.length,4);
  assert.equal(execution.observed[3].exception,'revert');
  assert.equal(execution.observed[3].returnData,'0x');
  const wrongValue = await replayBytecode(artifact,[{...vectors[0],expected:['999']}]);
  assert.equal(wrongValue.status,'broken');
  assert.deepEqual(wrongValue.observed[0].values,['4']);
  const wrongHalt = await replayBytecode(artifact,[{...vectors[3],failure:false}]);
  assert.equal(wrongHalt.status,'broken');
  assert.equal(wrongHalt.observed[0].exception,'revert');
  const exhausted = await replayBytecode(artifact,[vectors[3]],1);
  assert.equal(exhausted.status,'blocked');
  assert.match(exhausted.reason,/instruction budget exhausted/);
  const callExhausted = await replayBytecode(artifact,[vectors[3]],30);
  assert.equal(callExhausted.status,'blocked');
  assert.ok(callExhausted.deployment, 'deployment must finish before call-budget refusal');
  assert.match(callExhausted.reason,/instruction budget exhausted/);
  const runtimeSha256=sha(Buffer.from(artifact.evm.deployedBytecode.object,'hex'));
  assert.equal(runtimeSha256,execution.deployment.runtimeCodeSha256);
  const row = {viaIR,optimizer,version:solc.cwrap('solidity_version','string',[])(),compilerSha256,
    sourceSha256:sha(content),creationSha256:sha(Buffer.from(artifact.evm.bytecode.object,'hex')),runtimeSha256,
    settings,vectors,execution,controls:{wrongValue,wrongHalt,exhausted,callExhausted}};
  rows.push(row); console.log(JSON.stringify({viaIR,optimizer,status:execution.status,observed:execution.observed,controls:{wrongValue:wrongValue.status,wrongHalt:wrongHalt.status,exhausted:exhausted.status}}));
}
const provenance={node:process.version,initialGas:INITIAL_GAS.toString(),stepLimit:STEP_LIMIT,hardfork:'Osaka',
  runnerSha256:sha(readFileSync(fileURLToPath(import.meta.url))),
  adapterSha256:sha(readFileSync(fileURLToPath(new URL('./evm-reference/replay.mjs',import.meta.url)))),
  packageLockSha256:sha(readFileSync(fileURLToPath(new URL('./evm-reference/package-lock.json',import.meta.url)))),
  packages:JSON.parse(readFileSync(fileURLToPath(new URL('./evm-reference/package.json',import.meta.url)),'utf8')).dependencies,
  refusalScope:'1 instruction stops deployment; 30 instructions permits deployment and stops the call. Both are host-runner BLOCKED, not source THalt.exhausted.'};
const result = {provenance,claim:'Sampled actual EthereumJS EVM execution in four solc modes; not a compiler refinement theorem or universal source coverage.',rows};
const i=process.argv.indexOf('--output');
if(i>=0) writeFileSync(process.argv[i+1],JSON.stringify(result,null,2)+'\n');
