import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync, writeFileSync} from 'node:fs';
import {createRequire} from 'node:module';
import {createHash} from 'node:crypto';
import {resolve} from 'node:path';
import {hexToBytes} from '@ethereumjs/util';
import {machine, observation, creationObservation, replayBytecode} from './replay.mjs';

const compiler = resolve(process.env.SOLC_MEMORY_COPY ?? '/workspace/.setup/soljson/soljson-v0.8.34+commit.80d5c536.js');
const compilerSha = 'c8649f8d57f81b3244c7d2dd662efc0620d1ae296f623b347a2c616a6cfd11d8';
const sha = x => createHash('sha256').update(x).digest('hex');
assert.equal(sha(readFileSync(compiler)), compilerSha);
const solc = createRequire(import.meta.url)(compiler);
const compile = solc.cwrap('solidity_compile', 'string', ['string', 'number', 'number']);
const source = readFileSync(new URL('../../tests/solc/MemoryStorageCopies.sol', import.meta.url), 'utf8');
const reports = [];
const word = n => BigInt.asUintN(256, BigInt(n)).toString(16).padStart(64, '0');
for (const viaIR of [false, true]) for (const optimized of [false, true]) {
  test(`memory-to-storage copies viaIR=${viaIR}, optimizer=${optimized}`, async () => {
    const input = {language:'Solidity',sources:{'MemoryStorageCopies.sol':{content:source}},settings:{
      viaIR, optimizer:{enabled:optimized}, evmVersion:'osaka', metadata:{appendCBOR:false},
      outputSelection:{'*':{'*':['abi','evm.bytecode.object','evm.methodIdentifiers']}}}};
    const out = JSON.parse(compile(JSON.stringify(input), 0, 0));
    assert.deepEqual((out.errors ?? []).filter(x => x.severity === 'error'), []);
    const artifact = out.contracts['MemoryStorageCopies.sol'].MemoryStorageCopies;
    const vm = await machine();
    const deployed = await vm.call({data:hexToBytes('0x'+artifact.evm.bytecode.object)});
    assert.equal(deployed.result.execResult.exceptionError, undefined);
    const address = deployed.result.createdAddress;
    assert.ok(address);
    const observed = [];
    async function call(signature, args=[]) {
      const data = artifact.evm.methodIdentifiers[signature] + args.map(word).join('');
      const {result, metrics} = await vm.call({to:address, data:hexToBytes('0x'+data)});
      const obs = observation(result.execResult, signature, metrics);
      observed.push(obs);
      return obs;
    }
    assert.deepEqual((await call('exercise(uint256)', [3])).values, ['1','4','12','77','77']);
    assert.deepEqual((await call('signedAndBool()')).values, [(2n**256n-7n).toString(),'9','1','0']);
    const bad = await call('outOfBounds()');
    assert.equal(bad.exception, 'revert');
    assert.equal(bad.returnData, '0x4e487b71'+word(0x32));
    assert.deepEqual((await call('unchanged()')).values, ['1','4']);
    assert.deepEqual((await call('runtimeLength(uint256)', [0])).values, ['0','0','0']);
    assert.deepEqual((await call('runtimeLength(uint256)', [1])).values, ['1','17','99']);
    assert.deepEqual((await call('runtimeLength(uint256)', [3])).values, ['3','17','99']);
    const guarded = await call('runtimeLength(uint256)', [4]);
    assert.equal(guarded.exception, 'revert');
    assert.equal(guarded.returnData, '0x');
    assert.deepEqual((await call('unchanged()')).values, ['3','17']);
    assert.deepEqual((await call('fixedCopy(bool)', [0])).values, ['31','47','0','0','31','47','99']);
    assert.deepEqual((await call('fixedCopy(bool)', [1])).values, ['31','47','31','47','31','47','99']);
    assert.deepEqual((await call('fixedShape()')).values, ['31','47','0','2','31','47']);
    const fixedBad = await call('fixedBadDestination()');
    assert.equal(fixedBad.exception, 'revert');
    assert.equal(fixedBad.returnData, '0x4e487b71'+word(0x32));
    assert.deepEqual((await call('mixedCopy()')).values, ['31','47','2','91','92','77']);
    assert.deepEqual((await call('lifecycle()')).values, ['31','47','0','2','31','47','77','99','88']);
    // A deliberately wrong observation must fail the independent replay adapter.
    const wrong = await replayBytecode(artifact, [{signature:'exercise(uint256)',args:['3'],expected:['999'],failure:false}]);
    assert.equal(wrong.status, 'broken');
    assert.deepEqual(wrong.observed[0].values, ['1','4','12','77','77']);
    reports.push({viaIR,optimized,compilerSha,sourceSha:sha(source),inputSha:sha(JSON.stringify(input)),
      bytecodeSha:sha(artifact.evm.bytecode.object),deployment:creationObservation(deployed.result.execResult,'constructor',deployed.metrics),observed,
      negativeControl:wrong});
    if (process.env.COPY_REPORT_PATH) writeFileSync(process.env.COPY_REPORT_PATH, JSON.stringify(reports,null,2)+'\n');
  });
}
