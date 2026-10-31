#!/usr/bin/env node
// Read-only adapter: reuse the published comparator, never reimplement semantics.
import {compare} from './evm-reference/generated.mjs';
import {createHash} from 'node:crypto';
import {readFileSync} from 'node:fs';
const report = JSON.parse(readFileSync(0, 'utf8'));
for (const {record, variants} of report.records) {
  for (const actual of variants) {
    const input = {language:'Solidity',sources:{'generated.sol':{content:record.source}},settings:{
      viaIR:actual.variant.viaIR,optimizer:{enabled:actual.variant.optimizer,runs:200},evmVersion:'osaka',
      metadata:{appendCBOR:false},outputSelection:{'*':{'*':['abi','storageLayout','evm.bytecode.object',
        'evm.deployedBytecode.object','evm.methodIdentifiers']}}}};
    const inputHash = createHash('sha256').update(JSON.stringify(input)).digest('hex');
    if (actual.inputSha256 !== inputHash) throw Error('changed compiler input/settings');
    if (actual.status === 'agree' && !compare(record, actual))
      throw Error('contradictory agreement: ' + record.index);
    if (actual.status === 'agree') {
      for (const [field, signature] of [['setup', 'setUp()'], ['before', 'observe()'],
        ['run', 'run()'], ['storage', 'observe()'], ['deployment', 'constructor']]) {
        const obs = actual[field];
        if (!obs || obs.signature !== signature || typeof obs.failed !== 'boolean' ||
            !Array.isArray(obs.values) || !/^0x(?:[0-9a-f]{2})*$/.test(obs.returnData) ||
            (typeof obs.gasUsed !== 'string' || !/^[0-9]+$/.test(obs.gasUsed)) || !('exception' in obs))
          throw Error('missing/malformed retained observation: ' + field);
        if (!Number.isSafeInteger(obs.steps) || obs.steps < 0 || obs.steps > 5_000_000 ||
            !Number.isSafeInteger(obs.maxStack) || obs.maxStack < 0 || obs.maxStack > 1024)
          throw Error('missing/invalid retained host metrics');
        if ((!obs.failed && obs.exception !== null) ||
            (obs.failed && !['revert','out of gas','stack overflow'].includes(obs.exception)))
          throw Error('contradictory exception');
        const values = obs.failed ? [] : (obs.returnData.length - 2) % 64 === 0
          ? Array.from({length:(obs.returnData.length - 2) / 64}, (_,i) =>
              BigInt('0x' + obs.returnData.slice(2 + i*64, 2 + (i+1)*64)).toString()) : null;
        if (JSON.stringify(values) !== JSON.stringify(obs.values)) throw Error('contradictory ABI values');
      }
      const layout = actual.layout;
      if (!layout || !Array.isArray(layout.storage) || layout.storage.length !== 2 ||
          layout.storage.some((v,i) => v.label !== ['x','y'][i] || v.slot !== String(i) ||
            v.offset !== 0 || layout.types?.[v.type]?.label !== 'uint256'))
        throw Error('changed retained storage layout');
      if (actual.setup.failed || actual.before.failed || actual.deployment.failed ||
          actual.setup.returnData !== '0x') throw Error('failed setup/deployment');
      const before = '0x' + [record.a, record.b].map(n => BigInt(n).toString(16).padStart(64, '0')).join('');
      if (actual.before.returnData !== before) throw Error('changed initial observation');
    }
  }
}
process.stdout.write('V17_COMPARE_PASS\n');
