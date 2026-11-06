import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {fileURLToPath} from 'node:url';
import {resolve} from 'node:path';
const root=fileURLToPath(new URL('../..',import.meta.url));
const facts=["decode_output", "decode_revert", "decode_short", "decode_wrong", "call_decode", "static_decode", "consume_halt", "consume_refused", "consume_missing", "completion_frame", "sample_run", "static_sample", "call_refused_decode", "timeout_decode", "input_refused_decode", "missing_code", "sample_state", "call_decode_encoded", "copied_decoder"];
const hash=bytes=>createHash('sha256').update(bytes).digest('hex');
export function validateReturningLedger(v,moduleText,provenance,readProducer) {
  assert.equal(v.module,'Solidity/Yul/Composition/ReturningPhysical.lean');
  assert.equal(v.moduleSha256,'4212dc29a6cedca0a800d8709f37255755bcc3abdb97bbe4790cec2eded6895d');
  assert.equal(hash(moduleText),v.moduleSha256,'owned module drift');
  assert.deepEqual(v.facts,facts,'missing/reordered/changed exact kernel signature registration');
  assert.equal(v.producer,'fd3da385f5e4ada7aa889821d3ae59a34833d235');
  assert.equal(v.producerProvenance,'/workspace/vy5-composition/return-consumer-20261102/producer-provenance.json','wrong provenance path');
  assert.equal(hash(JSON.stringify(provenance)),'3487797a1dd51de9a0195dc66a4eb713586b1dc63ac23fb1dc959bd6d1295352','immutable producer closure drift');
  assert.equal(provenance.producer,v.producer,'wrong peer identity');
  assert.ok(provenance.closure.length>0,'absent producer closure');
  const names=new Set();
  for(const row of provenance.closure) {
    assert.ok(!names.has(row.path),'duplicate producer body');names.add(row.path);
    assert.equal(hash(readProducer(row.path)),row.sha256,'private producer body drift');
  }
  for(const n of ['GeneralReturning','GeneralReturningStatic','GeneralReturningOutput'])
    assert.ok(names.has('Solidity/Yul/World/'+n+'.lean'),'required producer absent');
  assert.equal(v.fullCoverage,false);assert.equal(v.fullProofGate,'pending');
  assert.equal(v.originalObligations,24);assert.equal(v.originalCombinations,6);
  assert.equal(v.freshNativeComparisons,0);assert.equal(v.existingNativeJournalFailures,5);
  assert.ok(v.pending.includes('ordinary nonempty revert producer packet'));
  assert.ok(v.pending.includes('general Source try selector'));
  return {kernelDeclarations:facts.length,fullProofGate:'pending',freshNativeComparisons:0};
}
export function verifyReturning() {
  const v=JSON.parse(readFileSync(resolve(root,'tests/yul-composition/returning-ledger.json')));
  const registration=JSON.parse(readFileSync(resolve(root,'tests/yul-composition/ledger.json')));
  assert.equal(registration.returningEvidence,'tests/yul-composition/returning-ledger.json');
  return validateReturningLedger(v,readFileSync(resolve(root,v.module)),
    JSON.parse(readFileSync(v.producerProvenance)),
    name=>readFileSync(resolve('/workspace/vy5-dependencies-20261101',name)));
}
if(process.argv[1]===fileURLToPath(import.meta.url))console.log(JSON.stringify(verifyReturning()));
