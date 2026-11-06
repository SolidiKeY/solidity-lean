import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {validateComponentExtras,validateLoopLedger,validateTrustRegistration,validateExtrasRoot} from './component-extras.mjs';
const DEP='/workspace/vy5-dependencies-20261101';
test('selected31local/12loop facts and six ordinary method registrations verify',()=>{assert.deepEqual(validateComponentExtras(DEP),{localFacts:31,loopFacts:12,privateMethodSites:6,fullObligationsClosed:0,fullCombinationsClosed:0});});
test('selected required local/loop/trust catalogs cannot disappear',()=>{const root=JSON.parse(readFileSync('tests/yul-composition/ledger.json'));for(const key of ['localComponentEvidence','loopComponentEvidence','localTrustRegistration']){const x=structuredClone(root);delete x[key];assert.throws(()=>validateExtrasRoot(x));}});
test('loop source, missing proof facts and false full loop closure fail closed',()=>{const bytes=readFileSync('tests/yul-composition/loop-component-ledger.json');for(const change of [r=>r.facts.pop(),r=>r.sourceSha256='0'.repeat(64),r=>r.localLedgerSha256='0'.repeat(64),r=>r.fullProofGate='pass',r=>r.fullCombinationProof='assumed',r=>r.fullCombinationStatus='done']){const r=JSON.parse(bytes);change(r);assert.throws(()=>validateLoopLedger(Buffer.from(JSON.stringify(r))));}});
test('isolated trust catalog cannot lose, duplicate or permit forbidden sites',()=>{const bytes=readFileSync('tests/yul-composition/local-trust-registration.json');for(const change of [r=>r.entries.pop(),r=>r.entries.push(r.entries[0]),r=>r.entries[0].kind='forbidden',r=>r.baseInventorySha256='0'.repeat(64)]){const r=JSON.parse(bytes);change(r);assert.throws(()=>validateTrustRegistration(DEP,Buffer.from(JSON.stringify(r))));}});
