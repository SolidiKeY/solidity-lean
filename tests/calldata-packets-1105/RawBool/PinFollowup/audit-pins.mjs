import { readFileSync, writeFileSync } from 'node:fs';
import { execFileSync } from 'node:child_process';
import assert from 'node:assert/strict';
import { pins, STANDARD } from '../../../../scripts/check-axiom-pins.mjs';
const base='3ad22f66d8fc6431378c22e71823436c79dede7f';
const proposal={};let total=0;
for (const part of ['Execution','Controls']) {
 const file=`Solidity/Backend/CalldataPackets/RawBool/${part}.lean`;
 const source=readFileSync(file,'utf8'); const found=pins(source);
 assert.equal(found.length,(source.match(/^(?:private )?theorem /gm)||[]).length);
 assert.equal(found.length,(source.match(/^#print axioms /gm)||[]).length);
 const stripped=source.replace(/\/-- info:[\s\S]*?-\/\n#guard_msgs in\n/g,'');
 assert.equal(stripped,execFileSync('git',['show',`${base}:${file}`],{encoding:'utf8'}));
 for (const pin of found) {
  assert.ok(pin.axioms!==null); assert.ok(pin.name.endsWith('.'+pin.target));
  assert.ok(pin.axioms.every(a=>STANDARD.includes(a)));
  proposal[`${file}:${pin.name}`]=pin.axioms;total++;
 }
}
assert.equal(total,64);
writeFileSync('tests/calldata-packets-1105/RawBool/PinFollowup/pins-proposal.json',JSON.stringify(proposal,null,2)+'\n');
console.log('PIN_COVERAGE_PASS64 PROOFS_UNCHANGED STANDARD_AXIOMS_ONLY');
