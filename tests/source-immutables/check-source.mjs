#!/usr/bin/env node
/** Diagnose current Source admission against unchanged desired expectations.
Positive #eval controls are diagnostic execution, never kernel proof claims. */
import {readFileSync,writeFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import assert from 'node:assert/strict';
const [diagnostics,expectedPath,baselinePath,sourceHead,destination]=process.argv.slice(2);
assert(diagnostics && expectedPath && baselinePath && sourceHead && destination);
assert.match(sourceHead,/^[a-f0-9]{40}$/);
const EXPECTED_SHA256='a37502caf84098877d0c02a44b08e476a400bb9afaedc205da298d95a71ede8d';
const sha=x=>createHash('sha256').update(x).digest('hex');
const raw=readFileSync(diagnostics,'utf8'),expectedBytes=readFileSync(expectedPath);
assert.equal(sha(expectedBytes),EXPECTED_SHA256,'expected manifest hash mismatch');
const expected=JSON.parse(expectedBytes);
assert.equal(sourceHead,expected.baselineSourceHead,'stale source head');
assert.equal(sha(readFileSync(baselinePath)),expected.baselineSha256,'stale baseline source');
const lines=raw.split('\n').filter(x=>x.startsWith('tests/source-immutables/ImmutableBaseline.lean '));
assert.equal(lines.length,1,'missing or duplicate complete baseline diagnostics');
const data=JSON.parse(lines[0].slice(lines[0].indexOf('{'))).structuredContent?.result;
assert(data?.success && !data.partial && !data.timed_out,'missing/incomplete/failed baseline evidence');
const matches=[];
for(const item of data.items??[]) {
 const m=item.message.match(/H12_SOURCE_ACCEPTANCE pipeline=(legacy|viaIR) ctor=(true|false) initializer=(true|false) ordinary=(true|false) mutable=(true|false)/);
 if(m) matches.push({pipeline:m[1],values:m.slice(2).map(x=>x==='true')});
}
assert.deepEqual(matches.map(x=>x.pipeline),['legacy','viaIR'],'missing/reordered Source pipeline evidence');
const fields=['Constructor.sol','Initializer.sol','OrdinaryWrite.sol','MutableConstructor.sol'];
const rows=matches.flatMap(row=>fields.map((fixture,i)=>{
 const entry=expected.fixtures.find(x=>x.file===fixture);
 assert(entry && typeof entry.sourceDesiredAccepted==='boolean');
 return {pipeline:row.pipeline,fixture,actualAccepted:row.values[i],desiredAccepted:entry.sourceDesiredAccepted,
   match:row.values[i]===entry.sourceDesiredAccepted};
}));
const report={kind:'Source-admission-diagnostic-not-correspondence',sourceHead,
  diagnosticsSha256:sha(raw),baselineSha256:sha(readFileSync(baselinePath)),expectedSha256:sha(readFileSync(expectedPath)),
  rows,allMatch:rows.every(x=>x.match),kernelFacts:'Current constructor rejection, ordinary write rejection and constructor/method context identity; standard axioms only.',
  positiveControls:'Lean diagnostic execution, not replacement kernel proofs.',
  pending:['ConstantWrite Source diagnostic not run; compiler refusal verified','Actual immutable constructor implementation']};
writeFileSync(destination,JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({rows:rows.length,matches:rows.filter(x=>x.match).length,
  mismatches:rows.filter(x=>!x.match),implementation:'pending'}));
if(!report.allMatch) process.exitCode=1;
