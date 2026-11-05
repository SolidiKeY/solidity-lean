'use strict';

/** The shared fragment uses constants within uint256, avoiding overflow and
 * Dafny's unbounded-integer/termination semantics. Obligations are paired by
 * ordinal, never by a source range that belongs to a different language. */
function workload(target, count = 8, failing = false) {
  if (!Number.isSafeInteger(count) || count < 1 || count > 1000) throw new Error('Invalid workload size');
  const expected = failing ? 2 : 1;
  const declarations = Array.from({length:count},(_,i)=> target === 'dafny'
    ? `method f${i}() returns (r: int)\n  ensures r == ${expected}\n{ r := 1; }`
    : `  /// @custom:key ensures \\result == ${expected}\n  function f${i}() public pure returns (uint256 result) { return 1; }`);
  return target === 'dafny' ? declarations.join('\n')+'\n' : `// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34;\ncontract Parity {\n${declarations.join('\n')}\n}\n`;
}
function symbolPosition(target, text, ordinal = 0) {
  const lines = text.split('\n');
  const line = lines.findIndex(s => s.includes(`f${ordinal}(`));
  return {line,character:lines[line].indexOf(`f${ordinal}`)};
}
/** Assert outcomes as well as completion: a terminal error is not a proof. */
function verificationOutcomes(target, report, count, expected = 'proved') {
  const assert=require('node:assert/strict');
  assert.ok(['proved','failed'].includes(expected),'explicit expected outcome');
  if(target==='local')assert.deepEqual(report.errors,[],'backend errors');
  const rows=target==='local'?report.results.filter(r=>/^f\d+$/.test(r.function)):report.namedVerifiables;
  assert.equal(rows.length,count,'all paired obligations must be reported');
  if(target==='local'){
    assert.equal(new Set(rows.map(r=>r.function)).size,count,'unique paired obligations');
    assert.deepEqual(rows.map(r=>r.function).sort(),Array.from({length:count},(_,i)=>'f'+i).sort(),'exact paired obligation names');
  }
  const statuses=rows.map(r=>target==='local'?r.status:r.status===5?'proved':r.status===4?'failed':'unfinished');
  assert.ok(statuses.every(s=>expected==='proved'?s==='proved':['failed','refuted'].includes(s)),
    `Expected ${expected} for every obligation; observed ${JSON.stringify(statuses)}`);
  return statuses;
}

function servicesWorkload(target) {
  // Member completion has a real trigger in both languages. Addition stays in
  // the language-services fixture, outside the constant-proof benchmark.
  const text=require('node:fs').readFileSync(require('node:path').join(__dirname,'../../tests/editor-parity/services.'+(target==='dafny'?'dfy':'sol')),'utf8');
  const position=(offset,source=text)=>{const prefix=source.slice(0,offset).split('\n');return {line:prefix.length-1,character:prefix.at(-1).length};};
  const call=text.lastIndexOf('helper(');
  const completionText=text.replace('this.helper(1,2)','this.helper(1,2) + this.');
  const nameRange=offset=>({start:position(offset),end:position(offset+6)});
  return {text,declarationRange:nameRange(text.indexOf('helper(')),callRange:nameRange(call),call:position(call+2),completionInsertion:position(call+'helper(1,2)'.length),completion:position(completionText.lastIndexOf('this.')+5,completionText),signature:position(call+'helper('.length),signatureSecond:position(call+'helper(1,'.length),completionText};
}
function assertServiceResponse(kind,fixture,uri,value){
  const assert=require('node:assert/strict');
  const range=r=>({start:{line:r?.start?.line,character:r?.start?.character},end:{line:r?.end?.line,character:r?.end?.character}});
  const key=r=>JSON.stringify(range(r));
  if(kind==='hover'){
    const rows=Array.isArray(value)?value:[value];
    assert.ok(rows.some(h=>(Array.isArray(h?.contents)?h.contents:[h?.contents]).some(c=>(typeof c==='string'?c:c?.value)?.trim())),'nonempty hover text');
  }else if(kind==='definition'||kind==='references'){
    const rows=Array.isArray(value)?value:[value];
    assert.ok(rows.every(l=>(l?.targetUri||l?.uri)?.toString()===uri),'locations belong to the requested document');
    const ranges=rows.map(l=>key(l.targetSelectionRange||l.range)).sort();
    assert.deepEqual(ranges,(kind==='definition'?[key(fixture.declarationRange)]:[key(fixture.declarationRange),key(fixture.callRange)]).sort(),'exact declaration/call ranges');
  }else if(kind==='rename'){
    const edits=value?.documentChanges?.flatMap(d=>{assert.equal(d.textDocument?.uri,uri);return d.edits||[];})||Object.entries(value?.changes||{}).flatMap(([u,rows])=>{assert.equal(u,uri);return rows;});
    assert.equal(edits.length,2,'declaration and call rename');assert.ok(edits.every(e=>e.newText==='renamed'),'expected replacement text');
    assert.deepEqual(edits.map(e=>key(e.range)).sort(),[key(fixture.declarationRange),key(fixture.callRange)].sort(),'rename edits cover declaration and call');
  }
}
module.exports = {workload,symbolPosition,verificationOutcomes,servicesWorkload,assertServiceResponse};
