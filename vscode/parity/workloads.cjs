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
  const hoverExpected=target==='local'?{text:'```solidity\n'+text.slice(text.indexOf('function helper'),text.indexOf('{return')).trim()+'\n```',range:nameRange(call),exact:true}:{text:'```dafny\nfunction Services.helper(a: int, b: int): int\n```',exact:false};
  return {target,hoverExpected,text,declarationRange:nameRange(text.indexOf('helper(')),callRange:nameRange(call),call:position(call+2),completionInsertion:position(call+'helper(1,2)'.length),completion:position(completionText.lastIndexOf('this.')+5,completionText),signature:position(call+'helper('.length),signatureSecond:position(call+'helper(1,'.length),completionText};
}
function assertServiceResponse(kind,fixture,uri,value){
  const assert=require('node:assert/strict');
  const range=r=>({start:{line:r?.start?.line,character:r?.start?.character},end:{line:r?.end?.line,character:r?.end?.character}});
  const key=r=>JSON.stringify(range(r));
  if(kind==='hover'){
    const rows=Array.isArray(value)?value:[value];
    assert.ok(rows.some(h=>(Array.isArray(h?.contents)?h.contents:[h?.contents]).some(c=>(typeof c==='string'?c:c?.value)?.trim())),'nonempty hover text');
    assertHoverObservation(value,fixture.hoverExpected);
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
function assertServiceSymbols(value,expected,absent=[]){
  const assert=require('node:assert/strict'),names=[];
  const visit=rows=>{assert.ok(Array.isArray(rows),'symbol response is an array');for(const row of rows){assert.equal(typeof row.name,'string','symbol name');names.push(row.name);if(row.children!==undefined)visit(row.children);}};
  visit(value);assert.ok(names.includes(expected),'expected symbol name '+expected);
  for(const old of absent)assert.ok(!names.includes(old),'obsolete/foreign symbol name '+old);
  return names;
}
module.exports = {workload,symbolPosition,verificationOutcomes,servicesWorkload,assertServiceResponse,assertServiceSymbols};


// Compiler-only stress input. No proof annotation, axiom or assumed result.
function largeFileWorkload(){
  return '// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34;\ncontract LargeFile {\n'+Array.from({length:1000},(_,i)=>'  function f'+i+'() external pure returns (uint256) { return '+i+'; }').join('\n')+'\n}\n';
}
function assertLargeFileSymbols(symbols,text,{historical=false}={}){
  const assert=require('node:assert/strict'),position=offset=>{const lines=text.slice(0,offset).split('\n');return{line:lines.length-1,character:lines.at(-1).length};};
  assert.equal(symbols.length,1,'exact one current contract');const parent=symbols[0];assert.equal(parent.name,'LargeFile');assert.equal(parent.kind,5);
  const declarations=[...text.matchAll(/  function ([A-Za-z0-9_]+)\(\) external pure returns \(uint256\) \{ return (\d+); \}/g)];assert.equal(declarations.length,1000,'workload retains every declaration');
  assert.equal(parent.children.length,1000,'all thousand function symbols, no duplicates/extras');
  const seen=new Set();for(let i=0;i<declarations.length;i++){const match=declarations[i],symbol=parent.children[i],start=match.index+2,name=start+'function '.length;assert.equal(symbol.name,match[1]);assert.equal(symbol.kind,12);assert.equal(seen.has(symbol.name),false);seen.add(symbol.name);assert.deepEqual(symbol.range,{start:position(start),end:position(match.index+match[0].length)},'exact function range '+symbol.name);assert.deepEqual(symbol.selectionRange,{start:position(name),end:position(name+symbol.name.length)},'exact UTF16 name range '+symbol.name);assert.equal(symbol.detail.startsWith('Outdated: '),historical,'honest symbol provenance');}
  assert.deepEqual(parent.range,{start:position(text.indexOf('contract LargeFile')),end:position(text.lastIndexOf('}')+1)});const name=text.indexOf('LargeFile');assert.deepEqual(parent.selectionRange,{start:position(name),end:position(name+9)});assert.equal(parent.detail.startsWith('Outdated: '),historical);
}
module.exports.largeFileWorkload=largeFileWorkload;
module.exports.assertLargeFileSymbols=assertLargeFileSymbols;

function assertHoverObservation(value,expected){
  const assert=require('node:assert/strict');assert.ok(expected,'source-derived hover expectation required');
  if(expected.absent){assert.equal(value,null,'unknown invocation has no invented declaration');return;}
  assert.ok(value&&!Array.isArray(value),'one hover result');assert.equal(value.contents?.kind,'markdown','hover Markdown markup');
  assert.equal(typeof value.contents.value,'string');if(expected.exact!==false)assert.equal(value.contents.value,expected.text,'exact source-derived hover contents');else assert.ok(value.contents.value.includes(expected.text),'pinned required declaration/type/signature/comment');
  if(expected.range)assert.deepEqual(value.range,expected.range,'exact queried lexical occurrence range');
}
module.exports.assertHoverObservation=assertHoverObservation;

function hoverWorkload(target,text){
  const fs=require('node:fs'),path=require('node:path'),local=target==='local';
  text??=fs.readFileSync(path.join(__dirname,'../../tests/editor-parity/hover.'+(local?'sol':'dfy')),'utf8');
  const position=offset=>{const lines=text.slice(0,offset).split('\n');return{line:lines.length-1,character:lines.at(-1).length};};
  const range=(needle,token,from=0)=>{const base=text.indexOf(needle,from);if(base<0)throw Error('Missing hover source anchor '+needle);const at=base+needle.indexOf(token);return{start:position(at),end:position(at+token.length)};};
  const def={helper:range('function helper','helper'),param:range(local?'uint256 a)':'a: int)','a'),field:range(local?'public x;':'var x: int;','x'),outer:range(local?'bool x = true':'var x := true','x'),inner:range(local?'uint256 x = 1':'var x := 1','x')};
  const header=local?'function helper(uint256 a) public pure returns (uint256)':'function HoverCases.helper(a: int): int';
  const helper=(local?'@notice Add values.\n@param a Left input.':'Add values.')+'\n```'+(local?'solidity':'dafny')+'\n'+header+'\n```';
  const declaration=(name,type)=>'```'+(local?'solidity':'dafny')+'\n'+name+': '+type+'\n```';
  const entry=(id,r,target,content)=>({id,position:r.start,declarationRange:def[target],expected:{text:content,exact:local,...(local?{range:r}:{})}});
  return{text,cases:[entry('helper-declaration',def.helper,'helper',helper),entry('helper-use',range('this.helper','helper'),'helper',helper),entry('parameter-use',range(local?'return a;':'{ a }','a'),'param',declaration('a',local?'uint256':'int')),entry('field-declaration',def.field,'field',local?declaration('x','uint256'):'```dafny\nvar HoverCases.x: int\n```'),entry('outer-declaration',def.outer,'outer',declaration('x','bool')),entry('inner-use',range(local?'inside = x':'inside := x','x'),'inner',declaration('x',local?'uint256':'int')),entry('scope-exit-use',range(local?'outside = x':'outside := x','x'),'outer',declaration('x','bool')),entry('explicit-field-use',range(local?'this.x()':'this.x)','x'),'field',local?declaration('x','uint256'):'```dafny\nvar HoverCases.x: int\n```')]};
}
module.exports.hoverWorkload=hoverWorkload;

/** Separate compiler-only import scenario. Never replaces the annotated proof workload. */
function customImportWorkload(target){
 if(target==='local')return{source:'// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34;\nimport "alias/Dependency.sol";\ncontract Parity { function f0() public pure returns (uint256) { return 1; } }\n',dependency:'pragma solidity ^0.8.34; contract Dependency {}\n',path:'vendor with spaces/lib/Dependency.sol'};
 if(target==='dafny')return{source:'include "vendor with spaces/Dependency.dfy"\nmethod f0() returns (r: int) { r := Dependency.one(); }\n',dependency:'module Dependency { function one(): int { 1 } }\n',path:'vendor with spaces/Dependency.dfy'};
 throw Error('Unknown custom import target');
}
module.exports.customImportWorkload=customImportWorkload;
