#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {compileFixture} from './solc-ast.mjs';
import {suiteSources,measureNative} from './testsuite-performance.mjs';
const root=path.resolve('.'),directory=path.join(root,'.lake/testsuite-performance/controls');
fs.mkdirSync(directory,{recursive:true});
const rows=suiteSources(fs.readFileSync('Bridge/SolidityVelvet/TestSuite.lean','utf8'));
const controls=[
 ['additionSimple','assert(r == 3)','assert(r == 4)','refuted'],
 ['storageRootReadWrite','assert(r == 34)','assert(r == 35)','refuted'],
 ['storageIndexRootMapping','assert(r == 42)','assert(r == 43)','refuted'],
 ['whileCountsUp','assert(i == 3)','assert(i == 4)','refuted'],
 ['invariantCountsToBound','assert(i == n)','assert(i != n)','refuted'],
 ['requireFalseLiteral','assert(false)','assert(false)','proved']
];
const trials=[];
for(const [name,before,after,expected] of controls){
 const original=rows.find(r=>r.name===name).source;
 assert.ok(original.includes(before));const text=original.replace(before,after);
 const source=path.join(directory,name+'.sol'),out=path.join(directory,name+'.ast.json');fs.writeFileSync(source,text);
 const compiled=compileFixture({args:['--source',source,'--out',out,'--no-wrapper'],quiet:true});
 const contract=compiled.fixture.ast.nodes.find(n=>n.nodeType==='ContractDefinition');
 trials.push({name,source,sourceHash:createHash('sha256').update(text).digest('hex'),expected,request:{contract,function:name}});
}
const closed=JSON.parse(fs.readFileSync('tests/automation/ClosedSpecs.ast.json','utf8'));
const contract=closed.ast.nodes.find(n=>n.nodeType==='ContractDefinition');
for(const [name,expected] of [['maximum','proved'],['falseMaximum','refuted'],['storeMaximum','proved'],
 ['twoChoices','proved'],['constantOne','proved'],['falseConstant','refuted'],['store','proved'],['falseStore','refuted']]){
 trials.push({name,expected,sourceHash:'fixture:ClosedSpecs',requireExact:true,request:{contract,function:name}});
}
const result=await measureNative({trials},path.join(root,'.lake/direct-native/direct-check'),1);
for(const trial of result.trials){
 const input=trials.find(t=>t.name===trial.name),expected=input.expected;
 const status=trial.result.results?.[0]?.status;
 if(input.requireExact)assert.equal(status,expected,JSON.stringify(trial));
 else if(expected==='proved')assert.equal(status,'proved',JSON.stringify(trial));
 else assert.ok(['pending','refuted'].includes(status),'a false assertion must never be proved: '+JSON.stringify(trial));
 if(status==='refuted'){
  assert.equal(trial.result.results[0].verification,'direct');
  assert.equal(trial.result.results[0].counterexample.certified,false);
 }
}
fs.writeFileSync(path.join(directory,'results.json'),JSON.stringify(result,null,2)+'\n');
console.log('PASS eight exact specification verdicts; five false assertions remain refuted/unknown and the vacuity control is proved using generated C');
