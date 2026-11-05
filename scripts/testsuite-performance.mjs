#!/usr/bin/env node
// The linked Velvet suite is the inventory, including its documented source
// adaptations. Each workload is a real, separately compiled Solidity contract.
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import assert from 'node:assert/strict';
import {spawn} from 'node:child_process';
import {createInterface} from 'node:readline';
import {compileFixture} from './solc-ast.mjs';

const root=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'..');
const sha=bytes=>createHash('sha256').update(bytes).digest('hex');
export function suiteSources(text){
  const start=text.indexOf('contract TestSuite {');
  if(start<0)throw new Error('Missing TestSuite contract');
  const first=text.indexOf('  function ',start);
  const declarations=text.slice(start+'contract TestSuite {'.length,first)
    .split('\n').filter(line=>!line.trim().startsWith('--')).join('\n');
  const rows=[];
  const pattern=/^  function (\w+)\(/gm;pattern.lastIndex=first;
  for(let match;(match=pattern.exec(text));){
    const open=text.indexOf('{',match.index);let depth=1,end=open+1;
    for(;end<text.length&&depth;end++){if(text[end]==='{')depth++;if(text[end]==='}')depth--;}
    if(depth)throw new Error('Unterminated function '+match[1]);
    let body=text.slice(match.index,end).replaceAll('−−','--');
    // Move Velvet's invariants to the comment position consumed by solc-ast.
    body=body.replace(/(^[ \t]*(?:while|for)\([^\n]*\)|^[ \t]*(?:while|for) \([^\n]*\))\n((?:[^\n]*\n)*?)([ \t]*\{)/gm,(all,header,annotations,brace)=>{
      if(!annotations.trim().startsWith('invariant '))return all;
      const clauses=annotations.trim().split(/\n\s*invariant /).map(s=>s.replace(/^invariant /,'').trim().replace(/\s+/g,' '));
      const comments=clauses.map(c=>'    /// @custom:key invariant '+c.replace(/forall \((uint|bool) (\w+)\)/g,'\\forall $1 $2;').replaceAll('==>','->')).join('\n');
      return comments+'\n'+header+'\n'+brace;
    });
    const source='// SPDX-License-Identifier: MIT\npragma solidity ^0.8.34;\ncontract TestSuite {\n'+declarations+
      '\n  /// @custom:key box\n'+body+'\n}\n';
    rows.push({name:match[1],source});pattern.lastIndex=end;
  }
  if(rows.length!==new Set(rows.map(r=>r.name)).size)throw new Error('Duplicate TestSuite function');
  return rows;
}

export async function prepare(directory){
  fs.mkdirSync(directory,{recursive:true});
  const inventory=fs.readFileSync(path.join(root,'Bridge/SolidityVelvet/TestSuite.lean'),'utf8');
  const rows=suiteSources(inventory),trials=[];
  for(const row of rows){
    const source=path.join(directory,row.name+'.sol'),fixture=path.join(directory,row.name+'.ast.json');
    fs.writeFileSync(source,row.source);
    const start=performance.now();
    const compiled=compileFixture({args:['--source',source,'--out',fixture,'--no-wrapper'],quiet:true});
    const ast=compiled.primaryAst??compiled.fixture.ast;
    const contract=ast.nodes.find(n=>n.nodeType==='ContractDefinition'&&n.name==='TestSuite');
    trials.push({name:row.name,function:row.name,contract:'TestSuite',source,sourceHash:sha(Buffer.from(row.source)),fixture,
      compilationMs:performance.now()-start,fixtureSha256:sha(fs.readFileSync(fixture)),request:{contract,function:row.name},requestSha256:sha(Buffer.from(JSON.stringify({contract,function:row.name})))});
  }
  const result={inventory:'Bridge/SolidityVelvet/TestSuite.lean',inventorySha256:sha(Buffer.from(inventory)),
    reading:'box (Velvet partial correctness)',count:rows.length,trials};
  fs.writeFileSync(path.join(directory,'inputs.json'),JSON.stringify(result,null,2)+'\n');
  return result;
}

export function validateInputs(inputs){
  const inventory=fs.readFileSync(path.join(root,inputs.inventory),'utf8');
  assert.equal(sha(Buffer.from(inventory)),inputs.inventorySha256,'stale TestSuite inventory');
  const current=suiteSources(inventory);
  assert.deepEqual(inputs.trials.map(t=>t.name),current.map(t=>t.name));
  for(const [i,t] of inputs.trials.entries()){
    assert.equal(sha(fs.readFileSync(t.source)),t.sourceHash,'changed workload source');
    assert.equal(t.sourceHash,sha(Buffer.from(current[i].source)),'stale workload conversion');
    assert.equal(sha(fs.readFileSync(t.fixture)),t.fixtureSha256,'changed workload AST');
    assert.equal(sha(Buffer.from(JSON.stringify(t.request))),t.requestSha256,'changed workload request');
  }
}

export async function measureNative(inputs,executable,repeats=3){
  const manifestPath=path.join(path.dirname(executable),'build.json');
  const manifest=JSON.parse(fs.readFileSync(manifestPath,'utf8'));
  assert.equal(sha(fs.readFileSync(path.join(root,'web/browser/direct-bridge.c'))),manifest.bridgeSha256,'stale compiled ABI bridge');
  assert.equal(sha(fs.readFileSync(executable)),manifest.executable,'compiled verifier bytes changed');
  for(const entry of manifest.sourceFiles)assert.equal(sha(fs.readFileSync(path.join(root,entry.module.replaceAll('.','/')+'.lean'))),entry.sourceSha256,'stale compiled verifier: '+entry.module);
  const start=performance.now(),child=spawn(executable,[],{stdio:['pipe','pipe','pipe']});
  let pending,stderr='';
  const receive=()=>new Promise((resolve,reject)=>{pending={resolve,reject};});
  const ready=receive();
  createInterface({input:child.stdout}).on('line',line=>{const p=pending;pending=undefined;try{p?.resolve(JSON.parse(line));}catch(e){p?.reject(e);}});
  child.stderr.on('data',d=>{stderr=(stderr+d).slice(-4000);});
  child.on('error',e=>pending?.reject(e));child.on('exit',()=>pending?.reject(new Error('Verifier exited: '+stderr)));
  const report={backend:'generated-c-native',executableSha256:manifest.executable,manifestSha256:sha(fs.readFileSync(manifestPath)),leanCommit:manifest.leanCommit,trials:[]};
  try{
    const boot=await ready;if(boot.ready!==true)throw new Error('Invalid startup handshake');
    report.startupMs=performance.now()-start;
    for(let round=0;round<repeats;round++)for(const input of inputs.trials){
      const before=performance.now(),reply=receive();
      child.stdin.write(JSON.stringify(input.request)+'\n');
      const result=await reply;
      report.trials.push({name:input.name,round,sourceHash:input.sourceHash,wallMs:performance.now()-before,result});
    }
  }finally{child.kill();}
  return report;
}

if(process.argv[1]&&path.resolve(process.argv[1])===fileURLToPath(import.meta.url)){
  const directory=path.resolve(process.env.TESTSUITE_BENCH_DIR||path.join(root,'.lake/testsuite-performance'));
  const inputs=process.argv.includes('--reuse')?JSON.parse(fs.readFileSync(path.join(directory,'inputs.json'),'utf8')):await prepare(directory);
  validateInputs(inputs);
  console.log('Prepared '+inputs.count+' TestSuite functions');
  if(process.argv.includes('--native')){
    const report=await measureNative(inputs,path.resolve(process.env.DIRECT_NATIVE||path.join(root,'.lake/direct-native/direct-check')));
    report.passed=report.trials.length===inputs.count*3&&report.trials.every(t=>t.result.results?.length===1&&t.result.results[0].status==='proved');
    fs.writeFileSync(path.join(directory,'native.json'),JSON.stringify(report,null,2)+'\n');
    assert.equal(report.passed,true,'all 83 suite obligations must be proved in every round');
    console.log(JSON.stringify({startupMs:report.startupMs,firstRound:report.trials.filter(t=>t.round===0).map(t=>({name:t.name,ms:t.wallMs,status:t.result.results?.[0]?.status,gap:t.result.gap}))},null,2));
  }
}
