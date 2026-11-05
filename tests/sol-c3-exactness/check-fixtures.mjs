#!/usr/bin/env node
/** External analysis comparison; mathematical claims reside in kernel proofs. */
import {readFileSync, writeFileSync} from 'node:fs';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import assert from 'node:assert/strict';
const sha=b=>createHash('sha256').update(b).digest('hex');
const root='tests/sol-c3-exactness/';
const args=process.argv.slice(2);
assert.equal(args.length,2,'usage: check-fixtures.mjs COMPILER OUTPUT');
const manifestBytes=readFileSync(root+'fixtures/manifest.json');
assert.equal(sha(manifestBytes),'9a2ab74a8040178026a74a04929116ce6d7d9ce064b315c5ba5c0678b342190f','fixed fixture expectations');
const m=JSON.parse(manifestBytes);
const pin={version:'0.8.38+commit.1835d247.Emscripten.clang',file:'soljson-v0.8.38+commit.1835d247.js',sha256:'6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390'};
assert.deepEqual(m.compiler,pin);
assert.equal(sha(readFileSync(args[0])),pin.sha256,'compiler digest');
const solc=createRequire(import.meta.url)(args[0]);
assert.equal(solc.cwrap('solidity_version','string',[])(),pin.version);
const compile=solc.cwrap('solidity_compile','string',['string','number','number']);
const results=[];
const errorsOnly=errors=>errors.map(({errorCode,type,message})=>({errorCode,type,message}));
function checkErrors(errors,expected){assert.deepEqual(errorsOnly(errors),expected,'exact diagnostic sequence');}
// Negative controls challenge the same comparison predicates used below.
const sample={errorCode:'5005',type:'TypeError',message:'Linearization of inheritance graph impossible'};
for(const changed of [[{...sample,errorCode:'2449'}],[{...sample,message:''}],[],[sample,sample]])
  assert.throws(()=>checkErrors(changed,[sample]));
assert.throws(()=>assert.deepEqual({D:['D','B','C','A']},{D:['D','C','B','A']}));
assert.throws(()=>assert.equal('0'.repeat(64),pin.sha256));
console.log('COMPILER_NEGATIVE_CONTROLS_PASS 6');
assert.deepEqual(m.fixtures.map(f=>f.name),['diamond','shared','redundant','interface','mixed','obstruction','self-cycle','mutual-cycle','illegal-interface']);
for(const f of m.fixtures){
  const bytes=readFileSync(f.source), content=new TextDecoder('utf-8',{fatal:true}).decode(bytes);
  assert.equal(sha(bytes),f.source_sha256,'source digest '+f.name);
  const input={language:'Solidity',sources:{[f.name+'.sol']:{content}},settings:{outputSelection:{'*':{'':['ast']}}}};
  const raw=compile(JSON.stringify(input),0,0), out=JSON.parse(raw);
  const errors=(out.errors??[]).filter(e=>e.severity==='error');
  checkErrors(errors,f.expected_errors);
  const row={name:f.name,source:f.source,source_sha256:f.source_sha256,input_sha256:sha(JSON.stringify(input)),output_sha256:sha(raw),errors};
  if(f.linearizations){
    assert.deepEqual(errors,[],f.name+' errors');
    const ast=out.sources?.[f.name+'.sol']?.ast;
    assert.equal(ast?.nodeType,'SourceUnit');
    const defs=ast.nodes.filter(n=>n.nodeType==='ContractDefinition');
    const ids=new Map(defs.map(d=>[d.id,d.name]));
    assert.equal(ids.size,defs.length);
    const orders={};
    for(const d of defs){
      assert.ok(Array.isArray(d.linearizedBaseContracts));
      const names=d.linearizedBaseContracts.map(i=>{assert.ok(ids.has(i),'foreign compiler identity');return ids.get(i);});
      assert.equal(new Set(names).size,names.length);
      orders[d.name]=names;
    }
    assert.deepEqual(orders,f.linearizations,'exact order '+f.name);
    row.linearizations=orders;
    row.reverse_name_sequences=Object.fromEntries(Object.entries(orders).map(([k,v])=>[k,[...v].reverse()]));
  }else{
    assert.ok(errors.length>0,'negative accepted '+f.name);
    assert.ok(f.expected_errors.length>0,'empty rejection expectation');
    row.rejection_boundary=['self-cycle','mutual-cycle'].includes(f.name)?'declaration-order admission; not a compiler C3-stage observation':'compiler semantic analysis';
  }
  row.kernel_observations=f.kernel_observations;
  if(f.comparison_limit)row.comparison_limit=f.comparison_limit;
  results.push(row);
  console.log('PASS '+f.name+(row.linearizations?' '+JSON.stringify(row.linearizations):' '+errors.map(e=>e.errorCode+': '+e.message).join('; ')));
}
const packet={compiler:pin,manifest_sha256:sha(manifestBytes),checker_sha256:sha(readFileSync(root+'check-fixtures.mjs')),results,negative_controls:6,boundary:m.boundary};
writeFileSync(args[1],JSON.stringify(packet,null,2)+'\n');
console.log('FIXTURE_PACKET_SHA256 '+sha(readFileSync(args[1])));
console.log('SOL_C3_COMPILER_FIXTURES_PASS '+results.length);
