import {controls as controlSources, expected} from './control-spec.mjs';
import {createHash} from 'node:crypto';
import {readFileSync, readdirSync} from 'node:fs';
import {dirname, join, resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import assert from 'node:assert/strict';
import {COMPILERS} from '../../../scripts/solc-unit.mjs';
const here=dirname(fileURLToPath(import.meta.url));
const sha = bytes => createHash('sha256').update(bytes).digest('hex');
export function verify(dir=join(here,'fixtures')) {
  const read = name => readFileSync(join(dir,name));
  const json = name => JSON.parse(read(name));
  const manifest=json('manifest.json');
  assert.deepEqual(manifest.compiler, COMPILERS.find(p=>p.version.startsWith('0.8.38+')));
  const names=manifest.files.map(f=>f.name);
  assert.equal(new Set(names).size,names.length,'duplicate manifest name');
  assert.deepEqual([...names,'manifest.json'].sort(), readdirSync(dir).sort(), 'inventory mismatch');
  for(const entry of manifest.files) {
    assert.match(entry.name,/^[A-Za-z0-9_.-]+$/, 'unsafe filename');
    const bytes=read(entry.name);
    assert.equal(bytes.length,entry.bytes,`${entry.name} length mismatch`);
    assert.equal(sha(bytes),entry.sha256,`${entry.name} hash mismatch`);
  }
  const source=readFileSync(join(here,'Census.sol'));
  assert.equal(sha(source),manifest.sourceSha256);
  const input=json('input.json'), output=json('output.json');
  assert.equal(input.language,'Solidity');
  assert.deepEqual(input.sources,{'Census.sol':{content:source.toString('utf8')}});
  assert.equal(input.settings.viaIR,true);
  assert.equal(input.settings.evmVersion,'osaka');
  assert.deepEqual(input.settings.optimizer,{enabled:false,runs:200});
  assert.equal((output.errors??[]).filter(d=>d.severity==='error').length,0);
  const census=json('census.json');
  assert.equal(census.length,2*Object.keys(output.contracts['Census.sol']).length);
  for(const [contract, value] of Object.entries(output.contracts['Census.sol'])) {
    for(const [field, mode] of [['ir','unoptimized'],['irOptimized','optimized']]) {
      assert.equal(read(`${contract}.${mode}.yul`).toString('utf8'),value[field], 'output channel mismatch');
      assert.equal(census.filter(c=>c.contract===contract&&c.mode===mode).length,1);
    }
  }
  const codeOnly=ir=>ir.replace(/\/\/[^\n]*|\/\*[\s\S]*?\*\/|"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*'/g, text=>text.replace(/[^\n]/g,' '));
  for(const row of census) {
    const functions=[...codeOnly(read(`${row.contract}.${row.mode}.yul`).toString('utf8'))
      .matchAll(/\bfunction\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*\(/g)].map(m=>m[1]);
    assert.deepEqual(row.functions,functions,'census declaration mismatch');
    assert.deepEqual(row.sourceFunctions,functions.filter(n=>n.startsWith('fun_')));
    assert.deepEqual(row.helpers,functions.filter(n=>!n.startsWith('fun_')));
  }
  const controls=json('controls.json');

  assert.deepEqual(controls.negative.map(c=>c.id).sort(),Object.keys(expected).sort());
  for(const control of controls.negative) {
    const content=controlSources.find(([id])=>id===control.id)[1];
    assert.deepEqual(control.input,{language:'Yul',sources:{'control.yul':{content}},settings:{evmVersion:'osaka',outputSelection:{'*':{'*':['evm.bytecode.object']}}}});
    assert.deepEqual(control.diagnostics.map(d=>[d.type,d.message]),[expected[control.id]]);
  }
  assert.deepEqual(controls.positive,{id:'memoryguard-literal',diagnostics:[]});
  const crosswalk=json('source-id-crosswalk.json');
  const definitions=output.sources['Census.sol'].ast.nodes
    .filter(n=>n.nodeType==='ContractDefinition')
    .flatMap(c=>c.nodes.filter(n=>n.nodeType==='FunctionDefinition')
      .map(n=>({contract:c.name,id:n.id,name:n.name,kind:n.kind,src:n.src})));
  assert.deepEqual(crosswalk.definitions,definitions);
  const associated=census.filter(c=>c.mode==='unoptimized').flatMap(c=>c.sourceFunctions.map(irName=>{
    const match=/^fun_(.+)_([0-9]+)$/.exec(irName);
    assert.ok(match);
    const definition=definitions.find(d=>d.contract===c.contract&&d.id===Number(match[2])&&d.name===match[1]);
    assert.ok(definition);
    return {irName,definition};
  }));
  assert.deepEqual(crosswalk.crosswalk,associated);
  return {files:names.length, compiler:manifest.compiler.version};
}
if(process.argv[1] && resolve(process.argv[1])===fileURLToPath(import.meta.url))
  console.log(JSON.stringify(verify(process.argv[2])));
