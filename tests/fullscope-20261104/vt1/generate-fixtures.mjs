import {controls, expected} from './control-spec.mjs';
import {createHash} from 'node:crypto';
import {readFileSync, writeFileSync} from 'node:fs';
import {createRequire} from 'node:module';
import {fileURLToPath} from 'node:url';
import {resolve, dirname, join} from 'node:path';
import assert from 'node:assert/strict';
import {COMPILERS} from '../../../scripts/solc-unit.mjs';

const here = dirname(fileURLToPath(import.meta.url));
const compiler = resolve(process.argv[2] ?? '/workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js');
const sha = bytes => createHash('sha256').update(bytes).digest('hex');
const pin = COMPILERS.find(p => p.version.startsWith('0.8.38+'));
assert.equal(sha(readFileSync(compiler)), pin.sha256, 'compiler SHA-256 mismatch');
const solc = createRequire(import.meta.url)(compiler);
assert.equal(solc.cwrap('solidity_version', 'string', [])(), pin.version);
const compile = solc.cwrap('solidity_compile', 'string', ['string', 'number', 'number']);
const run = input => JSON.parse(compile(JSON.stringify(input), 0, 0));
const errors = output => (output.errors ?? []).filter(e => e.severity === 'error');
const content = readFileSync(join(here, 'Census.sol'), 'utf8');
const input = {language:'Solidity', sources:{'Census.sol':{content}}, settings:{
  viaIR:true, evmVersion:'osaka', optimizer:{enabled:false, runs:200},
  outputSelection:{'*':{'*':['ir','irOptimized','evm.bytecode.object','evm.deployedBytecode.object'], '':['ast']}}
}};
const output = run(input);
assert.deepEqual(errors(output), []);
const files = [];
function save(name, bytes) {
  const data = typeof bytes === 'string' ? bytes : JSON.stringify(bytes, null, 2) + '\n';
  writeFileSync(join(here, 'fixtures', name), data);
  files.push({name, sha256:sha(data), bytes:Buffer.byteLength(data)});
}
save('input.json', input);
save('output.json', output);
// Mask comments and quoted strings together: a function spelling inside either
// is not a declaration. This remains a census, not a checked Yul parser.
const codeOnly = ir => ir.replace(/\/\/[^\n]*|\/\*[\s\S]*?\*\/|"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*'/g,
  text => text.replace(/[^\n]/g, ' '));
assert.equal(codeOnly('// function fake()\n"function quoted()"\nfunction real()').match(/function/g).length, 1);
const census = [];
for (const [name, contract] of Object.entries(output.contracts['Census.sol'])) {
  for (const [field, mode] of [['ir','unoptimized'], ['irOptimized','optimized']]) {
    const ir = contract[field];
    assert.equal(typeof ir, 'string');
    assert.ok(ir.includes('object "'), 'object output absent');
    save(`${name}.${mode}.yul`, ir);
    // Census only: this is neither a parser nor semantic function matching.
    const functions = [...codeOnly(ir).matchAll(/\bfunction\s+([A-Za-z_$][A-Za-z0-9_$]*)\s*\(/g)].map(m=>m[1]);
    census.push({contract:name, mode, functions,
      sourceFunctions:functions.filter(n=>n.startsWith('fun_')),
      helpers:functions.filter(n=>!n.startsWith('fun_'))});
  }
}
assert.ok(census.some(c=>c.helpers.some(n=>n.startsWith('checked_add_'))));
assert.ok(census.some(c=>c.helpers.some(n=>n.startsWith('abi_decode_'))));
assert.ok(census.some(c=>c.helpers.some(n=>n.startsWith('array_push_'))));
save('census.json', census);
// Diagnostic crosswalk only: compiler AST IDs identify definitions; no Stmt
// lowering, helper meaning, or simulation certificate is inferred from names.
const definitions=output.sources['Census.sol'].ast.nodes
  .filter(n=>n.nodeType==='ContractDefinition')
  .flatMap(c=>c.nodes.filter(n=>n.nodeType==='FunctionDefinition')
    .map(n=>({contract:c.name,id:n.id,name:n.name,kind:n.kind,src:n.src})));
const crosswalk=census.filter(c=>c.mode==='unoptimized').flatMap(c=>c.sourceFunctions.map(irName=>{
  const match=/^fun_(.+)_([0-9]+)$/.exec(irName);
  assert.ok(match, `unexpected unoptimized function name ${irName}`);
  const definition=definitions.find(d=>d.contract===c.contract&&d.id===Number(match[2])&&d.name===match[1]);
  assert.ok(definition, `no matching compiler AST ID: ${irName}`);
  return {irName,definition};
}));
assert.equal(crosswalk.length,8);
save('source-id-crosswalk.json',{status:'external name/id association, not semantic matching',definitions,crosswalk});
const results = controls.map(([id, content])=>{
  const request={language:'Yul',sources:{'control.yul':{content}},settings:{evmVersion:'osaka',outputSelection:{'*':{'*':['evm.bytecode.object']}}}};
  const diagnostics=errors(run(request));
  assert.deepEqual(diagnostics.map(d=>[d.type,d.message]), [expected[id]], `wrong diagnostic: ${id}`);
  return {id, input:request, diagnostics};
});
const positive = run({language:'Yul',sources:{'valid.yul':{content:'object "A" { code { let p := memoryguard(128) pop(p) } }'}},settings:{evmVersion:'osaka',outputSelection:{'*':{'*':['evm.bytecode.object']}}}});
assert.deepEqual(errors(positive), []);
save('controls.json', {negative:results, positive:{id:'memoryguard-literal', diagnostics:errors(positive)}});
save('manifest.json', {compiler:pin, sourceSha256:sha(content), files});
console.log(JSON.stringify({compiler:pin.version, contracts:census.length/2, censusFunctions:census.reduce((n,c)=>n+c.functions.length,0), rejectedControls:results.length, positiveControls:1}));
