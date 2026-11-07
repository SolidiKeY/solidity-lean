#!/usr/bin/env node
/** Pinned compiler admission probe only. This never certifies Source support. */
import {readFileSync,writeFileSync,mkdirSync} from 'node:fs';
import {resolve,join} from 'node:path';
import {pathToFileURL} from 'node:url';
import {createHash} from 'node:crypto';
import assert from 'node:assert/strict';
const [compilerPath, helperPath, fixtureDir, destination] = process.argv.slice(2);
assert(compilerPath && helperPath && fixtureDir && destination,
  'usage: probe.mjs pinned-soljson committed-harness.mjs fixture-directory output-directory');
const hash = data => createHash('sha256').update(data).digest('hex');
const EXPECTED_SHA256='a37502caf84098877d0c02a44b08e476a400bb9afaedc205da298d95a71ede8d';
const expectedBytes=readFileSync(join(fixtureDir,'expected.json'));
assert.equal(hash(expectedBytes),EXPECTED_SHA256,'expected manifest hash mismatch');
const expected=JSON.parse(expectedBytes);
const helperBytes=readFileSync(helperPath);
assert.equal(hash(helperBytes),expected.compilerHelperSha256,'compiler helper hash mismatch');
const {checkedCompiler,inputFor,VERSION,COMPILER_SHA} = await import(pathToFileURL(resolve(helperPath)));
assert.equal(expected.compiler,VERSION);
assert.equal(expected.evmVersion,'osaka');
assert.deepEqual(expected.pipelines,['legacy','viaIR']);
assert.deepEqual(expected.optimizer,[false,true]);
const compile=checkedCompiler(compilerPath);
assert.equal(hash(readFileSync(compilerPath)),COMPILER_SHA);
mkdirSync(destination,{recursive:true});
const rows=[];
for(const fixture of expected.fixtures) {
  assert.match(fixture.file,/^[A-Za-z]+\.sol$/);
  assert.equal(typeof fixture.compilerAccepted,'boolean');
  assert.equal(typeof fixture.sourceDesiredAccepted,'boolean');
  const source=readFileSync(join(fixtureDir,fixture.file),'utf8');
  assert.equal(hash(source),fixture.sourceSha256,'fixture source hash mismatch');
  for(const pipeline of expected.pipelines) for(const optimized of expected.optimizer) {
    const input=inputFor({[fixture.file]:{content:source}},pipeline,optimized);
    const raw=compile(input),output=JSON.parse(raw);
    const errors=(output.errors??[]).filter(x=>x.severity==='error');
    const accepted=errors.length===0 && typeof output.contracts?.[fixture.file]?.C?.evm?.bytecode?.object==='string';
    const id=fixture.file.replace('.sol','')+'-'+pipeline+'-'+(optimized?'on':'off');
    writeFileSync(join(destination,id+'.input.json'),JSON.stringify(input,null,2)+'\n');
    writeFileSync(join(destination,id+'.output.json'),raw+'\n');
    rows.push({id,fixture:fixture.file,pipeline,optimized,sourceSha256:hash(source),
      inputSha256:hash(JSON.stringify(input)),rawOutputSha256:hash(raw),accepted,
      expectedAccepted:fixture.compilerAccepted,match:accepted===fixture.compilerAccepted,
      diagnostics:errors.map(({errorCode,message})=>({errorCode,message})),
      storageLayout:output.contracts?.[fixture.file]?.C?.storageLayout??null});
  }
}
assert.equal(rows.length,expected.fixtures.length*4);
const report={kind:'compiler-admission-only',compiler:VERSION,compilerSha256:COMPILER_SHA,
  helperSha256:hash(readFileSync(helperPath)),expectedSha256:hash(readFileSync(join(fixtureDir,'expected.json'))),
  rows,allMatch:rows.every(x=>x.match),sourceSupport:'not implemented by this probe',nativeRuntimeComparisons:0};
writeFileSync(join(destination,'report.json'),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({compiler:VERSION,rows:rows.length,matches:rows.filter(x=>x.match).length,
  sourceSupport:report.sourceSupport,nativeRuntimeComparisons:0}));
if(!report.allMatch) process.exitCode=1;
