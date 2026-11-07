// Fresh compiler provenance for the eight existing specification controls.
import fs from 'node:fs';
import path from 'node:path';
import assert from 'node:assert/strict';
import {createHash} from 'node:crypto';
import {compileFixture} from '../../../scripts/solc-ast.mjs';
import {measureNative} from '../../../scripts/testsuite-performance.mjs';
const root=path.resolve('.'),out=path.join(root,'docs/benchmarks/directruntime-2026-11-04/before/fresh-spec-controls');
if(fs.existsSync(out))throw new Error('Refusing to overwrite fresh control evidence');
fs.mkdirSync(out,{recursive:true});
const sha=bytes=>createHash('sha256').update(bytes).digest('hex');
const original=path.join(root,'tests/automation/ClosedSpecs.sol'),text=fs.readFileSync(original);
const source=path.join(out,'ClosedSpecs.sol'),fixture=path.join(out,'ClosedSpecs.ast.json');
fs.writeFileSync(source,text);
const compiled=compileFixture({args:['--source',source,'--out',fixture,'--no-wrapper'],quiet:true});
assert.equal(compiled.fixture.header.sourceSha256,sha(text));
const ast=compiled.primaryAst??compiled.fixture.ast;
const contract=ast.nodes.find(n=>n.nodeType==='ContractDefinition');
const trials=[['maximum','proved'],['falseMaximum','refuted'],['storeMaximum','proved'],['twoChoices','proved'],['constantOne','proved'],['falseConstant','refuted'],['store','proved'],['falseStore','refuted']].map(([name,expected])=>{
 const request={contract,function:name};
 return {name,expected,source,sourceHash:sha(text),fixture,fixtureSha256:sha(fs.readFileSync(fixture)),request,requestSha256:sha(Buffer.from(JSON.stringify(request)))};
});
const report=await measureNative({trials},path.join(root,'.lake/direct-native/direct-check'),1);
report.sourceSha256=sha(text);report.compilerHeader=compiled.fixture.header;
report.originalFixtureSha256=sha(fs.readFileSync('tests/automation/ClosedSpecs.ast.json'));
report.freshFixtureSha256=sha(fs.readFileSync(fixture));report.failures=[];
for(const [i,trial]of report.trials.entries()){
 const expected=trials[i];
 if(trial.result.results?.length!==1||trial.result.results[0].function!==expected.name||trial.result.results[0].status!==expected.expected)
  report.failures.push({name:expected.name,expected:expected.expected,result:trial.result});
}
assert.equal(sha(fs.readFileSync(original)),report.sourceSha256);
assert.equal(sha(fs.readFileSync(source)),report.sourceSha256);
report.passed=report.trials.length===8&&!report.failures.length;
fs.writeFileSync(path.join(out,'inputs.json'),JSON.stringify({trials},null,2)+'\n');
fs.writeFileSync(path.join(out,'results.json'),JSON.stringify(report,null,2)+'\n');
console.log(JSON.stringify({passed:report.passed,requests:report.trials.length,failures:report.failures}));
assert.equal(report.passed,true);
