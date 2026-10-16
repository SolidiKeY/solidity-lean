import test from 'node:test';
import assert from 'node:assert/strict';
import { ruleInventory, diffRules, ruleDelta, compareResults, snapshot, verifySnapshot } from './solkey-migration.mjs';
import { mkdtempSync, mkdirSync, writeFileSync, readFileSync, rmSync } from 'node:fs';
import { tmpdir } from 'node:os';
import { join } from 'node:path';
import { execFileSync } from 'node:child_process';
test('rule changes include bodies and ignore comments', () => {
  const a = ruleInventory('    example {\n \\find(x) \\replacewith(y)\n }');
  const b = ruleInventory('    example { // comment\n \\find(x) \\replacewith(z)\n }\n    newRule { \\find(z) }');
  assert.deepEqual(diffRules(a,b), {added:['newRule'], removed:[], changed:['example']});
  assert.deepEqual(ruleInventory('    example { /* comment */\n \\find(x) \\replacewith(y)\n }'),a);
});
test('coverage comparison rejects missing, duplicate, unexpected and error rows', () => {
  const row = {source:'a.sol',contract:'A',function:'f',status:'proved'};
  const expected = {version:1,commit:'abc',mode:'proof',sources:['a.sol'],results:[row]};
  const report = {...expected,completed:['a.sol'],errors:[]};
  assert.deepEqual(compareResults(expected, report), []);
  assert.equal(compareResults(expected, {...report,results:[]})[0].kind,'missing');
  assert.equal(compareResults(expected, {...report,results:[row,row]})[0].kind,'duplicate');
  assert.equal(compareResults(expected, {...report,results:[row,{...row,function:'g'}]})[0].kind,'unexpected');
  assert.equal(compareResults(expected, {...report,errors:[{reason:'timeout'}]})[0].kind,'error');
  assert.equal(compareResults(expected, {...report,results:[{...row,status:'pending'}]})[0].kind,'changed');
  assert.equal(compareResults(expected, {...report,completed:[]})[0].kind,'incomplete');
  assert.equal(compareResults(expected, {...report,commit:'wrong'})[0].kind,'commit');
  assert.equal(compareResults(expected, {...report,mode:'listing'})[0].kind,'mode');
  assert.equal(compareResults(expected, {...report,sources:[]})[0].kind,'sourceCoverage');
  assert.throws(() => compareResults({...expected,results:[]},report));
  assert.equal(compareResults({...expected,importGaps:[{source:'a.sol',contract:'A'}]},report)[0].kind,'unaccountedImport');
  assert.equal(compareResults({...expected,results:[{...row,status:'pending'}]},
    {...report,results:[{...row,status:'pending',reason:'maximum number of heartbeats exceeded'}]})[0].kind,'runtimeFailure');
});
test('rule strings preserve spaces and comment markers', () => {
  const r = s => ruleInventory(`    rule { \\branchlabel("${s}") }`);
  assert.notDeepEqual(r('a  b'),r('a b'));
  assert.notDeepEqual(r('a//b'),r('a'));
  assert.notDeepEqual(r('a/*b*/'),r('a'));
});
test('snapshots round-trip committed content and reject drift and repinning', () => {
  const repo=mkdtempSync(join(tmpdir(),'migration-test-'));
  const git = (...args) => execFileSync('git',['-C',repo,...args], {stdio:'pipe'});
  try {
    git('init'); git('config','user.name','Test'); git('config','user.email','test@example.invalid');
    mkdirSync(join(repo,'keyext.solidity.examples'));
    writeFileSync(join(repo,'keyext.solidity.examples/A.sol'),'contract A {}');
    const coreExample = 'keyext.solidity.core/src/test/resources/org/key_project/solidity/examples/fixture.key';
    mkdirSync(join(repo,'keyext.solidity.core/src/test/resources/org/key_project/solidity/examples'),{recursive:true});
    writeFileSync(join(repo,coreExample),'\\problem { true }');
    const rulePath='core/proof/rules/fixture.key';
    mkdirSync(join(repo,'core/proof/rules'),{recursive:true});
    writeFileSync(join(repo,rulePath),'    removedRule { \\find(x) }');
    git('add','.'); git('commit','-m','fixture');
    const destination=join(repo,'snapshot');
    const m=snapshot(repo,'HEAD',destination);
    assert.ok(m.files.some(f => f.path === coreExample));
    assert.equal(verifySnapshot(destination).commit,m.commit);
    writeFileSync(join(repo,'keyext.solidity.examples/A.sol'),'uncommitted');
    assert.equal(readFileSync(join(destination,'keyext.solidity.examples/A.sol'),'utf8'),'contract A {}');
    const manifestPath=join(destination,'snapshot.json'); const original=readFileSync(manifestPath);
    writeFileSync(manifestPath,JSON.stringify({...m,files:[]}));
    assert.throws(()=>verifySnapshot(destination),/manifest drift/);
    writeFileSync(manifestPath,original);
    git('rm',rulePath);
    git('add','keyext.solidity.examples/A.sol');git('commit','-m','change');
    assert.deepEqual(ruleDelta(repo,m.commit,'HEAD')[rulePath],{added:[],removed:['removedRule'],changed:[]});
    assert.throws(()=>snapshot(repo,'HEAD',destination),/another revision/);
    writeFileSync(join(destination,'keyext.solidity.examples/A.sol'),'drift');
    assert.throws(()=>verifySnapshot(destination),/snapshot drift/);
  } finally { rmSync(repo,{recursive:true,force:true}); }
});
