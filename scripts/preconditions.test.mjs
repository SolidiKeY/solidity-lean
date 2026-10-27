import {test} from 'node:test';
import assert from 'node:assert/strict';
import {mkdtempSync,mkdirSync,writeFileSync,rmSync} from 'node:fs';
import {tmpdir} from 'node:os';
import {join} from 'node:path';
import {fileURLToPath} from 'node:url';
import backend from '../vscode/src/backend.cjs';
import {runSolidityTests,testsPassed} from './test-solidity.mjs';

test('strict reports require possible entry conditions when auditing is requested', () => {
  const report = preconditions => ({results:[{status:'proved',preconditions}],errors:[]});
  assert.equal(testsPassed(report(undefined)), true);
  assert.equal(testsPassed(report('possible')), true);
  assert.equal(testsPassed(report('notApplicable')), true);
  assert.equal(testsPassed(report('impossible')), false);
  assert.equal(testsPassed(report('unknown')), false);
  assert.equal(testsPassed(report('notRun')), false);
  assert.equal(testsPassed(report('guessed')), false);
  assert.throws(() => runSolidityTests(['tests/solc/Preconditions.sol'],{list:true,auditPreconditions:true,build:false}), /omit --list/);
});

test('source precondition audits retain kernel-checked possibility separately from postconditions', () => {
  const plain = runSolidityTests(['tests/solc/Preconditions.sol'],{build:false,function:'impossible'});
  assert.deepEqual(plain.errors, []);
  assert.equal(plain.results[0].status, 'proved');
  assert.equal(plain.results[0].preconditions, undefined);
  assert.equal(testsPassed(plain), true);

  const audited = runSolidityTests(['tests/solc/Preconditions.sol'],{build:false,auditPreconditions:true,batchSize:2});
  assert.deepEqual(audited.errors, []);
  const rows = Object.fromEntries(audited.results.map(row => [row.function,row]));
  assert.equal(rows.impossible.status, 'proved');
  assert.equal(rows.impossible.preconditions, 'impossible');
  assert.match(rows.impossible.preconditionReason, /kernel-checked/);
  assert.equal(rows.possible.status, 'proved');
  assert.equal(rows.possible.preconditions, 'possible');
  assert.equal(rows.badPost.status, 'pending');
  assert.equal(rows.badPost.preconditions, 'possible');
  assert.equal(rows.plain.preconditions, 'notApplicable');
  assert.equal(rows.wide.status, 'proved');
  assert.equal(rows.wide.preconditions, 'possible');
  assert.ok(audited.results.every(row => row.range && row.sourceHash));
  assert.equal(testsPassed(audited), false);

  const selected = runSolidityTests(['tests/solc/Preconditions.sol'],{build:false,auditPreconditions:true,function:'possible'});
  assert.deepEqual(selected.errors, []);
  assert.equal(testsPassed(selected), true);
});

test('audited batch failure retains completed siblings through the extension adapter', {skip:process.platform === 'win32'}, async () => {
  const root = mkdtempSync(join(tmpdir(),'solidity-audit-batch-'));
  const previousPath = process.env.PATH;
  try {
    const bin = join(root,'bin');
    mkdirSync(bin);
    const source = join(root,'Batch.sol');
    writeFileSync(source, 'pragma solidity ^0.8.34;\ncontract Batch {\n' + Array.from({length:33},(_,i) =>
      `/// @custom:key ensures true\nfunction f${i}() public pure {}`).join('\n') + '\n}\n');
    // Use the real compiler and protocol, with a fixture Lake process that
    // completes one batch and fails the next before its first checkpoint.
    writeFileSync(join(bin,'lake'), `#!${process.execPath}
const {readFileSync,writeFileSync}=require('node:fs');
const {dirname,join}=require('node:path');
if(process.argv[2]==='build') process.exit(0);
const wrapper=process.argv.find(a=>a.endsWith('.lean'));
const text=readFileSync(wrapper,'utf8');
const output=JSON.parse(/ to ("(?:\\\\.|[^"\\\\])*")/.exec(text)[1]);
const ast=JSON.parse(readFileSync(join(dirname(wrapper),'source.ast.json'),'utf8')).ast;
const funs=ast.nodes.find(n=>n.nodeType==='ContractDefinition').nodes.filter(n=>n.nodeType==='FunctionDefinition');
let rows=funs.map(f=>({function:f.name,signature:f.name+'()',sourceId:f.id,status:'ready',tag:'specified',reason:'',reading:'solc',elapsedMs:0}));
if(!text.includes(' listing ')) {
 const first=Number(/ from (\\d+)/.exec(text)[1]);
 const count=Number(/ count (\\d+)/.exec(text)[1]);
 if(first>0) process.exit(2);
 rows=rows.slice(first,first+count).map(r=>({...r,status:'proved',preconditions:'possible',preconditionReason:'fixture certificate'}));
}
writeFileSync(output,JSON.stringify(rows));
`, {mode:0o700});
    process.env.PATH = bin + ':' + (previousPath || '');
    const report = await backend.runBackend({backendPath:fileURLToPath(new URL('../',import.meta.url)),
      nodePath:process.execPath,source,auditPreconditions:true,timeoutMs:20000});
    assert.equal(report.results.length,33);
    assert.equal(report.results[0].status,'proved');
    assert.equal(report.results[0].preconditions,'possible');
    assert.equal(report.results[32].status,'notRun');
    assert.equal(report.results[32].preconditions,'notRun');
    assert.match(report.results[32].preconditionReason,/before checkpoint/);
    assert.equal(report.errors.length,1);
    assert.equal(testsPassed(report),false);
  } finally {
    if(previousPath === undefined) delete process.env.PATH;
    else process.env.PATH = previousPath;
    rmSync(root,{recursive:true,force:true});
  }
});
