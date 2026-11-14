import test from 'node:test';
import assert from 'node:assert/strict';
import {compareModes} from './verify-agreement.mjs';
const row = {source:'fixture.sol', contract:'C', function:'f', sourceId:12, status:'proved', reading:'solc', assumptions:{callback:'noCallback',overflow:'default',tails:'solc',order:'legacy',hash:'opaque',zeroAddress:'noCode'}, sourceSha256:'a'.repeat(64), requestSha256:'b'.repeat(64)};
const report = (verification, rows = [row]) => ({results:rows.map(r => ({...r, verification})), errors:[]});
const fast = () => report('native');
const certified = () => report('certified');
test('matching explicit verdicts agree without mutating reports', () => {
  const a=fast(), b=certified(), before=JSON.stringify([a,b]);
  assert.deepEqual(compareModes(a,b,[row]), {status:'agree', obligations:1, bugs:[]});
  assert.equal(JSON.stringify([a,b]),before);
});
test('a false native success is a bug', () => {
  assert.match(compareModes(fast(),report('certified',[{...row,status:'refuted'}]),[row]).bugs.join(' '), /verdict disagreement/);
});
test('missing, duplicate, empty and failed workloads cannot agree', () => {
  for (const a of [report('native',[]), report('native',[row,row]), {results:fast().results,errors:[{reason:'timeout'}]}, null])
    assert.equal(compareModes(a,certified(),[row]).status,'bug');
});
test('direct output cannot masquerade as native or certified', () => {
  for (const marker of [undefined,'direct','certified']) assert.equal(compareModes(report(marker),certified(),[row]).status,'bug');
  for (const marker of [undefined,'direct','native']) assert.equal(compareModes(fast(),report(marker),[row]).status,'bug');
});
test('identity includes source, contract and source id', () => {
  for (const changed of [{source:'other.sol'},{contract:'D'},{sourceId:13},{function:'g'}])
    assert.equal(compareModes(fast(),report('certified',[{...row,...changed}]),[row]).status,'bug');
});

test('shared omissions, changed readings and failed rows are bugs', () => {
  assert.equal(compareModes(fast(),certified(),[row,{...row,function:'missing'}]).status,'bug');
  assert.equal(compareModes(fast(),certified()).status,'bug');
  for (const changed of [{reading:'clean'}, {sourceSha256:'c'.repeat(64)}, {requestSha256:'d'.repeat(64)}, {status:'error'}, {sourceId:undefined}, {assumptions:{...row.assumptions,callback:'withCallback'}}])
    assert.equal(compareModes(report('native',[{...row,...changed}]),report('certified',[{...row,...changed}]),[row]).status,'bug');
  assert.equal(compareModes(report('native',[null]),certified(),[row]).status,'bug');
  assert.equal(compareModes({results:fast().results,errors:[null]},certified(),[row]).status,'bug');
});
