import { test } from 'node:test';
import assert from 'node:assert/strict';
import { sourceHash, sourceRange, sourceLocations } from './source-locations.mjs';

test('solc byte offsets become zero-based UTF-16 positions across CRLF and Unicode', () => {
  const prefix = '// 🐦 é\r\ncontract C { /* 🦉 */ ';
  const body = 'function f() {}';
  const bytes = Buffer.from(prefix + body + '\r\n}');
  const src = `${Buffer.byteLength(prefix)}:${Buffer.byteLength(body)}:0`;
  assert.deepEqual(sourceRange(bytes, src), {
    start: { line: 1, character: 'contract C { /* 🦉 */ '.length },
    end: { line: 1, character: 'contract C { /* 🦉 */ '.length + body.length },
  });
  assert.equal(sourceHash(bytes), sourceHash(Buffer.from(bytes)));
  assert.notEqual(sourceHash(bytes), sourceHash(Buffer.from(prefix + body)));
});

test('invalid, foreign-source and split UTF-8 ranges have no editor location', () => {
  const bytes = Buffer.from('é');
  for (const src of [undefined, '', '-1:1:0', '0:1:1', '0:1:-1', '1:1:0', '0:1:0', '0:3:0', '999999999999999999:0:0'])
    assert.equal(sourceRange(bytes, src), undefined, src);
  assert.deepEqual(sourceRange(bytes, '2:0:0'), {start:{line:0,character:1},end:{line:0,character:1}});
});

test('editor positions omit the UTF-8 BOM and recognize CR-only lines', () => {
  assert.deepEqual(sourceRange(Buffer.from('\uFEFFabc'), '3:3:0'), {
    start:{line:0,character:0}, end:{line:0,character:3},
  });
  assert.deepEqual(sourceRange(Buffer.from('a\rb'), '2:1:0'), {
    start:{line:1,character:0}, end:{line:1,character:1},
  });
});

test('declaration IDs distinguish same-line overloads, contracts and renamed functions', () => {
  const bytes = Buffer.from('contract C { function f() {} function f(uint x) {} }');
  const first = bytes.indexOf('function'), second = bytes.indexOf('function', first + 1);
  const locate = sourceLocations({nodes:[{nodeType:'ContractDefinition',name:'C',src:`0:${bytes.length}:0`,nodes:[
    {nodeType:'FunctionDefinition',id:12,src:`${first}:15:0`},
    {nodeType:'FunctionDefinition',id:24,src:`${second}:20:0`},
  ]}]}, bytes);
  assert.equal(locate('C', {sourceId:12,function:'renamed'}).start.character, first);
  assert.equal(locate('C', {sourceId:24,function:'f'}).start.character, second);
  assert.equal(locate('Other', {sourceId:12}), undefined);
  assert.equal(locate('C', {sourceId:99,function:'f'}), undefined);
  assert.equal(locate('C', {function:'f'}), undefined);
  assert.equal(locate('C', {sourceId:-1,function:'constructor'}).start.character, 0);
  assert.equal(locate('C', {sourceId:-1,function:'f'}), undefined);
});
