// Lexical completion admission controls, not native editor or kernel evidence.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),lang=require('../src/language-services.cjs');
function query(marked){const at=marked.indexOf('|'),text=marked.replace('|','');return lang.completion(text,lang.position(text,at));}
test('comments and string literals cannot supply code completions',()=>{
 for(const source of ['// con|','// con|\ncontract C {}','/* con| */','/* con|','"con|"',"'con|'",'unicode"con|"','hex"ab|"','"con|','"escaped\\\" con|'])assert.deepEqual(query(source).items,[],source);
});
test('comments cannot masquerade as incomplete array receivers',()=>{assert.deepEqual(query('uint[] array; // array.|').items,[]);assert.deepEqual(query('uint[] array; /* array.| */').items,[]);});
test('closed tokens and CR LF CRLF line endings do not suppress following code',()=>{
 for(const newline of ['\r','\n','\r\n'])assert.ok(query('// ignored'+newline+'con|').items.some(i=>i.label==='contract'));
 for(const before of ['/* comment */','"string";',"'string';"])assert.ok(query(before+' con|').items.some(i=>i.label==='contract'));
 assert.ok(query('uint[] array; array.|').items.some(i=>i.label==='length'));
});

test('overlapping block opener is not a closing delimiter',()=>{assert.deepEqual(query('/*/|').items,[]);assert.ok(query('/**/ con|').items.some(i=>i.label==='contract'));});
