// Live incomplete-buffer fallback; no compiler/kernel/native UI evidence.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),lang=require('../src/language-services.cjs');
const names=text=>lang.completion(text,lang.position(text,text.length)).items.map(i=>i.label);
test('comment and literal declarations cannot shadow real fallback receiver types',()=>{
 const base=names('uint[] array; array.');assert.ok(base.includes('length'));
 for(const decoy of ['// bool array;\n','/* bool array; */','string s="bool array";','string s=unicode"😀 bool array";'])assert.deepEqual(names('uint[] array; '+decoy+' array.'),base,decoy);
});
test('commented or quoted functions cannot become fallback contract members',()=>{
 const source='contract C { /* function phantom() public {} */ string s="function fake() public {}"; function real() public {} function use() public { this.';
 assert.deepEqual(names(source),['real','use']);
});
test('struct member scans ignore comments while preserving real names',()=>{
 assert.deepEqual(names('struct S { uint real; /* bool phantom; */ } S item; item.'),['real']);
 assert.deepEqual(names('enum E { First, /* Phantom, */ Second } E.'),[],'existing unsupported static-enum fallback remains unchanged');
});
test('CR LF CRLF and unicode masking preserve following declarations and live receivers',()=>{
 for(const newline of ['\r','\n','\r\n'])assert.ok(names('uint[] array; // 😀 bool array;'+newline+'array.').includes('length'));
 assert.deepEqual(names('uint[] array; bool array; array.'),[],'real latest declaration behavior retained');
});
