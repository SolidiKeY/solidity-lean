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

test('dynamic array fallback accepts token whitespace without changing storage rules',()=>{
 const expected=names('uint[] items; items.');
 for(const type of ['uint []','uint[ ]','uint [ ]','uint\t[\t]','uint\n[\n]','uint\r\n[\r\n]','uint\r[\r]'])assert.deepEqual(names(type+' items; items.'),expected,type);
 for(const location of ['memory','calldata'])assert.deepEqual(names('function use(){ uint [ ] '+location+' items; items.'),['length']);
 assert.deepEqual(names('function use(){ uint [ ] storage items; items.'),['length','push','pop']);
 for(const type of ['uint[2]','uint[][]'])assert.deepEqual(names(type+' items; items.'),[],'Existing unsupported fallback shape: '+type);
});
test('fallback receivers preserve dollar identifiers and cannot borrow longer names',()=>{
 for(const name of ['$items','items$','$'])assert.deepEqual(names('uint[] '+name+'; '+name+'.'),['length','push','pop'],name);
 assert.deepEqual(names('bool items; uint[] items$; items.'),[],'items$ cannot masquerade as items');
 assert.deepEqual(names('uint[] $items; bool $items; $items.'),[],'Actual same-name shadowing still wins');
});

test('same-contract state declarations after methods retain default-storage fallback hints',()=>{
 const expected=['length','push','pop'];
 for(const prior of ['constructor() {}','function toString() public {}','function valueOf() public {}','function __proto__() public {}','function before() public {}','struct functionMarker { uint value; }','function before() public returns(uint){return 1;}'])assert.deepEqual(names('contract C { '+prior+' uint[] items; function use() public { items.'),expected,prior);
 for(const local of ['uint[] items;','uint[] memory items;'])assert.deepEqual(names('contract C { function prior() public {} function use() public { '+local+' items.'),['length']);
 assert.deepEqual(names('contract C { function use(uint[] items) public { items.'),['length'],'Parameters are not state declarations');
 assert.deepEqual(names('contract First { function before() public {} uint[] items; } contract Second { function use() public { items.'),['length'],'No new mutation inference across contract owners');
 assert.deepEqual(names('contract C { function before() public {} ) uint[] items; function use() public { items.'),['length'],'Malformed declaration prefix cannot gain new storage inference');
 for(const broken of ['function before() public { ( } )','function before() public {} [','function before() public {} ]'])assert.deepEqual(names('contract C { '+broken+' uint[] items; function use() public { items.'),['length'],'Broken nesting: '+broken);
});
