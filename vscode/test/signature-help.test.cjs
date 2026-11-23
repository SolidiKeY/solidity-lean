// Guard regressions: literal/comment punctuation and nested AST calls cannot
// select a foreign signature or advance the active argument. Injected controls only.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),lang=require('../src/language-services.cjs');
function fn(id,name,count=3){return{nodeType:'FunctionDefinition',id,name,parameters:{parameters:Array.from({length:count},(_,i)=>({name:'arg'+i,typeDescriptions:{typeString:'uint256'}}))}};}
function hint(text,analysis={nodes:[],declarations:new Map([[1,fn(1,'f')]])}){return lang.signatureHelp(text,lang.position(text,text.length),analysis);}
test('signature delimiters inside quoted and unicode literals are indivisible',()=>{for(const text of ['f("a,b(", 2',String.raw`f("a, and \"(", 2`,'f(unicode"é,😀(", 2']){const result=hint(text);assert.ok(result,text);assert.match(result.signatures[0].label,/^f\(/);assert.equal(result.activeParameter,1,text);}});
test('comments cannot create call parentheses or argument commas',()=>{for(const text of ['f(1 /* , ) ( */ , 2','f(1 // , (\r\n, 2','f /* ( , ) */ (1, 2']){const result=hint(text);assert.ok(result,text);assert.equal(result.activeParameter,1,text);}});
test('nested calls tuples and arrays preserve top-level argument counting',()=>{assert.equal(hint('f(g(1,2), [3,4], 5').activeParameter,2);assert.equal(hint('f((1,2), [3,4], 5').activeParameter,2);assert.equal(hint('f(1,2,3,4').activeParameter,2);});
test('non-call comments literals and completed calls produce no signature',()=>{for(const text of ['/* f( */','"f("','f(1)','plain'])assert.equal(hint(text),null,text);});
test('nested call selection uses real range width rather than src-string width',()=>{const text='outer(inner(123), 2)',at=text.indexOf('123'),innerStart=text.indexOf('inner'),innerLength='inner(123)'.length,outer={nodeType:'FunctionCall',src:`0:${text.length}:0`,expression:{referencedDeclaration:1}},inner={nodeType:'FunctionCall',src:`${innerStart}:${innerLength}:0`,expression:{referencedDeclaration:2}},analysis={nodes:[outer,inner],nodeRange:n=>lang.byteRange(text,n.src),declarations:new Map([[1,fn(1,'outer',2)],[2,fn(2,'inner',1)]])};assert.equal(outer.src.length,inner.src.length);const result=lang.signatureHelp(text,lang.position(text,at),analysis);assert.match(result.signatures[0].label,/^inner\(/);const parent=lang.signatureHelp(text,lang.position(text,innerStart+innerLength),analysis);assert.match(parent.signatures[0].label,/^outer\(/);assert.equal(parent.activeParameter,0);});
test('zero parameters and invalid positions retain their existing contracts',()=>{const analysis={nodes:[],declarations:new Map([[1,fn(1,'f',0)]])};assert.equal(hint('f(',analysis).activeParameter,0);assert.throws(()=>lang.signatureHelp('f(',{line:99,character:0},analysis),/outside/);assert.equal(lang.signatureHelp('f(',{line:0,character:2},undefined),null);});

test('CR-only comments terminate consistently with LSP lines and Solidity imports',()=>{const syntax=require('../src/solidity-text.cjs');for(const newline of [String.fromCharCode(10),String.fromCharCode(13,10),String.fromCharCode(13)]){assert.equal(hint('f(1 // comment'+newline+', 2').activeParameter,1);assert.deepEqual(syntax.imports('// comment'+newline+'import "./Dep.sol";'),['./Dep.sol']);assert.equal(syntax.tokens('// comment'+newline+'x')[0].text,'// comment');}});

test('function declaration parameters cannot masquerade as a call signature',()=>{
 for(const newline of ['\n','\r\n','\r'])for(const prefix of ['function f(', 'function /* declaration */ f(', 'function'+newline+'f('])assert.equal(hint(prefix+'uint arg0, uint arg1'),null,prefix);
 assert.ok(hint('f(1, 2'));assert.ok(hint('return f(1, 2'));assert.ok(hint('object.f(1, 2'));
});

test('grouping parentheses retain the enclosing named-call argument',()=>{
 for(const [text,argument]of [['f((1+2',0],['f(1,(2+3',1],['f(1, /* comma , ( */ (2+3',1],['f((1 // comma ,'+String.fromCharCode(13)+'+2',0]]){const result=hint(text);assert.ok(result,text);assert.match(result.signatures[0].label,/^f\(/);assert.equal(result.activeParameter,argument);}
 for(const text of ['f((g)(1','f(array[0](1','f(g{gas:100}(1,2','f(object.g{gas:100}(1,2'])assert.equal(hint(text),null,'Unresolved indirect callee must not borrow f signature');
 const analysis={nodes:[],declarations:new Map([[1,fn(1,'f')],[2,fn(2,'g')]])},result=hint('f(g((1+2',analysis);assert.match(result.signatures[0].label,/^g\(/);assert.equal(result.activeParameter,0);
});
