// Injected protocol/DOM fixtures test rejection predicates; never native parity evidence.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path');
const {normalize,wireDocument,traceResponse,assertPresentation,digest}=require('../parity/trace-presentation.cjs');
const binding={uri:'file:///trace.dfy',version:1,textHash:digest('source'),session:'document-a',protocolOpenIndex:0};
const trace=[{position:{line:2,character:8},assumption:'assume 1 == r;'}];
const annotation={uri:binding.uri,line:3,text:'r == 1',backgroundColor:'rgb(13, 71, 161)',color:'rgb(227, 242, 253)',marginLeft:'30px',marginTop:'0px',marginRight:'0px',marginBottom:'0px',visible:true};
const menu=shown=>({labels:['Dafny: Copy verification trace as Dafny (experimental)',`Dafny: ${shown?'Hide':'Show'} verification trace (experimental)`]});
const observation=shown=>({activeUri:binding.uri,annotations:shown?[{...annotation}]:[],menu:menu(shown)});
test('trace presentation rejects successful capture with wrong text, hidden leftovers, wrong URI, style, range or menu',()=>{
 assert.ok(assertPresentation(observation(true),{binding,trace,shown:true,menu:'hide'}).asserted);assert.ok(assertPresentation(observation(false),{binding,shown:false,menu:'show'}).asserted);
 for(const field of ['text','line','color','backgroundColor','marginLeft','marginTop','marginRight','marginBottom','visible']){const observed=observation(true);observed.annotations[0][field]=field==='visible'?false:field==='line'?4:'wrong';assert.throws(()=>assertPresentation(observed,{binding,trace,shown:true,menu:'hide'}));}
 assert.throws(()=>assertPresentation(observation(true),{binding,shown:false,menu:'show'}),/disappearance/);assert.throws(()=>assertPresentation({...observation(true),activeUri:'file:///other.dfy'},{binding,trace,shown:true}),/URI/);assert.throws(()=>assertPresentation({...observation(false),menu:menu(true)},{binding,shown:false,menu:'show'}),/transition/);
});
const client=(method,params)=>({direction:'client',message:{method,params}}),open=(text='source',version=1)=>client('textDocument/didOpen',{textDocument:{uri:binding.uri,version,text}}),request=id=>({direction:'client',message:{id,method:'dafny/counterExample',params:{textDocument:{uri:binding.uri}}}}),response=id=>({direction:'server',message:{id,result:trace}});
test('trace reply requires stable matching wire text/version/open lifetime, URI and request ID',()=>{
 const records=[open(),request(7),response(7)];assert.deepEqual(traceResponse(records,1,binding).result,trace);
 assert.throws(()=>traceResponse([open(),request(7),response(8)],1,binding),/matching/);assert.throws(()=>traceResponse([open(),request(7),request(8),response(7)],1,binding),/unambiguous/);
 assert.throws(()=>traceResponse([open('wrong'),request(7),response(7)],1,binding),/text/);assert.throws(()=>traceResponse([open('source',2),request(7),response(7)],1,binding),/version/);
 for(const method of ['textDocument/didChange','textDocument/didClose'])assert.throws(()=>traceResponse([open(),request(7),client(method,{textDocument:{uri:binding.uri}}),response(7)],1,binding),/boundary/);
 const reopened=[open(),client('textDocument/didClose',{textDocument:{uri:binding.uri}}),open(),request(9),response(9)];assert.throws(()=>traceResponse(reopened,3,binding),/lifetime/);assert.equal(traceResponse(reopened,3,{...binding,protocolOpenIndex:2,session:'reopened'}).requestId,9);
});
test('wire replay preserves CRLF, UTF16 ranges, nonconsecutive versions and multi-file isolation',()=>{
 const text='🦀x\r\nnext',change=client('textDocument/didChange',{textDocument:{uri:binding.uri,version:9},contentChanges:[{range:{start:{line:0,character:2},end:{line:0,character:3}},text:'y'}]});
 const records=[open(text),client('textDocument/didOpen',{textDocument:{uri:'file:///other',version:2,text:'other'}}),change];assert.equal(wireDocument(records,3,binding.uri).text,'🦀y\r\nnext');assert.equal(wireDocument(records,3,binding.uri).version,9);
});
test('expected normalization corresponds to the pinned upstream algorithm when source is available',t=>{
 const file=path.resolve(__dirname,'../../.cache/dafny-extension/src/ui/verificationTraceView.ts');if(!fs.existsSync(file)){t.skip('pinned upstream source unavailable; inventory source gate still required');return;}
 const source=fs.readFileSync(file,'utf8'),start=source.indexOf('    if(contentText.startsWith(AssumePrefix))'),end=source.indexOf('\n  private static createDecorator',start);assert.ok(start>0&&end>start);const body=source.slice(start,end).replace(/\n  }\s*$/,'').replace('(v: string)','(v)');const reference=new Function('contentText','AssumePrefix','SemicolonSuffix',body);
 for(const value of ['assume true;','assume 1 == r;','assume 1 == r && 2 == s;','assume a == b;','  assume x;','assume z == x\' ;'])assert.equal(normalize(value),reference(value,'assume ',';'));
});

test('native source close selects exact URI tabs through public API regardless of terminal focus (injected boundary)',async()=>{
 const {closeSourceTabs}=require('../parity/trace-presentation.cjs'),uri={toString:()=>binding.uri},owned={input:{uri}},other={input:{uri:{toString:()=>binding.uri+'.other'}}};let selected;
 const vscode={window:{tabGroups:{all:[{tabs:[owned,other]}],close:async(tabs,preserveFocus)=>{selected=tabs;assert.equal(preserveFocus,true);return true;}}}};assert.equal(await closeSourceTabs(vscode,{uri}),1);assert.deepEqual(selected,[owned]);vscode.window.tabGroups.close=async()=>false;await assert.rejects(closeSourceTabs(vscode,{uri}),/close/);
});
