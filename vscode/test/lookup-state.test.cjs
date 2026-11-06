// Read-only lookup migration regressions. Compilation is injected; no verification proof is claimed.
'use strict';
const {test}=require('node:test'),assert=require('node:assert/strict'),fs=require('node:fs'),path=require('node:path'),os=require('node:os'),{pathToFileURL}=require('node:url'),{createHash}=require('node:crypto');
const lookup=require('../src/lookup-state.cjs'),language=require('../src/language-services.cjs'),{SolidityService}=require('../src/lsp-server.cjs');
const source='// 😀\r\ncontract C {\r\n  uint public x;\r\n  function get() public view returns(uint) { return x; }\r\n  function second() public pure returns(uint) { return 2; }\r\n}\r\n';
const range=(a,b,c,d)=>({start:{line:a,character:b},end:{line:c,character:d}});
const hash=s=>createHash('sha256').update(s).digest('hex');
function ast(text){
  const src=(start,end)=>`${Buffer.byteLength(text.slice(0,start))}:${Buffer.byteLength(text.slice(start,end))}:0`;
  const variable=text.indexOf('x;'),call=text.indexOf('return x;')+7,first=text.indexOf('function get'),second=text.indexOf('function second');
  const node=(id,name,start,end,type)=>({id,name,nodeType:type,src:src(start,end),nameLocation:src(text.indexOf(name,start),text.indexOf(name,start)+name.length)});
  return{nodeType:'SourceUnit',id:0,src:src(0,text.length),nodes:[{...node(1,'C',text.indexOf('contract'),text.length,'ContractDefinition'),nodes:[
    {...node(2,'x',text.indexOf('uint public'),variable+1,'VariableDeclaration'),typeDescriptions:{typeString:'uint256'}},
    {...node(3,'get',first,text.indexOf('}',first)+1,'FunctionDefinition'),body:{nodeType:'Identifier',id:5,name:'x',src:src(call,call+1),referencedDeclaration:2},parameters:{parameters:[]},typeDescriptions:{typeString:'function () view returns (uint256)'}},
    {...node(4,'second',second,text.indexOf('}',second)+1,'FunctionDefinition'),parameters:{parameters:[]},typeDescriptions:{typeString:'function () pure returns (uint256)'}}
  ]}]};
}
function fixture(){
  const root=fs.mkdtempSync(path.join(os.tmpdir(),'lookup-migration-')),events=[],state={calls:0};
  const service=new SolidityService({notify:(method,params)=>events.push({method,params:structuredClone(params)})},root,{automaticVerification:'never'},
    {fingerprint:()=> 'fixed',analyze:async doc=>{state.calls++;if(doc.text.includes('BROKEN'))throw Error('incomplete compiler input');return{sourceHash:hash(doc.text),rawAst:ast(doc.text),diagnostics:[]};}});
  const uri=pathToFileURL(path.join(root,'C.sol')).href,doc=service.open({uri,version:1,text:source});clearTimeout(doc.timer);
  const query=(method,point,signal)=>service.language('textDocument/'+method,{textDocument:{uri,version:doc.version},position:point},signal);
  const change=changes=>{service.change({textDocument:{uri,version:doc.version+1},contentChanges:changes});clearTimeout(doc.timer);};
  return{root,events,state,service,uri,doc,query,change,dispose(){service.dispose();fs.rmSync(root,{recursive:true,force:true});}};
}
test('unaffected definitions and symbols survive an incomplete insertion with exact UTF16 ranges',async()=>{
  const s=fixture();try{
    const point={line:3,character:52};assert.deepEqual(await s.query('definition',point),{uri:s.uri,range:range(2,14,2,15)});
    s.change([{range:range(4,0,4,0),text:'  function BROKEN( {\r\n'}]);
    assert.deepEqual(await s.query('definition',point),{uri:s.uri,range:range(2,14,2,15)});
    const symbols=await s.query('documentSymbol');assert.equal(symbols[0].children.find(c=>c.name==='second').selectionRange.start.line,5);
    assert.equal(s.doc.index,null);assert.equal(s.doc.compiled,null);assert.equal(s.doc.report,null);
  }finally{s.dispose();}
});
module.exports={fixture,source,range,ast};

test('sequential insertions relocate declarations, occurrences and symbol boundaries without populating compiler state',async()=>{
  const s=fixture();try{
    await s.query('documentSymbol');
    s.change([{range:range(0,0,0,0),text:'// BROKEN\r\n'},{range:range(3,0,3,0),text:'// shift\r\n'}]);
    const point={line:5,character:52};assert.deepEqual(await s.query('definition',point),{uri:s.uri,range:range(4,14,4,15)});
    const hover=await s.query('hover',point);assert.equal(hover.contents.value,'Outdated: x: uint256');assert.deepEqual(hover.range,range(5,52,5,53));
    const refs=await s.query('references',point);assert.deepEqual(refs,[{uri:s.uri,range:range(4,14,4,15)},{uri:s.uri,range:range(5,52,5,53)}]);
    assert.equal(s.doc.index,null);assert.equal(s.doc.compiled,null);assert.equal(s.doc.report,null);
  }finally{s.dispose();}
});
test('edited identifier, crossed declaration and full-buffer replacement invalidate lookup links',async()=>{
  for(const kind of ['name','declaration','full']){
    const s=fixture();try{
      await s.query('documentSymbol');
      const changes=kind==='name'?[{range:range(2,14,2,15),text:'y'},{range:range(4,0,4,0),text:'BROKEN\r\n'}]:kind==='declaration'?[{range:range(2,0,3,0),text:''},{range:range(0,0,0,0),text:'// BROKEN\r\n'}]:[{text:'BROKEN\n'+source}];
      s.change(changes);const point=kind==='full'?{line:4,character:52}:{line:3,character:52};
      assert.equal(await s.query('definition',point),null);
    }finally{s.dispose();}
  }
});
test('new shadowing names and import directive changes never reuse prior bindings',async()=>{
  for(const insertion of ['uint x; // BROKEN\r\n','import "./Other.sol"; // BROKEN\r\n']){
    const s=fixture();try{await s.query('documentSymbol');s.change([{range:range(4,0,4,0),text:insertion}]);assert.equal(await s.query('definition',{line:3,character:52}),null);}finally{s.dispose();}
  }
});
test('historical lookup never authorizes rename, prepareRename or verification',async()=>{
  const s=fixture();let verified=0;s.service.testing.verify=async()=>{verified++;throw Error('must not reach verifier');};
  try{
    await s.query('documentSymbol');s.change([{range:range(4,0,4,0),text:'function BROKEN( {\r\n'}]);
    assert.deepEqual(await s.query('definition',{line:3,character:52}),{uri:s.uri,range:range(2,14,2,15)});
    assert.equal(await s.query('prepareRename',{line:3,character:52}),null);
    assert.equal(await s.service.language('textDocument/rename',{textDocument:{uri:s.uri,version:s.doc.version},position:{line:3,character:52},newName:'renamed'}),null);
    await assert.rejects(s.service.verify(s.uri),/incomplete compiler/);assert.equal(verified,0);assert.equal(s.service.cache.size,0);
    assert.equal(lookup.methods.has('textDocument/formatting'),false);assert.equal(lookup.methods.has('textDocument/codeAction'),false);
  }finally{s.dispose();}
});
test('reset and close/reopen cannot revive historical lookups, even at the same document version',async()=>{
  for(const kind of ['reset','close']){
    const s=fixture();try{await s.query('documentSymbol');s.change([{range:range(4,0,4,0),text:'BROKEN\r\n'}]);await s.query('definition',{line:3,character:52});
      if(kind==='reset'){s.service.reset();assert.equal(s.doc.lookup,null);assert.equal(await s.query('definition',{line:3,character:52}),null);}
      else{s.service.close(s.uri);const doc=s.service.open({uri:s.uri,version:s.doc.version,text:s.doc.text});clearTimeout(doc.timer);assert.equal(doc.lookup,undefined);assert.equal(await s.service.language('textDocument/definition',{textDocument:{uri:s.uri,version:doc.version},position:{line:3,character:52}}),null);}
    }finally{s.dispose();}
  }
});
test('request cancellation and newer document generations cannot return a pending historical result',async()=>{
  const s=fixture();let release,started;
  try{await s.query('documentSymbol');s.change([{range:range(4,0,4,0),text:'BROKEN\r\n'}]);
    const gate=new Promise(r=>{release=r;}),ready=new Promise(r=>{started=r;});s.service.testing.analyze=async()=>{started();await gate;throw Error('incomplete');};
    const abort=new AbortController(),pending=s.query('definition',{line:3,character:52},abort.signal),cancelled=assert.rejects(pending,e=>e.code===-32800);await ready;abort.abort();await cancelled;
    const newer=s.query('definition',{line:3,character:52}),obsolete=assert.rejects(newer,e=>[-32800,-32801].includes(e.code));s.change([{range:range(0,0,0,0),text:'\r\n'}]);release();await obsolete;
  }finally{release?.();s.dispose();}
});
test('cached expression qualifiers must stay unchanged',()=>{
  const before='this.x',snapshot={uri:'file:///C.sol',version:1,generation:'g',outdated:false,dependencies:{files:{}},declarations:[{id:1,name:'x',description:'x:uint',location:{uri:'file:///Other.sol',range:range(0,0,0,1)},nameText:'x',scopes:[]}],entries:[{target:1,range:range(0,5,0,6),context:range(0,0,0,6),scopes:[]}],symbols:[]};
  const next=lookup.migrate(snapshot,before,[{range:range(0,0,0,4),text:'other'}],2);assert.equal(lookup.query(next,'textDocument/definition',{position:{line:0,character:6}}),null);
});

test('opening comments or strings cannot turn their unchanged contents into historical code lookups',()=>{
  for(const prefix of ['//','/*','"']){
    const before='return x;  ',state={uri:'file:///C.sol',version:1,generation:'g',outdated:false,dependencies:{files:{}},declarations:[{id:1,name:'x',description:'x:uint',location:{uri:'file:///Other.sol',range:range(0,0,0,1)},nameText:'x',scopes:[]}],entries:[{target:1,range:range(0,7,0,8),context:range(0,7,0,8),scopes:[range(0,0,0,11)]}],symbols:[]};
    const next=lookup.migrate(state,before,[{range:range(0,0,0,0),text:prefix}],2);
    assert.equal(lookup.query(next,'textDocument/definition',{position:{line:0,character:7+prefix.length}}),null);
  }
});

test('new qualification adjacent to a bare identifier invalidates its historical binding',()=>{
  for(const [at,prefix,position] of [[7,'this.',12],[8,'.field',7]]){
    const before='return x;  ',state={uri:'file:///C.sol',version:1,generation:'g',outdated:false,dependencies:{files:{}},declarations:[{id:1,name:'x',description:'x:uint',location:{uri:'file:///Other.sol',range:range(0,0,0,1)},scopes:[]}],entries:[{target:1,range:range(0,7,0,8),context:range(0,7,0,8),scopes:[range(0,0,0,11)]}],symbols:[]};
    const next=lookup.migrate(state,before,[{range:range(0,at,0,at),text:prefix}],2);
    assert.equal(lookup.query(next,'textDocument/definition',{position:{line:0,character:position}}),null);
  }
});

test('qualification across whitespace or comments invalidates the historical binding',()=>{
  for(const [before,at,text,oldColumn,newColumn] of [['return  x;',7,'this.',8,13],['return x  ;',9,'.field',7,7],['return /*gap*/ x;',7,'this.',15,20]]){
    const r=range(0,oldColumn,0,oldColumn+1),state={uri:'file:///C.sol',version:1,generation:'g',outdated:false,dependencies:{files:{}},declarations:[{id:1,name:'x',description:'x:uint',location:{uri:'file:///Other.sol',range:range(0,0,0,1)},scopes:[]}],entries:[{target:1,range:r,context:r,scopes:[]}],symbols:[]};
    const next=lookup.migrate(state,before,[{range:range(0,at,0,at),text}],2);
    assert.equal(lookup.query(next,'textDocument/definition',{position:{line:0,character:newColumn}}),null);
  }
});

test('scope delimiter changes away from an occurrence retire its historical binding',async()=>{
 const s=fixture();try{
  await s.query('definition',{line:3,character:52});
  const brace=source.split('\r\n')[3].indexOf('{')+1;
  s.change([{range:range(3,brace,3,brace),text:'{'},{range:range(4,0,4,0),text:'// BROKEN\r\n'}]);
  assert.equal(await s.query('definition',{line:3,character:53}),null);
  const historical=await s.query('documentSymbol');assert.ok(historical[0].detail.startsWith('Outdated: ')); // prior symbol tree is historical display, not current scope authority
 }finally{s.dispose();}
});
test('changed declaration type or containing signature cannot preserve old lookup authority',async()=>{
 for(const kind of ['type','signature']){
  const s=fixture();try{
   await s.query('definition',{line:3,character:52});
   s.change([{range:kind==='type'?range(2,2,2,6):range(3,24,3,28),text:kind==='type'?'bool':'pure'},{range:range(4,0,4,0),text:'// BROKEN\r\n'}]);
   assert.equal(await s.query('definition',{line:3,character:52}),null);
  }finally{s.dispose();}
 }
});

test('inserting a shadow receiver retires historical member lookup even if member name is unchanged',()=>{
 const before='return receiver.value;  ',r=range(0,16,0,21),state={uri:'file:///C.sol',version:1,generation:'g',outdated:false,dependencies:{files:{}},declarations:[{id:1,name:'value',description:'value:uint',location:{uri:'file:///A.sol',range:range(0,0,0,5)},scopes:[]}],entries:[{target:1,range:r,context:range(0,7,0,21),names:['receiver','value'],scopes:[]}],symbols:[]};
 const text='Other receiver; ',next=lookup.migrate(state,before,[{range:range(0,0,0,0),text}],2);
 assert.equal(lookup.query(next,'textDocument/definition',{position:{line:0,character:16+text.length}}),null);
});

test('same-depth replacement of an enclosing brace identity retires the lookup',async()=>{
 const s=fixture();try{
  await s.query('definition',{line:3,character:52});const brace=source.split('\r\n')[3].indexOf('{')+1;
  s.change([{range:range(3,brace,3,brace),text:'} {'},{range:range(4,0,4,0),text:'// BROKEN\r\n'}]);
  assert.equal(await s.query('definition',{line:3,character:55}),null);
 }finally{s.dispose();}
});
