// Current symbols and verification outcomes are injected unless explicitly compiler-derived.
'use strict';
const test=require('node:test'),assert=require('node:assert/strict'),{fixture,row}=require('./controller-fixture.cjs'),{createHash}=require('node:crypto');
const tick=()=>new Promise(resolve=>setImmediate(resolve));
const packet=(doc,rows)=>({uri:doc.uri.toString(),version:doc.version,sourceHash:createHash('sha256').update(doc.getText()).digest('hex'),report:{results:rows,errors:[]}});
const range=(s,e)=>({start:{line:0,character:s},end:{line:0,character:e}});
const symbol=(name,kind,range,selectionRange,children=[])=>({name,kind,range,selectionRange,children});
const leaves=item=>item.children.size?[...item.children.values()].flatMap(leaves):[item];
test('accepted rows form contract/function hierarchy without inventing parent proof results or source ranges',async()=>{
 const e=fixture();try{e.service.emit('report',packet(e.doc,[row(e.doc),{...row(e.doc),contract:'D',function:'g',signature:'g()'}]));const file=e.controller.items.get(e.doc.uri.toString());assert.deepEqual([...file.children.values()].map(item=>item.label),['C','D']);assert.equal(file.children.values().next().value.range,undefined);assert.equal(leaves(file).length,2);assert.ok(e.runs[0].calls.filter(call=>call[0]==='passed').every(call=>call[1].id.includes('#C:')||call[1].id.includes('#D:')));}finally{await e.api.dispose();}
});
test('current nested symbols place exact overloaded leaves and parent exclusions block directly included descendants',async()=>{
 const e=fixture();try{e.doc.text='contract C { function f() external {} function f(uint x) external {} }';e.service.request=async()=>[symbol('C',5,range(0,e.doc.text.length),range(9,10),[symbol('f',12,range(13,37),range(22,23)),symbol('f',12,range(38,67),range(47,48))])];const rows=[{...row(e.doc),status:'ready',range:range(13,37)},{...row(e.doc),status:'ready',signature:'f(uint256)',range:range(38,67)}];e.service.emit('report',packet(e.doc,rows));await tick();const file=e.controller.items.get(e.doc.uri.toString()),parent=[...file.children.values()][0];assert.equal(parent.label,'C');assert.deepEqual(parent.range.start,{line:0,character:9});assert.deepEqual(leaves(parent).map(item=>item.label),['C.f()','C.f(uint256)']);await e.controller.run({include:[...leaves(parent)],exclude:[parent]},null);assert.deepEqual(e.runs.at(-1).calls.map(call=>call[0]),['end']);}finally{await e.api.dispose();}
});

const file=e=>e.controller.items.get(e.doc.uri.toString()),snapshot=item=>({id:item.id,label:item.label,range:item.range,description:item.description,children:[...item.children.values()].map(snapshot)});
function symbolsFor(e){return[symbol('C',5,range(0,e.doc.text.length),range(9,10),[symbol('f',12,range(13,e.doc.text.length-2),range(22,23))])];}
function source(e){e.doc.text='contract C { function f() external {} }';return{...row(e.doc),status:'ready',range:range(13,e.doc.text.length-2)};}
for(const cause of ['edit','close-reopen','restart','configuration','hide','dispose','newer-report'])test(`stale asynchronous symbol reply after ${cause} cannot move or revive retired tests`,async()=>{
 const e=fixture(),jobs=[];try{const r=source(e);e.service.request=(method,doc,params,options)=>new Promise(resolve=>jobs.push({resolve,signal:options.signal}));e.service.emit('report',packet(e.doc,[r]));await tick();assert.equal(jobs.length,1);const old=e.doc,tree=snapshot(file(e));
 if(cause==='edit'){e.doc.version++;e.doc.text+=' ';e.events.change({document:e.doc,contentChanges:[{}]});}
 else if(cause==='close-reopen'){old.isClosed=true;e.events.close(old);const reopened={...old,isClosed:false};e.doc=reopened;e.events.open(reopened);}
 else if(cause==='restart')await e.commands.get('solidityLean.restartServer')();
 else if(cause==='configuration'){e.changeConfig('solidityLean.workers');await tick();}
 else if(cause==='hide'){e.config.displayVerificationAsTests=false;e.changeConfig('solidityLean.displayVerificationAsTests');}
 else if(cause==='dispose')await e.api.dispose();
 else e.service.emit('report',packet(e.doc,[{...r,function:'g',signature:'g()'}]));
 assert.equal(jobs[0].signal.aborted,true);jobs[0].resolve(symbolsFor({...e,doc:old}));await tick();
 if(cause==='newer-report')assert.deepEqual(leaves(file(e)).map(item=>item.label),['C.g()']);else assert.equal(e.controller.items.size,0);
 assert.equal(e.runs.length,0);
 }finally{await e.api.dispose();}
});
test('historical and unmatched symbols never become current compiler parents; matched leaves remain visible',async()=>{
 const e=fixture();try{const r=source(e);e.service.request=async()=>symbolsFor(e).map(s=>({...s,detail:'Outdated: previous compile'}));e.service.emit('report',packet(e.doc,[r]));await tick();assert.equal([...file(e).children.values()][0].range,undefined);assert.match([...file(e).children.values()][0].description,/unavailable/);
 e.service.request=async()=>[symbol('Other',5,range(0,e.doc.text.length),range(9,10),[])];e.service.emit('report',packet(e.doc,[r]));await tick();assert.equal(leaves(file(e)).length,1);assert.equal([...file(e).children.values()][0].range,undefined);
 e.service.request=async()=>symbolsFor(e);e.service.emit('report',packet(e.doc,[r]));await tick();assert.equal([...file(e).children.values()][0].description,'Current compiler symbol');assert.equal(e.runs.length,0);
 }finally{await e.api.dispose();}
});
test('moving fallback leaves into compiler parents preserves manual selection identity and automatic outcome ownership',async()=>{
 const e=fixture(),jobs=[];try{const r=source(e);e.service.request=()=>new Promise(resolve=>jobs.push(resolve));e.service.emit('report',packet(e.doc,[r]));await tick();const leaf=leaves(file(e))[0],fallback=[...file(e).children.values()][0];jobs[0](symbolsFor(e));await tick();assert.equal(leaves(file(e))[0],leaf);assert.notEqual([...file(e).children.values()][0],fallback);
 await e.controller.run({include:[fallback]},null);assert.deepEqual(e.runs.at(-1).calls.map(call=>call[0]),['end']);
 e.service.emit('status',{uri:e.doc.uri.toString(),version:e.doc.version,sourceHash:r.sourceHash,state:'running',progressScope:'functions',functions:[{name:'C.f()',range:r.range,status:'running'}]});e.service.emit('report',packet(e.doc,[{...r,status:'proved'}]));assert.deepEqual(e.runs.at(-1).calls.map(call=>call[0]),['started','passed','end']);assert.equal(leaves(file(e))[0],leaf);
 }finally{await e.api.dispose();}
});
test('row removal invalidates old selection recursively',async()=>{
 const e=fixture();try{const r=source(e);e.service.emit('report',packet(e.doc,[r,{...r,function:'g',signature:'g()'}]));const removed=leaves(file(e))[1];e.service.emit('report',packet(e.doc,[r]));await e.controller.run({include:[removed]},null);assert.deepEqual(e.runs.at(-1).calls.map(call=>call[0]),['end']);assert.equal(leaves(file(e)).length,1);}finally{await e.api.dispose();}
});
test('duplicate obligation identities are rejected before changing the tree',async()=>{
 const e=fixture();try{const r=source(e);e.service.emit('report',packet(e.doc,[r,r]));assert.equal(e.controller.items.size,0);assert.match(e.notices[0],/duplicate obligation identities/);}finally{await e.api.dispose();}
});

function strictCollections(e){const make=()=>{const map=new Map();return{get size(){return map.size;},forEach(fn){map.forEach(item=>fn(item));},get:id=>map.get(id),add:item=>map.set(item.id,item),delete:id=>map.delete(id),replace(items){map.clear();for(const item of items)map.set(item.id,item);}};};e.controller.items=make();e.controller.createTestItem=(id,label,uri)=>({id,label,uri,children:make()});}
test('real documented non-iterable TestItemCollection boundary supports projection, run-all and disposal',async()=>{
 const e=fixture();try{strictCollections(e);const r=source(e);e.service.emit('report',packet(e.doc,[r]));assert.equal(e.notices.length,0);assert.equal(e.controller.items.size,1);await e.controller.run({},null);assert.deepEqual(e.runs.at(-1).calls.map(call=>call[0]),['enqueued','started','passed','end']);await e.api.dispose();assert.equal(e.controller.items.size,0);}finally{await e.api.dispose();}
});
test('inherited row retains declaration source parent and labels distinct verification context explicitly',async()=>{
 const e=fixture();try{e.doc.text='contract Base { function f() public {} } contract Derived is Base {}';const body=range(16,38),r={...row(e.doc),contract:'Derived',range:body,status:'ready'};e.service.request=async()=>[symbol('Base',5,range(0,40),range(9,13),[symbol('f',12,body,range(25,26))]),symbol('Derived',5,range(41,e.doc.text.length),range(50,57))];e.service.emit('report',packet(e.doc,[r]));await tick();const parent=[...file(e).children.values()][0];assert.equal(parent.label,'Base');assert.equal(leaves(parent)[0].label,'Derived.f()');assert.match(leaves(parent)[0].description,/declared in Base; verification context Derived/);assert.equal(e.runs.length,0);}finally{await e.api.dispose();}
});

test('synthetic constructor and missing locations remain separate leaves without invented compiler-parent ranges',async()=>{
 const e=fixture();try{const r=source(e);e.service.request=async()=>symbolsFor(e);e.service.emit('report',packet(e.doc,[{...r,function:'constructor',signature:'constructor()',sourceId:-1,range:range(0,e.doc.text.length)},{...r,function:'missing',signature:'missing()',range:undefined}]));await tick();const parent=[...file(e).children.values()][0];assert.equal(parent.range,undefined);assert.deepEqual(leaves(parent).map(item=>item.label),['C.constructor()','C.missing()']);assert.equal(leaves(parent)[1].range,undefined);assert.equal(e.runs.length,0);}finally{await e.api.dispose();}
});
test('manual parent selection deduplicates overlapping descendants without changing signatures or starting automatic runs',async()=>{
 const calls=[],e=fixture(async args=>{calls.push(args.function);return{results:[{...row(args.document),signature:args.function,function:args.function.split('(')[0]}],errors:[]};});try{
 const r=source(e);e.service.emit('report',packet(e.doc,[r,{...r,signature:'f(uint256)'}]));const parent=[...file(e).children.values()][0],selected=leaves(parent);await e.controller.run({include:[parent,...selected,parent]},null);assert.deepEqual(calls,['f()','f(uint256)']);assert.equal(e.runs.length,1);assert.deepEqual(e.runs[0].calls.map(call=>call[0]),['enqueued','enqueued','started','passed','started','passed','end']);
 }finally{await e.api.dispose();}
});

test('manual verification can finish after its exact leaf moves into current compiler parents',async()=>{
 let finish;const e=fixture(args=>new Promise(resolve=>{finish=()=>resolve({results:[{...row(args.document),range:range(13,args.document.text.length-2)}],errors:[]});})),symbols=[];
 try{const r=source(e);e.service.request=()=>new Promise(resolve=>symbols.push(resolve));e.service.emit('report',packet(e.doc,[r]));await tick();const selected=leaves(file(e))[0];const running=e.controller.run({include:[selected]},null);await tick();symbols[0](symbolsFor(e));await tick();assert.equal(leaves(file(e))[0],selected);assert.equal([...file(e).children.values()][0].description,'Current compiler symbol');finish();await running;assert.equal(e.runs.length,1);assert.deepEqual(e.runs[0].calls.map(call=>call[0]),['enqueued','started','passed','end']);}finally{finish?.();await e.api.dispose();}
});
test('ordinary symbol provider failure retains explicit fallback results without authorizing work',async()=>{
 const e=fixture();try{e.service.request=async()=>{throw Error('injected compiler symbol failure');};e.service.emit('report',packet(e.doc,[source(e)]));await tick();assert.equal(leaves(file(e)).length,1);assert.match([...file(e).children.values()][0].description,/unavailable/);assert.ok(e.logs.some(line=>line.includes('Testing symbols unavailable: injected compiler symbol failure')));assert.equal(e.runs.length,0);}finally{await e.api.dispose();}
});
