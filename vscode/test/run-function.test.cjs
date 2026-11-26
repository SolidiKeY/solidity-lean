'use strict';
const {test}=require('node:test');
const assert=require('node:assert/strict');
const fs=require('node:fs'),os=require('node:os'),path=require('node:path');
const server=require('../src/server-features/run-function.cjs');
const client=require('../src/features/run-function.cjs');
const {hash}=require('../src/project.cjs');
function fixture(t,backend=async()=>({status:'ok',returns:['42'],code:null,logs:[],storageWrites:[]})) {
  const directory=fs.mkdtempSync(path.join(os.tmpdir(),'run-function-test-'));t.after(()=>fs.rmSync(directory,{recursive:true,force:true}));
  const text='contract C { function f(uint8 n) public {} }',source=path.join(directory,'C.sol');fs.writeFileSync(source,text);
  const uri='file://'+source,doc={uri,path:source,version:1,text,compiled:{primaryAst:{nodes:[{nodeType:'ContractDefinition',id:1,name:'C',nodes:[{nodeType:'FunctionDefinition',id:2,kind:'function',name:'f',src:'13:27:0',implemented:true,parameters:{parameters:[{name:'n',typeDescriptions:{typeString:'uint8'}}]}}]}]}}};
  const requests=new Map(),service={directory,root:directory,settings:{},docs:new Map([[uri,doc]]),requests:new Map(),generation:1,
    language:async()=>[],current:(d,v,g)=>service.docs.get(uri)===d&&d.version===v&&service.generation===g,projectDocuments:()=>[{path:source,text:doc.text,version:doc.version}]};
  const registration=server.register({service,onRequest:(name,handler)=>requests.set(name,handler)},backend);t.after(()=>registration.dispose());
  const params={textDocument:{uri,version:1},sourceHash:hash(text),functionId:'1:2',args:['42']};
  return {doc,service,params,registration,run:(p=params)=>requests.get('solidityLean/runFunction')(p,17),discover:()=>requests.get('solidityLean/runFunctions')({textDocument:params.textDocument},18)};
}
test('discovers compiler function and invokes backend with exact typed arguments',async t=>{
  let request;const f=fixture(t,async r=>{request=r;return {status:'ok',returns:['42'],code:null,logs:[{topics:['0x01']}],storageWrites:[{slot:'0',value:'42'}]};});
  const listing=await f.discover();assert.equal(listing.functions[0].signature,'f(uint8)');
  const result=await f.run();assert.equal(request.args[0],'42');assert.equal(request.project.sources['C.sol'].content,f.doc.text);
  assert.match(client.render(listing.functions[0],result),/Storage slots written:.*42/);assert.equal(f.service.requests.size,0);
});
for(const status of ['revert','panic'])test(`injected ${status} preserves code, logs and storage trace`,async t=>{
  const expected={status,code:'0x11',returns:[],logs:[],storageWrites:[]};const f=fixture(t,async()=>expected);
  assert.deepEqual(await f.run(),expected);assert.match(client.render({contract:'C',signature:'f(uint8)'},expected),/Code: 0x11/);
});
test('bad ABI argument rejected before backend',async t=>{
  let called=false;const f=fixture(t,async()=>{called=true;});await assert.rejects(f.run({...f.params,args:['256']}),/outside uint8/);assert.equal(called,false);
  for(const [type,value]of [['bool','1'],['uint256','1.2'],['address','-1'],['bytes2','0x12']])assert.throws(()=>server.argument(type,value));
  assert.equal(server.argument('uint256',String(2n**256n-1n)),String(2n**256n-1n));assert.equal(server.argument('int8','-128'),'-128');
});
test('cancellation propagates to injected backend',async t=>{
  let start;const started=new Promise(r=>{start=r;});const f=fixture(t,async(_,{signal})=>{start();await new Promise(resolve=>signal.addEventListener('abort',resolve,{once:true}));return {status:'ok'};});
  const pending=f.run();await started;f.service.requests.get(17).abort();await assert.rejects(pending,{code:-32800});assert.equal(f.service.requests.size,0);
});
test('stale buffer before and during execution is refused',async t=>{
  const f=fixture(t,async()=>{f.doc.version++;return {status:'ok'};});
  await assert.rejects(f.run({...f.params,sourceHash:'old'}),{code:-32801});await assert.rejects(f.run(),{code:-32801});
});
test('feature disposal cancels outstanding execution',async t=>{
  let start;const started=new Promise(r=>{start=r;});const f=fixture(t,async(_,{signal})=>{start();await new Promise(resolve=>signal.addEventListener('abort',resolve,{once:true}));return {status:'ok'};});
  const pending=f.run();await started;f.registration.dispose();await assert.rejects(pending,{code:-32800});
});
test('CLI adapter reports actual text without inventing missing trace',()=>{
  const result=server.outcome({results:[{status:'panic',text:'panic 17'}],errors:[]});assert.equal(result.code,null);assert.equal(result.logs,null);assert.equal(result.storageWrites,null);
  assert.throws(()=>server.outcome({results:[{status:'unsupported',reason:'not supported'}]}),/not supported/);
});
function editorHarness(responses={}) {
  let handler,version=1,source='contract C {}';const calls=[],lines=[],errors=[];
  const doc={languageId:'solidity',uri:{scheme:'file',toString:()=> 'file:///C.sol'},get version(){return version;},getText:()=>source};
  const fn={id:'1:2',contract:'C',signature:'f(uint8)',parameters:[{name:'n',type:'uint8'}]};
  const vscode={workspace:{isTrusted:true},ProgressLocation:{Notification:15},window:{activeTextEditor:{document:doc},
    showInformationMessage:async message=>errors.push(message),showErrorMessage:async message=>errors.push(message),
    showQuickPick:async items=>responses.pick===false?undefined:items[0],showInputBox:async options=>{calls.push(options);return responses.input===null?undefined:responses.input??'42';},
    withProgress:async(_,run)=>run({}, {isCancellationRequested:false,onCancellationRequested:()=>({dispose(){}})})}};
  const feature=client.activate({}, {vscode,registerCommand:(_,h)=>{handler=h;return {dispose(){}};},output:{appendLine:line=>lines.push(line),show(){}},client:{request:async(method,doc,params)=>{
    if(method.endsWith('runFunctions'))return {sourceHash:'hash',functions:[fn]};
    if(responses.stale)version++;
    return {status:'ok',returns:['42'],code:null,logs:[],storageWrites:[]};
  }}});
  return {run:()=>handler(),calls,lines,errors,feature};
}
test('editor prompts with ABI type and remembers previous function arguments',async()=>{
  const h=editorHarness();await h.run();await h.run();assert.equal(h.calls[0].prompt,'n (uint8)');assert.equal(h.calls[1].value,'42');assert.equal(h.lines.length,2);h.feature.dispose();
});
test('editor picker/input cancellation and stale response never publish outcome',async()=>{
  for(const responses of [{pick:false},{input:null},{stale:true},{input:'999'}]){const h=editorHarness(responses);await h.run();assert.equal(h.lines.length,0);h.feature.dispose();}
});

test('ABI strings, bytes, addresses and nested arrays validate without rounding',()=>{
  assert.equal(server.argument('string','hello'),'hello');assert.equal(server.argument('bytes','0x1234'),'0x1234');
  assert.equal(server.argument('address','0x0000000000000000000000000000000000000001'),'1');
  assert.deepEqual(server.argument('uint256[2][]','[["1","9007199254740993"]]'),[['1','9007199254740993']]);
  assert.throws(()=>server.argument('uint256[]','[9007199254740993]'),/quote integers/);
});
test('native adapter registers accepted ownership and reuses existing runner API',async t=>{
  const directory=fs.mkdtempSync(path.join(os.tmpdir(),'concrete-adapter-'));t.after(()=>fs.rmSync(directory,{recursive:true,force:true}));
  fs.mkdirSync(path.join(directory,'scripts'));
  fs.writeFileSync(path.join(directory,'scripts/test-solidity.mjs'),`export function runSolidityTests(paths,options){if(options.action!=='run'||options.args[0]!=='42'||process.env.LEAN_NUM_THREADS!=='1')throw Error('wrong request');return {results:[{status:'ok',text:'ok\\nreturns 42'}],errors:[]};}`);
  const ownership=[],service={root:directory,directory,settings:{timeoutMs:5000},registerOwned:async(kind)=>{assert.equal(kind,'proof');ownership.push('spawn');},releaseOwned:()=>ownership.push('close')};
  const result=await server.runBackend({project:{mainSource:'C.sol',sources:{'C.sol':{content:'contract C {}'}},remappings:[]},function:{contract:'C',signature:'f(uint8)',parameters:[{type:'uint8'}]},args:['42']},{service,signal:new AbortController().signal});
  assert.equal(result.status,'ok');assert.deepEqual(ownership,['spawn','close']);assert.deepEqual(fs.readdirSync(directory),['scripts']);
});

test('payable address retains numeric ABI validation',()=>{assert.equal(server.argument('address payable','42'),'42');assert.equal(server.supported('address payable'),true);});

test('absolute imports, contextual absolute remappings and relative parents relocate consistently',t=>{
  const directory=fs.mkdtempSync(path.join(os.tmpdir(),'run-remapping-'));t.after(()=>fs.rmSync(directory,{recursive:true,force:true}));
  const root=path.join(directory,'original'),vendor=path.join(root,'vendor'),nested=path.join(root,'nested');
  fs.mkdirSync(vendor,{recursive:true});fs.mkdirSync(nested,{recursive:true});
  const dependency=path.join(vendor,'Lib.sol'),leaf=path.join(nested,'N.sol');
  fs.writeFileSync(dependency,'import "@nested/N.sol"; library Lib {}');fs.writeFileSync(leaf,'library N {}');
  const text=`import "@dep/Lib.sol"; import "${leaf}"; contract C {}`;
  const source=path.join(root,'C.sol');fs.writeFileSync(source,text);
  const projects=require('../src/project.cjs');
  const project=projects.snapshot(source,text,{projectRoot:root,remappings:[`@dep/=${vendor}/`,`${vendor}/:@nested/=${nested}/`]});
  assert.ok(project.sources[dependency]);assert.ok(project.sources[leaf]);
  const execution=path.join(directory,'execution');fs.mkdirSync(execution);
  const snapshot=server.materialize(project,execution);
  const mirrored=projects.snapshot(snapshot.source,text,{projectRoot:snapshot.projectRoot,includePaths:snapshot.includePaths,remappings:snapshot.remappings});
  assert.deepEqual(Object.values(mirrored.sources).map(s=>s.content).sort(),Object.values(project.sources).map(s=>s.content).sort());
  for(const file of Object.values(mirrored.files))assert.ok(!path.relative(execution,file.path).startsWith('..'));
  assert.equal(fs.readFileSync(dependency,'utf8'),project.sources[dependency].content);
  const relative={mainSource:'C.sol',sources:{'C.sol':{content:'import "../D.sol"; contract C {}'},'../D.sol':{content:'library D {}'}},remappings:[]};
  const nestedExecution=path.join(directory,'relative');fs.mkdirSync(nestedExecution);
  const moved=server.materialize(relative,nestedExecution);
  const resolved=projects.snapshot(moved.source,relative.sources['C.sol'].content,{projectRoot:moved.projectRoot,includePaths:[nestedExecution],remappings:moved.remappings});
  assert.equal(Object.keys(resolved.sources).length,2);
});

test('relative imports in absolute dependencies honor absolute-prefix redirects and lexical aliases',t=>{
  const directory=fs.mkdtempSync(path.join(os.tmpdir(),'run-prefix-remapping-'));t.after(()=>fs.rmSync(directory,{recursive:true,force:true}));
  const vendor='/virtual/vendor/',override='/virtual/override/Leaf.sol';
  const original={mainSource:'C.sol',sources:{'C.sol':{content:'import "@dep/Lib.sol"; import "@alias/Lib.sol"; contract C {}'},
    [vendor+'Lib.sol']:{content:'import "./Leaf.sol"; library Lib {}'},
    [vendor+'sub/../Lib.sol']:{content:'import "./Leaf.sol"; library Alias {}'},
    [override]:{content:'library Leaf {}'}},remappings:[`@dep/=${vendor}`,`@alias/=${vendor}sub/../`,`${vendor}Leaf.sol=${override}`]};
  const moved=server.materialize(original,directory),projects=require('../src/project.cjs');
  const resolved=projects.snapshot(moved.source,original.sources['C.sol'].content,{projectRoot:moved.projectRoot,remappings:moved.remappings});
  assert.deepEqual(Object.values(resolved.sources).map(s=>s.content).sort(),Object.values(original.sources).map(s=>s.content).sort());
  assert.equal(fs.readdirSync(path.join(directory,'units')).length,4);
});

test('materialize normalizes remapping target separators like project.snapshot',t=>{
  const directory=fs.mkdtempSync(path.join(os.tmpdir(),'run-remap-slashes-'));t.after(()=>fs.rmSync(directory,{recursive:true,force:true}));
  const project={mainSource:'C.sol',sources:{'C.sol':{content:'import "@dep/Lib.sol"; contract C {}'},'vendor/Lib.sol':{content:'library Lib {}'}},remappings:['@dep/=vendor\\']};
  const moved=server.materialize(project,directory),projects=require('../src/project.cjs');
  assert.equal(Object.keys(projects.snapshot(moved.source,project.sources['C.sol'].content,{projectRoot:moved.projectRoot,remappings:moved.remappings}).sources).length,2);
});
test('native adapter refuses identity-sensitive compiler-code observations before execution',async()=>{
  await assert.rejects(server.runBackend({compilerCode:true},{signal:new AbortController().signal,service:{}}),/source-identity-preserving/);
});
