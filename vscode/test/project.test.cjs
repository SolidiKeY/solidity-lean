'use strict';
const {test}=require('node:test');
const assert=require('node:assert/strict');
const fs=require('node:fs');
const {join,resolve}=require('node:path');
const {tmpdir}=require('node:os');
const {pathToFileURL}=require('node:url');
const {snapshot,current}=require('../src/project.cjs');
const {tokens,imports,format}=require('../src/solidity-text.cjs');
const language=require('../src/language-services.cjs');

test('project snapshots resolve remapped cyclic imports and exact unsaved dependencies',()=>{
  const root=fs.mkdtempSync(join(tmpdir(),'solidity-project-'));
  try{
    fs.mkdirSync(join(root,'lib'));fs.writeFileSync(join(root,'lib/A.sol'),'import "../Main.sol"; contract A {}');
    const main='import {A} from "@lib/A.sol"; contract Main {}';fs.writeFileSync(join(root,'Main.sol'),main);
    const project=snapshot(join(root,'Main.sol'),main,{projectRoot:root,remappings:['@lib/=lib/']});
    assert.deepEqual(Object.keys(project.sources),['Main.sol','lib/A.sol']);assert.equal(current(project),true);
    const changed={path:join(root,'lib/A.sol'),text:'import "../Main.sol"; contract A { uint x; }',version:2};
    assert.equal(current(project,[changed]),false);const next=snapshot(join(root,'Main.sol'),main,{projectRoot:root,remappings:['@lib/=lib/']},[changed]);
    assert.notEqual(next.digest,project.digest);assert.equal(next.files['lib/A.sol'].version,2);assert.match(fs.readFileSync(changed.path,'utf8'),/A \{\}/);
    assert.throws(()=>snapshot(join(root,'Main.sol'),'import "../../outside.sol";',{}),/resolve|outside/);
  }finally{fs.rmSync(root,{recursive:true,force:true});}
});
test('imports ignore comment/string decoys and formatting preserves exact tokens and strings',()=>{
  assert.deepEqual(imports('string s="import \\"fake.sol\\";"; // import "wrong.sol";\nimport {A as B} from "A.sol";'),['A.sol']);
  const text='contract C{function f(uint x)public pure returns(uint){for(uint i=0;i<2;i++){x+=i;}string memory s="a;{b}";return x;}}';
  const pretty=format(text,{tabSize:4,insertSpaces:true});assert.match(pretty,/\n {4}function/);
  assert.deepEqual(tokens(pretty).map(t=>t.text),tokens(text).map(t=>t.text));assert.equal(format(pretty,{tabSize:4,insertSpaces:true}),pretty);
  const literals='contract C { bytes constant b=hex"1234"; string constant s=unicode"é"; uint constant n=1e+3; }';
  const output=format(literals);assert.match(output,/hex"1234"/);assert.match(output,/unicode"é"/);assert.match(output,/1e\+3/);
});
test('relative imports apply context remappings and symlink aliases use the open buffer',()=>{
  const root=fs.mkdtempSync(join(tmpdir(),'solidity-remapped-'));
  try{
    fs.mkdirSync(join(root,'src'));fs.mkdirSync(join(root,'lib'));
    const source=join(root,'src/A.sol'),target=join(root,'lib/B.sol'),alias=join(root,'lib/Alias.sol');
    fs.writeFileSync(source,'import "./B.sol"; contract A {}');fs.writeFileSync(target,'contract B {}');fs.symlinkSync(target,alias);
    const config={projectRoot:root,remappings:['src/:src/=lib/']};
    const project=snapshot(source,fs.readFileSync(source,'utf8'),config);assert.ok(project.sources['lib/B.sol']);
    const main='import "lib/Alias.sol"; contract Main {}',path=join(root,'Main.sol');fs.writeFileSync(path,main);
    const open={path:target,text:'contract B { uint dirty; }',version:4};
    const dirty=snapshot(path,main,{projectRoot:root},[open]);assert.equal(dirty.sources['lib/Alias.sol'].content,open.text);assert.equal(current(dirty,[open]),true);assert.equal(current(dirty),false);
    assert.equal(current(dirty,[{...open,version:5}]),true);assert.equal(current(dirty,[{...open,version:5}],true),false);
  }finally{fs.rmSync(root,{recursive:true,force:true});}
});
test('incomplete member completion filters by live receiver type',()=>{
  const text='contract C { struct S { uint alpha; bool beta; } function unrelated() public {} function test(S memory s) public { s. } }';
  const point=language.position(text,text.indexOf('s. }')+2);
  const items=language.completion(text,point,null).items.map(i=>i.label);assert.deepEqual(items,['alpha','beta']);
});

test('real project compiler and LSP support imports, project services and dependency changes',
 {skip:!process.env.SOLIDITY_LEAN_REAL_BACKEND,timeout:180000},async t=>{
  const root=fs.mkdtempSync(join(tmpdir(),'solidity-project-real-')),backend=resolve(process.env.SOLIDITY_LEAN_REAL_BACKEND);
  const {spawn}=require('node:child_process'),{RpcPeer}=require('../src/rpc.cjs'),{terminateTree}=require('../src/backend.cjs');
  const main=join(root,'Main.sol'),lib=join(root,'Lib.sol'),other=join(root,'Other.sol');
  const library='pragma solidity ^0.8.34; library Lib { function identity(uint x) internal pure returns(uint) { return x; } }';
  const body='pragma solidity ^0.8.34; import "./Lib.sol"; contract Main { function passes() public pure { assert(Lib.identity(7)==7); } function unrelated() public pure {} }';
  const otherBody='pragma solidity ^0.8.34; import "./Lib.sol"; contract Other { function use() public pure returns(uint) {return Lib.identity(8);} }';
  fs.writeFileSync(main,body);fs.writeFileSync(lib,library);fs.writeFileSync(other,otherBody);
  const child=spawn(process.execPath,[join(backend,'vscode/src/lsp-server.cjs')],{cwd:backend,detached:true,stdio:['pipe','pipe','pipe']});
  const rpc=new RpcPeer(child.stdout,child.stdin);let stderr='';child.stderr.on('data',c=>stderr+=c);child.on('exit',code=>rpc.close(new Error(`Server exited ${code}: ${stderr}`)));
  const uri=pathToFileURL(main).href,libUri=pathToFileURL(lib).href;
  const invalidations=[],diagnostics=[];rpc.onNotification('solidityLean/invalidated',p=>invalidations.push(p));rpc.onNotification('textDocument/publishDiagnostics',p=>diagnostics.push(p));
  const point=language.position(body,body.indexOf('identity(7)')+2),doc={uri,version:1};
  const request=(method,params={})=>rpc.request(method,{textDocument:doc,...params},{timeoutMs:60000});
  try{
    await rpc.request('initialize',{rootUri:pathToFileURL(backend).href,initializationOptions:{settings:{projectRoot:root,automaticVerification:'never',workers:2}}});rpc.notify('initialized',{});
    rpc.notify('textDocument/didOpen',{textDocument:{uri,version:1,text:body}});
    await t.test('definitions and references retain foreign compiler source identities',async()=>{
      const definition=await request('textDocument/definition',{position:point});assert.equal(definition.uri,libUri);
      const references=await request('textDocument/references',{position:point,context:{includeDeclaration:true}});assert.equal(new Set(references.map(r=>r.uri)).size,3);
      const completions=await request('textDocument/completion',{position:language.position(body,body.indexOf('identity(7)'))});
      assert.ok(completions.items.some(i=>i.label==='identity'));assert.ok(!completions.items.some(i=>i.label==='unrelated'));
    });
    await t.test('workspace symbols find unopened contracts and functions',async()=>{
      const symbols=await rpc.request('workspace/symbol',{query:'Other'});assert.ok(symbols.some(s=>s.location.uri===pathToFileURL(other).href));
    });
    await t.test('formatting is usable and compiler diagnostics produce a real quick fix',async()=>{
      const edits=await request('textDocument/formatting',{options:{tabSize:2,insertSpaces:true}});assert.equal(edits.length,1);assert.match(edits[0].newText,/\n/);
      const actions=await request('textDocument/codeAction',{range:{start:{line:0,character:0},end:{line:0,character:0}},context:{diagnostics:[{code:'1878',message:'SPDX license identifier not provided',range:{start:{line:0,character:0},end:{line:0,character:0}}}]}});
      assert.ok(actions.some(a=>a.edit.documentChanges[0].edits[0].newText.includes('SPDX-License-Identifier')));
    });
    await t.test('formatting preserves Solidity literal syntax and refuses changed loop annotations',async()=>{
      const literalText='pragma solidity ^0.8.34; contract Literals {function f() public pure returns(bytes memory,string memory,uint) {return (hex"1234",unicode"é",1e+3);}}';
      const literalUri=pathToFileURL(join(root,'Literals.sol')).href;rpc.notify('textDocument/didOpen',{textDocument:{uri:literalUri,version:1,text:literalText}});
      const edits=await rpc.request('textDocument/formatting',{textDocument:{uri:literalUri,version:1},options:{tabSize:2}});
      assert.match(edits[0].newText,/hex"1234"/);assert.match(edits[0].newText,/unicode"é"/);assert.match(edits[0].newText,/1e\+3/);
      const annotated='pragma solidity ^0.8.34; import "./Lib.sol"; contract Annotated { function f() public pure { uint i;\n/// @custom:key invariant false\n\nwhile(i<1) { i++; } } }';
      const annotationUri=pathToFileURL(join(root,'Annotated.sol')).href;rpc.notify('textDocument/didOpen',{textDocument:{uri:annotationUri,version:1,text:annotated}});
      await assert.rejects(rpc.request('textDocument/formatting',{textDocument:{uri:annotationUri,version:1},options:{tabSize:2}}),/specification attachment/);
    });
    await t.test('unused-parameter quick fixes preserve ordinary NatSpec',async()=>{
      const source='pragma solidity ^0.8.34; contract Documented {\n/// @param unused documented parameter\nfunction f(uint unused) public pure returns(uint) { return 1; } }';
      const uri=pathToFileURL(join(root,'Documented.sol')).href;rpc.notify('textDocument/didOpen',{textDocument:{uri,version:1,text:source}});
      const position=language.position(source,source.indexOf('uint unused'));
      const actions=await rpc.request('textDocument/codeAction',{textDocument:{uri,version:1},context:{diagnostics:[{code:'5667',range:{start:position,end:position},message:'Unused parameter'}]}});
      assert.ok(!actions.some(a=>a.title.includes('unused parameter')));
    });
    await t.test('rename validates compiler output across multiple files without writing sources',async()=>{
      const edit=await request('textDocument/rename',{position:point,newName:'renamed'});assert.equal(edit.documentChanges.length,3);
      assert.equal(fs.readFileSync(lib,'utf8'),library);assert.equal(fs.readFileSync(main,'utf8'),body);
    });
    await t.test('rename rejects a consumer collision when initiated at an exported declaration',async()=>{
      const declaration=join(root,'Free.sol'),consumer=join(root,'Consumer.sol');
      const free='pragma solidity ^0.8.34; function source(uint x) pure returns(uint) {return x;}';
      fs.writeFileSync(declaration,free);fs.writeFileSync(consumer,'pragma solidity ^0.8.34; import "./Free.sol"; contract Consumer { function f() public pure returns(uint) { uint renamed=1; return source(renamed); } }');
      const freeUri=pathToFileURL(declaration).href;rpc.notify('textDocument/didOpen',{textDocument:{uri:freeUri,version:1,text:free}});
      await assert.rejects(rpc.request('textDocument/rename',{textDocument:{uri:freeUri,version:1},position:language.position(free,free.indexOf('source(')+2),newName:'renamed'}));
      assert.equal(fs.readFileSync(declaration,'utf8'),free);
    });
    await t.test('CLI compiler and verifier accept the same original multi-file unit',async()=>{
      const {runSolidityTests}=await import('../../scripts/test-solidity.mjs');const report=runSolidityTests([main],{build:false,function:'passes()'});
      assert.deepEqual(report.errors,[]);assert.equal(report.results.find(r=>r.function==='passes').status,'proved');
    });
    await t.test('imported libraries produce a real kernel-checked proof',async()=>{
      const report=await request('solidityLean/verify',{options:{function:'passes()'}});assert.deepEqual(report.errors,[]);assert.equal(report.results.find(r=>r.function==='passes').status,'proved');
      assert.equal(report.results.find(r=>r.function==='passes').range.start.line,0);
    });
    await t.test('function scheduling retains exact non-applicable audits for skipped rows',async()=>{
      const text='pragma solidity ^0.8.34; contract Mixed { function a() public pure {assert(true);} function b() public pure {assert(true);}\n/// @custom:key skip\nfunction skipped() public pure {} }';
      const mixedUri=pathToFileURL(join(root,'Mixed.sol')).href;rpc.notify('textDocument/didOpen',{textDocument:{uri:mixedUri,version:1,text}});
      const audited=await rpc.request('solidityLean/verify',{textDocument:{uri:mixedUri,version:1},options:{auditPreconditions:true}});
      assert.deepEqual(audited.errors,[]);assert.ok(audited.results.every(r=>r.preconditions!==undefined));
      assert.equal(audited.results.find(r=>r.function==='a').status,'proved');assert.equal(audited.results.find(r=>r.function==='b').status,'proved');
      const parallel=await rpc.request('solidityLean/verify',{textDocument:{uri:mixedUri,version:1},options:{auditPreconditions:false}});
      assert.equal(parallel.backend.verificationMode,'functions');assert.equal(parallel.backend.workers.length,2);
    });
    await t.test('multi-file contract specifications keep declaring-contract constants and exact refutations',async()=>{
      const imported='pragma solidity ^0.8.34; library ScopedLib { uint private constant VALUE=7;\n/// @custom:key ensures \\result == VALUE\nfunction value() internal pure returns(uint) {return VALUE;} }';
      const text='pragma solidity ^0.8.34; import "./ScopedLib.sol"; contract Scoped { uint private constant VALUE=9;\n/// @custom:key ensures \\result == 7\nfunction imported() public pure returns(uint) {return ScopedLib.value();}\n/// @custom:key ensures \\result == VALUE\nfunction local() public pure returns(uint) {return VALUE;}\n/// @custom:key ensures \\result == 8\nfunction falsePost() public pure returns(uint) {return ScopedLib.value();} }';
      fs.writeFileSync(join(root,'ScopedLib.sol'),imported);const scopedUri=pathToFileURL(join(root,'Scoped.sol')).href;
      rpc.notify('textDocument/didOpen',{textDocument:{uri:scopedUri,version:1,text}});
      const report=await rpc.request('solidityLean/verify',{textDocument:{uri:scopedUri,version:1},options:{}},{timeoutMs:60000});assert.deepEqual(report.errors,[]);
      assert.equal(report.results.find(r=>r.function==='imported').status,'proved');assert.equal(report.results.find(r=>r.function==='local').status,'proved');assert.equal(report.results.find(r=>r.function==='falsePost').status,'pending');
      const refuted=await rpc.request('solidityLean/verify',{textDocument:{uri:scopedUri,version:1},options:{function:'falsePost()',counterexamples:true}},{timeoutMs:60000});
      assert.equal(refuted.results[0].status,'refuted');assert.ok(refuted.results[0].counterexample);
      const {compileFixture}=await import('../../scripts/solc-ast.mjs'),fixturePath=join(root,'Owned.ast.json');
      const compiled=compileFixture({args:['--source',join(root,'Scoped.sol'),'--out',fixturePath,'--no-wrapper'],sourceBytes:Buffer.from(text),project:snapshot(join(root,'Scoped.sol'),text,{projectRoot:root}),quiet:true});
      const badPaths=[];
      for(const kind of ['free','variable','nestedUnit','nestedArray','global','nominal']){
        const bad=structuredClone(compiled.fixture),unit=bad.sourceUnits.find(u=>u.name==='Scoped.sol'),contract=unit.ast.nodes.find(n=>n.nodeType==='ContractDefinition'),fn=contract.nodes.find(n=>n.nodeType==='FunctionDefinition');
        if(kind==='free')unit.ast.nodes.push(structuredClone(fn));
        if(kind==='variable')contract.nodes.push({...structuredClone(fn),nodeType:'VariableDeclaration'});
        if(kind==='nestedUnit')unit.ast.extra={...structuredClone(unit.ast),nodes:[structuredClone(contract)]};
        if(kind==='nestedArray')unit.ast.nodes.push([structuredClone(contract)]);
        if(kind==='global')unit.ast.nodes.push({nodeType:'VariableDeclaration',src:`0:0:${unit.id}`,id:999991});
        if(kind==='nominal')unit.ast.nodes.push({nodeType:'StructDefinition',src:`0:0:${unit.id}`,id:999992});
        const path=join(root,kind+'.ast.json');fs.writeFileSync(path,JSON.stringify(bad));badPaths.push(path);
      }
      const checker=join(root,'Ownership.lean');
      fs.writeFileSync(checker,`import Solidity.Frontend.SourceUnits\nopen Lean Elab Command Solidity.Frontend\nrun_cmd do\n  let original ← ofExcept (Json.parse (← IO.FS.readFile ${JSON.stringify(fixturePath)}))\n  unless (Source.readCompilationUnit original).isOk do throwError "original contract specifications refused"\n  for path in [${badPaths.map(p=>JSON.stringify(p)).join(',')}] do\n    let data ← ofExcept (Json.parse (← IO.FS.readFile path))\n    match Source.readCompilationUnit data with\n    | .ok _ => throwError "accepted forged specification ownership: {path}"\n    | .error reason => unless (reason.splitOn "compilationUnitSpecifications").length > 1 do throwError "wrong refusal: {reason}"\n`);
      require('node:child_process').execFileSync('lake',['--quiet','--no-build','lean',checker,'--','--tstack=131072'],{cwd:backend,encoding:'utf8',timeout:60000});
    });
    await t.test('foreign file globals cannot silently enter a multi-file specification',async()=>{
      fs.writeFileSync(join(root,'Globals.sol'),'pragma solidity ^0.8.34; uint constant VALUE=8;');
      const text='pragma solidity ^0.8.34; import "./Globals.sol"; contract GlobalScope {\n/// @custom:key ensures \\result == VALUE\nfunction f() public pure returns(uint) {return 7;} }';
      const globalUri=pathToFileURL(join(root,'GlobalScope.sol')).href;rpc.notify('textDocument/didOpen',{textDocument:{uri:globalUri,version:1,text}});
      const report=await rpc.request('solidityLean/verify',{textDocument:{uri:globalUri,version:1},options:{}});assert.equal(report.results.length,0);assert.match(report.errors[0].reason,/compilationUnitSpecifications/);
      const symbols=await rpc.request('textDocument/documentSymbol',{textDocument:{uri:globalUri,version:1}});assert.ok(symbols.length,'language services remain available for valid Solidity outside the proof profile');
    });
    await t.test('multi-file compiler-code gaps preserve navigation without inventing proof artifacts',async()=>{
      const text='pragma solidity ^0.8.34; import "./Other.sol"; contract CodeGap { function f() public pure returns(bytes memory) {return type(Other).creationCode;} }';
      const codeUri=pathToFileURL(join(root,'CodeGap.sol')).href;rpc.notify('textDocument/didOpen',{textDocument:{uri:codeUri,version:1,text}});
      const symbols=await rpc.request('textDocument/documentSymbol',{textDocument:{uri:codeUri,version:1}});assert.ok(symbols.length);
      const definition=await rpc.request('textDocument/definition',{textDocument:{uri:codeUri,version:1},position:language.position(text,text.indexOf('type(Other)')+7)});assert.equal(definition.uri,pathToFileURL(other).href);
      const report=await rpc.request('solidityLean/verify',{textDocument:{uri:codeUri,version:1},options:{}});assert.equal(report.results.length,0);assert.match(report.errors[0].reason,/compilation-unit code adapter/);
    });
    await t.test('unsaved imported edits invalidate cached dependent proofs',async()=>{
      rpc.notify('textDocument/didOpen',{textDocument:{uri:libUri,version:1,text:library.replace('return x;','return x+1;')}});
      const report=await request('solidityLean/verify',{options:{function:'passes()'}});assert.equal(report.results.find(r=>r.function==='passes').status,'pending');assert.equal(fs.readFileSync(lib,'utf8'),library);
      assert.ok(invalidations.some(p=>p.uri===uri&&p.version===1));
    });
    await t.test('imported errors retain foreign locations and cannot offer a main-file SPDX fix',async()=>{
      rpc.notify('textDocument/didChange',{textDocument:{uri:libUri,version:2},contentChanges:[{text:library.replace('return x;','return +;')}]});
      await request('textDocument/documentSymbol');
      const rows=diagnostics.filter(p=>p.uri===uri).at(-1).diagnostics;
      assert.ok(rows.some(d=>d.severity===1&&d.relatedInformation?.[0]?.location.uri===libUri));
      assert.ok(rows.filter(d=>d.relatedInformation?.length).every(d=>String(d.code).startsWith('import:')));
    });
  }finally{try{await rpc.request('shutdown',null);rpc.notify('exit',null);}catch{}terminateTree(child);rpc.close();fs.rmSync(root,{recursive:true,force:true});}
});
