#!/usr/bin/env node
// Use unchanged production solc_import and #upstream_batch. No builds, reduced
// reader callbacks, altered entry policy or independent interpreter.
import {readFileSync,writeFileSync,mkdirSync,existsSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {createHash} from 'node:crypto';
import {runTool} from './test-solidity.mjs';
const ROOT=resolve('.'),BASE=resolve(process.env.BASELINE_NATIVE_OUT??'tests/upstream/baseline-20261028/native-cache');
const PRIOR=resolve('tests/upstream/baseline-20261028/probes/rechecked');
const COMPILER='/workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js',PIN='6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390';
const sha=x=>createHash('sha256').update(x).digest('hex'),read=p=>JSON.parse(readFileSync(p)),save=(p,x)=>writeFileSync(p,JSON.stringify(x,null,2)+'\n');
if(sha(readFileSync(COMPILER))!==PIN)throw Error('compiler pin mismatch');
const fnv=b=>{let h=0xcbf29ce484222325n;for(const x of b)h=BigInt.asUintN(64,(h^BigInt(x))*0x100000001b3n);return '0x'+h.toString(16);};
const v=(signature,expected=[],args=[],failure=false,revertBytes=[])=>({signature,expected:expected.map(String),args,failure,revertBytes});
const panic=n=>[78,72,123,113,...Array(31).fill(0),n];
const vectors={
 SourceIdentifiers:[v('localMagic()')],
 CommentRanges:[v('f()'),v('f(uint256)',[],['7'])],
 SourceLiterals:['rationalRemainders','signedConstants','computedBounds','byteSequences','extremeConstants','degeneratePowers','addressContext'].map(f=>v(f+'()')),
 ConstantsEnums:[v('boundsAndValueTypes()'),v('otherValueTypes(address)',[],['7']),v('boundsFalsePost()',[],[],true,panic(1))],
 SourceTypes:[v('negativeAlias()')],
 ScalarMatrixValid:[...Object.entries({identifiers:7,comments:21,wrappers:255,bounds:255,literals:1,unicodeBytes:4,addressValue:7,unaryValue:5,bitwiseValue:0,shiftValue:(2n**256n-4n).toString(),comparison:1,lazyValue:1,increment:4,discard:1,deleteValue:0,uncheckedValue:0,freeCall:5,nominalArray:4,fixedCopy:7,construction:7,compound:7,publicEntry:7,hashKeccak:1,hashSha:1,hashRipemd:1,byteConcat:2,stringConcatValue:2,selfIdentity:1,nonpayable:7,recycled:5}).map(([name,n])=>v(name+'()',[n])),v('falseBounds()',[],[],true,panic(1)),v('uncheckedCaller()',[],[],true,panic(17))],
 NativePositive:[v('identifiers()',[7]),v('wrappers()',[255]),v('bounds()',[255]),v('falseBounds()',[],[],true,panic(1)),v('uncheckedCaller()',[],[],true,panic(17)),v('setCounter()'),v('writeFail()',[],[],true,panic(1)),v('readCounter()',[3])],
 CommentSpecPositive:[v('comments(uint256)',[],['7'])],
 PushedMemberMutation:[v('compound()',[107]),v('constantStore()',[207])],
 PushedMemberPositive:[v('positive()',[1])],TryContinuePositive:[v('positive()',[2])],
 ExactRethrow:[v('exact()',[],[],true,[1,2])],HexArrayExplicit:[v('f()',[291])],
 NominalStruct:[v('f()',[7])],PushedMember:[v('positive()',[1])],TryContinue:[v('positive()',[2])],
 BadClause:[v('bad()')],WrongRethrow:[v('wrong()',[],[],true,[1,2])],
 SpecBindings:[v('comments(uint256)',[],['7'])],
};
const calls=existsSync(join(BASE,'native-invocations.json'))?read(join(BASE,'native-invocations.json')):[];
function call(stage,args,job,command='lake'){
 let text='',tool={exitCode:0,timedOut:false},start=performance.now();try{text=runTool(command,args,120000);}catch(e){text=e.message;tool=e.tool??{exitCode:null,error:e.message};}
 const log=join(job,stage+'.log');writeFileSync(log,text);const x={stage,command:[command,...args],...tool,elapsedMs:performance.now()-start,log:log.slice(BASE.length+1),logSha256:sha(Buffer.from(text))};calls.push(x);save(join(BASE,'native-invocations.json'),calls);return x;
}
function reportWrapper(ast,name,out){return `import Solidity.Frontend.Import
open Lean Solidity.Frontend
solc_import ${JSON.stringify(ast)} hash ${fnv(readFileSync(ast))} as Native.«${name}» testing entrypoints
#eval IO.FS.writeFile ${JSON.stringify(out)} (toJson (Native.«${name}».report.map fun (r : ImportRow) => Json.mkObj [("name",toJson r.name),("sourceName",toJson r.sourceName),("signature",toJson r.sourceSignature),("sourceId",toJson r.sourceId),("status",toJson r.status.toStr),("reason",toJson r.reason),("admissionChecked",toJson r.admissionChecked),("tag",toJson r.tag.toStr),("payable",toJson r.payable),("rawRepr",toJson (reprStr r)),("sourceDiagnostic",match r.sourceDiagnostic with | none => Json.null | some d => Json.mkObj [("name",toJson d.name.toString),("reason",toJson d.reason),("kind",toJson (reprStr d.kind))])])).pretty
`;}
for(const name of process.argv.slice(2))for(const pipeline of ['legacy','viaIR']){
 const job=join(BASE,'runs',name,pipeline);if(existsSync(job))throw Error('refuse overwrite '+job);mkdirSync(job,{recursive:true});
 let ast,record={case:name,pipeline,stages:[],observationsAreNotProofs:true};
 const source=join(BASE,'inputs',name+'.sol');
 if(existsSync(source)){
  ast=join(job,'source.ast.json');record.source=source;record.sourceSha256=sha(readFileSync(source));
  const c=call('compiler',['scripts/solc-ast.mjs','--compiler-file',COMPILER,'--compiler-sha256',PIN,'--source',source,'--out',ast,'--no-wrapper',...(pipeline==='viaIR'?['--via-ir']:[])],job,process.execPath);record.stages.push(c);if(c.exitCode!==0){save(join(job,'record.json'),record);throw Error('positive diagnostic compiler failed');}
 }else{
  ast=join(PRIOR,'runs',name,pipeline,'source.ast.json');const previous=read(join(PRIOR,'runs',name,pipeline,'record.json'));
  if(sha(readFileSync(ast))!==previous.astSha256)throw Error('prior AST drift');record.reusedCompilerRecord=join(PRIOR,'runs',name,pipeline,'record.json');record.reusedCompilerRecordSha256=sha(readFileSync(record.reusedCompilerRecord));record.sourceSha256=previous.sourceSha256;
 }
 const fixture=read(ast);if(fixture.header.compilerSha256!==PIN||fixture.header.sourceSha256!==record.sourceSha256||fixture.header.settings.viaIR!==(pipeline==='viaIR'))throw Error('fixture provenance mismatch');
 record.fixture=ast;record.fixtureSha256=sha(readFileSync(ast));record.compilerSha256=PIN;
 const report=join(job,'typed-import.json'),wrapper=join(job,'TypedImport.lean');writeFileSync(wrapper,reportWrapper(ast,name,report));
 record.stages.push(call('typed-import',['--quiet','--no-build','lean',wrapper,'--','--tstack=131072','-j1'],job));
 if(existsSync(report))record.typedImport=read(report);
 if(vectors[name]){
  const entry={path:'native-diagnostic/'+name,pipeline,requiredPipelines:['legacy','viaIR'],fixture:ast,contract:name,vectors:vectors[name]};
  const input=join(job,'jobs.json'),output=join(job,'runtime.json'),runFile=join(job,'Replay.lean');save(input,[entry]);writeFileSync(runFile,`import Solidity.Tools.Upstream\n#upstream_batch ${JSON.stringify(input)} to ${JSON.stringify(output)}\n`);
  record.stages.push(call('replay',['--quiet','--no-build','lean',runFile,'--','--tstack=131072','-j1'],job));if(existsSync(output))record.runtime=read(output);
  if(name==='NativePositive'){
   const negInput=join(job,'negative-jobs.json'),negOutput=join(job,'negative-runtime.json'),negFile=join(job,'NegativeReplay.lean');save(negInput,[{...entry,path:'native-diagnostic/intentional-wrong-expectation',vectors:[v('identifiers()',[8])]}]);writeFileSync(negFile,`import Solidity.Tools.Upstream\n#upstream_batch ${JSON.stringify(negInput)} to ${JSON.stringify(negOutput)}\n`);
   record.stages.push(call('negative-replay',['--quiet','--no-build','lean',negFile,'--','--tstack=131072','-j1'],job));if(existsSync(negOutput))record.negativeRuntime=read(negOutput);
  }
 }
 save(join(job,'record.json'),record);console.log(JSON.stringify({case:name,pipeline,imports:record.typedImport?.map(r=>[r.sourceName,r.status]),runtime:record.runtime?.map(r=>[r.status,r.reason])}));
 if(record.stages.some(s=>s.timedOut||s.exitCode!==0))throw Error('native harness stage failed; inspect retained evidence before more checks');
}
