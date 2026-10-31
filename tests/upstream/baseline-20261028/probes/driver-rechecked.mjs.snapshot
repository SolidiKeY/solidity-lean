#!/usr/bin/env node
// Bounded separate diagnostics. Uses existing SHA-pinned compiler, listing and
// interpreter commands; never rewrites the upstream fixture/report corpus.
import {readFileSync,writeFileSync,mkdirSync,existsSync} from 'node:fs';
import {resolve,join} from 'node:path';
import {createHash} from 'node:crypto';
import {runTool} from './test-solidity.mjs';
import {sourceLocations,sourceHash} from './source-locations.mjs';
const root=resolve('.'),base=resolve(process.env.BASELINE_PROBE_OUT??'tests/upstream/baseline-20261028/probes');
const readerOnly=process.env.BASELINE_READER_ONLY==='1';
const compiler='/workspace/.setup/soljson/soljson-v0.8.38+commit.1835d247.js';
const compilerSha='6c74ffba0ea4cf9521e78b16052a98208770bb7677616de08ced239f4312d390';
const sha=b=>createHash('sha256').update(b).digest('hex');
if(sha(readFileSync(compiler))!==compilerSha)throw Error('compiler drift');
const save=(p,x)=>writeFileSync(p,JSON.stringify(x,null,2)+'\n');
const fnv=b=>{let x=0xcbf29ce484222325n;for(const v of b)x=BigInt.asUintN(64,(x^BigInt(v))*0x100000001b3n);return '0x'+x.toString(16);};
const all=existsSync(join(base,'invocations.json'))?JSON.parse(readFileSync(join(base,'invocations.json'))):[];
function call(stage,command,args,job){
 const start=performance.now();let output='',tool={exitCode:0,timedOut:false},ok=true;
 try{output=runTool(command,args,120000);}catch(e){ok=false;output=e.message;tool=e.tool??{exitCode:null,error:e.message};}
 const log=join(job,stage+'.log');writeFileSync(log,output);
 const item={stage,command:[command,...args],exitCode:tool.exitCode,tool,elapsedMs:performance.now()-start,log:log.slice(base.length+1),logSha256:sha(Buffer.from(output)),ok};all.push(item);save(join(base,'invocations.json'),all);return item;
}
const v=(signature,expected=[],args=[],failure=false,revertBytes=[])=>({signature,args,expected:expected.map(String),failure,revertBytes});
const panic=n=>[78,72,123,113,...Array(31).fill(0),n];
const vectors={
 SourceIdentifiers:[v('localMagic()')],
 SourceLiterals:['rationalRemainders','signedConstants','computedBounds','byteSequences','extremeConstants','degeneratePowers','addressContext'].map(f=>v(f+'()')),
 ConstantsEnums:[v('boundsAndValueTypes()'),v('otherValueTypes(address)',[],['7']),v('boundsFalsePost()',[],[],true,panic(1))],
 SourceTypes:[v('negativeAlias()')],
 ScalarMatrix:[...Object.entries({identifiers:7,comments:21,wrappers:255,bounds:255,literals:1,unicodeBytes:4,addressValue:7,unaryValue:5,bitwiseValue:0,shiftValue:(2n**256n-4n).toString(),comparison:1,lazyValue:1,increment:4,discard:1,deleteValue:0,uncheckedValue:0,freeCall:5,nominalArray:4,fixedCopy:7,construction:7,compound:7,publicEntry:7,hashKeccak:1,hashSha:1,hashRipemd:1,byteConcat:2,stringConcatValue:2,selfIdentity:1,nonpayable:7,recycled:5}).map(([f,n])=>v(f+'()',[n])),v('falseBounds()',[],[],true,panic(1)),v('uncheckedCaller()',[],[],true,panic(17))],
 NominalStruct:[v('f()',[7])],
 HexArray:[v('f()',[291])], ExactRethrow:[v('exact()',[],[],true,[1,2])],
 PushedMember:[v('positive()',[1])], TryContinue:[v('positive()',[2])],
};
function readerProgram(ast,name,output,pipeline){return `import Solidity.Frontend.SolcJson.Contract
open Lean Solidity.Frontend
private def readProbe : IO Unit := do
 let fixture := (Json.parse (← IO.FS.readFile ${JSON.stringify(ast)})).toOption.getD Json.null
 let ast := (fixture.getObjVal? "ast").toOption.getD Json.null
 let outcome : Json := match Source.read fixture ast with
  | .error e => Json.mkObj [("phase",toJson "provenance"),("status",toJson "refused"),("reason",toJson e)]
  | .ok provenance =>
   let scan := fun request => (Admission.scan ast provenance {request with declarationRoots := request.declarationRoots ++ [Admission.header [] ast] ++ (J.arrD ast "nodes").toList.filter (J.kind · == "PragmaDirective")}).normalize.requireCompilerCode false
   match readContract ast ${JSON.stringify(name)} [] true (scanSource := scan) (entrypoints := true) (viaIR := ${pipeline==='viaIR'?'true':'false'}) with
   | .error e => Json.mkObj [("phase",toJson "source-reader"),("status",toJson "refused"),("reason",toJson e)]
   | .ok c =>
    let functions := (c.ctor.toList ++ c.funs).map fun f =>
     let (status,reason,body) : String × String × Json := match f.body with
      | .error g => ("reader-refused",g.msg,Json.null)
      | .ok ss => ("reader-emitted","",toJson (ss.map fun (entry : Nat × String) => Json.mkObj [("line",toJson entry.1),("text",toJson entry.2)]))
     Json.mkObj [("function",toJson f.sourceName),("modelName",toJson f.name),("signature",toJson f.sourceSignature),("sourceId",toJson f.sourceId),("line",toJson f.line),("tag",toJson f.tag.toStr),("status",toJson status),("reason",toJson reason),("body",body),("scopeDiagnostic",match f.sourceScope.diagnostic? with | none => Json.null | some d => Json.mkObj [("name",toJson d.name.toString),("reason",toJson d.reason)])]
    Json.mkObj [("phase",toJson "source-reader"),("status",toJson "reader-completed"),("functions",toJson functions)]
 IO.FS.writeFile ${JSON.stringify(output)} outcome.pretty
#eval readProbe
`;}
vectors.ScalarMatrixValid=vectors.ScalarMatrix;
const names=process.argv.slice(2);if(!names.length)throw Error('provide explicit cases');
for(const name of names){for(const pipeline of ['legacy','viaIR']){
 const job=join(base,'runs',name,pipeline);if(existsSync(job))throw Error('refuse overwrite '+job);mkdirSync(job,{recursive:true});
 const source=join(base,'inputs',name+'.sol'),ast=join(job,'source.ast.json');
 const record={case:name,pipeline,source:source.slice(base.length+1),sourceSha256:sha(readFileSync(source)),compilerSha256:compilerSha,stages:[]};
 const c=call('compile',process.execPath,['scripts/solc-ast.mjs','--compiler-file',compiler,'--compiler-sha256',compilerSha,'--source',source,'--out',ast,'--no-wrapper',...(pipeline==='viaIR'?['--via-ir']:[])],job);record.stages.push(c);
 if(!c.ok){record.status='compiler-rejected-or-blocked';save(join(job,'record.json'),record);continue;}
 const data=readFileSync(ast),parsed=JSON.parse(data);record.astSha256=sha(data);record.settings=parsed.header.settings;
 if(readerOnly){
  const output=join(job,'reader.json'),file=join(job,'Reader.lean');writeFileSync(file,readerProgram(ast,name,output,pipeline));
  record.stages.push(call('source-reader','lake',['--quiet','--no-build','lean',file,'--','--tstack=131072','-j1'],job));
  if(existsSync(output)){
   record.reader=JSON.parse(readFileSync(output));const location=sourceLocations(parsed.ast,readFileSync(source));
   record.sourceLocations=(record.reader.functions??[]).map(r=>({function:r.function,signature:r.signature,sourceHash:sourceHash(readFileSync(source)),range:location(name,r)}));
  }
  record.typedAdmission={status:'blocked',reason:'Single900s API refresh exit124; full typed importer/Testing dependencies stale. No repeated build. Reader-only diagnostics do not include native typed elaboration, private specification binding/scanning, proof listing or replay.'};
  if(name==='ScalarMatrix'||name==='ScalarMatrixValid'){
   record.provenanceControls=[];
   for(const mutation of ['compiler-digest','pragma-record']){
    const altered=structuredClone(parsed);
    if(mutation==='compiler-digest')altered.header.compilerSha256='0'.repeat(64);else altered.header.acceptedPragmas=[['solidity','>=','0.9','.0']];
    const badAst=join(job,mutation+'.ast.json'),badFile=join(job,mutation+'.lean'),badOut=join(job,mutation+'.json');save(badAst,altered);writeFileSync(badFile,readerProgram(badAst,name,badOut,pipeline));
    const result=call(mutation,'lake',['--quiet','--no-build','lean',badFile,'--','--tstack=131072','-j1'],job);
    record.provenanceControls.push({mutation,fixture:badAst.slice(base.length+1),parentAstSha256:sha(data),result,...(existsSync(badOut)?{observation:JSON.parse(readFileSync(badOut))}:{})});
   }
  }
  record.status='reader-diagnostic-completed';save(join(job,'record.json'),record);
  if(!record.stages.every(x=>x.ok)||!record.reader)throw Error('reader harness stage failed; stopped before additional cases: '+name+'/'+pipeline);
  console.log(JSON.stringify({case:name,pipeline,reader:record.reader?.status,rows:record.reader?.functions?.map(r=>[r.function,r.status,r.reason])}));continue;
 }
 const list=join(job,'listing.json'),file=join(job,'Listing.lean');
 writeFileSync(file,`import Solidity.Frontend.Testing\nsolc_import ${JSON.stringify(ast)} hash ${fnv(data)} as Probe.«${name}» testing\nsolc_scoped_problems Probe.«${name}» decl\n#solkey_test Probe.«${name}» listing to ${JSON.stringify(list)}\n`);
 const l=call('listing','lake',['--quiet','--no-build','lean',file,'--','--tstack=131072','-j1'],job);record.stages.push(l);
 if(existsSync(list)){
  record.listing=JSON.parse(readFileSync(list));const location=sourceLocations(parsed.ast,readFileSync(source));
  record.sourceLocations=record.listing.map(r=>({function:r.function,signature:r.signature,sourceHash:sourceHash(readFileSync(source)),range:location(name,r)}));
 }
 if(name==='ScalarMatrix'||name==='ScalarMatrixValid'){
  record.provenanceControls=[];
  for(const mutation of ['compiler-digest','pragma-record']){
   const altered=structuredClone(parsed);
   if(mutation==='compiler-digest')altered.header.compilerSha256='0'.repeat(64);
   else altered.header.acceptedPragmas=[['solidity','>=','0.9','.0']];
   const badAst=join(job,mutation+'.ast.json'),badFile=join(job,mutation+'.lean');save(badAst,altered);
   writeFileSync(badFile,`import Solidity.Frontend.Testing\nsolc_import ${JSON.stringify(badAst)} hash ${fnv(readFileSync(badAst))} as Bad.«${name}» testing\n`);
   const result=call(mutation,'lake',['--quiet','--no-build','lean',badFile,'--','--tstack=131072','-j1'],job);
   record.provenanceControls.push({mutation,fixture:badAst.slice(base.length+1),parentAstSha256:sha(data),result});
  }
 }
 if(vectors[name]){
  const entry={path:'diagnostic/'+name,pipeline,requiredPipelines:['legacy','viaIR'],fixture:ast,contract:name,vectors:vectors[name]};
  const jobs=join(job,'jobs.json'),output=join(job,'runtime.json'),wrapper=join(job,'Replay.lean');save(jobs,[entry]);
  writeFileSync(wrapper,`import Solidity.Tools.Upstream\n#upstream_batch ${JSON.stringify(jobs)} to ${JSON.stringify(output)}\n`);
  const r=call('runtime','lake',['--quiet','--no-build','lean',wrapper,'--','--tstack=131072','-j1'],job);record.stages.push(r);if(existsSync(output))record.runtime=JSON.parse(readFileSync(output));
  // A deliberately false diagnostic expectation, separate from every positive
  // input. Its required mismatch demonstrates that replay is not unconditional.
  if(name==='ScalarMatrix'||name==='ScalarMatrixValid'){
   const negJobs=join(job,'negative-jobs.json'),negOut=join(job,'negative-runtime.json'),negFile=join(job,'Negative.lean');
   save(negJobs,[{...entry,path:'diagnostic/wrong-expected-identifiers',vectors:[v('identifiers()',[8])]}]);
   writeFileSync(negFile,`import Solidity.Tools.Upstream\n#upstream_batch ${JSON.stringify(negJobs)} to ${JSON.stringify(negOut)}\n`);
   record.stages.push(call('negative-runtime','lake',['--quiet','--no-build','lean',negFile,'--','--tstack=131072','-j1'],job));if(existsSync(negOut))record.negativeRuntime=JSON.parse(readFileSync(negOut));
  }
 }
 record.status='diagnostic-completed';save(join(job,'record.json'),record);
 console.log(JSON.stringify({case:name,pipeline,listingExit:l.exitCode,listingStatuses:record.listing?.map(r=>[r.function,r.status]),runtime:record.runtime?.map(r=>[r.status,r.reason])}));
}}
