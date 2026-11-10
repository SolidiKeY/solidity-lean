'use strict';
const {mkdirSync,readFileSync,writeFileSync,existsSync,rmSync}=require('node:fs');
const {join}=require('node:path');
const {pathToFileURL}=require('node:url');
const {createHash}=require('node:crypto');
const {LeanSession}=require('./lean-session.cjs');
const projects=require('./project.cjs');
const {checkDirect,disposeDirect}=require('./direct-runtime.cjs');

let session,compiler,locations;
function checkpointRows(path,contract,contracts=[]){
  if(!existsSync(path))return null;
  const lineage=new Set(contract.linearizedBaseContracts||[contract.id]);
  const members=[contract,...contracts.filter(c=>c!==contract&&lineage.has(c.id))].flatMap(c=>c.nodes);
  return JSON.parse(readFileSync(path,'utf8')).map(row=>{
    const declaration=members.find(n=>n.nodeType==='FunctionDefinition'&&n.id===row.sourceId);
    if(!(row.sourceId===-1&&row.function==='constructor')&&(!declaration||row.function!==(declaration.name||declaration.kind)))
      throw new Error('Verification checkpoint does not belong to the selected contract declaration');
    return row;
  });
}
const importDiagnostic=d=>d.severity===1||d.severity===2&&d.message?.includes('solc_import:');
async function execute(task){
  const {root,directory,source,text}=task;
  mkdirSync(directory,{recursive:true});
  compiler??=await import(pathToFileURL(join(root,'scripts/solc-ast.mjs')).href);
  locations??=await import(pathToFileURL(join(root,'scripts/source-locations.mjs')).href);
  if(task.action==='analyze') {
    const project=task.project??projects.snapshot(source,text,task.settings,task.documents);
    const compiled=compiler.compileFixture({args:['--source',source,'--out',join(directory,'source.ast.json'),'--no-wrapper'],sourceBytes:Buffer.from(text,'utf8'),project,analysisOnly:true,quiet:true});
    return compiled;
  }
  const {compiled,options={}}=task;
  if(createHash('sha256').update(text).digest('hex')!==(compiled.sourceHash??compiled.fixture?.header.sourceSha256))throw new Error('Compiler snapshot hash mismatch');
  if(compiled.proofGap)return {results:[],errors:[{source,stage:'admission',reason:compiled.proofGap}]};
  writeFileSync(join(directory,'source.ast.json'),compiled.text);
  const results=[],errors=[],benchmarkLog=[],directChecks=[];let usedLegacy=false,wasmBuild;
  const primary=compiled.primaryAst??compiled.fixture.ast;
  const allAsts=compiled.fixture.sourceUnits?.map(u=>u.ast)??[primary];
  const allContracts=allAsts.flatMap(a=>a.nodes).filter(n=>n.nodeType==='ContractDefinition');
  const contracts=primary.nodes.filter(n=>n.nodeType==='ContractDefinition'&&(!options.contract||n.name===options.contract));
  const locate=locations.sourceLocations(primary,Buffer.from(text));
  for(const contract of contracts){
    if(!/^[A-Za-z_$][A-Za-z0-9_$]*$/.test(contract.name))throw new Error('Unsupported contract name');
    // Rows the compiled verifier decides stay direct. Rows it reports
    // `unsupported`, or every row when it cannot take the input (a gap, no
    // runtime), are rechecked on the certified Lean path (kernel proofs; false
    // obligations stay pending without `counterexamples`) instead of being
    // reported `unsupported`.
    const decided=await checkDirect(root,contract,options);
    const directMode=options.certify!==true&&!options.auditPreconditions&&process.env.SOLIDITY_LEAN_DIRECT!=='0';
    const recheck=decided?new Set(decided.results.filter(r=>r.status==='unsupported').map(r=>r.sourceId)):null;
    if(decided){
      directChecks.push({contract:contract.name,backend:'unavailable',environmentImports:0,...decided.timings});wasmBuild=decided.build;
      errors.push(...(decided.errors||[]).map(error=>({source,contract:contract.name,...error})));
      for(const row of decided.results)if(!recheck.has(row.sourceId)){
        const range=locate(contract.name,row);
        results.push({...row,source,contract:contract.name,sourceHash:compiled.sourceHash??compiled.fixture.header.sourceSha256,...(range?{range}:{}),...(row.counterexample?{counterexample:locations.sourceWitness(primary,contract.name,row)}:{})});
      }
      if(!recheck.size)continue;
    }
    // Multi-file units always took the certified path; direct mode reaches
    // here only to recheck rows the compiled verifier could not decide.
    const certified=options.certify===true||allAsts.length>1||directMode;
    if(task.deferLegacyBuild)return {needsLegacyBuild:true};
    usedLegacy=true;session??=new LeanSession(root,directory);
    const output=join(directory,`result-${task.id}-${contract.id}.json`);
    rmSync(output,{force:true});
    const name=`SolTests.«${contract.name}»`;
    const command=`#solkey_test ${name}${options.function?` only ${JSON.stringify(options.function)}`:''}${options.listing?' listing':''}${options.auditPreconditions&&!options.listing?' audit_preconditions':''}${options.counterexamples&&!options.listing?' counterexamples':''} to ${JSON.stringify(output)}`;
    const wrapper=`import Solidity.Frontend.Testing\nset_option sol.testing.closedSpecs ${options.closedSpecs!==false}\nset_option sol.testing.direct ${!certified}\nset_option sol.benchmark ${options.benchmark===true}\nsolc_import "source.ast.json" hash ${compiled.hash} as ${name} testing\nsolc_scoped_problems ${name} decl\n${command}\n`;
    if(options.benchmark)session.stderr='';
    const diagnostics=await session.check(wrapper,options.timeoutMs??60000);
    if(options.benchmark){await new Promise(setImmediate);benchmarkLog.push(session.stderr,...diagnostics.map(d=>d.message||''));}
    for(const diagnostic of diagnostics)if(importDiagnostic(diagnostic))
      errors.push({source,contract:contract.name,stage:'lean',reason:diagnostic.message});
    const checkpoint=checkpointRows(output,contract,allContracts);
    if(checkpoint)for(const row of checkpoint.filter(r=>!recheck||recheck.has(r.sourceId))) {
      const inherited=allContracts.filter(n=>(contract.linearizedBaseContracts||[]).includes(n.id))
        .flatMap(n=>n.nodes).find(n=>n.nodeType==='FunctionDefinition'&&n.id===row.sourceId);
      const range=locate(contract.name,row)||(inherited?locations.sourceRange(Buffer.from(text),inherited.src,Number(primary.src.split(':').at(-1))):null);
      results.push({...row,source,contract:contract.name,
      sourceHash:compiled.sourceHash??compiled.fixture.header.sourceSha256,...(range?{range}:{}),
      ...(row.counterexample?{counterexample:locations.sourceWitness(primary,contract.name,row)}:{})});
    }
    else if(!errors.length)throw new Error('Lean completed without a verification checkpoint');
    // A rechecked row Lean did not return keeps its compiled-verifier answer.
    if(recheck)for(const row of decided.results)if(recheck.has(row.sourceId)&&!(checkpoint||[]).some(r=>r.sourceId===row.sourceId)){
      const range=locate(contract.name,row);
      results.push({...row,source,contract:contract.name,sourceHash:compiled.sourceHash??compiled.fixture.header.sourceSha256,...(range?{range}:{})});
    }
  }
  if(!contracts.length)errors.push({source,stage:'discovery',reason:'No contracts selected'});
  return {results,errors,backend:{workerPid:process.pid,directChecks,...(!usedLegacy&&directChecks.length?{kind:directChecks.every(c=>c.backend==='generated-c-wasm')?'generated-c-wasm':directChecks.every(c=>c.backend==='generated-c-native')?'generated-c-native':'compiled-unknown',wasmBuild,native:{active:directChecks.every(c=>c.backend==='generated-c-native'),reason:directChecks.every(c=>c.backend==='generated-c-native')?'standalone-native':'standalone-wasm-or-unavailable'}}:{kind:directChecks.length?'mixed':'lean',leanServerPid:session?.child?.pid,leanDocumentVersion:session?.version,native:session?.native??{active:false,reason:'no-contracts'}}),...(options.benchmark?{benchmarkMessages:benchmarkLog,phases:[...benchmarkLog.join(String.fromCharCode(10)).matchAll(/SOLKEY_BENCH (\{[^\r\n]*\})/g)].map(m=>JSON.parse(m[1])),nativeDirectNanos:[...benchmarkLog.join(String.fromCharCode(10)).matchAll(/NATIVE_DIRECT_CHECK (\d+)/g)].map(m=>Number(m[1])),nativeWalkNanos:[...benchmarkLog.join(String.fromCharCode(10)).matchAll(/NATIVE_SPEC_WALK (\d+)/g)].map(m=>Number(m[1]))}:{})}};
}
if(require.main===module){
let stopping=false;
process.on('message',async task=>{
  if(task.action==='shutdown'){
    if(stopping)return;stopping=true;
    try{const deadline=Math.min(Number.isSafeInteger(task.deadline)?task.deadline:Date.now(),Date.now()+1000);await Promise.all([session?.finishDispose({deadline}),disposeDirect({deadline})]);process.exit(0);}
    catch(error){process.stderr.write('Lean worker retirement failed: '+error.message+'\n');session?.dispose();process.exit(1);}
    return;
  }
  if(stopping)return;
  try{const result=await execute(task);if(!stopping)process.send({id:task.id,result});}
  catch(error){if(!stopping)process.send({id:task.id,error:{message:error.message,diagnostics:error.diagnostics}});}
});
process.on('disconnect',()=>{session?.dispose();process.exit(0);});
for(const signal of ['SIGTERM','SIGINT'])process.on(signal,()=>{session?.dispose();process.exit(0);});
}
module.exports={checkpointRows,importDiagnostic};
