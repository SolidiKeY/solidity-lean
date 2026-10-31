'use strict';
const {mkdirSync,readFileSync,writeFileSync,existsSync,rmSync}=require('node:fs');
const {join}=require('node:path');
const {pathToFileURL}=require('node:url');
const {createHash}=require('node:crypto');
const {LeanSession}=require('./lean-session.cjs');

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
    const compiled=compiler.compileFixture({args:['--source',source,'--out',join(directory,'source.ast.json'),'--no-wrapper'],sourceBytes:Buffer.from(text,'utf8'),quiet:true});
    return compiled;
  }
  const {compiled,options={}}=task;
  if(createHash('sha256').update(text).digest('hex')!==compiled.fixture.header.sourceSha256)throw new Error('Compiler snapshot hash mismatch');
  writeFileSync(join(directory,'source.ast.json'),compiled.text);
  const results=[],errors=[];
  const contracts=compiled.fixture.ast.nodes.filter(n=>n.nodeType==='ContractDefinition'&&(!options.contract||n.name===options.contract));
  const locate=locations.sourceLocations(compiled.fixture.ast,Buffer.from(text));
  session??=new LeanSession(root,directory);
  for(const contract of contracts){
    if(!/^[A-Za-z_$][A-Za-z0-9_$]*$/.test(contract.name))throw new Error('Unsupported contract name');
    const output=join(directory,`result-${task.id}-${contract.id}.json`);
    rmSync(output,{force:true});
    const name=`SolTests.«${contract.name}»`;
    const command=`#solkey_test ${name}${options.function?` only ${JSON.stringify(options.function)}`:''}${options.listing?' listing':''}${options.auditPreconditions&&!options.listing?' audit_preconditions':''}${options.counterexamples&&!options.listing?' counterexamples':''} to ${JSON.stringify(output)}`;
    const wrapper=`import Solidity.Frontend.Testing\nsolc_import "source.ast.json" hash ${compiled.hash} as ${name} testing\nsolc_scoped_problems ${name} decl\n${command}\n`;
    const diagnostics=await session.check(wrapper,options.timeoutMs??60000);
    for(const diagnostic of diagnostics)if(importDiagnostic(diagnostic))
      errors.push({source,contract:contract.name,stage:'lean',reason:diagnostic.message});
    const checkpoint=checkpointRows(output,contract,compiled.fixture.ast.nodes.filter(n=>n.nodeType==='ContractDefinition'));
    if(checkpoint)for(const row of checkpoint) {
      const inherited=compiled.fixture.ast.nodes.filter(n=>n.nodeType==='ContractDefinition'&&(contract.linearizedBaseContracts||[]).includes(n.id))
        .flatMap(n=>n.nodes).find(n=>n.nodeType==='FunctionDefinition'&&n.id===row.sourceId);
      const range=locate(contract.name,row)||(inherited?locations.sourceRange(Buffer.from(text),inherited.src):null);
      results.push({...row,source,contract:contract.name,
      sourceHash:compiled.fixture.header.sourceSha256,...(range?{range}:{}),
      ...(row.counterexample?{counterexample:locations.sourceWitness(compiled.fixture.ast,contract.name,row)}:{})});
    }
    else if(!errors.length)throw new Error('Lean completed without a verification checkpoint');
  }
  if(!contracts.length)errors.push({source,stage:'discovery',reason:'No contracts selected'});
  return {results,errors,backend:{workerPid:process.pid,leanServerPid:session.child.pid,leanDocumentVersion:session.version}};
}
if(require.main===module){
process.on('message',async task=>{
  try{process.send({id:task.id,result:await execute(task)});}
  catch(error){process.send({id:task.id,error:{message:error.message,diagnostics:error.diagnostics}});}
});
process.on('disconnect',()=>{session?.dispose();process.exit(0);});
for(const signal of ['SIGTERM','SIGINT'])process.on(signal,()=>{session?.dispose();process.exit(0);});
}
module.exports={checkpointRows,importDiagnostic};
