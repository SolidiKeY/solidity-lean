import {Buffer} from 'buffer';
import {parseReport} from '../../vscode/src/report.cjs';
import {sourceLocations,sourceRange,sourceWitness} from '../../scripts/source-locations.mjs';

let worker,booting,sequence=0;
const pending=new Map();
function request(method,params={}){
  const id=++sequence;
  return new Promise((resolve,reject)=>{pending.set(id,{resolve,reject});worker.postMessage({id,method,params});});
}
export function cancelProofs(reason=Object.assign(new Error('Verification cancelled'),{code:'CANCELLED'})){
  worker?.terminate();worker=undefined;booting=undefined;
  for(const task of pending.values())task.reject(reason);pending.clear();
}
export async function prepareProofs(progress){
  if(!booting){
    worker=new Worker('/kernel-worker.js');
    worker.onmessage=event=>{const message=event.data;if(message.method){progress?.(message);return;}const task=pending.get(message.id);if(!task)return;pending.delete(message.id);if(message.error){if(message.error.stack)progress?.({method:'log',message:message.error.stack});task.reject(new Error(message.error.message));}else task.resolve(message.result);};
    worker.onerror=event=>{for(const task of pending.values())task.reject(new Error(event.message||'Browser Lean worker failed'));pending.clear();booting=undefined;worker?.terminate();worker=undefined;};
    booting=request('boot');
  }
  return booting;
}
export async function verifyInBrowser({compiled,text,name,options={},timeoutMs=600000}){
  const deadline=Date.now()+timeoutMs;
  await prepareProofs();
  const source='/workspace/'+name;
  if(compiled.proofGap)return {results:[],errors:[{source,stage:'admission',reason:compiled.proofGap}]};
  const primary=compiled.primaryAst??compiled.fixture.ast;
  const allAsts=compiled.fixture.sourceUnits?.map(u=>u.ast)??[primary];
  const allContracts=allAsts.flatMap(a=>a.nodes).filter(n=>n.nodeType==='ContractDefinition');
  const contracts=primary.nodes.filter(n=>n.nodeType==='ContractDefinition'&&(!options.contract||n.name===options.contract));
  const results=[],errors=[],locate=sourceLocations(primary,Buffer.from(text));
  for(const contract of contracts){
    if(!/^[A-Za-z_$][A-Za-z0-9_$]*$/.test(contract.name))throw new Error('Unsupported contract name');
    const output='/output/result-'+(++sequence)+'-'+contract.id+'.json',namespace=`SolTests.«${contract.name}»`;
    const command=`#solkey_test ${namespace}${options.function?` only ${JSON.stringify(options.function)}`:''}${options.listing?' listing':''}${options.auditPreconditions&&!options.listing?' audit_preconditions':''}${options.counterexamples&&!options.listing?' counterexamples':''} to ${JSON.stringify(output)}`;
    const wrapper=`import Solidity.Frontend.Testing\nsolc_import "source.ast.json" hash ${compiled.hash} as ${namespace} testing\nsolc_scoped_problems ${namespace} decl\n${command}\n`;
    let timer;
    const checked=await Promise.race([
      request('check',{source:wrapper,files:{'/workspace/source.ast.json':compiled.text},outputs:[output]}),
      new Promise((_,reject)=>{timer=setTimeout(()=>{const error=Object.assign(new Error('Browser verification timed out'),{code:'TIMEOUT'});cancelProofs(error);reject(error);},Math.max(1,deadline-Date.now()));})
    ]).finally(()=>clearTimeout(timer));
    if(checked.code!==0)errors.push({source,contract:contract.name,stage:'lean',reason:`Lean browser check failed (exit ${checked.code})${checked.stderr?.length?': '+checked.stderr.join('\n'):''}`});
    for(const diagnostic of checked.diagnostics)if(diagnostic.severity==='error'||diagnostic.severity==='warning'&&diagnostic.message.includes('solc_import:'))errors.push({source,contract:contract.name,stage:'lean',reason:diagnostic.message});
    if(checked.outputs[output]){
      const lineage=new Set(contract.linearizedBaseContracts||[contract.id]);
      const members=[contract,...allContracts.filter(c=>c!==contract&&lineage.has(c.id))].flatMap(c=>c.nodes);
      const checkpoint=JSON.parse(checked.outputs[output]);if(!Array.isArray(checkpoint))throw new Error('Invalid kernel checkpoint');
      for(const row of checkpoint){
        const declaration=members.find(n=>n.nodeType==='FunctionDefinition'&&n.id===row.sourceId);
        if(!(row.sourceId===-1&&row.function==='constructor')&&(!declaration||row.function!==(declaration.name||declaration.kind)))throw new Error('Kernel checkpoint does not belong to the selected declaration');
        const range=locate(contract.name,row)||(declaration?sourceRange(Buffer.from(text),declaration.src,Number(primary.src.split(':').at(-1))):null);
        results.push({...row,source,contract:contract.name,sourceHash:compiled.sourceHash??compiled.fixture.header.sourceSha256,...(range?{range}:{}),...(row.counterexample?{counterexample:sourceWitness(primary,contract.name,row)}:{})});
      }
    }else if(!errors.length)throw new Error('Lean completed without a fresh verification checkpoint');
  }
  if(!contracts.length)errors.push({source,stage:'discovery',reason:'No contracts selected'});
  const report=parseReport(JSON.stringify({results,errors}));
  if((!options.counterexamples||options.listing)&&results.some(row=>row.status==='refuted'))throw new Error('Kernel returned unrequested model prestate evidence');
  if(options.auditPreconditions&&!options.listing&&results.some(row=>row.preconditions===undefined))throw new Error('Kernel did not return the requested precondition audit');
  return report;
}
