import {Buffer} from 'buffer';
import {parseReport} from '../../vscode/src/report.cjs';
import {sourceLocations,sourceRange,sourceWitness} from '../../scripts/source-locations.mjs';

import {VerifierWorker} from './verifier-worker.mjs';
import {prepareDirect,checkDirect,cancelDirect,abandonDirect} from './direct.mjs';
let legacy,sequence=0,progress;
const jobs=new Set();
function cancelJobs(){for(const job of jobs)job.cancelled=true;}
export function cancelProofs(reason){cancelJobs();legacy?.dispose(reason);legacy=undefined;cancelDirect(reason);}
export function abandonProofs(reason){cancelJobs();legacy?.abandon(reason);abandonDirect(reason);}
async function prepareLegacyProofs(){legacy??=new VerifierWorker('/kernel-worker.js',progress);return legacy.boot();}
export async function prepareProofs(onProgress){
  if(onProgress)progress=onProgress;
  return await prepareDirect(progress)||await prepareLegacyProofs();
}
export async function verifyInBrowser({compiled,text,name,options={},timeoutMs=600000}){
  const job={cancelled:false};jobs.add(job);
  const deadline=Date.now()+timeoutMs;
  const expired=()=>Object.assign(new Error('Verification timed out'),{code:'TIMEOUT',preserveRuntime:true});
  const live=()=>{if(Date.now()>=deadline)throw expired();if(job.cancelled)throw Object.assign(new Error('Verification cancelled'),{code:'CANCELLED'});};
  try{
  const bootWithinDeadline=async promise=>{
    let timer;try{return await Promise.race([promise,new Promise((_,reject)=>{timer=setTimeout(()=>reject(expired()),Math.max(1,deadline-Date.now()));})]);}finally{clearTimeout(timer);}
  };
  live();await bootWithinDeadline(prepareProofs());live();
  const source='/workspace/'+name;
  if(compiled.proofGap)return {results:[],errors:[{source,stage:'admission',reason:compiled.proofGap}]};
  const primary=compiled.primaryAst??compiled.fixture.ast;
  const allAsts=compiled.fixture.sourceUnits?.map(u=>u.ast)??[primary];
  const allContracts=allAsts.flatMap(a=>a.nodes).filter(n=>n.nodeType==='ContractDefinition');
  const contracts=primary.nodes.filter(n=>n.nodeType==='ContractDefinition'&&(!options.contract||n.name===options.contract));
  const results=[],errors=[],kernelChecks=[],directChecks=[],locate=sourceLocations(primary,Buffer.from(text));
  for(const contract of contracts){
    if(!/^[A-Za-z_$][A-Za-z0-9_$]*$/.test(contract.name))throw new Error('Unsupported contract name');
    live();
    const direct=await checkDirect(contract,options,Math.max(1,deadline-Date.now()));
    live();
    if(direct){
      directChecks.push({contract:contract.name,...direct.timings});
      for(const row of direct.results){
        const range=locate(contract.name,row);
        results.push({...row,source,contract:contract.name,sourceHash:compiled.sourceHash??compiled.fixture.header.sourceSha256,...(range?{range}:{}),...(row.counterexample?{counterexample:sourceWitness(primary,contract.name,row)}:{})});
      }
      continue;
    }
    await bootWithinDeadline(prepareLegacyProofs());live();
    const output='/output/result-'+(++sequence)+'-'+contract.id+'.json',namespace=`SolTests.«${contract.name}»`;
    const command=`#solkey_test ${namespace}${options.function?` only ${JSON.stringify(options.function)}`:''}${options.listing?' listing':''}${options.auditPreconditions&&!options.listing?' audit_preconditions':''}${options.counterexamples&&!options.listing?' counterexamples':''} to ${JSON.stringify(output)}`;
    const timed=(phase,command)=>options.benchmark?`#solkey_benchmark ${JSON.stringify(phase)} in ${command}`:command;
    const wrapper=`import Solidity.Frontend.Testing\nset_option sol.testing.direct ${options.certify!==true}\n${options.benchmark?'set_option sol.benchmark true\n':''}${timed('import',`solc_import "source.ast.json" hash ${compiled.hash} as ${namespace} testing`)}\n${timed('obligations',`solc_scoped_problems ${namespace} decl`)}\n${timed('test',command)}\n`;
    const checked=await legacy.request('check',{source:wrapper,files:{'/workspace/source.ast.json':compiled.text},outputs:[output]},Math.max(1,deadline-Date.now()));
    live();
    if(checked.timings)kernelChecks.push({contract:contract.name,...checked.timings});
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
  report.timings={kernelChecks,directChecks};
  if((!options.counterexamples||options.listing)&&results.some(row=>row.status==='refuted'&&row.verification!=='direct'))throw new Error('Kernel returned unrequested model prestate evidence');
  if(options.auditPreconditions&&!options.listing&&results.some(row=>row.preconditions===undefined))throw new Error('Kernel did not return the requested precondition audit');
  return report;
  }finally{jobs.delete(job);}
}
