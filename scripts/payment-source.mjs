/** Narrow source/world job preparation. Lean validates the complete AST shape;
 * this routing heuristic never establishes source admission or an outcome. */
import {writeFileSync,readFileSync,mkdirSync} from 'node:fs';
import {join} from 'node:path';
import {createHash} from 'node:crypto';
const sha=x=>createHash('sha256').update(x).digest('hex');
export function preparePaymentSource(path,fixture,compile,work,api) {
  const source=[...fixture.sources.values()].join('\n');
  if(!/\bnew\s+/.test(source)||!/[.]\s*(send|transfer)\s*\(/.test(source))return null;
  const blocked=reason=>({path,stage:'lean-runtime',status:'blocked',reason});
  if(fixture.sources.size!==1||Object.keys(fixture.settings).some(k=>!['EVMVersion','compileViaYul','revertStrings'].includes(k))||
    fixture.settings.revertStrings&&!['debug','default'].includes(fixture.settings.revertStrings))return null;
  if(!api.evmCompatible(fixture.settings.EVMVersion))return blocked('payment EVM constraint excludes osaka');
  const required=api.runtimePipelines(fixture.settings),jobs=[];
  for(const pipeline of required){
    const sources=Object.fromEntries([...fixture.sources].map(([n,s])=>[n,{content:api.withPreamble(s)}]));
    const settings={viaIR:pipeline==='viaIR',evmVersion:'osaka',optimizer:{enabled:false,runs:200},libraries:{},remappings:[],
      ...(fixture.settings.revertStrings?{debug:{revertStrings:fixture.settings.revertStrings}}:{}),
      outputSelection:{'*':{'':['ast'],'*':['abi']}}};
    const out=compile({language:'Solidity',sources,settings});
    if((out.errors??[]).some(e=>e.severity==='error'))return blocked('payment source compiler diagnostics');
    const analysisSettings={...settings,outputSelection:{'*':{'':['ast']}}};
    delete analysisSettings.debug;
    const analysis=compile({language:'Solidity',sources,settings:analysisSettings});
    if((analysis.errors??[]).some(e=>e.severity==='error'))return blocked('payment AST analysis diagnostics');
    const ast=analysis.sources[fixture.mainSource].ast;
    const owner=ast.nodes.filter(n=>n.nodeType==='ContractDefinition').at(-1);
    if(!owner)return blocked('payment source deployment owner missing');
    const abi=out.contracts[fixture.mainSource][owner.name].abi;
    const vectors=[],gas=[],ordered=[];
    for(const original of fixture.expectations){
      const line=original.trim();if(!line)continue;
      if(/^gas\s/.test(line)){
        if(!/^gas (ir|irOptimized|legacy|legacyOptimized)( code)?: \d+$/.test(line)||!vectors.length)return blocked('unadapted payment gas observation');
        gas.push({original,afterVector:vectors.length-1});ordered.push({kind:'independent-bytecode-gas',original,afterVector:vectors.length-1});continue;
      }
      const m=/^(constructor\([^)]*\)|\(\)|[A-Za-z_$][\w$]*\([^)]*\))(?:\s*,\s*(\d+)\s*(wei|ether))?\s*(->.*)$/.exec(line);
      if(!m)return blocked('unadapted ordered payment observation: '+line);
      const value=BigInt(m[2]??0)*(m[3]==='ether'?10n**18n:1n);
      if(value>=2n**256n)return blocked('incoming payment outside uint256');
      let v;
      if(m[1]==='()'){
        if(m[4].trim()!=='->')return blocked('unadapted empty-calldata expected bytes');
        v={signature:'()',args:[],expected:[],failure:false};
      }else [v]=api.semanticVectors({...fixture,expectations:[m[1]+' '+m[4]]},abi);
      vectors.push({...v,value:value.toString(),revertBytes:v.revertBytes??[]});
      ordered.push({kind:'typed-source-world',original,vector:vectors.length-1});
    }
    const normalize=v=>Array.isArray(v)?v.map(normalize):v&&typeof v==='object'?Object.fromEntries(Object.entries(v).map(([k,x])=>[k,
      ['referencedDeclaration','scope','superFunction'].includes(k)&&Number.isInteger(x)&&x>=2**31?x-2**32:normalize(x)])):v;
    const input={header:{solcVersion:api.VERSION,sourceSha256:sha(sources[fixture.mainSource].content),solkeyCommit:'',source:path,
      provenanceVersion:1,compilerFile:'soljson-v0.8.38+commit.1835d247.js',compilerSha256:api.COMPILER_SHA,
      validationStage:'analysis',settings:analysisSettings,acceptedPragmas:ast.nodes.filter(n=>n.nodeType==='PragmaDirective').map(n=>n.literals)},ast:normalize(ast)};
    const file=join(work,sha(path+'#payment#'+pipeline).slice(0,24)+'.ast.json');mkdirSync(work,{recursive:true});writeFileSync(file,JSON.stringify(input,null,2)+'\n');
    jobs.push({path,pipeline,requiredPipelines:required,contract:owner.name,fixture:file,paymentSource:true,vectors,
      originalSourceSha256:api.fixtureSha256,originalOrderedObservations:ordered,independentGasObservations:gas});
  }
  return {jobs};
}

/** Whole-fixture verdict: functional Lean evidence never discharges gas. */
export function certifyPaymentEvidence(row,job,report,provenance) {
  if(!job.paymentSource)return row;
  const sourceStatus=row.pendingPaymentGas?row.typedSourceStatus:row.status;
  const base={...row,typedSourceStatus:sourceStatus,paymentReferenceEvidence:report??null};
  if(sourceStatus!=='working')return base;
  if(!report)return {...base,status:'blocked',reason:'typed payment observations passed; independent payment bytecode evidence unavailable'};
  const m=report.metadata,r=report.result;
  if(!m||!r||Object.entries(provenance).some(([k,v])=>m[k]!==v)||r.path!==job.path||r.sourceSha256!==job.originalSourceSha256)
    return {...base,status:'blocked',reason:'payment gas provenance mismatch'};
  if(JSON.stringify(r.expectedObservations)!==JSON.stringify(job.originalOrderedObservations.map(x=>x.original)))
    return {...base,status:'broken',reason:'ordered source/gas expectations disagree with independent replay'};
  for(const pipeline of job.requiredPipelines){
    const source=row.variants?.find(v=>v.pipeline===pipeline);
    const evm=r.variants?.find(v=>v.profile===pipeline);
    if(!source||source.status!=='working'||!evm||evm.status!=='working')
      return {...base,status:r.status==='broken'?'broken':'blocked',reason:'incomplete paired source/bytecode observations'};
    const native=source.observed.map(o=>[o.signature,o.failed,o.values,o.revertBytes]);
    const reference=evm.observed.map(o=>[o.signature,o.failed,o.values,o.failed?Array.from(Buffer.from(o.returnData.slice(2),'hex')):[]]);
    if(JSON.stringify(native)!==JSON.stringify(reference))
      return {...base,status:'broken',reason:'typed source and actual payment bytecode observations disagree'};
  }
  const actual=r.variants?.flatMap(v=>v.gasObserved??[])??[];
  const expected=job.independentGasObservations.map(x=>x.original);
  if(r.status==='broken'||actual.some(x=>!x.matches||x.actual!==x.expected))
    return {...base,status:'broken',reason:'independent frozen payment gas mismatch'};
  if(r.status!=='working'||!job.requiredPipelines.every(p=>r.variants?.some(v=>v.profile===p&&v.status==='working'))||
     actual.length!==expected.length||!expected.every(x=>actual.some(g=>g.original===x&&g.matches)))
    return {...base,status:'blocked',reason:'incomplete independent payment gas observations'};
  return {...base,pendingPaymentGas:false,status:'working',reason:'typed ordered payment source and independent bytecode/gas observations match'};
}
