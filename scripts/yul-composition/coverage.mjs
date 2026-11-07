#!/usr/bin/env node
/** AST evidence inventory, never semantic/proof coverage. */
import {readFileSync,writeFileSync} from 'node:fs';
import {join,resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {ROOT,sha,validateProvenance} from './harness.mjs';
export const BUILTIN_FEATURES={
 mload:'memoryLayout',mstore:'memoryLayout',mstore8:'memoryLayout',mcopy:'memoryLayout',
 sload:'storageLayout',sstore:'storageLayout',tload:'transientLayout',tstore:'transientLayout',
 calldataload:'rawCalldata',calldatasize:'rawCalldata',calldatacopy:'rawCalldata',
 returndatasize:'rawReturndata',returndatacopy:'rawReturndata',keccak256:'keccakBuiltin',
 call:'lowLevelCall',staticcall:'lowLevelStaticcall',delegatecall:'delegatecall',
 create2:'create2Salt',selfdestruct:'selfdestruct',extcodesize:'addressCode',extcodecopy:'addressCode',extcodehash:'addressCodehash',
 log0:'eventLog',log1:'eventLog',log2:'eventLog',log3:'eventLog',log4:'eventLog',
 coinbase:'blockCoinbase',difficulty:'blockDifficulty',prevrandao:'blockPrevrandao',number:'blockNumber',
 timestamp:'blockTimestamp',gaslimit:'blockGaslimit',chainid:'blockChainid',basefee:'blockBasefee',blobbasefee:'blockBlobbasefee',slotnum:'blockSlotnum',
 origin:'txOrigin',gasprice:'txGasprice',blockhash:'blockhashBuiltin',blobhash:'blobhashBuiltin',
 address:'thisAddress',balance:'addressBalance',selfbalance:'addressBalance',
 gas:'gasleft',msize:'machineResources',pc:'machineResources',codesize:'machineResources',codecopy:'machineResources'
};
const CONSTRUCTION=new Set(['ForStatement','WhileStatement','DoWhileStatement','ModifierDefinition','TryStatement','TryCatchClause','UncheckedBlock']);
export function scan(ast) {
 const features=new Set(),contexts=new Set(),calls={};let blocks=0;
 function walk(n,path=[]) {
  if(!n || typeof n!=='object')return;
  const context=CONSTRUCTION.has(n.nodeType)?n.nodeType:
   n.nodeType==='FunctionDefinition' && n.kind==='constructor'?'constructor':
   n.nodeType==='ContractDefinition' && n.contractKind==='library'?'library':null;
  const next=context?[...path,context]:path;
  if(n.nodeType==='InlineAssembly') {blocks++;features.add('inlineAssembly');for(const c of next)contexts.add(c);}
  if(n.nodeType==='YulFunctionCall') {const name=n.functionName?.name;calls[name]=(calls[name]??0)+1;if(BUILTIN_FEATURES[name])features.add(BUILTIN_FEATURES[name]);}
  for(const v of Object.values(n)) {if(Array.isArray(v)) {for(const a of v)walk(a,next);} else if(v && typeof v==='object')walk(v,next);}
 }
 walk(ast);return {blocks,features:[...features].sort(),contexts:[...contexts].sort(),calls};
}
export function coverage(directory) {
 const bytes=readFileSync(join(directory,'report.json')),report=JSON.parse(bytes);
 const manifest=JSON.parse(readFileSync(join(ROOT,'docs/solidity-features.json')));
 const features=Object.fromEntries(manifest.features.map(f=>[f.id,f]));
 const totals={},rows=[];
 for(const r of report.results) {
  if(!r.provenance) {rows.push({id:r.id,status:'blocked',reason:'no compiler provenance'});continue;}
  const stem=join(directory,r.kind+'-'+r.id+'-'+r.pipeline+(r.optimized?'-optimized':''));
  const input=JSON.parse(readFileSync(stem+'.input.json')),raw=readFileSync(stem+'.output.json','utf8');
  validateProvenance(r.provenance,input,raw);
  const output=JSON.parse(raw),summary=scan(output.sources??{});
  rows.push({id:r.id,kind:r.kind,pipeline:r.pipeline,optimized:r.optimized,...summary,semanticCoverage:'pending'});
  for(const id of summary.features) {
   if(!features[id])throw Error('unknown manifest feature '+id);
   const f=features[id],entry=totals[id]??={feature:id,actualScope:f.scope,actualCurrent:f.current,localEvidence:f.localEvidence,compilerProbeVariants:0,fixtures:[],semanticCoverage:'pending',assemblyObligationsClosed:0};
   entry.compilerProbeVariants++;const fixture=r.kind+'/'+r.id;if(!entry.fixtures.includes(fixture))entry.fixtures.push(fixture);
  }
 }
 return {scope:'Compiler AST presence only, including refused/out-of-profile probes. No admission or correctness evidence.',
  reportSha256:sha(bytes),manifestSha256:sha(readFileSync(join(ROOT,'docs/solidity-features.json'))),
  collectorSha256:sha(readFileSync(fileURLToPath(import.meta.url))),features:Object.values(totals).sort((a,b)=>a.feature.localeCompare(b.feature)),rows};
}
if(process.argv[1] && resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
 if(process.argv.length!==4)throw Error('usage: coverage.mjs REPORT_DIRECTORY OUTPUT.json');
 const result=coverage(resolve(process.argv[2]));writeFileSync(process.argv[3],JSON.stringify(result,null,2)+'\n');
 console.log(JSON.stringify({features:result.features.length,compilerRows:result.rows.length,assemblyObligationsClosed:0}));
}
