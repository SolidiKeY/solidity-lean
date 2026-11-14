/** Compare both engines against an independent obligation listing. */
import {performance} from 'node:perf_hooks';
import {createHash} from 'node:crypto';
import {sourceReport} from './verify-source.mjs';
import {annotate} from './solidity-lean.mjs';
import {rowAssumptions} from './solidity-lean-assumptions.mjs';
import {fastReport} from './verify-native.mjs';
import {compareModes} from './verify-agreement.mjs';
const sha=value=>createHash('sha256').update(JSON.stringify(value)).digest('hex');
const key=row=>JSON.stringify([row.source,row.contract,row.sourceId,row.signature??row.function]);
export function differential(paths,options={},runners={listing:sourceReport,fast:fastReport,certified:sourceReport}) {
  const listing=runners.listing(paths,{...options,list:true,counterexamples:false});
  const expected=listing.results.map(input=>{const row={...input,reading:input.tag==='specified'?'solc':input.reading};return {...row,sourceSha256:row.sourceHash,assumptions:rowAssumptions(row),
    requestSha256:sha({source:row.source,sourceSha256:row.sourceHash,compilationSha256:row.compilationSha256,contract:row.contract,sourceId:row.sourceId,
      signature:row.signature??row.function,selfAddress:options.selfAddress??null})};});
  const identities=new Map(expected.map(row=>[key(row),row]));
  function bind(report,verification) {
    return {...report,results:report.results.map(row=>{
      const original=identities.get(key(row));
      // A source mismatch remains invalid; never repair a stale result's identity.
      return {...row,verification:row.verification??(verification==='certified'?'certified':undefined),sourceSha256:row.sourceHash,
        requestSha256:original?.sourceSha256===row.sourceHash && original?.compilationSha256===row.compilationSha256?original.requestSha256:undefined,
        assumptions:rowAssumptions(row)};
    })};
  }
  const before=performance.now();
  const fast=bind(runners.fast(paths,options),'native');
  const between=performance.now();
  const certified=bind(runners.certified(paths,{...options,counterexamples:true}),'certified');
  const after=performance.now();
  const comparison=compareModes(fast,certified,expected);
  if(listing.errors.length) {comparison.status='bug';comparison.bugs.push(...listing.errors.map(e=>'listing failed: '+e.reason));}
  return {schemaVersion:1,mode:'differential',...comparison,fast:annotate('verify',fast,options),certified:annotate('verify',certified,options),
    comparisonScope:'engine verdicts before caller assumption policy',
    timingsMs:{fast:between-before,certified:after-between},
    timingScope:'source-to-report wall time, discovery excluded; each mode includes its own compiler and process overhead'};
}
