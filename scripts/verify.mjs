#!/usr/bin/env node
/** One process entry for CLI callers and editors consuming --json. */
import {resolve} from 'node:path';
import {fileURLToPath} from 'node:url';
import {performance} from 'node:perf_hooks';
import {parseArgs, annotate, reportExitCode} from './solidity-lean.mjs';
import {sourceReport} from './verify-source.mjs';
import {fastReport} from './verify-native.mjs';
import {differential} from './verify-differential.mjs';
export function parseVerify(args) {
  if(!args.length) return {help:true};
  let mode='certified',compare=false; const rest=[]; let seen=false;
  for(let i=0;i<args.length;i++) {
    if(args[i]==='--') {rest.push(...args.slice(i));break;}
    if(args[i]==='--compare') {if(compare) throw new Error('duplicate --compare');compare=true;continue;}
    if(args[i]!=='--mode') {rest.push(args[i]);continue;}
    if(seen) throw new Error('duplicate --mode');
    seen=true; mode=args[++i];
    if(!['fast','certified'].includes(mode)) throw new Error('--mode must be fast or certified');
  }
  return {...parseArgs(['verify',...rest]),mode,compare};
}
export function main(args) {
  let parsed;
  try {
    parsed=parseVerify(args);
    if(parsed.help) {
      console.log('Usage: verify FILE.sol --mode fast|certified [--compare] [--json] [--function NAME|SIG] [--contract NAME]');return 0;
    }
    if(parsed.compare) {
      const result=differential(parsed.paths,parsed.options);
      if(parsed.options.json) console.log(JSON.stringify(result,null,2));
      else {console.log(result.status==='bug'?'BUG: verification modes disagree or the comparison failed.':`Modes agree on ${result.obligations} obligations.`);for(const bug of result.bugs) console.error(bug);}
      return result.status==='bug'?2:Math.max(reportExitCode('verify',result.fast),reportExitCode('verify',result.certified));
    }
    const started=performance.now();
    const raw=parsed.mode==='fast' ? fastReport(parsed.paths,parsed.options)
      : sourceReport(parsed.paths,{...parsed.options,counterexamples:true});
    const report=annotate('verify',raw,parsed.options);
    if(parsed.mode==='certified') report.results=report.results.map(row=>{
      if(row.verification!==undefined && row.verification!=='certified') {
        report.errors.push({source:row.source,reason:'BUG: certified backend returned a non-certified mode marker'});return row;
      }
      return {...row,verification:'certified'};
    });
    const result={schemaVersion:1,mode:parsed.mode,...report,elapsedMs:performance.now()-started};
    if(parsed.options.json) console.log(JSON.stringify(result,null,2));
    else {
      for(const row of result.results) {
        const line=row.range?.start.line;
        console.log(`${row.diagnosticSource??row.source}${line===undefined?'':':'+(line+1)}: ${row.contract}.${row.function}: ${row.status} (${row.verification})${row.reason?': '+row.reason:''}`);
        for(const branch of row.openBranches??[]) console.log(`  branch ${branch.id}: ${branch.sequent}`);
        if(row.counterexample) console.log(JSON.stringify(row.counterexample,null,2));
      }
      for(const error of result.errors) console.error(`${error.source??'verify'}: ${error.reason}`);
    }
    return reportExitCode('verify',report);
  } catch(error) {
    if(parsed?.options?.json || args.includes('--json')) console.log(JSON.stringify({schemaVersion:1,mode:parsed?.mode??null,results:[],errors:[{reason:error.message}]}));
    else console.error('verify: '+error.message);
    return 2;
  }
}
if(process.argv[1] && resolve(process.argv[1])===fileURLToPath(import.meta.url)) process.exitCode=main(process.argv.slice(2));
