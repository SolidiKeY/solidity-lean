#!/usr/bin/env node
/** Serial differential runner. Reports are external test evidence, never proofs. */
import {realpathSync} from 'node:fs';
import {resolve, dirname, join} from 'node:path';
import {fileURLToPath} from 'node:url';
import {loadCompiler} from './reference.mjs';
import {campaign, runCase, minimize} from './campaign.mjs';
import {transport} from './transport.mjs';
import {openRun} from './output.mjs';
const here = dirname(fileURLToPath(import.meta.url));
export function argumentsFor(args) {
  const result = {count:2000,seed:1128,fuel:10000,outputLimit:4096,timeout:60000,inputs:[]};
  const names = {'--compiler':'compiler','--driver':'driver','--output':'output','--count':'count',
    '--seed':'seed','--fuel':'fuel','--output-limit':'outputLimit','--timeout':'timeout','--input':'inputs'};
  const seen = new Set();
  for(let i=0;i<args.length;i+=2) {
    const name=names[args[i]], value=args[i+1];
    if(!name || value===undefined || !value.length || (seen.has(name)&&name!=='inputs')) throw Error('invalid or repeated option: '+args[i]);
    seen.add(name);
    if(name==='inputs') result.inputs.push(resolve(value));
    else if(['count','seed','fuel','outputLimit','timeout'].includes(name)) {
      if(!/^(0|[1-9][0-9]*)$/.test(value) || !Number.isSafeInteger(Number(value))) throw Error('invalid number: '+args[i]);
      result[name]=Number(value);
    } else result[name]=resolve(value);
  }
  if(!result.compiler||!result.driver||!result.output) throw Error('required: --compiler FILE --driver EXECUTABLE --output NEW_EXTERNAL_DIRECTORY');
  if(result.count<1||result.count>10000||result.seed>=2**32||result.fuel<1||result.outputLimit<1||result.timeout<1) throw Error('invalid run limits');
  return result;
}

/** Dependencies are injectable solely for orchestration tests. The CLI always
 * uses the real pinned compiler, EVM reference and explicit driver executable. */
export async function run(config, deps = {}) {
  // Pin execution to the same resolved files that are fingerprinted.
  config = {...config,compiler:realpathSync(config.compiler),driver:realpathSync(config.driver)};
  const compile = await (deps.loadCompiler ?? loadCompiler)(config.compiler);
  const lean = (deps.transport ?? transport)({executable:config.driver,fuel:config.fuel,
    outputLimit:config.outputLimit,timeout:config.timeout});
  const inputPaths = [...new Set([config.compiler,config.driver,process.execPath,
    ...['run.mjs','campaign.mjs','generate.mjs','reference.mjs','transport.mjs','output.mjs'].map(f=>join(here,f)),
    join(here,'../evm-reference/generated.mjs'),join(here,'../evm-reference/replay.mjs'),
    join(here,'../evm-reference/package-lock.json'),...(config.inputs ?? [])])];
  const writer = (deps.openRun ?? openRun)(config.output,{requested:config.count,inputPaths,
    metadata:{count:config.count,seed:config.seed,compiler:config.compiler,driver:config.driver,
      fuel:config.fuel,outputLimit:config.outputLimit,timeout:config.timeout,optimizer:true,
      stages:['ir','irOptimized'],nodeVersion:process.version}});
  const execute = record => (deps.runCase ?? runCase)(record,{compile,lean});
  const mismatches=[];
  try {
    const result = await campaign({count:config.count,seed:config.seed,execute,sink:async entry=>{
      writer.append(entry);
      for(const stage of entry.row.results.filter(r=>r.status==='mismatch').map(r=>r.stage))
        mismatches.push({record:entry.record,row:entry.row,stage});
    }});
    // Each stage is shrunk separately. No refusal counts as preservation, and
    // budget-limited results are explicitly incomplete, not certified minima.
    if(mismatches.length) {
      for(const item of mismatches) {
        const finding=await minimize(item.record,item.row,execute,{stage:item.stage});
        const payload={schema:1,originalSourceSha256:item.row.sourceSha256,...finding,
          triage:'untriaged: external mismatch; investigate compiler/import/evaluator/reference boundaries'};
        writer.writeFinding(payload);
      }
    }
    const report=writer.finish();
    return {report,exitCode:result.summary.executedPrograms!==config.count?2:mismatches.length?1:0};
  } finally { writer.abort(); }
}

if(process.argv[1] && resolve(process.argv[1])===fileURLToPath(import.meta.url)) {
  try {
    const {report,exitCode}=await run(argumentsFor(process.argv.slice(2)));
    console.log(JSON.stringify(report.summary)); process.exitCode=exitCode;
  } catch(error) { console.error(String(error.stack??error)); process.exitCode=2; }
}
