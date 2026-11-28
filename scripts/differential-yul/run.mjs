#!/usr/bin/env node
/**
# Differential Yul runner

The runner compiles deterministic small Solidity programs with the pinned solc
loader shared by `scripts/differential`, deploys their bytecode in the reference
EVM, and compares both emitted IR forms with the explicit stateful Lean driver.
It compares exact return/revert bytes, revert status and physical storage slots
0 and 1. The generator owns both storage words; constructors initialize neither.

After the stateful Yul prerequisite lands, compile a driver executable whose main
is `Solidity.Yul.StatefulImport.driver`. The runner requires its path explicitly;
there is no substitute interpreter or fabricated expected-value oracle.

```
node scripts/differential-yul/run.mjs --compiler /absolute/soljson.js \
  --driver /absolute/stateful-yul-driver --output /external/new-run
```

The default is 2,000 distinct programs with seed 1128, both IR forms, serial
execution, 10,000 Lean fuel, a 4,096-byte output bound and a 60-second per-driver
timeout. Optional flags: `--count`, `--seed`, `--fuel`, `--output-limit`, `--timeout`.
`--input FILE` may repeat to fingerprint additional driver/library build inputs.
Recorded hashes cover the listed files, not a complete transitive build proof.
Keep the compiler, driver and libraries immutable while running. Temporary IR
and all outputs must stay outside the checkout; the output parent must exist,
and the run directory must be new.

Exit 0 means every requested program completed both comparisons and agreed.
Exit 1 means completed comparisons include mismatches; exit 2 means a refusal,
process failure, incomplete campaign or harness error. Fuel/resource exhaustion
and unsupported syntax are not counted as agreement or as EVM reverts.
`observations.jsonl` preserves submitted programs and results. `report.json`
marks a completed observation campaign, which may still contain blocked cases.
Mismatches produce external `findings/<sha256>.json` with stage-specific operand
minimization; `complete:false` explicitly records incomplete shrinking. Findings
start untriaged and must be investigated before delivery. Never commit these run
outputs. Archive evidence through the coordinator tooling.

```
node --test scripts/differential-yul/*.test.mjs
```

Adapter and orchestration unit tests use injected processes. They do not establish
Lean/EVM agreement. Actual campaigns are external tests, not kernel proofs or a
proof of the `differentialAgreement` tracking goal.
*/
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
