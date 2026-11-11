#!/usr/bin/env node
/** Continuous semantic observations using the existing EVM engine, never a proof. */
import {execFileSync} from 'node:child_process';
import {readFileSync, mkdirSync, writeFileSync, appendFileSync, readdirSync, lstatSync, realpathSync, readlinkSync} from 'node:fs';
import {resolve, dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {compiler, execute, variants} from '../evm-reference/generated.mjs';

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const sha = b => createHash('sha256').update(b).digest('hex');
const require = (p, m) => {if (!p) throw Error(m);};
const mode = v => `${v.viaIR ? 'viaIR' : 'legacy'}-${v.optimizer ? 'on' : 'off'}`;

const sourceFiles=['scripts/differential/Driver.lean','scripts/differential/run.mjs',
  'scripts/differential/bounded.mjs','Solidity/Tools/SolCases.lean',
  'scripts/evm-reference/generated.mjs','scripts/evm-reference/replay.mjs',
  'scripts/evm-reference/package.json','scripts/evm-reference/package-lock.json',
  'lean-toolchain','lakefile.toml'];

function identity() {
  const files={};
  function walk(path) {
    const st=lstatSync(path);
    if (st.isSymbolicLink()) {
      const target=realpathSync(path);
      require(target.startsWith(ROOT+'/scripts/evm-reference/node_modules/'),'external dependency link');
      files[path.slice(ROOT.length+1)]={link:readlinkSync(path),sha256:sha(readFileSync(target))};
    } else if (st.isDirectory()) {
      for (const name of readdirSync(path).sort()) walk(resolve(path,name));
    } else files[path.slice(ROOT.length+1)]=sha(readFileSync(path));
  }
  for (const file of sourceFiles) walk(resolve(ROOT,file));
  walk(resolve(ROOT,'scripts/evm-reference/node_modules'));
  const lock=JSON.parse(readFileSync(resolve(ROOT,'scripts/evm-reference/package-lock.json')));
  for (const [name,pkg] of Object.entries(lock.packages)) if (name) {
    const installed=JSON.parse(readFileSync(resolve(ROOT,'scripts/evm-reference',name,'package.json')));
    require(installed.version===pkg.version,'installed package differs from lock: '+name);
  }
  const call=(cmd,args)=>execFileSync(cmd,args,{cwd:ROOT,encoding:'utf8'}).trim();
  return {revision:call('git',['rev-parse','HEAD']),
    trackedDiffSha256:sha(execFileSync('git',['diff','--binary','HEAD'],{cwd:ROOT})),
    status:call('git',['status','--porcelain','--untracked-files=all']),
    lean:call('lean',['--version']),lake:call('lake',['--version']),
    node:{version:process.version,path:realpathSync(process.execPath),sha256:sha(readFileSync(process.execPath))},
    files};
}

export function coverage(records) {
  const boundary=new Set(['0','1','2',(2n**256n-1n).toString()]);
  const families=Object.fromEntries(Array.from({length:10},(_,i)=>[i,{total:0,success:0,failure:0,aBoundary:0,bBoundary:0}]));
  for (const r of records) if (!r.refusal) {
    const f=families[r.kind];f.total++;f[r.expected.failed?'failure':'success']++;
    if (boundary.has(r.a)) f.aBoundary++;
    if (boundary.has(r.b)) f.bBoundary++;
  }
  return families;
}

export function validateRecords(records, count, seed) {
  require(records.length === count && count > 0, 'incomplete/empty generator output');
  for (const [i,r] of records.entries()) {
    require(r.index === i && r.seed === seed, 'generator identity/order mismatch');
    if (typeof r.refusal === 'string' && r.refusal.length) continue;
    require(r.schema === 1 && Number.isInteger(r.kind) && r.kind >= 0 && r.kind < 10,
      'unhandled generator grammar');
    require(typeof r.source === 'string' && r.source.includes('contract Generated'), 'missing source');
    require([r.a,r.b].every(x => typeof x === 'string' && /^(0|[1-9][0-9]*)$/.test(x) && BigInt(x)<2n**256n), 'invalid operands');
    require(typeof r.expected?.failed === 'boolean', 'missing Lean observation');
  }
}

export function summarize(rows, requested) {
  const result = {requested, admitted:0, refused:0, modes:Object.fromEntries(variants.map(v=>
    [mode(v), {agree:0,mismatch:0,blocked:0}]))};
  require(rows.length === requested && requested > 0, 'incomplete/empty report');
  for (const [i,row] of rows.entries()) {
    require(row.record.index === i, 'missing/duplicate case');
    if (row.record.refusal) {require(row.variants.length===0,'executed refusal');result.refused++;continue;}
    result.admitted++;
    require(row.variants.length===4,'incomplete compiler matrix');
    for (const [j,actual] of row.variants.entries()) {
      require(JSON.stringify(actual.variant)===JSON.stringify(variants[j]),'wrong/duplicate compiler mode');
      require(['agree','mismatch','blocked'].includes(actual.status),'unknown verdict');
      result.modes[mode(actual.variant)][actual.status]++;
    }
  }
  return result;
}

function driver(args) {
  const raw = execFileSync('lake',['env','lean','--tstack=131072','-j1','--run',
    'scripts/differential/Driver.lean',...args.map(String)],
    {cwd:ROOT,encoding:'utf8',timeout:300000,maxBuffer:64*1024*1024});
  return raw.trim().split('\n').map(JSON.parse);
}

/** Greedy operand reduction. Every candidate's expected result is recomputed by
 * Prog.run. Preserve family and mode; blocked candidates never count as shrinks.
 * This establishes a local reduction, not global or cause-preserving minimality. */
export async function shrink(record, variant, compile, generate = driver) {
  let best = record;
  const attempts = [];
  for (const field of ['a','b']) {
    const candidates = [...new Set(['0','1','2',(BigInt(best[field])/2n).toString()])];
    for (const value of candidates) {
      if (BigInt(value)>=BigInt(best[field])) continue;
      const args = ['case',best.seed,best.index,field==='a'?value:best.a,
        field==='b'?value:best.b,best.kind];
      const [candidate] = generate(args);
      require(candidate && candidate.kind===best.kind && candidate.index===best.index,
        'shrink driver identity mismatch');
      const actual = await execute(candidate,variant,compile);
      attempts.push({field,value,status:actual.status});
      if (actual.status==='mismatch') best=candidate;
    }
  }
  return {record:best,attempts,scope:'one greedy pass over operands; same family and mode; any mismatch cause'};
}

export async function main(args) {
  const overallStart=performance.now();
  const opts = {};
  require(args.length%2===0,'options require values');
  for (let i=0;i<args.length;i+=2) {
    require(['--compiler','--out','--count','--seed','--budget-seconds'].includes(args[i]) && !(args[i] in opts),'unknown/duplicate option');
    opts[args[i]]=args[i+1];
  }
  require(opts['--compiler'] && opts['--out'],'required: --compiler PATH --out DIRECTORY');
  const count=Number(opts['--count']??20), seed=Number(opts['--seed']??1108), budget=Number(opts['--budget-seconds']??840);
  require(Number.isSafeInteger(count)&&count>0&&count<=10000,'count must be 1..10000');
  require(Number.isSafeInteger(seed)&&seed>=0&&seed<2**32,'seed must be uint32');
  require(Number.isSafeInteger(budget)&&budget>0,'invalid budget');
  const out=resolve(opts['--out']);
  require(out!==ROOT && !out.startsWith(ROOT+'/'),'observations must be outside checkout');
  mkdirSync(out); // Never overwrite previous observations.
  const before=identity();
  before.compilerSha256=sha(readFileSync(resolve(opts['--compiler'])));
  writeFileSync(resolve(out,'inputs-before.json'),JSON.stringify(before)+'\n');
  const compile=compiler(resolve(opts['--compiler']));
  const records=driver(['sample',seed,count]);
  validateRecords(records,count,seed);
  const start=performance.now(), rows=[];
  for (const record of records) {
    const row={record,variants:[]};
    if (!record.refusal) for (const variant of variants) {
      const actual = performance.now()-start >= budget*1000 ?
        {variant,status:'blocked',reason:'overall time budget exhausted'} : await execute(record,variant,compile);
      // Persist observations before potentially failing/long shrinking or another mode.
      delete actual.creationCode; delete actual.runtimeCode;
      appendFileSync(resolve(out,'observations.jsonl'),JSON.stringify({record,actual})+'\n');
      if (actual.status==='mismatch' && performance.now()-start < budget*1000) {
        try { actual.shrink=await shrink(record,variant,compile); }
        catch(e) { actual.shrink={incomplete:true,reason:String(e)}; }
        appendFileSync(resolve(out,'shrinks.jsonl'),JSON.stringify({index:record.index,variant,shrink:actual.shrink})+'\n');
      }
      row.variants.push(actual);
    }
    if (record.refusal) appendFileSync(resolve(out,'observations.jsonl'),JSON.stringify({record,refused:true})+'\n');
    rows.push(row);
    writeFileSync(resolve(out,'progress.json'),JSON.stringify({completed:rows.length,requested:count})+'\n');
  }
  const summary=summarize(rows,count);
  const after=identity();
  after.compilerSha256=sha(readFileSync(resolve(opts['--compiler'])));
  writeFileSync(resolve(out,'inputs-after.json'),JSON.stringify(after)+'\n');
  require(JSON.stringify(before)===JSON.stringify(after),'execution inputs changed during run');
  const report={schema:1,summary,seed,coverage:coverage(records),
    executionLoopSeconds:(performance.now()-start)/1000,
    endToEndSeconds:(performance.now()-overallStart)/1000,softLoopBudgetSeconds:budget,
    inputs:before,
    boundary:'executable observations; not a kernel theorem; no logs in admitted grammar',rows};
  writeFileSync(resolve(out,'report.json'),JSON.stringify(report)+'\n');
  console.log(JSON.stringify(summary));
  return summary.refused || Object.values(summary.modes).some(m=>m.blocked||m.mismatch) ? 1 : 0;
}
if (process.argv[1] && resolve(process.argv[1])===fileURLToPath(import.meta.url))
  main(process.argv.slice(2)).then(c=>{process.exitCode=c;}).catch(e=>{console.error(e);process.exitCode=2;});
