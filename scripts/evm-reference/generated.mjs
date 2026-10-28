#!/usr/bin/env node
/** Generated typed-interpreter vs pinned solc/real EVM evidence. No core compiler. */
import {readFileSync, writeFileSync, mkdirSync} from 'node:fs';
import {resolve, dirname} from 'node:path';
import {fileURLToPath} from 'node:url';
import {createHash} from 'node:crypto';
import {createRequire} from 'node:module';
import {execFileSync} from 'node:child_process';
import {hexToBytes, bytesToHex} from '@ethereumjs/util';
import {machine, observation, creationObservation} from './replay.mjs';
import {COMPILER_SHA} from '../solidity-upstream.mjs';

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '../..');
const sha = data => createHash('sha256').update(data).digest('hex');
const VERSION = '0.8.38+commit.1835d247.Emscripten.clang';
export const variants = [false,true].flatMap(viaIR => [false,true].map(optimizer => ({viaIR,optimizer})));

export function compiler(path) {
  if (sha(readFileSync(path)) !== COMPILER_SHA) throw Error('wrong pinned compiler hash');
  const solc = createRequire(import.meta.url)(resolve(path));
  if (solc.cwrap('solidity_version','string',[])() !== VERSION) throw Error('wrong pinned compiler version');
  const compile = solc.cwrap('solidity_compile','string',['string','number','number']);
  return input => JSON.parse(compile(JSON.stringify(input),0,0));
}

export function expectedWords(record) {
  const s = record.expected.storage;
  if (!Array.isArray(s) || s.length !== 2 || !/^x = [0-9]+$/.test(s[0]) || !/^y = [0-9]+$/.test(s[1]))
    throw Error('unhandled typed storage shape');
  return s.map(x => BigInt(x.split(' = ')[1]).toString());
}
const encodedWords = words => '0x' + words.map(n=>BigInt(n).toString(16).padStart(64,'0')).join('');

/** Every adapted field participates: exact return/revert bytes, decoded roots,
raw layout words, logs admission, and post-failure rollback. Gas is retained as
an observation, not compared to the gas-free model. */
export function compare(record, actual) {
  const words = expectedWords(record);
  const e = record.expected;
  if (typeof e.failed !== 'boolean' || !/^0x(?:[0-9a-f]{2})*$/.test(e.revertData)) throw Error('invalid typed outcome');
  const returnData = e.failed ? e.revertData : encodedWords(words);
  return actual.run.failed === e.failed && actual.run.returnData === returnData &&
    (!e.failed || actual.run.exception === 'revert') &&
    actual.storage.returnData === encodedWords(words) && !actual.storage.failed &&
    JSON.stringify(actual.rawStorage) === JSON.stringify(words);
}

export async function execute(record, variant, compile) {
  const input = {language:'Solidity',sources:{'generated.sol':{content:record.source}},settings:{
    viaIR:variant.viaIR,optimizer:{enabled:variant.optimizer,runs:200},evmVersion:'osaka',
    metadata:{appendCBOR:false},outputSelection:{'*':{'*':['abi','storageLayout','evm.bytecode.object',
      'evm.deployedBytecode.object','evm.methodIdentifiers']}}}};
  const result = {index:record.index,seed:record.seed,variant,sourceSha256:sha(record.source),
    inputSha256:sha(JSON.stringify(input))};
  try {
    const output = compile(input);
    result.diagnostics = output.errors ?? [];
    if (result.diagnostics.some(e=>e.severity === 'error')) throw Error('solc rejected generated source');
    const artifact = output.contracts?.['generated.sol']?.Generated;
    if (!artifact) throw Error('missing Generated artifact');
    const layout = artifact.storageLayout;
    if (layout.storage.length !== 2 || layout.storage.some((v,i)=>v.label !== ['x','y'][i] ||
        v.slot !== String(i) || v.offset !== 0 || layout.types[v.type]?.label !== 'uint256'))
      throw Error('unhandled storage layout');
    result.layout = layout;
    const code = artifact.evm;
    result.creationSha256 = sha(Buffer.from(code.bytecode.object,'hex'));
    result.runtimeSha256 = sha(Buffer.from(code.deployedBytecode.object,'hex'));
    result.creationCode = code.bytecode.object;
    result.runtimeCode = code.deployedBytecode.object;
    const vm = await machine();
    const deployed = await vm.call({data:hexToBytes('0x'+code.bytecode.object)});
    result.deployment = creationObservation(deployed.result.execResult,'constructor',deployed.metrics);
    const address = deployed.result.createdAddress;
    if (result.deployment.failed || !address) throw Error('deployment failed');
    if (result.deployment.runtimeCodeSha256 !== result.runtimeSha256) throw Error('deployed runtime hash differs');
    async function call(signature) {
      const selector = code.methodIdentifiers[signature];
      if (!/^[0-9a-f]{8}$/.test(selector)) throw Error('missing canonical selector');
      const {result:r,metrics} = await vm.call({to:address,data:hexToBytes('0x'+selector)});
      return observation(r.execResult,signature,metrics);
    }
    result.setup = await call('setUp()');
    if (result.setup.failed || result.setup.returnData !== '0x') throw Error('setup failed');
    result.before = await call('observe()');
    if (result.before.failed || result.before.returnData !== encodedWords([record.a,record.b]))
      throw Error('setup observation differs');
    result.run = await call('run()');
    result.storage = await call('observe()');
    result.rawStorage = [];
    for (const entry of layout.storage) {
      const slot = hexToBytes('0x'+BigInt(entry.slot).toString(16).padStart(64,'0'));
      const bytes = await vm.evm.stateManager.getStorage(address,slot);
      result.rawStorage.push(bytes.length ? BigInt(bytesToHex(bytes)).toString() : '0');
    }
    result.status = compare(record,result) ? 'agree' : 'mismatch';
    result.expected = record.expected;
  } catch(e) { result.status = 'blocked'; result.reason = e.message; }
  return result;
}

/** Shrink within the same generated grammar and failure pipeline. Every
candidate is regenerated by Lean; no JavaScript arithmetic oracle is used. */
export async function shrink(record, variant, records, compile) {
  const size = r => BigInt(r.a).toString(2).length + BigInt(r.b).toString(2).length;
  const candidates = records.filter(r=>r.kind===record.kind && BigInt(r.a)<=BigInt(record.a) &&
    BigInt(r.b)<=BigInt(record.b)).sort((a,b)=>size(a)-size(b) || a.index-b.index);
  const attempts = [];
  for (const candidate of candidates) {
    const actual = await execute(candidate,variant,compile);
    attempts.push({index:candidate.index,status:actual.status});
    if (actual.status === 'mismatch') return {scope:'same kind and pipeline; any mismatch cause; boundary-pool operands only',attempts,record:candidate,actual};
  }
  return {scope:'same kind and pipeline; any mismatch cause; boundary-pool operands only',attempts,record};
}

export async function main(args) {
  const options = {};
  for (let i=0;i<args.length;i+=2) {
    if (!['--compiler','--seed','--out','--index'].includes(args[i]) || args[i+1]===undefined) throw Error('unknown/missing option');
    options[args[i].slice(2)] = args[i+1];
  }
  if (!options.compiler || !options.out) throw Error('required: --compiler PINNED_SOLJSON --out REPORT [--seed N] [--index N]');
  const seed = options.seed ?? '0';
  if (!/^[0-9]{1,9}$/.test(seed)) throw Error('invalid seed');
  const compile = compiler(options.compiler);
  const binary = resolve(ROOT,'.lake/build/bin/solcases');
  const raw = execFileSync(binary,[seed],{cwd:ROOT,encoding:'utf8',timeout:60000,maxBuffer:16*1024*1024});
  const records = raw.trim().split('\n').map(s=>JSON.parse(s));
  if (records.length !== 160 || records.some((r,i)=>r.schema!==1 || r.index!==i || r.seed!==Number(seed))) throw Error('invalid generated enumeration');
  let selected = records;
  if (options.index !== undefined) {
    if (!/^[0-9]+$/.test(options.index) || !records[Number(options.index)]) throw Error('invalid case index');
    selected = [records[Number(options.index)]];
  }
  const start = performance.now();
  const report = {metadata:{checkoutCommit:execFileSync('git',['rev-parse','HEAD'],{cwd:ROOT,encoding:'utf8'}).trim(),
    leanVersion:execFileSync('lean',['--version'],{encoding:'utf8'}).trim(),
    lakeVersion:execFileSync('lake',['--version'],{encoding:'utf8'}).trim(),
    seed:Number(seed),enumerated:records.length,selected:selected.length,compiler:VERSION,compilerSha256:COMPILER_SHA,
    generatorBinarySha256:sha(readFileSync(binary)),driverSha256:sha(readFileSync(resolve(ROOT,'SolCases.lean'))),
    gitDiffSha256:sha(execFileSync('git',['diff','HEAD'],{cwd:ROOT})),generatorSha256:sha(readFileSync(resolve(ROOT,'Solidity/Tools/SolCases.lean'))),
    runnerSha256:sha(readFileSync(fileURLToPath(import.meta.url))),
    replaySha256:sha(readFileSync(new URL('./replay.mjs',import.meta.url))),
    lockSha256:sha(readFileSync(new URL('./package-lock.json',import.meta.url))),
    engine:'@ethereumjs/evm 10.1.3',scope:'bounded differential evidence; no universal kernel correctness claim'},records:[]};
  for (const record of selected) {
    const row = {record,variants:[]};
    for (const variant of variants) {
      const actual = await execute(record,variant,compile);
      if (actual.status === 'mismatch') actual.shrink = await shrink(record,variant,records,compile);
      row.variants.push(actual);
    }
    report.records.push(row);
  }
  report.elapsedSeconds = (performance.now()-start)/1000;
  report.summary = {agree:0,mismatch:0,blocked:0};
  for (const row of report.records) for (const actual of row.variants) report.summary[actual.status]++;
  mkdirSync(dirname(resolve(options.out)),{recursive:true});
  writeFileSync(options.out,JSON.stringify(report,null,2)+'\n');
  console.log(JSON.stringify(report.summary));
  return report.summary.blocked || report.summary.mismatch ? 1 : 0;
}
if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url))
  main(process.argv.slice(2)).then(code=>{process.exitCode=code;}).catch(e=>{console.error(e);process.exitCode=2;});
