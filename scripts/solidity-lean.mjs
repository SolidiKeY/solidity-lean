#!/usr/bin/env node
/** Public CLI backend. Native entry point: `lake build solidity-lean`. */
import { readFileSync, existsSync } from 'node:fs';
import { dirname, resolve } from 'node:path';
import { fileURLToPath } from 'node:url';
import { runSolidityTests, runTool, testsPassed } from './test-solidity.mjs';

const ROOT = resolve(dirname(fileURLToPath(import.meta.url)), '..');
export const VERSION = readFileSync(resolve(ROOT, 'lakefile.toml'), 'utf8').match(/^version = "([^"]+)"/m)[1];
const HELP = `Usage: solidity-lean <command> [options] FILE_OR_DIR ...

Commands:
  verify       Verify source obligations with Lean's kernel and axiom checks
  list         Discover functions and import gaps without proof search
  inspect      Show an obligation, open goals, or an ordinary proof tree
  run          Execute one concrete call in the typed model
  rules check  Audit annotations against a solkey rules file

Source options:
  --contract NAME       Select a contract
  --function NAME|SIG   Select all overloads by name, or one source signature
  --timeout DURATION    Limit each build/compiler/Lean subprocess (default 5m)
  --self-address A      Pin the verification deployment address (160 bits)
  --solkey DIR          Solkey checkout (also SOLKEY_ROOT)
  --soljson DIR         Directory containing its pinned Solidity compiler
  --no-build            Use already built Lean modules

Inspect options:
  --show WHAT           obligation (default), goals, or tree

Run options:
  --arg VALUE           A boolean or integer argument; repeat in parameter order
  --state FILE          JSON start state (primitive storage roots and transaction)
                       --function must select exactly one function

Rules options:
  --key FILE            Rules file (also SOLKEY_RULES)

Common options:
  --json                Versioned JSON on stdout; diagnostics on stderr
  --help, -h            Show help
  --version             Print version
  --                    End options, allowing paths beginning with '-'

Examples:
  solidity-lean verify contracts/ --json
  solidity-lean list Token.sol
  solidity-lean inspect Token.sol --function 'transfer(address,uint256)' --show goals
  solidity-lean run Counter.sol --function inc --state initial.json
  solidity-lean rules check --key solidityProgramRules.key

Exit: 0 success; 1 unfinished, unsupported, failed verification/execution, or audit;
      2 invalid invocation, discovery, or initial setup/build failure.
Runtime: checkout, pinned Lean/Lake, Node, and the SHA-checked Solidity compiler.
`;

function duration(value) {
  const match = /^(\d+)(ms|s|m)?$/.exec(value);
  const n = match && Number(match[1]) * ({ms:1, s:1000, m:60000}[match[2] ?? 'ms']);
  if (!Number.isSafeInteger(n) || n <= 0 || n > 2147483647)
    throw new Error('--timeout needs a positive duration such as 500ms, 30s, or 5m');
  return n;
}

/** Preserve large words as decimal strings; never round JSON numbers. */
function integer(value, name, signed = true, bits = 256) {
  if (typeof value === 'number' && !Number.isSafeInteger(value))
    throw new Error(`${name}: use a string for integers beyond JavaScript's safe range`);
  if (!['string', 'number'].includes(typeof value) || !/^-?(?:0x[\da-fA-F]+|\d+)$/.test(String(value)))
    throw new Error(`${name}: expected an integer`);
  const s = String(value), n = s.startsWith('-') ? -BigInt(s.slice(1)) : BigInt(s);
  const lower = signed ? -(1n << BigInt(bits - 1)) : 0n;
  if (n < lower || n >= (1n << BigInt(bits))) throw new Error(`${name}: value outside ${bits}-bit range`);
  return n.toString();
}

function argument(value) {
  if (value === 'true' || value === true) return true;
  if (value === 'false' || value === false) return false;
  return integer(value, '--arg');
}

function startState(path) {
  const state = JSON.parse(readFileSync(resolve(path), 'utf8'));
  if (!state || typeof state !== 'object' || Array.isArray(state)) throw new Error('--state needs a JSON object');
  const result = {};
  for (const [key, value] of Object.entries(state)) {
    if (key === 'storage') {
      if (!value || typeof value !== 'object' || Array.isArray(value)) throw new Error('state.storage needs an object');
      result.storage = Object.fromEntries(Object.entries(value).map(([name, v]) =>
        [name, typeof v === 'boolean' ? v : integer(v, `storage.${name}`)]));
    } else if (['sender', 'value', 'timestamp', 'balance', 'selfAddress'].includes(key)) {
      result[key] = integer(value, `state.${key}`, false, key === 'selfAddress' ? 160 : 256);
    } else throw new Error(`unknown state field: ${key}`);
  }
  return result;
}

export function parseArgs(args) {
  const optionArgs = args.slice(0, args.indexOf('--') < 0 ? args.length : args.indexOf('--'));
  if (!args.length || optionArgs.includes('--help') || optionArgs.includes('-h')) return {help:true};
  if (args.length === 1 && args[0] === '--version') return {version:true};
  const [command, ...rest] = args;
  if (!['verify', 'list', 'inspect', 'run', 'rules'].includes(command)) throw new Error(`unknown command: ${command}`);
  if (command === 'rules' && rest.shift() !== 'check') throw new Error('expected: solidity-lean rules check');
  const options = {}, paths = [], seen = new Set();
  const common = ['--timeout', '--json', '--no-build'];
  const source = ['--contract', '--function', '--solkey', '--soljson'];
  const allowed = new Set([...common, ...(command === 'rules' ? ['--key'] : source),
    ...(['verify', 'list', 'inspect'].includes(command) ? ['--self-address'] : []),
    ...(command === 'inspect' ? ['--show'] : []), ...(command === 'run' ? ['--arg', '--state'] : [])]);
  for (let i=0; i<rest.length; i++) {
    const flag = rest[i];
    if (flag === '--') { paths.push(...rest.slice(i+1)); break; }
    if (!flag.startsWith('-')) { paths.push(flag); continue; }
    if (!allowed.has(flag)) throw new Error(`unknown option for ${command}: ${flag}`);
    if (seen.has(flag) && flag !== '--arg') throw new Error(`duplicate option: ${flag}`);
    seen.add(flag);
    if (flag === '--json') { options.json = true; continue; }
    if (flag === '--no-build') { options.build = false; continue; }
    const value = rest[++i];
    if (value === undefined || value.startsWith('--')) throw new Error(`${flag} needs a value`);
    if (flag === '--timeout') options.timeoutMs = duration(value);
    else if (flag === '--self-address') options.selfAddress = integer(value, flag, false, 160);
    else if (flag === '--arg') (options.args ??= []).push(argument(value));
    else if (flag === '--state') options.state = startState(value);
    else options[flag.slice(2)] = value;
  }
  if (command === 'rules') {
    if (paths.length) throw new Error('rules check takes --key FILE, not source paths');
  } else if (!paths.length) throw new Error(`${command} needs at least one Solidity file or directory`);
  if (command === 'run' && !options.function) throw new Error('run needs --function NAME or SIG');
  if (command === 'inspect' && !['obligation', 'goals', 'tree'].includes(options.show ?? 'obligation'))
    throw new Error('--show must be obligation, goals, or tree');
  return {command, options, paths};
}

export function reportExitCode(command, report) {
  if (report.errors.some(e => e.stage === 'discovery' || e.tool?.errorCode === 'ENOENT'
    || /(?:#solkey_test: |error: )no functions selected|run requires exactly one function/.test(e.reason))) return 2;
  if (command === 'verify' || command === 'list') return testsPassed(report, command === 'list') ? 0 : 1;
  const active = command === 'run' ? ['ok'] : command === 'rules' ? ['matched']
    : ['inspected', 'proved', 'pending'];
  // Inspecting open goals succeeds as an inspection, while errors and gaps remain failures.
  return !report.errors.length && report.results.some(r => active.includes(r.status))
    && report.results.every(r => [...active, 'skip', 'skipped', 'internal'].includes(r.status)) ? 0 : 1;
}

function rulesReport(options) {
  const key = resolve(options.key ?? process.env.SOLKEY_RULES ?? resolve(ROOT,
    '../solkey/keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key'));
  if (!existsSync(key)) throw new Error(`rules file not found: ${key}; use --key FILE or SOLKEY_RULES`);
  const args = options.build === false ? ['--no-build', 'exe'] : ['exe'];
  try {
    const text = runTool('lake', [...args, 'solkeycheck', '--key', key], options.timeoutMs ?? 300000);
    return {results:[{source:key, status:'matched', text}], errors:[]};
  } catch (e) {
    if (e.tool?.exitCode === 1 && /mismatch\(es\)/.test(e.message))
      return {results:[{source:key, status:'mismatch', text:e.message}], errors:[]};
    throw e;
  }
}

function envelope(command, report) {
  const summary = {};
  for (const r of report.results) summary[r.status] = (summary[r.status] ?? 0) + 1;
  return {schemaVersion:1, version:VERSION, command, ...report, summary};
}

export function main(args) {
  let parsed;
  try {
    parsed = parseArgs(args);
    if (parsed.help) { console.log(HELP); return 0; }
    if (parsed.version) { console.log(`solidity-lean ${VERSION}`); return 0; }
    const {command, options, paths} = parsed;
    const report = command === 'rules' ? rulesReport(options) : runSolidityTests(paths, {
      ...options, list:command === 'list',
      ...(['inspect', 'run'].includes(command) ? {action:command} : {}),
      onProgress: part => {
        if (process.stderr.isTTY) process.stderr.write(`\r${part.results.length} functions processed\x1b[K`);
      },
    });
    if (process.stderr.isTTY) process.stderr.write('\r\x1b[K');
    const result = envelope(command, report);
    if (options.json) console.log(JSON.stringify(result, null, 2));
    else {
      for (const r of report.results) {
        const label = r.contract ? `${r.contract}.${r.signature || r.function}` : r.source;
        console.log(`${r.status.toUpperCase().padEnd(13)}${label}${r.reason ? `  ${r.reason}` : ''}`);
        if (r.text && r.text !== r.reason) console.log(r.text.trimEnd());
      }
      for (const error of report.errors) console.error(`${error.source ?? 'solidity-lean'}: ${error.reason}`);
      console.log(Object.entries(result.summary).map(([status, n]) => `${n} ${status}`).join(', ') || 'No functions selected.');
    }
    return reportExitCode(command, report);
  } catch (e) {
    const optionArgs = args.slice(0, args.indexOf('--') < 0 ? args.length : args.indexOf('--'));
    if (parsed?.options?.json || optionArgs.includes('--json')) console.log(JSON.stringify(envelope(parsed?.command ?? args[0] ?? null,
      {results:[], errors:[{stage:'setup', reason:e.message, ...(e.tool ? {tool:e.tool} : {})}]}), null, 2));
    else console.error(`solidity-lean: ${e.message}`);
    return 2;
  }
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url))
  process.exitCode = main(process.argv.slice(2));
