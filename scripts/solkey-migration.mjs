#!/usr/bin/env node
/** Reproducible SolKey migration snapshots and strict coverage comparisons. */
import { readFileSync, writeFileSync, mkdirSync, existsSync, readdirSync } from 'node:fs';
import { resolve, dirname, join } from 'node:path';
import { spawnSync } from 'node:child_process';
import { createHash } from 'node:crypto';
import { fileURLToPath } from 'node:url';
import { runSolidityTests } from './test-solidity.mjs';
const root = resolve(dirname(fileURLToPath(import.meta.url)), '..');
const sha = data => createHash('sha256').update(data).digest('hex');
function git(repo, args) {
  const p = spawnSync('git', ['-C', repo, ...args], {maxBuffer: 64 * 1024 * 1024});
  if (p.error || p.status !== 0) throw new Error(p.error?.message || p.stderr.toString());
  return p.stdout;
}
export function snapshot(repo, revision, destination) {
  const commit = git(repo, ['rev-parse', '--verify', `${revision}^{commit}`]).toString().trim();
  const files = git(repo, ['ls-tree', '-r', '--name-only', commit]).toString().trim().split('\n').filter(p =>
    (p.startsWith('keyext.solidity.examples/') && /\.(sol|key)$/.test(p)) ||
    (p.startsWith('keyext.solidity.core/src/main/resources/') && p.endsWith('.key')) ||
    (p.startsWith('keyext.solidity.core/src/test/resources/org/key_project/solidity/examples/') && /\.(sol|key)$/.test(p)) ||
    p === 'keyext.solidity.core/build.gradle');
  if (existsSync(join(destination, 'snapshot.json'))) {
    const existing = verifySnapshot(destination);
    if (existing.commit !== commit) throw new Error('snapshot already pins another revision; choose a new destination');
    if (JSON.stringify(existing.files.map(f => f.path)) !== JSON.stringify(files))
      throw new Error('snapshot file scope changed; generate a new destination and review the added inputs');
    return existing;
  }
  if (existsSync(destination) && readdirSync(destination).length) throw new Error('snapshot destination must be empty');
  const entries = [];
  for (const path of files) {
    const bytes = git(repo, ['show', `${commit}:${path}`]);
    const target = join(destination, path);
    mkdirSync(dirname(target), {recursive:true}); writeFileSync(target, bytes);
    entries.push({path, sha256:sha(bytes), bytes:bytes.length});
  }
  const manifest = {version:1, commit, files:entries};
  mkdirSync(destination, {recursive:true});
  writeFileSync(join(destination, 'snapshot.json'), JSON.stringify(manifest, null, 2) + '\n');
  writeFileSync(destination + '.pin.json', JSON.stringify({commit, manifestSha256:sha(readFileSync(join(destination, 'snapshot.json')))}, null, 2) + '\n');
  return manifest;
}
export function verifySnapshot(destination) {
  const bytes = readFileSync(join(destination, 'snapshot.json'));
  const pin = JSON.parse(readFileSync(destination + '.pin.json'));
  if (sha(bytes) !== pin.manifestSha256) throw new Error('snapshot manifest drift');
  const manifest = JSON.parse(bytes);
  if (manifest.version !== 1 || manifest.commit !== pin.commit || !manifest.files.length) throw new Error('invalid snapshot manifest');
  const seen = new Set();
  for (const entry of manifest.files) {
    if (seen.has(entry.path)) throw new Error(`duplicate snapshot path: ${entry.path}`);
    seen.add(entry.path);
    const path = resolve(destination, entry.path);
    if (!path.startsWith(resolve(destination) + '/')) throw new Error(`unsafe snapshot path: ${entry.path}`);
    if (!existsSync(path) || sha(readFileSync(path)) !== entry.sha256) throw new Error(`snapshot drift: ${entry.path}`);
  }
  return manifest;
}
// Preserve string contents (including branch labels) while removing comments.
function keyText(source, compact = false) {
  let out = '', quoted = false;
  for (let i = 0; i < source.length; i++) {
    const c = source[i];
    if (quoted) {
      out += c;
      if (c === '\\' && i + 1 < source.length) out += source[++i];
      else if (c === '"') quoted = false;
    } else if (c === '"') { quoted = true; out += c; }
    else if (source.startsWith('//', i)) {
      while (i < source.length && source[i] !== '\n') i++;
      out += compact ? ' ' : '\n';
    } else if (source.startsWith('/*', i)) {
      const end = source.indexOf('*/', i+2);
      if (end < 0) throw new Error('unterminated comment');
      out += compact ? ' ' : source.slice(i,end+2).replace(/[^\n]/g,' '); i=end+1;
    } else if (compact && /\s/.test(c)) {
      if (!out.endsWith(' ')) out += ' ';
    } else out += c;
  }
  if (quoted) throw new Error('unterminated string');
  return out;
}
/** Parse named rule blocks, excluding comments, preserving nested braces and strings. */
export function ruleInventory(source) {
  const clean = keyText(source);
  const rules = {};
  const headers = /^    ([A-Za-z_][A-Za-z0-9_]*)\s*\{/gm;
  for (const match of clean.matchAll(headers)) {
    let depth = 1, quoted = false, i = match.index + match[0].length;
    const start = i;
    for (; i < clean.length && depth; i++) {
      const c = clean[i];
      if (quoted && c === '\\') { i++; continue; }
      if (c === '"') quoted = !quoted;
      if (!quoted) { if (c === '{') depth++; if (c === '}') depth--; }
    }
    if (depth) throw new Error(`unterminated rule ${match[1]}`);
    const body = keyText(clean.slice(start, i-1), true).trim();
    rules[match[1]] = sha((rules[match[1]] ?? '') + body);
  }
  return rules;
}
export function diffRules(before, after) {
  return {added:Object.keys(after).filter(k => !(k in before)).sort(),
    removed:Object.keys(before).filter(k => !(k in after)).sort(),
    changed:Object.keys(after).filter(k => k in before && before[k] !== after[k]).sort()};
}
export function ruleDelta(repo, before, after) {
  const paths = [...new Set([before,after].flatMap(rev => git(repo, ['ls-tree','-r','--name-only',rev]).toString().split('\n')))]
    .filter(p => p.includes('/proof/rules/') && p.endsWith('.key')).sort();
  const result = {};
  for (const path of paths) {
    const read = rev => {
      const p = spawnSync('git', ['-C',repo,'show',`${rev}:${path}`], {maxBuffer:16*1024*1024});
      if (p.error) throw new Error(p.error.message);
      return p.status === 0 ? ruleInventory(p.stdout.toString()) : {};
    };
    const delta = diffRules(read(before),read(after));
    if (Object.values(delta).some(xs => xs.length)) result[path] = delta;
  }
  return result;
}
export function generateTaclets(destination, output) {
  const pin = verifySnapshot(destination);
  const path = 'keyext.solidity.core/src/main/resources/org/key_project/solidity/proof/rules/solidityProgramRules.key';
  const source = keyText(readFileSync(join(destination,path),'utf8'));
  const headers = [...source.matchAll(/^    (\w+)\s*\{/gm)];
  const rules = headers.map((m,i) => ({name:m[1], heuristic:source.slice(m.index,headers[i+1]?.index ?? source.length).match(/\\heuristics\(([^)]+)\)/)?.[1]}));
  const heuristics = {simplify_prog:'simplifyProg',simplify_expression:'simplifyExpression',concrete_solidity:'concreteSolidity',
    simplify_prog_expensive:'simplifyProgExpensive',loop_expand:'loopExpand',loop_inv:'loopInv'};
  if (!rules.length || rules.some(r => !heuristics[r.heuristic]) || new Set(rules.map(r => r.name)).size !== rules.length)
    throw new Error('unrecognized or duplicate program taclets');
  const lines = [
    `/-!\n# SolKey program taclet inventory\n\nGenerated by \`node scripts/solkey-migration.mjs generate-taclets\` from\nSolKey \`${pin.commit}\` (${rules.length} taclets).\nThe source hashes are in \`tests/migration/solkey/snapshot.json\`.\nSee \`docs/solkey-migration.md\` for regeneration and remaining implementation gaps.\n-/`,
    'namespace Solidity',
    '/-- Upstream strategy annotations; documentary, not a Lean search strategy. -/\ninductive Heuristic where',
    ...Object.values(heuristics).map(h => `  | ${h}`), '  deriving DecidableEq, Repr',
    '/-- One constructor per upstream program taclet. -/\ninductive KeyTaclet where',
    ...rules.map(r => `  | ${r.name}`), '  deriving DecidableEq, Repr',
    'namespace KeyTaclet',
    '/-- The upstream name. -/\ndef name : KeyTaclet -> String',
    ...rules.map(r => `  | ${r.name} => "${r.name}"`),
    '/-- The upstream strategy annotation. -/\ndef heuristic : KeyTaclet -> Heuristic',
    ...rules.map(r => `  | ${r.name} => Heuristic.${heuristics[r.heuristic]}`),
    '/-- Every upstream program taclet in source order. -/\ndef all : List KeyTaclet := [',
    rules.map(r => `  KeyTaclet.${r.name}`).join(',\n'), ']', 'end KeyTaclet',
    '/-- The upstream taclet or family transcribed by a Lean rule. -/\ninductive KeyOrigin where\n  | taclet (t : KeyTaclet)\n  | merged (ts : List KeyTaclet)\n  deriving DecidableEq, Repr',
    'namespace KeyOrigin',
    '/-- The taclets an origin claims. -/\ndef taclets : KeyOrigin -> List KeyTaclet\n  | taclet t => [t]\n  | merged ts => ts',
    'end KeyOrigin', 'end Solidity',
  ];
  writeFileSync(output, lines.join('\n') + '\n');
  return rules.length;
}
/** Missing rows and subprocess errors never count as expected-open results. */
export function compareResults(expected, report) {
  const key = r => JSON.stringify([r.source, r.contract, r.signature ?? r.function]);
  const actual = new Map(), findings = [];
  if (expected.version !== 1 || !expected.commit || !['proof','listing'].includes(expected.mode) || !expected.sources?.length || !expected.results?.length)
    throw new Error('expectations need version, commit, mode, sources and nonempty results');
  if (report.commit !== expected.commit) findings.push({kind:'commit', expected:expected.commit, actual:report.commit});
  if (report.mode !== expected.mode) findings.push({kind:'mode', expected:expected.mode, actual:report.mode});
  const sameSet = (a,b) => Array.isArray(a) && Array.isArray(b) && a.length === new Set(a).size && b.length === new Set(b).size && a.length === b.length && a.every(x => b.includes(x));
  if (!sameSet(expected.sources,report.sources)) findings.push({kind:'sourceCoverage'});
  if (!sameSet(expected.sources,report.completed)) findings.push({kind:'incomplete'});
  for (const gap of expected.importGaps ?? [])
    findings.push({kind:'unaccountedImport',source:gap.source,contract:gap.contract});
  for (const row of report.results) {
    const k = key(row);
    if (actual.has(k)) findings.push({kind:'duplicate', key:k});
    actual.set(k, row);
  }
  const seen = new Set();
  for (const row of expected.results) {
    const k = key(row);
    if (seen.has(k)) throw new Error(`duplicate expectation: ${k}`);
    seen.add(k);
    const got = actual.get(k);
    if (!got) findings.push({kind:'missing', key:k});
    else if (got.status !== row.status) findings.push({kind:'changed', key:k, expected:row.status, actual:got.status});
    else if (got.status === 'pending' && got.reason !== 'open proof goals') findings.push({kind:'runtimeFailure',key:k,reason:got.reason});
    actual.delete(k);
  }
  for (const k of actual.keys()) findings.push({kind:'unexpected', key:k});
  for (const error of report.errors) findings.push({kind:'error', ...error});
  return findings;
}
export function baseline(destination, output, {list = false, soljson, timeoutMs = 120000, onlySource} = {}) {
  const manifest = verifySnapshot(destination);
  const sources = manifest.files.filter(f => f.path.endsWith('.sol') && (!onlySource || f.path === onlySource));
  if (!sources.length) throw new Error('no pinned Solidity sources selected');
  const report = {version:1, commit:manifest.commit, mode:list ? 'listing' : 'proof',
    sources:sources.map(f => f.path), completed:[], results:[], errors:[]};
  const save = () => writeFileSync(output, JSON.stringify(report, null, 2) + '\n');
  save();
  for (const {path} of sources) {
    const previous = {results:report.results,errors:report.errors};
    const retain = part => {
      for (const field of ['results','errors']) report[field] = previous[field].concat(part[field].map(r => ({...r,source:path})));
      save();
    };
    const part = runSolidityTests([join(destination, path)], {
      build:false, list, solkey:destination, soljson, timeoutMs, onProgress:retain,
      // Existing imported-suite correspondence, not a new struct definition.
      renaming:path === 'keyext.solidity.examples/TestSuite.sol' ? {Triple:'FixedTriple'} : {},
    });
    if (path.includes('/illegal/nocompile/') && part.errors.length === 1 &&
        part.errors[0].stage === 'compile' && /solc-ast: (TypeError|ParserError|DeclarationError|SyntaxError):/.test(part.errors[0].reason)) {
      part.results.push({source:path,contract:'<source>',function:'<compile>',status:'compileRejected',
        reason:part.errors[0].reason});
      part.errors = [];
    }
    retain(part);
    report.completed.push(path); save();
    console.error(`${report.completed.length}/${sources.length} ${path}: ${part.results.length} rows, ${part.errors.length} errors`);
  }
  return report;
}
export function expectations(destination, listing) {
  const pin = verifySnapshot(destination);
  const sources = pin.files.filter(f => f.path.endsWith('.sol')).map(f => f.path);
  if (listing.commit !== pin.commit || listing.mode !== 'listing' ||
      JSON.stringify(listing.sources) !== JSON.stringify(sources) ||
      JSON.stringify(listing.completed) !== JSON.stringify(sources)) throw new Error('expectations require a complete listing of the pinned sources');
  return {version:1,commit:pin.commit,mode:'proof',sources,
    results:listing.results.map(r => {
      const open = r.source.includes('/open/') || r.source.includes('/unprovable/');
      const status = r.status === 'compileRejected' ? r.status : r.tag === 'internal' ? 'internal' :
        r.tag === 'skip' ? 'skipped' : r.status === 'excluded' ? 'excluded' : open ? 'pending' : 'proved';
      return {source:r.source,contract:r.contract,function:r.function,...(r.signature ? {signature:r.signature} : {}),status,
        ...(open ? {meaning:'expected proof-open; no claim of falsity'} : {}),
        ...(status === 'excluded' ? {reason:r.reason} : {})};
    }),
    // Failed imports stay required source-level gaps, not expected successes.
    importGaps:listing.errors.map(({source,contract,reason}) => ({source,contract,reason}))};
}
export function summarize(report) {
  const count = rows => rows.reduce((out,r) => {out[r.status]=(out[r.status]??0)+1;return out;},{});
  const suites = {};
  for (const row of report.results) {
    const suite = row.source.split('/')[1] ?? row.source;
    (suites[suite] ??= []).push(row);
  }
  return {commit:report.commit,mode:report.mode,completedSources:report.completed.length,
    totalSources:report.sources.length,results:count(report.results),errors:report.errors.length,
    suites:Object.fromEntries(Object.entries(suites).map(([name,rows])=>[name,count(rows)]))};
}
function main() {
  const [command, ...args] = process.argv.slice(2);
  if (command === 'snapshot') {
    const [repo = '../solkey', revision = 'HEAD', out = 'tests/migration/solkey'] = args;
    const m = snapshot(resolve(repo), revision, resolve(out));
    console.log(`${m.commit}: ${m.files.length} files`);
  } else if (command === 'verify') {
    console.log(`${verifySnapshot(resolve(args[0] ?? 'tests/migration/solkey')).commit}: hashes verified`);
  } else if (command === 'rules') {
    const [repo = '../solkey', before = '1b4341a303', after = 'HEAD'] = args;
    console.log(JSON.stringify(ruleDelta(resolve(repo),before,after),null,2));
  } else if (command === 'compare') {
    const findings = compareResults(JSON.parse(readFileSync(args[0])), JSON.parse(readFileSync(args[1])));
    console.log(JSON.stringify(findings,null,2)); process.exitCode = findings.length ? 1 : 0;
  } else if (command === 'baseline') {
    const [destination = 'tests/migration/solkey', output = '/tmp/solkey-baseline.json', soljson = '../solkey/keyext.solidity.core/build/soljson', mode = 'proof', onlySource] = args;
    if (!['proof','listing'].includes(mode)) throw new Error('mode must be proof or listing');
    baseline(resolve(destination), resolve(output), {soljson:resolve(soljson), list:mode === 'listing',onlySource});
  } else if (command === 'generate-taclets') {
    console.log(`${generateTaclets(resolve(args[0] ?? 'tests/migration/solkey'),resolve(args[1] ?? join(root,'Solidity/Calculus/KeyTaclets.lean')))} taclets generated`);
  } else if (command === 'expectations') {
    const [destination, listing, output] = args;
    writeFileSync(output,JSON.stringify(expectations(resolve(destination),JSON.parse(readFileSync(listing))),null,2)+'\n');
  } else if (command === 'summary') {
    console.log(JSON.stringify(summarize(JSON.parse(readFileSync(args[0]))),null,2));
  } else throw new Error('usage: solkey-migration.mjs snapshot [repo revision out] | verify [snapshot] | rules [repo before after] | generate-taclets [snapshot output] | baseline [snapshot output soljson proof|listing] | expectations snapshot listing output | compare expectations.json results.json');
}
if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try { main(); } catch (e) { console.error(e.message); process.exitCode=2; }
}
