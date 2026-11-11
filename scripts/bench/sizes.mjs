#!/usr/bin/env node
/** U01 static source sizes only: never walk steps, verdicts or proof timings. */
import fs from 'node:fs';
import path from 'node:path';
import {fileURLToPath} from 'node:url';
import {execFileSync} from 'node:child_process';
import {compileFixture} from '../solc-ast.mjs';
import {sourceHash, sourceLocations} from '../source-locations.mjs';
import {sourceIdentityErrors} from './admission.mjs';
import {assertReportOutput} from './report-path.mjs';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '../..');
const statements = new Set(['ExpressionStatement', 'VariableDeclarationStatement', 'IfStatement',
  'ForStatement', 'WhileStatement', 'DoWhileStatement', 'Return', 'Break', 'Continue',
  'EmitStatement', 'RevertStatement', 'Throw', 'TryStatement', 'InlineAssembly', 'PlaceholderStatement']);
export const definition = 'Solidity statement AST nodes in the source function body; Block/UncheckedBlock are containers; modifiers/callees are not expanded; InlineAssembly counts once.';

export function sizeResolver(ast, bytes) {
  const locate = sourceLocations(ast, bytes);
  const functions = new Map((ast.nodes ?? []).flatMap(c => c.nodes ?? [])
    .filter(node => node.nodeType === 'FunctionDefinition').map(node => [node.id, node]));
  return row => {
    const unavailable = reason => ({statements: null, declarationSpanBytes: null, reason});
    if (!locate(row.contract, row)) return unavailable('declaration not located in selected contract/primary source');
    const fn = functions.get(row.sourceId);
    if (!fn) return unavailable('no primary-source function declaration (possibly synthesized constructor)');
    const declarationSpanBytes = Number(fn.src.split(':')[1]);
    if (!fn.body) return {statements: null, declarationSpanBytes, reason: 'function has no body'};
    let count = 0;
    const pending = [fn.body];
    while (pending.length) {
      const value = pending.pop();
      if (!value || typeof value !== 'object') continue;
      if (statements.has(value.nodeType)) count++;
      for (const child of Object.values(value)) if (child && typeof child === 'object') pending.push(child);
    }
    return {statements: count, declarationSpanBytes, reason: null};
  };
}

export function functionSize(ast, bytes, row) { return sizeResolver(ast, bytes)(row); }

function main(args) {
  let admission, output = path.join(root, '.lake/bench/static-sizes.json');
  for (let i = 0; i < args.length; i++) {
    if (args[i] === '--help') { console.log('Usage: node scripts/bench/sizes.mjs --admission REPORT [--out FILE]'); return 0; }
    const flag = args[i], value = args[++i];
    if (!['--admission', '--out'].includes(flag) || !value || value.startsWith('--')) throw new Error('Expected --admission REPORT or --out FILE');
    if (flag === '--admission') admission = path.resolve(value); else output = path.resolve(value);
  }
  if (!admission) throw new Error('--admission REPORT is required');
  let data, report, setupError;
  try { data = fs.readFileSync(admission); report = JSON.parse(data); }
  catch (error) { setupError = error; }
  const sources = Array.isArray(report?.inputs) ? report.inputs.filter(input => typeof input?.path === 'string').map(input => input.path) : [];
  assertReportOutput(output, [admission, ...sources]);
  fs.mkdirSync(path.dirname(output), {recursive: true});
  const result = {kind: 'u01-static-sizes-only', verification: 'not-run', sourceToVerdictBaseline: false,
    attemptFinished: false, sizesPassed: false, definition, admission, admissionSha256: null,
    head: null, runnerSha256: null, results: [], errors: [], compilers: []};
  const save = () => {
    const temporary = output + '.' + process.pid + '.tmp';
    fs.writeFileSync(temporary, JSON.stringify(result, null, 2) + '\n'); fs.renameSync(temporary, output);
  };
  save();
  let temporary;
  try {
    if (setupError) throw setupError;
    result.admissionSha256 = sourceHash(data);
    if (report.kind !== 'u01-admission-only' || report.attemptFinished !== true || !Array.isArray(report.inputs) || !Array.isArray(report.results) || !Array.isArray(report.errors))
      throw new Error('Expected a finished admission-only report');
    result.admissionListingPassed = report.listingPassed;
    result.admissionErrors = report.errors;
    result.results = report.results.map(row => ({...row, staticSize: {statements: null, declarationSpanBytes: null, reason: 'source not compiled'}}));
    result.errors.push(...sourceIdentityErrors(report.inputs, report.results));
    if (result.errors.length) throw new Error('Admission source identity is stale');
    result.head = execFileSync('git', ['rev-parse', 'HEAD'], {cwd: root, encoding: 'utf8'}).trim();
    result.runnerSha256 = sourceHash(fs.readFileSync(fileURLToPath(import.meta.url)));
    const directory = path.join(root, '.lake/bench'); fs.mkdirSync(directory, {recursive: true});
    temporary = fs.mkdtempSync(path.join(directory, 'sizes-'));
    for (const [index, input] of report.inputs.entries()) {
      try {
        const compiled = compileFixture({quiet: true, args: ['--source', input.path,
          '--out', path.join(temporary, index + '.ast.json'), '--no-wrapper',
          '--solkey', report.selection.solkey, '--soljson', report.selection.soljson]});
        if (compiled.sourceHash !== input.sha256) throw new Error('compiler source differs from admission snapshot');
        const bytes = fs.readFileSync(input.path);
        if (sourceHash(bytes) !== input.sha256) throw new Error('source changed during compilation');
        result.compilers.push({source: input.path, ...compiled.compiler});
        const size = sizeResolver(compiled.primaryAst, bytes);
        result.results = result.results.map(row => path.resolve(row.source) === path.resolve(input.path)
          ? {...row, staticSize: size(row)} : row);
        save();
      } catch (error) { result.errors.push({stage: 'static-size', source: input.path, reason: error.message}); }
    }
    result.errors.push(...sourceIdentityErrors(report.inputs, report.results));
    result.sizesPassed = result.errors.length === 0 && result.admissionErrors.length === 0 && result.results.length > 0 &&
      result.results.every(row => row.staticSize.statements !== null);
  } catch (error) { result.errors.push({stage: 'static-size', reason: error.message}); }
  finally { if (temporary) fs.rmSync(temporary, {recursive: true, force: true}); }
  result.attemptFinished = true; save();
  console.log(JSON.stringify({output, rows: result.results.length, sizesPassed: result.sizesPassed,
    sizedBodies: result.results.filter(row => row.staticSize.statements !== null).length, verification: result.verification}));
  return result.sizesPassed ? 0 : 1;
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try { process.exitCode = main(process.argv.slice(2)); }
  catch (error) { console.error(error.message); process.exitCode = 2; }
}
