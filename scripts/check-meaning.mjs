#!/usr/bin/env node
// H64: source policy plus live #print-axioms dependency checks. Run after builds.
import { execFileSync, spawnSync } from 'node:child_process';
import { readFileSync, writeFileSync, mkdtempSync, rmSync } from 'node:fs';
import { resolve, join } from 'node:path';
import { tmpdir } from 'node:os';
import { fileURLToPath } from 'node:url';
import { blankLean, findings } from './check-trust.mjs';
import { collect } from './check-axiom-pins.mjs';
const STANDARD = ['propext', 'Classical.choice', 'Quot.sound'];

const git = (...args) => execFileSync('git', args, { encoding: 'utf8', maxBuffer: 64 << 20 });
const counts = xs => { const out = new Map(); for (const x of xs) out.set(x, (out.get(x) ?? 0) + 1); return out; };

// Reuse the trust lexer, including nested comments, interpolations and quoted macros.
// Check option names in every context, not just literal set_option commands.
export function sites(src) {
  if (!/\b(?:sorry|sorryAx|admit|native_decide|axiom|ofReduceBool|mkSorry|mkSyntheticSorry|skipKernel\w*|Elab|implemented_by|unsafe)\b|\bdecide\s*\+\s*native\b/u.test(src)) return [];
  const clean = blankLean(src).replace(/[«»]/gu, '');
  const out = findings(src).filter(x => ['forbidden', 'kernel-option', 'recovery', 'override', 'unsafe'].includes(x.kind));
  for (const m of clean.matchAll(/\b(?:[\w]+\.)*skipKernel[\w]*\b|\bElab\s*\.\s*async\b/gu)) {
    if (/Elab\s*\.\s*async/.test(m[0]) && /^\s*(?:\.set\s*·\s*)?false\b/.test(clean.slice(m.index + m[0].length))) continue;
    const start = clean.lastIndexOf('\n', m.index - 1) + 1;
    const end = clean.indexOf('\n', m.index);
    out.push({ kind: 'kernel-bypass', code: clean.slice(start, end < 0 ? undefined : end).trim().replace(/\s+/gu, ' '), line: clean.slice(0, m.index).split('\n').length });
  }
  return out;
}
export function sourceErrors(file, src, old) {
  const errors = [];
  const before = counts(sites(old).map(x => JSON.stringify([x.kind, x.code])));
  for (const x of sites(src)) {
    // Production proof holes are never grandfathered. Existing implementation
    // recovery/options are exact, counted sites in the trusted merge base.
    const proofHole = x.kind === 'forbidden' && /^(sorry|sorryAx|admit)$/.test(x.code);
    const key = JSON.stringify([x.kind, x.code]);
    if (!proofHole && (before.get(key) ?? 0) > 0) before.set(key, before.get(key) - 1);
    else errors.push(`${file}:${x.line}: ${x.kind}: ${x.code}`);
  }
  return errors;
}

// Same Lean API as #print axioms. Enumerate declarations from module provenance,
// not source theorem regexes: includes macro-generated and private theorems too.
export function auditCommand(pins, bridge = false, extraNames = []) {
  const frozen = [...new Set(Object.keys(pins).filter(k => bridge ? /^Bridge\/Solidity(?:Bridge|Velvet)\//.test(k) : /^Solidity\//.test(k)).map(k => k.slice(k.indexOf('.lean:') + 6)).concat(extraNames))];
  const native = Object.entries(pins).filter(([, xs]) => xs.includes('Lean.ofReduceBool')).map(([key]) => key.slice(key.indexOf('.lean:') + 6));
  return `\nopen Lean Elab Command in
run_cmd do
  let env ← getEnv
  let frozen : List Name := []
${Array.from({length: Math.ceil(frozen.length / 100)}, (_, i) => '  let frozen := frozen ++ [' + frozen.slice(i * 100, (i + 1) * 100).map(n => '`' + n).join(', ') + ']').join('\n')}
  let frozenSet := frozen.foldl (fun (s : NameSet) n => s.insert n) {}
  let nativePins : List Name := [${[...new Set(native)].map(n => '`' + n).join(', ')}]
  let allowed : List Name := [${STANDARD.map(n => '`' + n).join(', ')}]
  let check (n : Name) : CommandElabM Unit := do
    let _ ← getConstInfo n
    let axioms ← collectAxioms n
    let extra := axioms.filter fun a => !(allowed.contains a || (a == \`Lean.ofReduceBool && nativePins.contains n))
    unless extra.isEmpty do throwError "meaning: {n} depends on unexpected axioms {extra}"
  for n in frozen do check n
  let mut total : Nat := frozen.length
  for (n, ci) in env.constants.toList do
    let inScope : Bool := match env.getModuleIdxFor? n with
      | none => true
      | some idx => [\`Solidity, \`SolidityBridge, \`SolidityVelvet].any (·.isPrefixOf env.header.moduleNames[idx.toNat]!)
    unless inScope do continue
    if ci matches .axiomInfo _ then
      throwError "meaning: project declares new axiom {n}"
    unless (ci matches .thmInfo _) || frozenSet.contains n do continue
    total := total + 1
    check n
  if total == 0 then throwError "meaning: no project theorems audited"
  logInfo m!"meaning: {total} live theorem axiom sets checked"
`;
}

export function main(args = process.argv.slice(2)) {
  if (args.some(x => x !== '--source-only' && !x.startsWith('--base='))) throw new Error('usage: check-meaning.mjs [--base=REF] [--source-only]');
  const start = performance.now();
  const base = args.find(x => x.startsWith('--base='))?.slice(7) ?? process.env.GATE_BASE ?? 'origin/master';
  const sourceOnly = args.includes('--source-only');
  const root = git('rev-parse', '--show-toplevel').trim(); process.chdir(root);
  const merge = git('merge-base', base, 'HEAD').trim();
  const files = git('ls-files', '-z', '--cached', '--others', '--exclude-standard').split('\0').filter(p => p.endsWith('.lean'));
  const errors = [];
  const changed = new Set(git('diff', '--name-only', merge, '--').split('\n'));
  const tracked = new Set(git('ls-tree', '-r', '--name-only', merge).split('\n'));
  for (const file of [...new Set(files)]) {
    // Vendored upstream files have their own admission policy; changed files
    // still receive H64's delta scan. All our production files scan in full.
    const production = !file.includes('/') || /^(Solidity|Bridge\/SolidityBridge|Bridge\/SolidityVelvet)\//u.test(file);
    const src = readFileSync(file, 'utf8');
    if (!production && !changed.has(file) && tracked.has(file)) continue;
    const r = changed.has(file) && tracked.has(file) ? spawnSync('git', ['show', `${merge}:${file}`], { encoding: 'utf8', maxBuffer: 16 << 20 }) : null;
    if (r && r.status !== 0) throw new Error(`cannot read trusted baseline for ${file}`);
    const old = !tracked.has(file) ? '' : r ? r.stdout : src;
    if (production || src !== old) errors.push(...sourceErrors(file, src, old));
  }
  // Never accept a widened pin/native allowlist supplied by the candidate head.
  const pins = JSON.parse(git('show', `${merge}:scripts/g07-axiom-pins.json`));
  for (const e of errors) console.error(e);
  if (errors.length) return 1;
  console.log(`meaning: source policy passed (${files.length} files, base ${merge})`);
  if (!sourceOnly) {
    const roots = spawnSync('bash', ['scripts/coord-tools/register.sh', '--check'], { stdio: 'inherit' });
    if (roots.status !== 0) return roots.status ?? 1;
    const dir = mkdtempSync(join(tmpdir(), 'h64-meaning-'));
    try {
      const packages = [
        [root, [...new Set(files.filter(p => /^Solidity\//.test(p) && !p.startsWith('Solidity/Scratch/')).map(p => p.slice(0, -5).replaceAll('/', '.')))]],
        [join(root, 'Bridge'), [...new Set(files.filter(p => /^Bridge\/Solidity(?:Bridge|Velvet)\//.test(p)).map(p => p.slice(7, -5).replaceAll('/', '.')))]],
      ];
      const run = (cwd, args) => {
        const result = spawnSync('lake', args, { cwd, stdio: 'inherit', env: { ...process.env, LEAN_NUM_THREADS: '1' } });
        if (result.error) throw result.error;
        return result.status ?? 1;
      };
      const currentPins = collect(root);
      for (const [cwd, imports] of packages) {
        // No compiler runs here: stale/missing artifacts fail closed. Build
        // them through the coordinator's bounded serial build before retrying.
        const fresh = run(cwd, ['--rehash', '--no-build', 'build', ...imports.map(m => '+' + m + ':olean')]);
        if (fresh) return fresh;
        const audit = join(dir, 'Audit.lean');
        writeFileSync(audit, imports.map(m => `import ${m}\n`).join('') + auditCommand(pins, cwd !== root, [...currentPins.values()].filter(p => cwd === root ? /^Solidity\//.test(p.file) : /^Bridge\/Solidity(?:Bridge|Velvet)\//.test(p.file)).map(p => p.name)));
        const result = run(cwd, ['env', 'lean', '--tstack=131072', '-j1', audit]);
        if (result) return result;
      }
      // Frozen test pins are not necessarily reachable from library roots.
      // Re-elaborate their actual source, then inspect the live declarations;
      // #guard_msgs expected text alone is never accepted as axiom evidence.
      const frozenFiles = new Map();
      for (const key of Object.keys(pins)) {
        const i = key.indexOf('.lean:');
        const file = key.slice(0, i + 5), name = key.slice(i + 6);
        if (/^(Solidity|Bridge\/Solidity(?:Bridge|Velvet))\//.test(file)) continue;
        if (!frozenFiles.has(file)) frozenFiles.set(file, new Set());
        frozenFiles.get(file).add(name);
      }
      for (const pin of currentPins.values()) {
        if (/^(Solidity|Bridge\/Solidity(?:Bridge|Velvet))\//.test(pin.file)) continue;
        if (!frozenFiles.has(pin.file)) frozenFiles.set(pin.file, new Set());
        frozenFiles.get(pin.file).add(pin.name);
      }
      for (const [file, names] of frozenFiles) {
        const cwd = file.startsWith('Bridge/') ? join(root, 'Bridge') : root;
        const audit = join(dir, 'Frozen.lean');
        writeFileSync(audit, readFileSync(file, 'utf8') + auditCommand({}, false, [...names]));
        const result = run(cwd, ['env', 'lean', '--tstack=131072', '-j1', audit]);
        if (result) return result;
      }
    } finally { rmSync(dir, { recursive: true, force: true }); }
  }
  console.log(`meaning: ${((performance.now() - start) / 1000).toFixed(3)}s${sourceOnly ? ' (source-only; not a full meaning PASS)' : ''}`);
  return 0;
}
if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try { process.exitCode = main(); } catch (e) { console.error(`meaning: ${e.message}`); process.exitCode = 1; }
}
