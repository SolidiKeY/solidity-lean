#!/usr/bin/env node
// H64: source policy, optional bounded artifact preparation, and live axiom checks.
import { execFileSync, spawnSync } from 'node:child_process';
import { readFileSync, writeFileSync, mkdtempSync, rmSync, statSync } from 'node:fs';
import { resolve, join } from 'node:path';
import { tmpdir } from 'node:os';
import { fileURLToPath } from 'node:url';
import { blankLean, blankLeanHeader, findings } from './check-trust.mjs';
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

// One inventory owns both build requests and audit imports. Explicit olean
// facets avoid unrelated executables, native code and optional package roots.
export function productionPackages(root, files) {
  return [
    [root, [...new Set(files.filter(p => p.endsWith('.lean') && /^Solidity\//.test(p) && !p.startsWith('Solidity/Scratch/')).map(p => p.slice(0, -5).replaceAll('/', '.')))].sort()],
    [join(root, 'Bridge'), [...new Set(files.filter(p => p.endsWith('.lean') && /^Bridge\/Solidity(?:Bridge|Velvet)\//.test(p)).map(p => p.slice(7, -5).replaceAll('/', '.')))].sort()],
  ];
}

// Lean.Parser.Module.import takes exactly one module identifier, even when
// whitespace/comments split it from `import`. Never consume arbitrary command
// identifiers after that module (e.g. register_simp_attr close_rw_s).
export function headerImports(src) {
  const ident = /^(?:«[^»]*»|[\p{L}_][\p{L}\p{N}_']*)(?:\.(?:«[^»]*»|[\p{L}_][\p{L}\p{N}_']*))*$/u;
  const tokens = blankLeanHeader(src).match(/(?:«[^»]*»|[\p{L}_][\p{L}\p{N}_']*)(?:\.(?:«[^»]*»|[\p{L}_][\p{L}\p{N}_']*))*|[^\s]/gu) ?? [];
  const out = [];
  let i = 0;
  if (tokens[i] === 'module') i++;
  if (tokens[i] === 'prelude') i++;
  while (i < tokens.length) {
    if (tokens[i] === 'public') i++;
    if (tokens[i] === 'meta') i++;
    if (tokens[i++] !== 'import') break;
    if (tokens[i] === 'all') i++;
    if (!tokens[i] || !ident.test(tokens[i])) throw new Error('invalid import header module');
    out.push(tokens[i++]);
  }
  return out;
}

// This check runs before any Lake invocation. Production names come exclusively
// from real .lean files beneath the configured library roots, never source text.
// Lake still checks external dependency availability and artifact freshness.
export function validateProductionInventory(packages) {
  let total = 0;
  for (const [cwd, names] of packages) {
    const config = readFileSync(join(cwd, 'lakefile.toml'), 'utf8');
    const libraries = [...config.matchAll(/^\[\[lean_lib\]\]\s*\nname\s*=\s*"([^"]+)"/gmu)].map(m => m[1]);
    for (const name of names) {
      if (!libraries.some(lib => name.startsWith(lib + '.'))) throw new Error(`meaning: no library owns target ${name} in ${cwd}`);
      const file = join(cwd, name.replaceAll('.', '/') + '.lean');
      if (!statSync(file, { throwIfNoEntry: false })?.isFile()) throw new Error(`meaning: target ${name} has no module file: ${file}`);
      total++;
    }
  }
  return total;
}

// Resolve prerequisite targets from package manifests and configured source
// directories, without lake query/build. Missing dependency checkouts fail closed.
export function validatePrerequisites(cwd, names) {
  if (!names.length) return;
  const roots = new Set(), visited = new Set();
  const visit = dir => {
    dir = resolve(dir);
    if (visited.has(dir)) return;
    visited.add(dir);
    roots.add(dir);
    const config = join(dir, 'lakefile.toml');
    if (statSync(config, { throwIfNoEntry: false })?.isFile()) {
      for (const m of readFileSync(config, 'utf8').matchAll(/^srcDir\s*=\s*"([^"]+)"/gmu)) roots.add(resolve(dir, m[1]));
    }
    const manifest = join(dir, 'lake-manifest.json');
    if (!statSync(manifest, { throwIfNoEntry: false })?.isFile()) return;
    const data = JSON.parse(readFileSync(manifest, 'utf8'));
    for (const pkg of data.packages ?? []) visit(pkg.type === 'path'
      ? resolve(dir, pkg.dir) : resolve(dir, data.packagesDir ?? '.lake/packages', pkg.name, pkg.subDir ?? ''));
  };
  visit(cwd);
  for (const name of names) {
    const relative = name.replaceAll('.', '/') + '.lean';
    if (![...roots].some(dir => statSync(join(dir, relative), { throwIfNoEntry: false })?.isFile())) {
      throw new Error(`meaning: prerequisite ${name} has no module file in configured packages`);
    }
  }
}

// Include roots as traversal vertices even though only audited modules are
// returned as build targets. Dependency closure is needed by Lake as well.
export function touchedProduction(root, files, changed) {
  const modules = new Map();
  for (const [cwd, names] of productionPackages(root, files)) {
    for (const name of names) modules.set(name, join(cwd, name.replaceAll('.', '/') + '.lean'));
  }
  const production = new Set(modules.keys());
  for (const file of files.filter(p => !p.includes('/') || /^Bridge\/[^/]+\.lean$/u.test(p))) {
    modules.set(file.replace(/^Bridge\//u, '').slice(0, -5), join(root, file));
  }
  const reverse = new Map(), forward = new Map(), selected = new Set();
  for (const [name, file] of modules) {
    if (changed.has(file.slice(root.length + 1))) selected.add(name);
    const imports = headerImports(readFileSync(file, 'utf8'));
    forward.set(name, imports);
    for (const dep of imports) {
      if (!reverse.has(dep)) reverse.set(dep, new Set());
      reverse.get(dep).add(name);
    }
  }
  const pending = [...selected];
  while (pending.length) for (const name of reverse.get(pending.pop()) ?? []) {
    if (!selected.has(name)) { selected.add(name); pending.push(name); }
  }
  // A root reached only as a dependent is traversal-only. Pulling all of
  // that root's imports here would turn every core edit into a full build.
  const dependencies = [...selected].filter(name => production.has(name));
  const visited = new Set();
  while (dependencies.length) {
    const current = dependencies.pop();
    if (visited.has(current)) continue;
    visited.add(current);
    for (const name of forward.get(current) ?? []) if (modules.has(name)) {
      selected.add(name);
      dependencies.push(name);
    }
  }
  return new Set([...selected].filter(name => production.has(name)));
}

export function productionPrerequisites(cwd, imports) {
  const selected = new Set(imports), prerequisites = new Set();
  for (const name of imports) for (const dep of headerImports(readFileSync(join(cwd, name.replaceAll('.', '/') + '.lean'), 'utf8'))) {
    if (!selected.has(dep) && !/^(?:Init|Lean|Std)(?:\.|$)/u.test(dep)) prerequisites.add(dep);
  }
  return [...prerequisites].sort();
}

// weakLeanArgs preserve artifact hashes. Both Lake's scheduler and each Lean
// child are single-threaded. The temporary config lives beside lakefile.toml
// so relative dependency paths retain their meaning.
export function serialConfig(text) {
  return text.split(/(?=^\[\[lean_(?:lib|exe)\]\])/mu).map(part => {
    if (!part.startsWith('[[lean_')) return part;
    if (/^weakLeanArgs\s*=/mu.test(part)) return part.replace(/(weakLeanArgs\s*=\s*\[)([^\]]*)(\])/u,
      (_, a, b, c) => a + b + (b.trim() ? ', ' : '') + '"-j1"' + c);
    return part.replace('\n', '\nweakLeanArgs = ["-j1"]\n');
  }).join('');
}

export function buildProduction(cwd, imports, run) {
  if (!imports.length) return 0;
  validateProductionInventory([[cwd, imports]]);
  const dir = mkdtempSync(join(cwd, '.coord-h64-'));
  const config = dir + '.toml';
  // Keep the config in the package root, including for Bridge path dependencies.
  try {
    writeFileSync(config, serialConfig(readFileSync(join(cwd, 'lakefile.toml'), 'utf8')));
    // Never compile external libraries or a path dependency with its original
    // threading options. They must already be fresh. This also prevents a
    // Bridge build from silently rebuilding core outside its serial config.
    const prerequisites = productionPrerequisites(cwd, imports);
    if (prerequisites.length) {
      validatePrerequisites(cwd, prerequisites);
      const fresh = run(cwd, ['-f', config, '--rehash', '--no-build', 'build', ...prerequisites.map(m => '+' + m + ':olean')]);
      if (fresh) return fresh;
    }
    return run(cwd, ['-f', config, '--rehash', 'build', ...imports.map(m => '+' + m + ':olean')]);
  } finally { rmSync(config, { force: true }); rmSync(dir, { recursive: true, force: true }); }
}

export function main(args = process.argv.slice(2)) {
  if (args.some(x => !['--source-only', '--inventory-only', '--build', '--touched'].includes(x) && !x.startsWith('--base='))) throw new Error('usage: check-meaning.mjs [--base=REF] [--inventory-only | --source-only | --build [--touched]]');
  if (args.includes('--touched') && !args.includes('--build')) throw new Error('--touched requires --build');
  if (args.includes('--source-only') && args.includes('--build')) throw new Error('--source-only cannot build');
  const start = performance.now();
  const base = args.find(x => x.startsWith('--base='))?.slice(7) ?? process.env.GATE_BASE ?? 'origin/master';
  const sourceOnly = args.includes('--source-only');
  if (args.includes('--inventory-only') && (sourceOnly || args.includes('--build'))) throw new Error('--inventory-only cannot scan or build');
  const root = git('rev-parse', '--show-toplevel').trim(); process.chdir(root);
  const merge = git('merge-base', base, 'HEAD').trim();
  const files = git('ls-files', '-z', '--cached', '--others', '--exclude-standard').split('\0').filter(p => p.endsWith('.lean'));
  const packages = productionPackages(root, files);
  const targetCount = validateProductionInventory(packages);
  console.log(`meaning: inventory verified (${targetCount} file-backed production targets; no Lake invocation)`);
  if (args.includes('--inventory-only')) {
    for (const [cwd, imports] of packages) {
      const prerequisites = productionPrerequisites(cwd, imports);
      validatePrerequisites(cwd, prerequisites);
      console.log(`meaning: inventory verified (${prerequisites.length} file-backed foreign prerequisites in ${cwd})`);
    }
    return 0;
  }
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
      const run = (cwd, args) => {
        const result = spawnSync('lake', args, { cwd, stdio: 'inherit', env: { ...process.env, LEAN_NUM_THREADS: '1' } });
        if (result.error) throw result.error;
        return result.status ?? 1;
      };
      if (args.includes('--build')) {
        const touched = args.includes('--touched') ? touchedProduction(root, files,
          new Set([...changed, ...files.filter(p => !tracked.has(p))])) : null;
        for (const [cwd, imports] of packages) {
          const targets = touched ? imports.filter(m => touched.has(m)) : imports;
          console.log(`meaning: prepare ${targets.length} production targets in ${cwd}; Lake rebuilds stale artifacts only`);
          const built = buildProduction(cwd, targets, run);
          if (built) return built;
        }
      }
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
