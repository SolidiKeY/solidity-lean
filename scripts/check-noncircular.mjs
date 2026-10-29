#!/usr/bin/env node
// Roadmap G07: G01's non-circularity gate
// (docs/feature-work/roadmap-g01-interfaces.md, "Non-circularity as a
// checkable gate"; docs/feature-work/roadmap-g07-gates.md), mechanically.
//
// 1. Import whitelist. A source module (`Solidity/Source/**`) or a module
//    that instantiates `SourceSpec` reaches, transitively, only the
//    whitelist: other source modules, `Solidity.Roadmap.Contracts`, its
//    closure `Solidity.Keccak`, and the named datatype modules of
//    `DATATYPES`, each with its correspondence theorem. No non-Solidity
//    import (not even `Lean`) is allowed.
// 2. No meaning through the pipeline. A source module names none of the
//    later layers (`IntrinsicSpec`, `Lowering`, `Compilation`, `Execution`,
//    `StateExport`, `EvmSpec`, `PublicCorrectness`) outside comments;
//    string literals count. (The second half of G01's part 2, the constants `lower`
//    unfolds to, needs a Lean-side audit once a real lowering exists: G16.)
// 3. The EVM end. A module that instantiates `EvmSpec` reaches no compiler,
//    frontend, elaborator or source module.
// 4. The artifact table is a variable: enforced by 1 (no `Solidity.Evm.*`
//    module in the source closure; `Contracts.lean` defines no compiler).
//
// Control modules (`CONTROLS`) build toy instances of both ends; they may
// import `Solidity.Roadmap.Contracts` only.
//
// Usage: node scripts/check-noncircular.mjs [--json]
// Exit 0 = every rule holds, 1 = a violation (each printed with a path).
import { readFileSync, readdirSync, statSync } from "node:fs";
import { join, resolve, dirname } from "node:path";
import { fileURLToPath } from "node:url";
import { blankLean } from "./check-trust.mjs";

export const WHITELIST = [/^Solidity\.Source(\.|$)/, /^Solidity\.Roadmap\.Contracts$/, /^Solidity\.Keccak$/];
// Named datatype modules a source module may import: module -> the
// correspondence theorem (S05) that must be declared in `file`.
export const DATATYPES = [];
export const CONTROLS = ["Solidity.Roadmap.Controls"];
export const LATER = ["IntrinsicSpec", "Lowering", "Compilation", "Execution", "StateExport", "EvmSpec", "PublicCorrectness"];
export const COMPILER = [
  /^Solidity\.Evm\.(Compile|Compiler|Correct|Interpreter|Sim|SimLemmas|Stmt|Expr|Exp)$/,
  /^Solidity\.Evm\.Memory.*(Compile|Source|Code).*$/,
  /^Solidity\.(Frontend|Source)(\.|$)/,
  /^Solidity\.Syntax\.(Elab|Quote|Splice)(\.|$)/,
  /^Solidity\.Roadmap\.TypedRun$/,
];

const SOURCE_INSTANCE = /:\s*SourceSpec\s*(where|:=)|\bSourceSpec\.mk\b/u;
const EVM_INSTANCE = /:\s*EvmSpec\s*(where|:=)|\bEvmSpec\.mk\b/u;

export function parseImports(text) {
  return text.split("\n").filter((l) => /^import\s/.test(l)).map((l) => l.split(/\s+/)[1]);
}

function reachPath(graph, from, bad) {
  const prev = new Map([[from, null]]);
  const queue = [from];
  while (queue.length) {
    const m = queue.shift();
    for (const n of graph.get(m) ?? []) {
      if (prev.has(n)) continue;
      prev.set(n, m);
      if (bad(n)) {
        const path = [n];
        for (let x = m; x !== null; x = prev.get(x)) path.unshift(x);
        return path;
      }
      queue.push(n);
    }
  }
  return null;
}

// `modules`: Map name -> source text. Returns a list of violations.
export function check(modules) {
  const graph = new Map([...modules].map(([m, t]) => [m, parseImports(t)]));
  const out = [];
  const allowed = (m) => WHITELIST.some((r) => r.test(m)) || DATATYPES.some((d) => d.module === m);
  for (const d of DATATYPES) {
    const t = modules.get(d.correspondenceModule);
    if (!t || !new RegExp(`\\b(theorem|def)\\s+${d.theorem.replaceAll(".", "\\.")}\\b`).test(blankLean(t)))
      out.push(`DATATYPE  ${d.module}: correspondence ${d.theorem} not declared in ${d.correspondenceModule}`);
  }
  for (const [m, text] of [...modules].sort()) {
    const clean = blankLean(text);
    const control = CONTROLS.includes(m);
    const source = /^Solidity\.Source(\.|$)/.test(m) || (!control && SOURCE_INSTANCE.test(clean));
    const evm = !control && EVM_INSTANCE.test(clean);
    if (control) {
      for (const i of graph.get(m)) if (i !== "Solidity.Roadmap.Contracts")
        out.push(`CONTROL   ${m} imports ${i}; a control imports Solidity.Roadmap.Contracts only`);
    }
    if (source) {
      const path = reachPath(graph, m, (n) => !allowed(n));
      if (path) out.push(`WHITELIST ${path.join(" → ")}`);
      for (const word of LATER) {
        const hit = clean.match(new RegExp(`(?<![\\w.])${word}(?![\\w])`, "u"));
        if (hit) out.push(`LATER     ${m} names ${word} (line ${clean.slice(0, hit.index).split("\n").length})`);
      }
    }
    if (evm) {
      const path = reachPath(graph, m, (n) => COMPILER.some((r) => r.test(n)));
      if (path) out.push(`EVM-END   ${path.join(" → ")}`);
    }
  }
  return out;
}

export function loadModules(root) {
  const modules = new Map();
  (function walk(dir) {
    for (const f of readdirSync(join(root, dir)).sort()) {
      const p = join(dir, f);
      if (p === "Solidity/Scratch") continue;
      if (statSync(join(root, p)).isDirectory()) walk(p);
      else if (p.endsWith(".lean")) modules.set(p.slice(0, -5).replaceAll("/", "."), readFileSync(join(root, p), "utf8"));
    }
  })("Solidity");
  return modules;
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
  const modules = loadModules(root);
  const bad = check(modules);
  const sources = [...modules.keys()].filter((m) => /^Solidity\.Source(\.|$)/.test(m)).length;
  if (process.argv.includes("--json")) console.log(JSON.stringify({ sources, violations: bad }));
  else {
    for (const b of bad) console.log(b);
    console.log(`noncircular: ${sources} source modules, ${CONTROLS.length} control modules, ${bad.length} violations`);
  }
  process.exit(bad.length ? 1 : 0);
}
