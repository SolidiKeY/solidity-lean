#!/usr/bin/env node
// Roadmap G07: G01's non-circularity gate
// (docs/feature-work/roadmap-g01-interfaces.md, "Non-circularity as a
// checkable gate"; docs/feature-work/roadmap-g07-gates.md, §3), mechanically.
//
// 0. The contracts. `Solidity.Roadmap.Contracts` reaches only
//    `Solidity.Keccak`, and defines no function into `Artifact` (no compiler).
// 1. Import whitelist. A source module (`Solidity/Source/**`) or a module
//    that instantiates `SourceSpec` reaches, transitively, only other source
//    modules, `Solidity.Roadmap.Contracts`, `Solidity.Keccak` and the named
//    datatype modules of `DATATYPES`, each with its correspondence theorem.
//    No non-Solidity import (not even `Lean`) is allowed.
// 2. No meaning through the pipeline. A source module names none of the
//    later layers (`LATER`), qualified or not, outside comments; string
//    literals count. (The constants `Lowering.lower` unfolds to need a
//    Lean-side audit once a real lowering exists: G16.)
// 3. The EVM end. A module that instantiates `EvmSpec` reaches only the EVM
//    whitelist (`EVM_WHITELIST`: the G06 interface, the contracts, the fixed
//    functions, and the pinned EVM modules of `EVM_MODULES`), and reaches the
//    G06 interface `Solidity.Roadmap.Evm` or an `EVM_MODULES` module.
// 4. The artifact table is a variable: rule 1 keeps every `Solidity.Evm.*`
//    module out of the source closure and rule 0 keeps the compiler out of
//    the contracts. That `meaning` reads the table only as
//    `creationCode`/`runtimeCode` bytes is not checked here (S02/S05).
//
// Control modules (`CONTROLS`) build toy instances of both ends; they may
// import `Solidity.Roadmap.Contracts` only.
//
// Scans the Lean files on disk (tracked or not) under `Solidity/`, `Bridge/`
// (module names relative to `Bridge/`), `tests/` and the repository root.
//
// Usage: node scripts/check-noncircular.mjs [--json]
// Exit 0 = every rule holds, 1 = a violation (each printed with a path).
import { readFileSync, readdirSync, statSync, existsSync } from "node:fs";
import { join, resolve, dirname } from "node:path";
import { fileURLToPath } from "node:url";
import { blankLean } from "./check-trust.mjs";

export const WHITELIST = [/^Solidity\.Source(\.|$)/, /^Solidity\.Roadmap\.Contracts$/, /^Solidity\.Keccak$/];
// Named datatype modules a source module may import:
// { module, theorem, theoremModule }: `theorem` (its last component) must be
// declared in `theoremModule`.
export const DATATYPES = [];
// Modules of the pinned EVM an `EvmSpec` instance may import (G06/G46).
export const EVM_MODULES = [];
export const EVM_WHITELIST = [/^Solidity\.Roadmap\.(Evm|Contracts)$/, /^Solidity\.(Keccak|Secp256k1)$/];
export const CONTROLS = ["Solidity.Roadmap.Controls"];
export const LATER = ["IntrinsicSpec", "Lowering", "Compilation", "Execution", "StateExport", "EvmSpec",
  "PublicCorrectness", "SpecTransfer", "Pass", "Cert", "ofWorld", "typedRunPrefixes"];

const qualified = (word) => `(?<![\\w.'])(?:[\\w']+\\.)*${word}(?![\\w'])`;
const SOURCE_INSTANCE = new RegExp(`:\\s*${qualified("SourceSpec")}\\s*(where|:=)|[}⟩]\\s*:\\s*${qualified("SourceSpec")}\\s*\\)|${qualified("SourceSpec")}\\.mk\\b`, "u");
const EVM_INSTANCE = new RegExp(`:\\s*${qualified("EvmSpec")}\\s*(where|:=)|[}⟩]\\s*:\\s*${qualified("EvmSpec")}\\s*\\)|${qualified("EvmSpec")}\\.mk\\b`, "u");

// The imports of a module: every name on every `import` command of the
// header, modifiers (`public`, `meta`, `private`) allowed, comments blanked.
export function parseImports(text) {
  const out = [];
  for (const line of blankLean(text).split("\n")) {
    const l = line.trim();
    if (l === "" || l === "module" || l.startsWith("prelude")) continue;
    const m = l.match(/^(?:(?:public|meta|private)\s+)*import\s+(.*)$/u);
    if (!m) break;
    out.push(...m[1].split(/\s+/).filter((x) => x && x !== "all"));
  }
  return out;
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
  const evmAllowed = (m) => EVM_WHITELIST.some((r) => r.test(m)) || EVM_MODULES.includes(m);
  for (const d of DATATYPES) {
    const t = modules.get(d.theoremModule);
    const short = d.theorem.split(".").at(-1);
    if (!t || !new RegExp(`\\b(theorem|def)\\s+(?:[\\w']+\\.)*${short}\\b`, "u").test(blankLean(t)))
      out.push(`DATATYPE  ${d.module}: correspondence ${d.theorem} not declared in ${d.theoremModule}`);
  }
  const contracts = modules.get("Solidity.Roadmap.Contracts");
  if (contracts !== undefined) {
    const path = reachPath(graph, "Solidity.Roadmap.Contracts", (n) => n !== "Solidity.Keccak");
    if (path) out.push(`CONTRACTS ${path.join(" → ")}`);
    const clean = blankLean(contracts);
    for (const m of clean.matchAll(/^(?:noncomputable\s+)?(?:def|abbrev)\s+([\w'.]+)[^\n]*(?:\n(?!\S)[^\n]*)*/gmu)) {
      const sig = m[0].split(":=")[0];
      if (/(?:→|:)\s*(?:Option\s+)?Artifact\s*$/u.test(sig.trim()))
        out.push(`CONTRACTS Solidity.Roadmap.Contracts defines ${m[1]} into Artifact (a compiler)`);
    }
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
        const hit = clean.match(new RegExp(qualified(word), "u"));
        if (hit) out.push(`LATER     ${m} names ${hit[0]} (line ${clean.slice(0, hit.index).split("\n").length})`);
      }
    }
    if (evm) {
      const path = reachPath(graph, m, (n) => !evmAllowed(n));
      if (path) out.push(`EVM-END   ${path.join(" → ")}`);
      else if (!reachPath(graph, m, (n) => n === "Solidity.Roadmap.Evm" || EVM_MODULES.includes(n)))
        out.push(`EVM-END   ${m} instantiates EvmSpec without the pinned EVM (Solidity.Roadmap.Evm or EVM_MODULES)`);
    }
  }
  return out;
}

export function loadModules(root) {
  const modules = new Map();
  const add = (p, base) => modules.set(p.slice(base.length, -5).replaceAll("/", "."), readFileSync(join(root, p), "utf8"));
  const walk = (dir, base) => {
    if (!existsSync(join(root, dir))) return;
    for (const f of readdirSync(join(root, dir)).sort()) {
      const p = join(dir, f);
      if (p === "Solidity/Scratch" || f.startsWith(".") || f === "node_modules") continue;
      if (statSync(join(root, p)).isDirectory()) walk(p, base);
      else if (p.endsWith(".lean")) add(p, base);
    }
  };
  walk("Solidity", "");
  walk("Bridge", "Bridge/");
  walk("tests", "");
  for (const f of readdirSync(root)) if (f.endsWith(".lean")) add(f, "");
  return modules;
}

if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  const root = resolve(dirname(fileURLToPath(import.meta.url)), "..");
  const modules = loadModules(root);
  if (!modules.has("Solidity.Roadmap.Contracts")) throw new Error("Solidity/Roadmap/Contracts.lean not found");
  const bad = check(modules);
  const sources = [...modules.keys()].filter((m) => /^Solidity\.Source(\.|$)/.test(m)).length;
  if (process.argv.includes("--json")) console.log(JSON.stringify({ modules: modules.size, sources, violations: bad }));
  else {
    for (const b of bad) console.log(b);
    console.log(`noncircular: ${modules.size} modules scanned, ${sources} source modules, ${CONTROLS.length} control modules, ${bad.length} violations`);
  }
  process.exit(bad.length ? 1 : 0);
}
