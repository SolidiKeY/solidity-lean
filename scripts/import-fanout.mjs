#!/usr/bin/env node
// The import graph of `Solidity/**/*.lean` and `Solidity.lean`: per module,
// how many modules depend on it transitively (what an edit to it rebuilds),
// and the longest import chain (the build's critical path in modules).
// `Solidity/Scratch/` is never committed and is skipped.
//
// Usage: node scripts/import-fanout.mjs [--top N] [--json] [MODULE…]
//          per module: fan-out (dependents), fan-in (dependencies), lines;
//          sorted by fan-out, the top N (default 40), or only the MODULEs
//          named (`Syntax.Elab` or `Solidity.Syntax.Elab`)
//        node scripts/import-fanout.mjs --path A B
//          one import path from A down to B, or exit 1 if A does not reach B
//        node scripts/import-fanout.mjs --chain
//          the longest import chain, root first
import { readFileSync, readdirSync, statSync } from "node:fs";
import { join } from "node:path";

process.chdir(new URL("..", import.meta.url).pathname);

export function loadGraph() {
  const graph = new Map();
  const lines = new Map();
  const add = (path) => {
    const text = readFileSync(path, "utf8");
    const name = path.slice(0, -5).replaceAll("/", ".");
    graph.set(name, text.split("\n")
      .filter((l) => l.startsWith("import "))
      .map((l) => l.split(/\s+/)[1])
      .filter((m) => m === "Solidity" || m.startsWith("Solidity.")));
    lines.set(name, text.split("\n").length - (text.endsWith("\n") ? 1 : 0));
  };
  (function walk(dir) {
    for (const f of readdirSync(dir).sort()) {
      const p = join(dir, f);
      if (p === "Solidity/Scratch") continue;
      if (statSync(p).isDirectory()) walk(p);
      else if (p.endsWith(".lean")) add(p);
    }
  })("Solidity");
  add("Solidity.lean");
  for (const [m, is] of graph) graph.set(m, is.filter((i) => graph.has(i)));
  return { graph, lines };
}

export function reach(graph, from) {
  const seen = new Set();
  const stack = [...(graph.get(from) ?? [])];
  while (stack.length) {
    const m = stack.pop();
    if (seen.has(m)) continue;
    seen.add(m);
    stack.push(...graph.get(m));
  }
  return seen;
}

export function findPath(graph, from, to) {
  const prev = new Map([[from, null]]);
  const queue = [from];
  while (queue.length) {
    const m = queue.shift();
    if (m === to) {
      const path = [];
      for (let x = to; x !== null; x = prev.get(x)) path.unshift(x);
      return path;
    }
    for (const i of graph.get(m) ?? []) if (!prev.has(i)) { prev.set(i, m); queue.push(i); }
  }
  return null;
}

function longestChain(graph) {
  const memo = new Map();
  const depth = (m) => {
    if (memo.has(m)) return memo.get(m);
    let best = [m];
    for (const i of graph.get(m)) {
      const c = depth(i);
      if (c.length + 1 > best.length) best = [m, ...c];
    }
    memo.set(m, best);
    return best;
  };
  let best = [];
  for (const m of graph.keys()) { const c = depth(m); if (c.length > best.length) best = c; }
  return best;
}

const full = (m) => (m === "Solidity" || m.startsWith("Solidity.") ? m : `Solidity.${m}`);
const short = (m) => m.replace(/^Solidity\./, "");

if (process.argv[1] === new URL(import.meta.url).pathname) {
  const args = process.argv.slice(2);
  const { graph, lines } = loadGraph();
  const need = (m) => { if (!graph.has(m)) { console.error(`unknown module ${m}`); process.exit(2); } return m; };
  if (args[0] === "--path") {
    const path = findPath(graph, need(full(args[1])), need(full(args[2])));
    if (!path) { console.log(`${short(full(args[1]))} does not import ${short(full(args[2]))}`); process.exit(1); }
    console.log(path.map(short).join(" → "));
    process.exit(0);
  }
  const chain = longestChain(graph);
  if (args[0] === "--chain") {
    console.log(chain.map(short).join("\n"));
    process.exit(0);
  }
  const dependents = new Map([...graph.keys()].map((m) => [m, 0]));
  const deps = new Map();
  for (const m of graph.keys()) {
    const r = reach(graph, m);
    deps.set(m, r.size);
    for (const d of r) dependents.set(d, dependents.get(d) + 1);
  }
  const ti = args.indexOf("--top");
  const top = ti < 0 ? 40 : Number(args[ti + 1]);
  const named = args.filter((a, k) => !a.startsWith("--") && args[k - 1] !== "--top").map((a) => need(full(a)));
  const rows = (named.length ? named : [...graph.keys()].sort((a, b) => dependents.get(b) - dependents.get(a) || a.localeCompare(b)).slice(0, top))
    .map((m) => ({ module: short(m), fanOut: dependents.get(m), fanIn: deps.get(m), lines: lines.get(m) }));
  if (args.includes("--json")) {
    console.log(JSON.stringify({ modules: graph.size, criticalPath: chain.length, chain: chain.map(short), rows }, null, 1));
  } else {
    console.log(`${graph.size} modules; longest import chain ${chain.length} modules (--chain prints it)`);
    console.log("fan-out  fan-in  lines  module");
    for (const r of rows) console.log(`${String(r.fanOut).padStart(7)}  ${String(r.fanIn).padStart(6)}  ${String(r.lines).padStart(5)}  ${r.module}`);
  }
}
