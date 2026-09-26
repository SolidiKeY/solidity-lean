#!/usr/bin/env node
// Every `Solidity/**/*.lean` must be reachable, by imports, from a library
// root declared in `lakefile.toml`. A module nothing imports is never built,
// so it can rot unnoticed: that is how the old untyped layer outlived the
// rewrite of the core.
//
// Usage: node scripts/check-orphans.mjs [--allow <file-of-module-names>]
// The allow-list names modules that may stay orphaned for now (port sources).
// Exit 0 = no orphan outside the allow-list, 1 = at least one.
import { readFileSync, readdirSync, statSync, existsSync } from "node:fs";
import { join } from "node:path";

process.chdir(new URL("..", import.meta.url).pathname);

const modules = new Map();
(function walk(dir) {
  for (const f of readdirSync(dir)) {
    const p = join(dir, f);
    if (statSync(p).isDirectory()) walk(p);
    else if (p.endsWith(".lean")) modules.set(p.slice(0, -5).replaceAll("/", "."), imports(p));
  }
})("Solidity");

function imports(path) {
  return readFileSync(path, "utf8").split("\n")
    .filter((l) => l.startsWith("import "))
    .map((l) => l.split(/\s+/)[1]);
}

const roots = [...readFileSync("lakefile.toml", "utf8").matchAll(/^(?:name|root)\s*=\s*"([^"]+)"/gm)]
  .map((m) => m[1])
  .filter((r) => existsSync(`${r}.lean`));

const seen = new Set();
const stack = roots.flatMap((r) => imports(`${r}.lean`));
while (stack.length) {
  const m = stack.pop();
  if (seen.has(m) || !modules.has(m)) continue;
  seen.add(m);
  stack.push(...modules.get(m));
}

const i = process.argv.indexOf("--allow");
const allowed = new Set(i < 0 ? [] : readFileSync(process.argv[i + 1], "utf8").split(/\s+/).filter(Boolean));
const orphans = [...modules.keys()].filter((m) => !seen.has(m)).sort();
const bad = orphans.filter((m) => !allowed.has(m));

for (const m of orphans) console.log(`${allowed.has(m) ? "allowed" : "ORPHAN "}  ${m}`);
console.log(`${seen.size} reachable, ${orphans.length} orphaned, ${bad.length} not allowed`);
process.exit(bad.length ? 1 : 0);
