#!/usr/bin/env node
// Structural scope/registration guard; this is not a Lean proof or an EVM test.
import { readFileSync, readdirSync } from "node:fs";
import { execFileSync } from "node:child_process";
import { loadGraph, reach } from "./import-fanout.mjs";
const base = "2fe1f8932f96be15b00df03ba2cde46f64a87758";
const dir = "Solidity/Backend/Executable";
const files = readdirSync(dir).filter(x => x.endsWith(".lean")).map(x => `${dir}/${x}`);
const root = readFileSync("Solidity.lean", "utf8");
const { graph } = loadGraph();
const failures = [];
for (const file of files) {
  const module = file.slice(0, -5).replaceAll("/", ".");
  const source = readFileSync(file, "utf8");
  if (root.split("\n").filter(x => x === `import ${module}`).length !== 1)
    failures.push(`${module}: expected exactly one root registration`);
  if (/\b(?:sorry|sorryAx|native_decide|implemented_by)\b|^\s*axiom\s|set_option\s+(?:maxHeartbeats|maxRecDepth)/m.test(source))
    failures.push(`${module}: forbidden trust/budget escape`);
  for (const dep of reach(graph, module)) {
    if (/^(?:Bridge\.|Solidity\.(?:Frontend|Source)\.|Solidity\.Syntax\.(?:Elab|Quote|Splice)(?:\.|$)|Solidity\.Calculus\.(?:Print|Surface|Quote|NamedTerm|TacticSyntax))/.test(dep))
      failures.push(`${module}: forbidden dependency ${dep}`);
  }
}
const changed = execFileSync("git", ["diff", "--name-only", base], {encoding:"utf8"}).trim().split("\n").filter(Boolean);
for (const file of changed) {
  if (!(file.startsWith(`${dir}/`) || file.startsWith("tests/v14-executable/") ||
    ["Solidity.lean", "docs/module-map.md", "docs/README.md", "docs/feature-work/roadmap-v14-executable.md", "scripts/check-v14-executable.mjs"].includes(file)))
    failures.push(`out-of-scope tracked change: ${file}`);
}
for (const file of ["Solidity.lean", "docs/module-map.md", "docs/README.md"]) {
  const before = execFileSync("git", ["show", `${base}:${file}`], {encoding:"utf8"});
  if (!readFileSync(file, "utf8").startsWith(before)) failures.push(`${file}: registration must be append-only`);
}
for (const failure of failures) console.error(failure);
console.log(`V14 structural guard: ${files.length} owned modules, ${failures.length} findings (no semantic completion claim)`);
process.exitCode = failures.length ? 1 : 0;
