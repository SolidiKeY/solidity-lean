#!/usr/bin/env node
import { loadGraph, reach } from "../../scripts/import-fanout.mjs";
import { readFileSync, readdirSync } from "node:fs";
function importsFrom(source) {
  let clean = "", depth = 0, quoted = false;
  for (let i = 0; i < source.length; i++) {
    const pair = source.slice(i, i + 2), c = source[i];
    if (depth) {
      if (pair === "/-") { depth++; i++; }
      else if (pair === "-/") { depth--; i++; }
      else if (c === "\n") clean += "\n";
    } else if (quoted) {
      if (c === "\\") i++;
      else if (c === '"') quoted = false;
      else if (c === "\n") clean += "\n";
    } else if (pair === "/-") { depth = 1; i++; }
    else if (pair === "--") {
      while (i < source.length && source[i] !== "\n") i++;
      clean += "\n";
    } else if (c === '"') quoted = true;
    else clean += c;
  }
  return clean.split("\n").filter(line => /^\s*import\s/.test(line))
    .flatMap(line => line.trim().split(/\s+/).slice(1));
}
// Protect against the shared graph silently filtering external edges.
const scannerControl = importsFrom("/- outer /- nested -/\nimport Bridge.Hidden -/\nimport Bridge.Visible -- retained edge\nimport Init\n");
if (JSON.stringify(scannerControl) !== JSON.stringify(["Bridge.Visible", "Init"]))
  throw new Error("raw import scanner control failed");
const { graph } = loadGraph();
const owned = readdirSync("Solidity/Backend/InternalFlow").filter(x => x.endsWith(".lean"))
  .map(x => "Solidity.Backend.InternalFlow." + x.slice(0, -5)).sort();
const forbidden = /^(Bridge\.|Solidity\.(Frontend|Source|Tools)\.|Solidity\.Syntax\.(Elab|Quote|Splice)(\.|$)|Solidity\.Calculus\.(Print[^.]*|Surface[^.]*|TacticSyntax|Quote|NamedTerm)(\.|$))/;
let bad = 0;
for (const name of owned) {
  const closure = new Set([name, ...reach(graph, name)]);
  for (const dependency of closure) {
    // loadGraph filters non-Solidity edges: inspect raw imports as well.
    const direct = importsFrom(readFileSync(dependency.replaceAll(".", "/") + ".lean", "utf8"));
    for (const imported of direct) {
      if (forbidden.test(imported) || !/^(Solidity(?:\.|$)|Init(?:\.|$)|Std(?:\.|$)|Lean(?:\.|$))/.test(imported)) {
        console.log(`${dependency} has forbidden raw import ${imported}`); bad++;
      }
    }
    if (forbidden.test(dependency)) { console.log(`${name} reaches ${dependency}`); bad++; }
  }
  const file = name.replaceAll(".", "/") + ".lean";
  const source = readFileSync(file, "utf8");
  if (/\b(sorry|axiom|native_decide)\b/.test(source.replaceAll(/\/--?[\s\S]*?-\//g, "").replaceAll(/--[^\n]*/g, "").replaceAll(/#print axioms[^\n]*/g, "")) ||
      /implemented_by|maxHeartbeats/.test(source)) { console.log(`${file}: forbidden new trust/budget site`); bad++; }
}
console.log(`${owned.length} owned modules, ${bad} import/trust/budget findings`);
process.exitCode = bad ? 1 : 0;
