#!/usr/bin/env node
// Structural lane guard. Kernel proofs and fetched EVM agreement are separate.
import { readFileSync, readdirSync } from "node:fs";
import { execFileSync } from "node:child_process";
import { resolve } from "node:path";
import { fileURLToPath } from "node:url";
import { loadGraph, reach } from "./import-fanout.mjs";
export const frozenBase = "2fe1f8932f96be15b00df03ba2cde46f64a87758";
const owned = "Solidity.Backend.Executable.";
const registrations = ["Solidity.lean", "docs/module-map.md", "docs/README.md"];

// Mask comments, string literals (including raw strings), and character
// literals independently. Comment-looking text in a string cannot hide code.
export function leanCode(source, rejectInterpolation = false) {
  let depth = 0, code = "";
  const mask = text => text.replace(/[^\n]/g, " ");
  for (let i = 0; i < source.length;) {
    if (depth) {
      if (source.slice(i, i + 2) === "/-") { depth++; i += 2; continue; }
      if (source.slice(i, i + 2) === "-/") { depth--; i += 2; continue; }
      code += source[i] === "\n" ? "\n" : " "; i++; continue;
    }
    if (source.slice(i, i + 2) === "/-") { depth = 1; i += 2; continue; }
    if (source.slice(i, i + 2) === "--") {
      while (i < source.length && source[i] !== "\n") i++;
      continue;
    }
    if (rejectInterpolation && /^[A-Za-z_][\w']*!\s*"/.test(source.slice(i)))
      throw new Error("owned interpolation requires an explicit term-aware trust scan");
    const raw = source.slice(i).match(/^r(#*)"/);
    if (raw) {
      const start = i + raw[0].length, close = source.indexOf('"' + raw[1], start);
      if (close < 0) throw new Error("unterminated raw string");
      const end = close + 1 + raw[1].length;
      if (rejectInterpolation && /[{}]/.test(source.slice(start, close)))
        throw new Error("owned brace-bearing string requires term-aware interpolation scanning");
      code += mask(source.slice(i, end)); i = end; continue;
    }
    const character = source.slice(i).match(/^'(?:\\(?:u\{[0-9a-fA-F]+\}|.)|[^'\\\n])'/u);
    if (character) { code += mask(character[0]); i += character[0].length; continue; }
    if (source[i] === '"') {
      let end = i + 1;
      while (end < source.length && source[end] !== '"') {
        if (source[end] === "\\") end += 2; else end++;
      }
      if (end >= source.length) throw new Error("unterminated string");
      if (rejectInterpolation && /[{}]/.test(source.slice(i + 1, end)))
        throw new Error("owned brace-bearing string requires term-aware interpolation scanning");
      end++; code += mask(source.slice(i, end)); i = end; continue;
    }
    if (source[i] === "«") {
      const end = source.indexOf("»", i + 1);
      if (end < 0) throw new Error("unterminated quoted identifier");
      if (rejectInterpolation) throw new Error("owned quoted identifier requires token-aware trust scanning");
      code += " __V14_QUOTED_IDENTIFIER__ "; i = end + 1; continue;
    }
    code += source[i++];
  }
  if (depth) throw new Error("unterminated Lean block comment");
  return code;
}
export function rawImports(source) {
  const code = leanCode(source), imports = [];
  const pattern = /^\s*(?:(?:public|private|meta)\s+)*import\s+(?:all\s+)?([^\n]+)/gm;
  const command = /^(?:import|public|private|meta|prelude|module|namespace|section|end|open|export|variable|variables|universe|universes|set_option|attribute|def|theorem|lemma|example|structure|inductive|class|instance|noncomputable|unsafe|opaque|axiom|abbrev|syntax|macro|elab|declare_syntax_cat|notation|infix|prefix|postfix|local|scoped)$/;
  const name = /^[A-Za-z_][\w']*(?:\.[A-Za-z_][\w']*)*$/;
  for (const match of code.matchAll(pattern)) {
    const names = match[1].trim().split(/\s+/);
    for (const module of names) {
      if (!name.test(module)) throw new Error(`unrecognized raw import token: ${module}`);
      imports.push(module);
    }
    // Reject ambiguous identifier-only continuations instead of skipping them.
    // Normal Lean 4.24 headers import one name per command; meta/public/all
    // forms and whitespace before that name are recognized above.
    let rest = code.slice(match.index + match[0].length);
    const continuation = rest.match(/^\n[ \t]+([^\n]+)/);
    if (continuation) {
      const tokens = continuation[1].trim().split(/\s+/);
      if (tokens.every(token => name.test(token)) && !command.test(tokens[0]))
        throw new Error(`ambiguous import continuation refused: ${tokens.join(" ")}`);
    }
  }
  return imports;
}
// Published pure source semantics/control closure is a permitted read-only dependency.
// Reserved Source files stay outside writable scope; every raw/transitive edge
// is still checked. This is an import audit, not a source-profile restriction.
const publishedSource = new Set(["Const", "Ctor", "Decls", "Elaborated", "Eval", "Examples", "Ledger", "Machine", "Observe", "Resolve", "Resolved", "Semantics", "SemanticsExamples", "State", "Syntax", "Types", "Typing", "TypingExamples", "Upstream", "Value", "WellFormed", "World"].map(n => `Solidity.Source.${n}`));
export function forbidden(module) {
  return /^Lean\./.test(module) || /^(?:Bridge|SolidityBridge|Mathlib|Std)(?:\.|$)/.test(module) ||
    /^Solidity\.(?:Frontend|Tools)(?:\.|$)/.test(module) ||
    (/^Solidity\.Source(?:\.|$)/.test(module) && !publishedSource.has(module)) ||
    /^Solidity\.Syntax\.(?:Elab|Quote|Splice)(?:\.|$)/.test(module) ||
    /^Solidity\.Calculus\.(?:Print[^.]*|Surface[^.]*|Quote|NamedTerm|TacticSyntax)(?:\.|$)/.test(module);
}
// Filesystem census includes untracked and nested owned sources, independently
// of the Git index and the shared graph's filtered edges.
export function scanSources(root) {
  const sources = new Map();
  function walk(dir) {
    for (const entry of readdirSync(resolve(root, dir), { withFileTypes: true })) {
      const path = `${dir}/${entry.name}`;
      if (entry.isSymbolicLink()) throw new Error(`source symlink refused: ${path}`);
      if (entry.isDirectory()) walk(path);
      else if (entry.isFile() && path.endsWith(".lean"))
        sources.set(path.slice(0, -5).replaceAll("/", "."), readFileSync(resolve(root, path), "utf8"));
    }
  }
  walk("Solidity");
  return sources;
}
export function analyzeSources(sources, registration, graph) {
  const modules = [...sources.keys()].filter(name => name.startsWith(owned));
  const failures = [];
  if (!modules.length) failures.push("owned source census is empty; scan cannot pass");
  let rootImports;
  try { rootImports = rawImports(registration); }
  catch (error) { failures.push(`root registration: ${error.message}`); rootImports = []; }
  if (!rootImports.length) failures.push("root registration is empty or missing");
  for (const module of modules) {
    if (rootImports.filter(name => name === module).length !== 1)
      failures.push(`${module}: expected exactly one raw root registration`);
    let code = "";
    try { code = leanCode(sources.get(module), true); }
    catch (error) { failures.push(`${module}: trust scan refused: ${error.message}`); }
    if (/\b(?:sorry|sorryAx|native_decide|implemented_by)\b|\baxiom\b|set_option\s+(?:maxHeartbeats|maxRecDepth)/m.test(code))
      failures.push(`${module}: forbidden trust/budget escape`);
    // Raw edges are checked recursively before the published graph. That graph
    // can remove missing modules and imports outside the Solidity prefix.
    const pending = [module], seen = new Set();
    while (pending.length) {
      const current = pending.pop();
      if (seen.has(current)) continue;
      seen.add(current);
      if (!sources.has(current)) {
        if (!/^Init(?:\.|$)/.test(current)) failures.push(`${module}: missing raw dependency ${current}`);
        continue;
      }
      for (const dep of rawImports(sources.get(current))) {
        if (forbidden(dep) || (dep === "Lean" && !["Solidity.AST", "Solidity.Eqns"].includes(current))) failures.push(`${module}: forbidden raw dependency ${current} -> ${dep}`);
        else if (dep !== "Lean") pending.push(dep);
      }
    }
    if (!graph.has(module)) failures.push(`${module}: absent from published graph`);
    else for (const dep of reach(graph, module))
      if (forbidden(dep) || dep === "Lean") failures.push(`${module}: forbidden published dependency ${dep}`);
  }
  return { modules, failures };
}
export function changedPaths(root, base = frozenBase) {
  const git = args => execFileSync("git", ["-C", root, ...args], { encoding: "utf8" }).split("\0").filter(Boolean);
  return [...new Set([...git(["diff", "--no-renames", "--name-only", "-z", base]),
    ...git(["ls-files", "--others", "--exclude-standard", "-z"])])];
}
export function scopeFindings(paths) {
  return paths.filter(file => !(file.startsWith("Solidity/Backend/Executable/") || file.startsWith("tests/v14-executable/") ||
    [...registrations, "docs/feature-work/roadmap-v14-executable.md", "scripts/check-v14-executable.mjs"].includes(file)))
    .map(file => `out-of-scope changed or untracked file: ${file}`);
}
export function main() {
  const root = resolve(fileURLToPath(new URL("..", import.meta.url)));
  const sources = scanSources(root);
  const { graph } = loadGraph();
  const result = analyzeSources(sources, readFileSync(resolve(root, "Solidity.lean"), "utf8"), graph);
  result.failures.push(...scopeFindings(changedPaths(root)));
  for (const file of registrations) {
    const before = execFileSync("git", ["-C", root, "show", `${frozenBase}:${file}`], { encoding: "utf8" });
    if (!readFileSync(resolve(root, file), "utf8").startsWith(before)) result.failures.push(`${file}: registration must be append-only`);
  }
  for (const failure of result.failures) console.error(failure);
  console.log(`V14 structural guard: ${result.modules.length} owned modules, ${result.failures.length} findings (no semantic completion claim)`);
  return result.failures.length ? 1 : 0;
}
if (process.argv[1] && resolve(process.argv[1]) === fileURLToPath(import.meta.url)) {
  try { process.exitCode = main(); }
  catch (error) { console.error(`V14 guard failed closed: ${error.message}`); process.exitCode = 1; }
}
