// Guard new core import escapes, including paths through other core modules.
// Existing audited boundary edges are debt, never permission to add another.
import { readFileSync, existsSync } from "node:fs";
import { createHash } from "node:crypto";
import { execFileSync } from "node:child_process";
export const BASELINE_SHA256 = "d202b21ddde800b40237b9c4a95482c17b8d5ea8d2c78c1b42e4bad7344ac80b";
const activePath = "scripts/core-import-allowlist.json";
const key = (a, b) => `${a} → ${b}`;
export function edgeSet(rows) {
  if (!Array.isArray(rows)) throw Error("allowlist must be an edge array");
  const result = new Set();
  for (const row of rows) {
    if (!Array.isArray(row) || row.length !== 2 || row.some(x => typeof x !== "string" || !/^Solidity(?:\.[A-Za-z0-9_]+)+$/.test(x)))
      throw Error("invalid allowlist edge");
    const edge = key(...row);
    if (result.has(edge)) throw Error("duplicate allowlist edge");
    result.add(edge);
  }
  return result;
}
export function requireSubset(next, previous) {
  for (const edge of next) if (!previous.has(edge)) throw Error(`allowlist can only shrink: ${edge}`);
}
export const CURRENT_BASELINE_SHA256 = "880486dcbe8f1004449dc9f1d90f25a9964d0b2c5ea64dad3de3dd5cfc548b8d";
export function loadAllowlist() {
  const raw = readFileSync("scripts/core-import-baseline.json");
  if (createHash("sha256").update(raw).digest("hex") !== BASELINE_SHA256) throw Error("audit baseline SHA256 mismatch");
  const baseline = edgeSet(JSON.parse(raw));
  if (baseline.size !== 95) throw Error("audit baseline must contain 95 edges");
  const currentRaw = readFileSync("scripts/core-import-current-baseline.json");
  if (createHash("sha256").update(currentRaw).digest("hex") !== CURRENT_BASELINE_SHA256) throw Error("current baseline SHA256 mismatch");
  const snapshot = JSON.parse(currentRaw);
  if (snapshot.schema !== 1 || snapshot.sourceCommit !== "fea090bf9fec1a372ad32952a5e72eb4d7015888" ||
      snapshot.previousBaselineSha256 !== BASELINE_SHA256 || snapshot.additions.length !== 12) throw Error("invalid authorized baseline epoch");
  const all = edgeSet(snapshot.edges), additions = edgeSet(snapshot.additions.map(row=>[row.source,row.target]));
  if (all.size !== 107 || additions.size !== 12 || [...baseline].some(edge=>!all.has(edge)) ||
      [...additions].some(edge=>!all.has(edge)||baseline.has(edge))) throw Error("authorized107baseline is not original95 plus exact12");
  // Independent components preserve all removals in the original95 history.
  // A removed original edge cannot be smuggled into the new12 component.
  return new Set([...loadSubset(activePath,baseline),
    ...loadSubset("scripts/core-import-additions-allowlist.json",additions)]);
}
function loadSubset(activePath, baseline) {
  const active = edgeSet(JSON.parse(readFileSync(activePath, "utf8")));
  requireSubset(active, baseline);
  const git = (...args) => execFileSync("git", ["--no-replace-objects", ...args], {encoding:"utf8", stdio:["ignore","pipe","pipe"]});
  if (git("rev-parse", "--is-shallow-repository").trim() !== "false") throw Error("full history required for shrink-only baseline");
  const at = rev => {
    const exists = git("ls-tree", rev, "--", activePath).trim();
    return exists ? edgeSet(JSON.parse(git("show", `${rev}:${activePath}`))) : null;
  };
  if (process.env.GIT_GRAFT_FILE !== undefined || process.env.GIT_SHALLOW_FILE !== undefined ||
      existsSync(git("rev-parse", "--git-path", "info/grafts").trim())) throw Error("custom history is not allowed");
  const head = at("HEAD");
  if (head) requireSubset(active, head);
  // Check every recorded change, including merge parents: removing an allowance
  // is permanent, even if an attempted re-addition is followed by other commits.
  // Explicit separate diffs include every merge parent, regardless of Git config; name-only omits unrelated
  // historical merges instead of probing thousands of absent-file revisions.
  const revisions = new Set(git("log", "--full-history", "--diff-merges=separate", "--format=%H", "--name-only", "HEAD", "--", activePath)
    .split("\n").filter(line => /^[0-9a-f]{40}$/.test(line)));
  for (const rev of revisions) {
    const [, ...parents] = git("rev-list", "--parents", "-n", "1", rev).trim().split(" ");
    const current = at(rev);
    if (!current) {
      if (parents.some(parent => at(parent))) throw Error("allowlist deletion is not permitted");
      continue;
    }
    requireSubset(current, baseline);
    const prior = parents.map(at).filter(Boolean);
    if (!prior.length && current.size !== baseline.size) throw Error("initial allowlist must equal pinned component baseline");
    for (const previous of prior) requireSubset(current, previous);
  }
  return active;
}
export function closureViolations(graph, isCore, allowed) {
  const found = new Map();
  for (const root of [...graph.keys()].filter(isCore).sort()) {
    const seen = new Set([root]);
    const queue = [[root]];
    for (let i=0; i<queue.length; i++) {
      const path = queue[i], from = path.at(-1);
      for (const to of graph.get(from) ?? []) {
        if (!isCore(to)) {
          const edge = key(from,to);
          if (!allowed.has(edge) && !found.has(edge)) found.set(edge,[...path,to]);
        } else if (!seen.has(to)) { seen.add(to); queue.push([...path,to]); }
      }
    }
  }
  return [...found.values()];
}

// Comments cannot create imports; unsupported multiline/quoted import syntax
// fails closed rather than silently dropping a possible boundary edge.
export function parseImports(text) {
  let clean = "", depth=0, line=false, quoted=false, escaped=false;
  for (let i=0; i<text.length; i++) {
    const c=text[i], next=text[i+1];
    if (line) { if (c==="\n") { line=false; clean+="\n"; } continue; }
    if (depth) {
      if (c==="/" && next==="-") {depth++;i++;}
      else if (c==="-" && next==="/") {depth--;i++;}
      else if (c==="\n") clean+="\n";
      continue;
    }
    if (quoted) {
      clean+=c==="\n" ? "\n" : " ";
      if (escaped) escaped=false; else if (c==="\\") escaped=true; else if (c==='"') quoted=false;
      continue;
    }
    if (c==="-" && next==="-") {line=true;i++;continue;}
    if (c==="/" && next==="-") {depth++;i++;clean+=" ";continue;}
    if (c==='"') {quoted=true;clean+=" ";continue;}
    clean+=c;
  }
  const imports=[];
  for (const row of clean.split("\n")) {
    const match=row.match(/^\s*(?:(?:public|meta)\s+)*import\b(.*)$/);
    if (!match) continue;
    const tokens=match[1].trim().split(/\s+/);
    if (tokens[0]==="all") tokens.shift();
    if (!tokens.length || tokens.some(x=>!x || !/^[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*$/.test(x)))
      throw Error("unsupported import syntax; cannot verify core closure");
    imports.push(...tokens);
  }
  return imports;
}
export function closureGraph(graph) {
  return new Map([...graph.keys()].map(module => [module,
    parseImports(readFileSync(module.replaceAll(".","/")+".lean","utf8"))
      .filter(name=>name==="Solidity" || name.startsWith("Solidity."))]));
}
