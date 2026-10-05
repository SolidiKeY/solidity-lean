#!/usr/bin/env bash
# Audit what is derived of solkey's `TestSuite.sol` (no Lean is run):
#
#   1. trust: no `native_decide`, `sorry` or `maxHeartbeats` in the code (not
#      the comments) of Solidity/TestSuite/ and Solidity/Solkey/;
#   2. axioms: `#solkey_obligations` (Frontend/Problems.lean, pinned in
#      Solidity/TestSuite/Report.lean) already counts a theorem derived only
#      when it uses no axiom but propext, Classical.choice and Quot.sound, and
#      lists any other "unsound"; this checks that the pin lists none, nor a
#      "mismatched" theorem;
#   3. parity: the TestSuite rows of tests/solkey/expected.tsv are solkey's
#      `testSuiteFunctions` (every function of TestSuite.sol not tagged
#      `@custom:key skip`, 418 of 420) plus the skipped ones, and the table is
#      what scripts/solkey-port.mjs writes from the pins today.
#
# Usage: scripts/check-testsuite.sh [--complete] [--solkey <keyext.solidity.examples>]
#   --complete  also fail while a function is pending: the goal is
#               418 = derived + excluded + divergent, plus 2 skip.
# Exit 0 = clean, 1 = a finding.
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

complete=0
args=()
for a in "$@"; do
  if [ "$a" = "--complete" ]; then complete=1; else args+=("$a"); fi
done
solkey="${SOLKEY_EXAMPLES:-$repo_root/../solkey/keyext.solidity.examples}"
for ((i = 0; i < ${#args[@]}; i++)); do
  if [ "${args[$i]}" = "--solkey" ]; then solkey="${args[$((i + 1))]}"; fi
done

scratch="$(mktemp -d)"
trap 'rm -rf "$scratch"' EXIT
node scripts/solkey-port.mjs --solkey "$solkey" --out "$scratch" >/dev/null

node --input-type=module - "$solkey" "$scratch" "$complete" <<'EOF'
import { readFileSync, readdirSync, statSync } from "node:fs";
import { join } from "node:path";

const [solkey, scratch, complete] = process.argv.slice(2);
let ok = true;
const fail = (msg) => { console.log(`check-testsuite: ${msg}`); ok = false; };

// 1. trust: tokens in the code, with comments and strings blanked
const strip = (src) => {
  let out = "";
  let depth = 0;
  for (let i = 0; i < src.length; i++) {
    if (src.startsWith("/-", i)) { depth++; i++; out += "  "; continue; }
    if (depth > 0 && src.startsWith("-/", i)) { depth--; i++; out += "  "; continue; }
    if (depth > 0) { out += src[i] === "\n" ? "\n" : " "; continue; }
    if (src.startsWith("--", i)) { while (i < src.length && src[i] !== "\n") i++; out += "\n"; continue; }
    if (src[i] === '"') {
      out += " ";
      for (i++; i < src.length && src[i] !== '"'; i++) { if (src[i] === "\\") i++; out += " "; }
      out += " ";
      continue;
    }
    out += src[i];
  }
  return out;
};
const files = (dir) => readdirSync(dir).flatMap((f) => {
  const p = join(dir, f);
  return statSync(p).isDirectory() ? files(p) : p.endsWith(".lean") ? [p] : [];
});
let scanned = 0;
for (const file of [...files("Solidity/TestSuite"), ...files("Solidity/Solkey")]) {
  scanned++;
  strip(readFileSync(file, "utf8")).split("\n").forEach((line, k) => {
    const m = line.match(/\b(native_decide|sorry|admit|maxHeartbeats)\b/);
    if (m) fail(`${file}:${k + 1}: \`${m[1]}\``);
  });
}
console.log(`trust: ${scanned} modules: ` +
  (ok ? "no native_decide, sorry, admit or maxHeartbeats in code" : "FAILED"));

// 2. axioms: the pin lists no unsound or mismatched theorem
const report = readFileSync("Solidity/TestSuite/Report.lean", "utf8");
for (const m of report.matchAll(/^(unsound|mismatched|unstated) (\w+)$/gm)) {
  fail(`Report.lean pins \`${m[1]} ${m[2]}\``);
}
console.log("axioms: #solkey_obligations counts a theorem derived only with propext, " +
  "Classical.choice and Quot.sound; Report.lean pins no unsound or mismatched theorem");

// 3. parity with solkey's testSuiteFunctions
const sol = readFileSync(join(solkey, "TestSuite.sol"), "utf8").split("\n");
const provable = new Set();
const skipped = new Set();
let tags = [];
for (const line of sol) {
  const t = line.trim();
  if (t.startsWith("///")) { tags.push(t.slice(3).trim()); continue; }
  const f = t.match(/^function\s+(\w+)\s*\(/);
  if (f) (tags.includes("@custom:key skip") ? skipped : provable).add(f[1]);
  if (t !== "") tags = [];
}
const tsvRows = (path) => readFileSync(path, "utf8").split("\n")
  .map((l) => l.split("\t")).filter((r) => r[1] === "TestSuite");
const rows = tsvRows("tests/solkey/expected.tsv");
const by = (st) => new Set(rows.filter((r) => st.includes(r[3])).map((r) => r[2]));
const stated = by(["derived", "pending", "divergent", "excluded", "unsupported"]);
const skip = by(["skip"]);
const same = (a, b) => a.size === b.size && [...a].every((x) => b.has(x));
if (!same(stated, provable)) {
  fail(`the stated rows are not testSuiteFunctions: missing ${[...provable].filter((f) => !stated.has(f)).join(" ") || "-"}, ` +
    `extra ${[...stated].filter((f) => !provable.has(f)).join(" ") || "-"}`);
}
if (!same(skip, skipped)) fail("the skip rows are not the functions tagged skip");
if (rows.length !== provable.size + skipped.size) fail("a function has more than one row");
const fresh = tsvRows(join(scratch, "tests/solkey/expected.tsv"));
if (JSON.stringify(fresh) !== JSON.stringify(rows)) {
  fail("the TestSuite rows are not what scripts/solkey-port.mjs writes (re-run it)");
}
const n = (st) => by([st]).size;
const closed = n("derived") + n("excluded") + n("divergent");
console.log(`parity: ${provable.size} testSuiteFunctions = ${n("derived")} derived + ` +
  `${n("pending")} pending + ${n("divergent")} divergent + ${n("excluded")} excluded` +
  `${n("unsupported") ? ` + ${n("unsupported")} unsupported` : ""}; ${skip.size} skip`);
if (complete === "1" && closed !== provable.size) {
  fail(`${provable.size - closed} of ${provable.size} not derived, excluded or divergent`);
}
process.exit(ok ? 0 : 1);
EOF
echo "check-testsuite: ok"
