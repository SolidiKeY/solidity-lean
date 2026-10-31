import test from "node:test";
import assert from "node:assert/strict";
import { mkdtempSync, mkdirSync, writeFileSync, rmSync } from "node:fs";
import { tmpdir } from "node:os";
import { join } from "node:path";
import { execFileSync } from "node:child_process";
import { analyzeSources, scanSources, scopeFindings, rawImports, changedPaths } from "../../scripts/check-v14-executable.mjs";
const name = "Solidity.Backend.Executable.Consumer";
const analyze = (source, registration = `import ${name}\n`) =>
  analyzeSources(new Map([[name, source]]), registration, new Map([[name, []]]));
test("nonempty source census and exact registration are required", () => {
  assert.ok(analyzeSources(new Map(), "", new Map()).failures.some(x => x.includes("census is empty")));
  assert.ok(analyze("", "").failures.some(x => x.includes("registration is empty")));
  assert.ok(analyze("", "-- import " + name).failures.length);
  assert.ok(analyze("", `import ${name}\nimport ${name}\n`).failures.length);
  assert.equal(analyze("").failures.length, 0);
});
test("raw forbidden edges cannot disappear in filtered graph", () => {
  for (const dep of ["Bridge.Hidden", "SolidityBridge.Hidden", "Solidity.Frontend.Absent", "Solidity.Source.Absent",
    "Solidity.Syntax.Elab.Hidden", "Solidity.Calculus.PrintHidden", "Solidity.Tools.Hidden", "Lean.Elab"]) {
    assert.ok(analyze(`  import ${dep}\n`).failures.some(x => x.includes("forbidden raw dependency")), dep);
  }
});
test("raw transitive edge and published graph are both checked", () => {
  const helper = "Solidity.Backend.Helper";
  const sources = new Map([[name, `import ${helper}\n`], [helper, "import Bridge.Hidden\n"]]);
  const filtered = new Map([[name, [helper]], [helper, []]]);
  assert.ok(analyzeSources(sources, `import ${name}\n`, filtered).failures.some(x => x.includes("Bridge.Hidden")));
  const graphOnly = new Map([[name, ["Solidity.Frontend.Hidden"]], ["Solidity.Frontend.Hidden", []]]);
  assert.ok(analyzeSources(new Map([[name, ""]]), `import ${name}\n`, graphOnly).failures.some(x => x.includes("forbidden published")));
});
test("filesystem census includes new untracked nested owned trust escapes", () => {
  const root = mkdtempSync(join(tmpdir(), "v14-guard-"));
  try {
    mkdirSync(join(root, "Solidity/Backend/Executable/New"), { recursive: true });
    writeFileSync(join(root, "Solidity/Backend/Executable/New/Untracked.lean"), "axiom bad : False\n");
    const sources = scanSources(root), module = "Solidity.Backend.Executable.New.Untracked";
    assert.equal(sources.size, 1);
    assert.ok(analyzeSources(sources, `import ${module}\n`, new Map([[module, []]])).failures.some(x => x.includes("trust/budget")));
  } finally { rmSync(root, { recursive: true, force: true }); }
});
test("comments, missing dependencies and out-of-scope new files fail closed", () => {
  assert.deepEqual(rawImports("/- import Bridge.Hidden /- nested -/ -/\n  import A B -- note\n"), ["A", "B"]);
  assert.ok(analyze("import Solidity.Absent\n").failures.some(x => x.includes("missing raw")));
  assert.equal(scopeFindings(["Solidity/Backend/Executable/New.lean"]).length, 0);
  assert.equal(scopeFindings(["Solidity/Backend/Scalar/NewUntracked.lean"]).length, 1);
});

test("meta/public/all headers and ambiguous continuations cannot hide imports", () => {
  for (const source of ["module\nmeta import Bridge.Hidden\n", "public meta import all SolidityBridge.Hidden\n",
    "import\n  Bridge.Hidden\n"]) {
    assert.ok(analyze(source).failures.some(x => x.includes("forbidden raw")));
  }
  assert.throws(() => rawImports("import Solidity.KeySort\n  Bridge.Hidden\n"), /continuation refused/);
});
test("string and raw-string comment markers cannot hide private or attributed axioms", () => {
  for (const declaration of ["axiom bad : False", "private axiom bad : False", "@[simp] axiom bad : False",
    "namespace Hidden axiom bad : False\nend Hidden"]) {
    for (const [start, end] of [['"/-"', '"-/"'], ['r#"/-"#', 'r#"-/"#']]) {
      const source = `def start : String := ${start}\n${declaration}\ndef finish : String := ${end}\n`;
      assert.ok(analyze(source).failures.some(x => x.includes("trust/budget")));
    }
  }
  assert.equal(analyze('def harmless : String := "axiom /- -- \\\""\n').failures.length, 0);
});
test("existing core Lean bootstrap is distinct from a new owned meta import", () => {
  const sources = new Map([[name, "import Solidity.AST\n"], ["Solidity.AST", "import Lean\n"]]);
  const graph = new Map([[name, ["Solidity.AST"]], ["Solidity.AST", []]]);
  assert.equal(analyzeSources(sources, `import ${name}\n`, graph).failures.length, 0);
  assert.ok(analyze("import Lean\n").failures.some(x => x.includes("forbidden raw")));
});
test("Git census includes untracked files and both sides of a reserved rename", () => {
  const root = mkdtempSync(join(tmpdir(), "v14-guard-git-"));
  const git = args => execFileSync("git", ["-C", root, ...args], { stdio: "pipe" });
  try {
    git(["init", "-q"]);
    mkdirSync(join(root, "Solidity/Backend/Scalar"), { recursive: true });
    mkdirSync(join(root, "Solidity/Backend/Executable"), { recursive: true });
    writeFileSync(join(root, "Solidity/Backend/Scalar/Reserved.lean"), "def reserved := 7\n");
    git(["add", "."]);
    git(["-c", "user.name=Fixture", "-c", "user.email=fixture@example.invalid", "-c", "commit.gpgsign=false", "-c", "core.hooksPath=/dev/null", "commit", "-qm", "fixture"]);
    git(["mv", "Solidity/Backend/Scalar/Reserved.lean", "Solidity/Backend/Executable/Moved.lean"]);
    writeFileSync(join(root, "Solidity/Backend/Executable/Untracked.lean"), "axiom bad : False\n");
    const paths = changedPaths(root, "HEAD");
    assert.ok(paths.includes("Solidity/Backend/Scalar/Reserved.lean"));
    assert.ok(paths.includes("Solidity/Backend/Executable/Moved.lean"));
    assert.ok(paths.includes("Solidity/Backend/Executable/Untracked.lean"));
    assert.ok(scopeFindings(paths).some(x => x.includes("Scalar/Reserved")));
  } finally { rmSync(root, { recursive: true, force: true }); }
});

test("zero-hash raw backslash literals cannot hide real following axioms", () => {
  const source = String.raw`def opener : String := r"\"
axiom bad : False
def closer : String := "\""
`;
  assert.ok(analyze(source).failures.some(x => x.includes("trust/budget")));
});
test("owned interpolated term code is refused rather than masked as plain text", () => {
  for (const source of ['def hidden : String := s!"{(by sorry : Nat)}"\n',
    'def n : String := s!"{(show Nat from by have h : True := by native_decide; exact 7)}"\n']) {
    assert.ok(analyze(source).failures.some(x => x.includes("interpolation")));
  }
});
test("a filtered plain Lean graph edge is reported without an undefined variable", () => {
  const graph = new Map([[name, ["Lean"]], ["Lean", []]]);
  assert.ok(analyzeSources(new Map([[name, ""]]), `import ${name}\n`, graph).failures.some(x => x.includes("forbidden published")));
});

test("comments before interpolation and non-bang interpolators cannot hide code", () => {
  for (const source of ['def hidden : String := s! /- gap -/ "{(by sorry : Nat)}"\n',
    'def hidden : String := s! -- gap\n "{(by sorry : Nat)}"\n',
    'def hidden : Nat := by dbg_trace "{(by sorry : Nat)}"; exact 0\n']) {
    assert.ok(analyze(source).failures.some(x => x.includes("interpolation")));
  }
});
test("comment markers in quoted identifiers cannot hide declarations", () => {
  const source = 'def «/-» : Nat := 0\naxiom bad : False\ndef «-/» : Nat := 0\n';
  assert.ok(analyze(source).failures.some(x => x.includes("quoted identifier") || x.includes("trust/budget")));
});
