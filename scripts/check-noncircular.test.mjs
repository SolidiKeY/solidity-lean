import { test } from "node:test";
import assert from "node:assert/strict";
import { check } from "./check-noncircular.mjs";

const mods = (o) => new Map(Object.entries(o));

test("a source module may reach only the whitelist", () => {
  assert.deepEqual(check(mods({
    "Solidity.Source.A": "import Solidity.Source.B\nimport Solidity.Roadmap.Contracts\n",
    "Solidity.Source.B": "",
    "Solidity.Roadmap.Contracts": "import Solidity.Keccak\n",
    "Solidity.Keccak": "",
  })), []);
  const bad = check(mods({
    "Solidity.Source.A": "import Solidity.Source.B\n",
    "Solidity.Source.B": "import Solidity.Semantics.Run\n",
    "Solidity.Semantics.Run": "",
  }));
  assert.ok(bad.some((b) => b.startsWith("WHITELIST") && b.includes("Solidity.Semantics.Run")), bad.join("\n"));
  assert.ok(check(mods({ "Solidity.Source.A": "import Lean\n" })).some((b) => b.includes("Lean")));
});

test("a SourceSpec instance outside Source is a source module", () => {
  const bad = check(mods({
    "Solidity.Other": "import Solidity.Syntax.Scoped\ndef s : SourceSpec where\n",
    "Solidity.Syntax.Scoped": "",
  }));
  assert.ok(bad.some((b) => b.startsWith("WHITELIST")));
});

test("source modules name no later layer, comments aside", () => {
  assert.deepEqual(check(mods({ "Solidity.Source.A": "/- Lowering -/\n-- EvmSpec\ndef x := 1\n" })), []);
  assert.ok(check(mods({ "Solidity.Source.A": "def x := Lowering\n" })).some((b) => b.startsWith("LATER")));
});

test("the EVM end reaches no compiler", () => {
  const bad = check(mods({
    "Solidity.V": "import Solidity.Evm.Machine\ndef v : EvmSpec where\n",
    "Solidity.Evm.Machine": "import Solidity.Evm.Compile\n",
    "Solidity.Evm.Compile": "",
  }));
  assert.ok(bad.some((b) => b.startsWith("EVM-END")));
});

test("controls import the contracts only", () => {
  assert.deepEqual(check(mods({ "Solidity.Roadmap.Controls": "import Solidity.Roadmap.Contracts\ndef v : EvmSpec where\n", "Solidity.Roadmap.Contracts": "" })), []);
  assert.ok(check(mods({ "Solidity.Roadmap.Controls": "import Solidity.Evm.Compile\n", "Solidity.Evm.Compile": "" })).some((b) => b.startsWith("CONTROL")));
});

test("qualified names, multi-module imports and modifiers are caught", () => {
  for (const src of ["def s : Solidity.Roadmap.SourceSpec where\n", "def s := ({ t with } : Roadmap.SourceSpec)\n"]) {
    const bad = check(mods({ "Solidity.Other": "import Solidity.Semantics.Run\n" + src, "Solidity.Semantics.Run": "" }));
    assert.ok(bad.some((b) => b.startsWith("WHITELIST")), src);
  }
  assert.ok(check(mods({ "Solidity.Source.A": "def x := Solidity.Roadmap.Lowering\n" })).some((b) => b.startsWith("LATER")));
  for (const imp of ["import Solidity.Roadmap.Contracts Solidity.Semantics.Run\n", "public import Solidity.Semantics.Run\n", "/- c -/\nimport Solidity.Source.B\n  import Solidity.Semantics.Run\n"]) {
    const bad = check(mods({ "Solidity.Source.A": imp, "Solidity.Source.B": "", "Solidity.Roadmap.Contracts": "", "Solidity.Semantics.Run": "" }));
    assert.ok(bad.some((b) => b.startsWith("WHITELIST")), imp);
  }
  assert.deepEqual(check(mods({ "Solidity.Source.A": "/-\nimport Solidity.Semantics.Run\n-/\n", "Solidity.Semantics.Run": "" })), []);
});

test("the EVM end is a whitelist and must reach the pinned EVM", () => {
  const ok = check(mods({ "Solidity.V": "import Solidity.Roadmap.Evm\ndef v : EvmSpec where\n", "Solidity.Roadmap.Evm": "import Solidity.Keccak\n", "Solidity.Keccak": "" }));
  assert.deepEqual(ok, []);
  assert.ok(check(mods({ "Solidity.V": "import Solidity.Roadmap.Evm\nimport Solidity.Semantics.Run\ndef v : Roadmap.EvmSpec where\n", "Solidity.Roadmap.Evm": "", "Solidity.Semantics.Run": "" })).some((b) => b.startsWith("EVM-END")));
  assert.ok(check(mods({ "Solidity.V": "import Solidity.Roadmap.Contracts\ndef v : EvmSpec where\n", "Solidity.Roadmap.Contracts": "" })).some((b) => b.includes("without the pinned EVM")));
});

test("the contracts reach only Keccak and define no compiler", () => {
  assert.ok(check(mods({ "Solidity.Roadmap.Contracts": "import Solidity.Evm.Compile\n", "Solidity.Evm.Compile": "" })).some((b) => b.startsWith("CONTRACTS")));
  assert.ok(check(mods({ "Solidity.Roadmap.Contracts": "def compile (p : Prog) : Option Artifact := none\n" })).some((b) => b.includes("into Artifact")));
  assert.deepEqual(check(mods({ "Solidity.Roadmap.Contracts": "def Artifact.initcode (a : Artifact) (k : Nat) : Bytes := []\n" })), []);
});
