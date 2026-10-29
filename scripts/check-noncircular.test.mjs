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
