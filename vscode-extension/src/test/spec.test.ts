/**
 * Unit tests for the SolSpec front-end: the parser, the clause grammar,
 * the code generator, and verdict attribution.
 *
 * Run with `npm test` (`tsc -p . && node --test out/test/`). Nothing
 * here needs Lean — the tests pin the *shape* of the generated
 * obligations, which is what the Lean side (`Spec/Examples.lean`) is
 * written to match.
 */

import assert from "node:assert/strict";
import { test } from "node:test";

import { parseClauseLine, parseSourceUnit, parseSpecExpr } from "../spec/parser";
import { tokenize } from "../spec/lexer";
import { compileSpecFile, computeVerdicts } from "../spec/pipeline";
import { generateLean } from "../spec/emitLean";

const BANK = `
/// @custom:invariant a + b <= 100
contract Bank {
    uint8 a;
    uint8 b;

    /// @custom:requires amount <= a
    /// @custom:ensures a == old(a) - amount
    /// @custom:modifies a, b
    function move(uint8 amount) public {
        a -= amount;
        b += amount;
    }
}
`;

function compile(source: string) {
  const r = compileSpecFile(source);
  assert.equal(r.error, undefined, r.error?.message);
  return r.generated!;
}

/* ---------------------------------------------------------------- */
/* Lexer                                                             */
/* ---------------------------------------------------------------- */

test("doc comments attach to the next token, ordinary comments do not", () => {
  const toks = tokenize(`
// noise
/// @custom:requires x > 0
// more noise
function f() {}
`);
  const fn = toks.find((t) => t.text === "function");
  assert.ok(fn);
  assert.deepEqual(
    fn!.docs.map((d) => d.text),
    ["@custom:requires x > 0"],
  );
});

test("block doc comments produce one clause line each, located correctly", () => {
  const toks = tokenize(["/**", " * @custom:requires x > 0", " * @custom:ensures y == 1", " */", "function f() {}"].join("\n"));
  const fn = toks.find((t) => t.text === "function")!;
  assert.deepEqual(
    fn.docs.map((d) => d.text),
    ["@custom:requires x > 0", "@custom:ensures y == 1"],
  );
  assert.deepEqual(
    fn.docs.map((d) => d.loc.line),
    [1, 2],
  );
});

/* ---------------------------------------------------------------- */
/* Clause grammar                                                    */
/* ---------------------------------------------------------------- */

const loc = { line: 3, col: 0, endLine: 3, endCol: 10 };

test("known @custom: tags become clauses, unknown ones are ignored", () => {
  assert.equal(parseClauseLine({ text: "@custom:requires x > 0", loc })!.tag, "requires");
  assert.equal(parseClauseLine({ text: "@custom:security-contact a@b.c", loc }), undefined);
  assert.equal(parseClauseLine({ text: "@notice hello", loc }), undefined);
});

test("a clause carries the line it was written on", () => {
  const c = parseClauseLine({ text: "@custom:ensures x == 1", loc })!;
  assert.equal(c.loc.line, 3);
  assert.equal(c.expr!.loc.line, 3);
});

test("@custom:modifies with no argument is the empty frame", () => {
  const c = parseClauseLine({ text: "@custom:modifies", loc })!;
  assert.deepEqual(c.targets, []);
  assert.equal(c.error, undefined);
});

test("a malformed clause is reported, not thrown", () => {
  const c = parseClauseLine({ text: "@custom:ensures x ==", loc })!;
  assert.ok(c.error, "expected a clause error");
});

test("@custom:decreases and function-level @custom:invariant are rejected", () => {
  const gen = compile(`
contract C {
    uint256 x;
    /// @custom:invariant x == 0
    function f() public { x = 0; }
}
`);
  assert.equal(gen.obligations.length, 0);
  assert.match(gen.skipped[0].reason, /belongs on the contract/);
});

/* ---------------------------------------------------------------- */
/* Specification expressions                                         */
/* ---------------------------------------------------------------- */

test("==> is right associative and binds looser than ||", () => {
  const e = parseSpecExpr("a || b ==> c ==> d", loc);
  assert.equal(e.k, "bin");
  assert.equal((e as any).op, "==>");
  assert.equal((e as any).lhs.op, "||");
  assert.equal((e as any).rhs.op, "==>");
});

test("quantifiers parse over a half-open range", () => {
  const e = parseSpecExpr("forall i in 0 .. n :: a[i] == 0", loc) as any;
  assert.equal(e.k, "quant");
  assert.equal(e.quantifier, "forall");
  assert.equal(e.binder, "i");
  assert.equal(e.hi.name, "n");
});

test("old(e) is a distinct node", () => {
  const e = parseSpecExpr("old(x) + 1", loc) as any;
  assert.equal(e.lhs.k, "old");
});

/* ---------------------------------------------------------------- */
/* Solidity subset                                                   */
/* ---------------------------------------------------------------- */

test("state variables, structs and mappings parse with their types", () => {
  const unit = parseSourceUnit(`
contract C {
    struct P { uint256 age; bool ok; }
    mapping(uint256 => bool) flags;
    uint256[] xs;
    P p;
    function f() public {}
}
`);
  const c = unit.contracts[0];
  assert.deepEqual(
    c.stateVars.map((v) => v.type.kind),
    ["mapping", "array", "struct"],
  );
  assert.equal(c.structs[0].fields.length, 2);
});

test("uint defaults to 256 bits and address to 160", () => {
  const unit = parseSourceUnit(`contract C { uint a; address b; uint8 c; function f() public {} }`);
  assert.deepEqual(
    unit.contracts[0].stateVars.map((v) => (v.type as any).bits),
    [256, 160, 8],
  );
});

test("a function whose body leaves the fragment is recorded, not fatal", () => {
  const unit = parseSourceUnit(`
contract C {
    uint256 x;
    function loopy() public { for (uint256 i = 0; i < 3; i++) { x = 0; } }
    function fine() public { x = 1; }
}
`);
  const [loopy, fine] = unit.contracts[0].functions;
  assert.match(loopy.unsupported!.reason, /loops are outside/);
  assert.equal(fine.unsupported, undefined);
  assert.equal(fine.body.length, 1);
});

/* ---------------------------------------------------------------- */
/* Code generation                                                   */
/* ---------------------------------------------------------------- */

test("one obligation per clause, plus range and frame", () => {
  const gen = compile(BANK);
  assert.deepEqual(
    gen.obligations.map((o) => o.name),
    [
      "Bank_move_ensures_1",
      "Bank_move_invariant_1",
      "Bank_move_range",
    ],
  );
  /* `modifies a, b` leaves no other root, so there is no frame goal. */
  assert.equal(gen.skipped.length, 0);
});

test("each obligation points at the clause line that produced it", () => {
  const gen = compile(BANK);
  const ensures = gen.obligations.find((o) => o.kind === "ensures")!;
  const line = BANK.split("\n")[ensures.loc.line];
  assert.match(line, /@custom:ensures/);
  const inv = gen.obligations.find((o) => o.kind === "invariant")!;
  assert.match(BANK.split("\n")[inv.loc.line], /@custom:invariant/);
});

test("the pre-state is symbolic and old() reads its variables", () => {
  const gen = compile(BANK);
  assert.match(gen.text, /def Bank_move_state \(a b amount : Int\) : State/);
  assert.match(gen.text, /\("a", \(SVal\.int a\)\)/);
  /* `old(a) - amount` becomes `a - <read of amount>`, not a state read
     of `a`: that is what makes the precondition linear arithmetic. */
  const ensures = /theorem Bank_move_ensures_1[\s\S]*?:= by/.exec(gen.text)![0];
  assert.match(ensures, /hpre_1 : \(\(Spec\.localInt|hpre_1 : \(amount ≤ a\)/);
  assert.match(ensures, /= \(a - /);
});

test("uint8 bounds are emitted as numerals, in and out", () => {
  const gen = compile(BANK);
  assert.match(gen.text, /Spec\.inRange 0 255 a\b/);
  assert.match(gen.text, /theorem Bank_move_range[\s\S]*?Spec\.inRange 0 255 \(Spec\.intAt s "a" \[\]\)/);
});

test("@custom:partial switches the modality; the default is total", () => {
  const gen = compile(`
contract C {
    uint256 x;
    /// @custom:partial
    /// @custom:ensures x == 1
    function f() public { require(x == 0); x = 1; }
    /// @custom:ensures x == 2
    function g() public { x = 2; }
}
`);
  assert.match(gen.text, /theorem C_f_ensures_1[\s\S]*?Spec\.partialVC/);
  assert.match(gen.text, /theorem C_g_ensures_1[\s\S]*?Spec\.totalVC/);
});

test("a ghost assert gets its own obligation and becomes an assumption elsewhere", () => {
  const gen = compile(`
contract C {
    uint256 x;
    /// @custom:ensures x == 2
    function f() public {
        x = 1;
        /// @custom:assert x == 1
        x = 2;
    }
}
`);
  const names = gen.obligations.map((o) => o.name);
  assert.ok(names.includes("C_f_assert_1"), names.join(","));
  /* In the body every other obligation uses, the proved assert is an
     assumption — Dafny's reading. */
  assert.match(gen.text, /def C_f_body[\s\S]*?Spec\.Ann\.assume/);
  assert.match(gen.text, /def C_f_assert_1_body[\s\S]*?Spec\.Ann\.assert/);
});

test("@custom:free skips the function and says so", () => {
  const gen = compile(`
contract C {
    uint256 x;
    /// @custom:free
    /// @custom:ensures x == 1
    function f() public { x = 1; }
}
`);
  assert.equal(gen.obligations.length, 0);
  assert.equal(gen.skipped[0].why, "free");
});

test("@custom:tactic replaces the proof script", () => {
  const gen = compile(`
contract C {
    uint256 x;
    /// @custom:ensures x == 1
    /// @custom:tactic simp [C_f_state, C_f_body]; decide
    function f() public { x = 1; }
}
`);
  assert.match(gen.text, /simp \[C_f_state, C_f_body\]; decide/);
  assert.doesNotMatch(gen.text, /sol_spec/);
});

test("reading a[i] in a proved clause carries its range obligation", () => {
  const gen = compile(`
contract C {
    uint256[] xs;
    /// @custom:ensures xs[0] == 1
    function f() public { xs[0] = 1; }
}
`);
  assert.match(gen.text, /0 ≤ \(0 : Int\) ∧ \(0 : Int\) < \(Spec\.lenAt s "xs" \[\]\)/);
});

test("a function with no clauses generates nothing", () => {
  const gen = compile(`contract C { uint256 x; function f() public { x = 1; } }`);
  assert.equal(gen.obligations.length, 0);
  assert.equal(gen.skipped.length, 0);
});

test("generated line spans cover their theorem and do not overlap", () => {
  const gen = compile(BANK);
  const lines = gen.text.split("\n");
  for (const o of gen.obligations) {
    assert.ok(
      lines.slice(o.genStartLine - 1, o.genEndLine).some((l) => l.startsWith(`theorem ${o.name}`)),
      `${o.name} not inside its own span`,
    );
  }
  const sorted = [...gen.obligations].sort((x, y) => x.genStartLine - y.genStartLine);
  for (let i = 1; i < sorted.length; i++) {
    assert.ok(sorted[i].genStartLine > sorted[i - 1].genEndLine, "spans overlap");
  }
});

test("a parse error is returned with a location, never thrown", () => {
  const r = compileSpecFile("contract C { uint256 x");
  assert.ok(r.error);
  assert.equal(typeof r.error!.loc.line, "number");
});

/* ---------------------------------------------------------------- */
/* Verdicts                                                          */
/* ---------------------------------------------------------------- */

test("a Lean error inside a theorem span fails exactly that obligation", () => {
  const gen = compile(BANK);
  const target = gen.obligations[1];
  const result = computeVerdicts(gen.obligations, gen.skipped, [
    { severity: "error", line: target.genEndLine, endLine: target.genEndLine, message: "unsolved goals" },
  ]);
  assert.equal(result.verified, gen.obligations.length - 1);
  const failed = result.verdicts.filter((v) => v.status === "failed");
  assert.equal(failed.length, 1);
  assert.equal(failed[0].label, target.label);
  assert.deepEqual(result.globalErrors, []);
});

test("an error outside every span is an infrastructure error", () => {
  const gen = compile(BANK);
  const result = computeVerdicts(gen.obligations, gen.skipped, [
    { severity: "error", line: 1, endLine: 1, message: "unknown identifier" },
  ]);
  assert.equal(result.globalErrors.length, 1);
  assert.equal(result.verified, gen.obligations.length);
});

test("skipped functions appear in the report as unsupported or assumed", () => {
  const gen = compile(`
contract C {
    uint256 x;
    /// @custom:ensures x == 0
    function loopy(uint256 n) public { while (n > 0) { x = 0; } }
}
`);
  const result = computeVerdicts(gen.obligations, gen.skipped, []);
  assert.equal(result.verdicts[0].status, "unsupported");
  assert.equal(result.attempted, 0);
});

/* ---------------------------------------------------------------- */
/* End to end on the shipped examples                                */
/* ---------------------------------------------------------------- */

test("the shipped examples generate cleanly", async () => {
  const fs = await import("node:fs");
  const path = await import("node:path");
  const dir = path.join(__dirname, "..", "..", "examples", "spec");
  for (const name of fs.readdirSync(dir).filter((f) => f.endsWith(".sol"))) {
    const gen = compile(fs.readFileSync(path.join(dir, name), "utf8"));
    assert.ok(gen.obligations.length > 0, `${name} produced no obligations`);
    for (const s of gen.skipped) {
      assert.equal(s.why, "unsupported", `${name}: unexpected skip ${s.reason}`);
    }
  }
});

test("generateLean is a pure function of the parsed unit", () => {
  const unit = parseSourceUnit(BANK);
  const a = generateLean(unit.contracts, unit.fileStructs).text;
  const b = generateLean(parseSourceUnit(BANK).contracts, []).text;
  assert.equal(a, b);
});
