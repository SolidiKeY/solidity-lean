#!/usr/bin/env node
/**
 * solkey-port — translate solkey's `.sol` example suites into Lean
 * obligations over the typed syntax, and pin what Lean says of each.
 *
 * Source of truth: `keyext.solidity.examples` in a solkey checkout (by
 * default `../solkey`, beside this repository). There are no `.key` problem
 * files for the `.sol` suites: KeY's `SolidityProblemSynthesizer` makes one
 * obligation per function, `\<{ f(…)@C; }\>(true)`, and the whole
 * specification is the `require` and `assert` statements in the body.
 *
 * ## The obligation
 *
 * Each function becomes `Corpus.Diamond σ sol[C]{ body }` — the formula
 * `holds σ dl{ ⟨ body ⟩ true }` at the store `σ = State.<contract>Store`
 * the ported contract `C` starts in (`Solidity/Corpus/Basic.lean`). That
 * is solkey's diamond read in the contract's initial state, and it is the
 * one reading that is both faithful and decidable here:
 *
 *   - `⊨ dl[C]{ ⟨ body ⟩ true }` quantifies over every state, including
 *     those without the contract's roots, where the first storage write is
 *     stuck: it is invalid for any body that touches storage;
 *   - `⊨ dl[C]{ [ body ] true }` is valid for *every* body, since a failing
 *     `assert` halts like a `require` and a halt satisfies the box;
 *   - `⊨ dl[C]{ pre → ⟨ body ⟩ true }` with `pre` describing the store
 *     would be the faithful validity, but `sol_close` does not close a
 *     storage write under the diamond (`Calculus/Close.lean`), so it would
 *     leave nearly every obligation open while proving nothing more.
 *
 * The diamond at the store is a closed term, and the kernel decides it
 * (`corpus_decide`, i.e. `decide +kernel` on the run). Where the run needs
 * a well-founded definition the kernel cannot unfold — the default a
 * `push()` appends or a fresh memory object starts at (`defaultForTy`), a
 * memory-to-storage copy (`copyMToSt`) — the run is instead pinned by
 * `#eval` of `Corpus.outcome` under `#guard_msgs`.
 *
 * ## Verdicts
 *
 * One row per obligation in `tests/solkey/expected.tsv`, six tab-separated
 * columns: suite, contract, function, status, note, reason. The *note* says
 * what the translation did; the *reason* says why the status is what it is.
 * The status is one of
 *
 *   - `proved`: a theorem, kernel-checked;
 *   - `evaluated`: the run ends normally, pinned by `#eval` (reason: the
 *     well-founded definition the kernel stops at);
 *   - `open`: the run reverts or is stuck — solkey proves it, the
 *     interpreter disagrees (reason: how the run ends), pinned by `#eval`;
 *   - `unsupported`: no obligation is emitted; the reason is the
 *     translator's (a construct the typed syntax lacks) or Lean's (the
 *     elaboration error, verbatim);
 *   - `unported` (the `.key` suites only): hand-written in the removed
 *     untyped layer, not yet re-derived over the typed syntax.
 *
 * The statuses are Lean's, not this script's: `--probe` elaborates every
 * translated obligation (in `.lake/corpus-probe/`), tries the kernel, runs
 * the interpreter, and re-pins `expected.tsv`; without `--probe` the script
 * reads the pins back and emits each obligation in the form its status
 * calls for, so the build fails if a pinned verdict stops being true.
 * `scripts/check-corpus.sh` does both and diffs. `docs/corpus-parity.md`,
 * the scoreboard, is generated from the same rows.
 *
 * ## Translation rules
 *
 * 1. **Modality.** Every port is a diamond. solkey tags a function
 *    `/// @custom:key box` when its `require`s must be read as assumptions
 *    about unconstrained parameters; here the assumptions are made true
 *    (rules 2, 3) and the diamond also proves no-revert. A tagged function
 *    whose point is that it *does* revert (`assert(false)` after the
 *    reverting statement) has no diamond reading: `unsupported`.
 *
 * 2. **Parameters are concretized.** `require(x == 5 && y == 7)` on
 *    parameters becomes `uint x = 5; uint y = 7;` and the conjuncts are
 *    dropped (`x > N` and `x >= N` pick the least witness, `x < a.length`
 *    picks 0). Strictly weaker than KeY, which proves the asserts for all
 *    `x`, `y`: the note says `concretized` and gives the witness.
 *
 * 3. **Storage bounds are established.** `require(1 < values.length)`
 *    becomes the pushes that make it true, since each store starts with
 *    every array empty. A value element is pushed as its default spelt out
 *    (`values.push(0)`, `boolFlags.push(false)`): the same value, but
 *    `push()` needs `defaultForTy`, which the kernel does not unfold even at
 *    `uint`. Only top-level `require`s are discharged; one inside a branch
 *    is kept as written.
 *
 * 4. **Renames.** Some state variables are renamed in the ported contracts
 *    (`Syntax.lean`), because a name means different things in different
 *    contracts; `RENAMES` is the map. It applies to state variables only,
 *    not to a local of the same name. A local named like a Lean keyword or
 *    like a state variable of the contract gets a trailing `_`.
 *
 * 5. **Syntax.** Statements are Solidity as written, re-emitted one per
 *    `;` with braced branches; `uint r = x++;` is `uint r; r = x++;` (the
 *    grammar has `++` only as a statement and in `v = x++`); a nested
 *    ternary in a branch is parenthesized; `2e3` is spelt out.
 *
 * 6. **Anything else** is `unsupported` with the reason: a state variable
 *    the Lean contract does not declare, `--` (Lean's comment token, and
 *    the grammar has no decrement), `.length`, `**`, `new`, loops, calls,
 *    `return`, a type outside `uint`/`int`/`bool`/`address`/structs/
 *    dynamic arrays/mappings. What the translator lets through and Lean
 *    rejects is recorded with Lean's message.
 *
 * Usage: node scripts/solkey-port.mjs [--probe] [--solkey <dir>] [--out <repo>]
 *   --probe   elaborate everything and re-pin expected.tsv (needs the
 *             `Solidity.Corpus.Basic` olean: `lake build Solidity.Corpus.Basic`)
 *   --out     where to write (default: this repository); pins are always
 *             read from this repository's `tests/solkey/expected.tsv`
 */

import { readFileSync, readdirSync, writeFileSync, mkdirSync, existsSync, rmSync } from "node:fs";
import { join, basename, dirname } from "node:path";
import { spawn, execFileSync } from "node:child_process";
import { fileURLToPath } from "node:url";

const args = process.argv.slice(2);
const optionOf = (flag, fallback) => {
  const i = args.indexOf(flag);
  return i >= 0 && args[i + 1] ? args[i + 1] : fallback;
};

const ROOT = join(dirname(fileURLToPath(import.meta.url)), "..");
const SOLKEY = optionOf(
  "--solkey",
  process.env.SOLKEY_EXAMPLES || join(ROOT, "../solkey/keyext.solidity.examples"),
);
const OUT = optionOf("--out", ROOT);
const PROBE = args.includes("--probe");

/**
 * The contracts to port, in report order: the `.sol` file, the ported
 * `Contract` constant (`Syntax.lean`), and the store it starts in.
 */
const CONTRACTS = [
  { file: "TestSuite.sol", suite: "taclets", store: "testSuiteStore" },
  { file: "solc/SolcExpressions.sol", suite: "solc", store: "solcExpressionsStore" },
  { file: "solc/SolcStructs.sol", suite: "solc", store: "solcStructsStore" },
  { file: "solc/SolcArrays.sol", suite: "solc", store: "solcArraysStore" },
  { file: "solc/SolcMemory.sol", suite: "solc", store: "solcMemoryStore" },
  { file: "solc/SolcMappings.sol", suite: "solc", store: "solcMappingsStore" },
  { file: "solc/SolcControlFlow.sol", suite: "solc", store: "solcControlFlowStore" },
];

/**
 * State-variable renames, keyed by contract: the ported contracts' names
 * for solkey's (`Syntax.lean`, `Semantics.lean`'s stores say why).
 */
const RENAMES = {
  TestSuite: { people: "folks", a: "aux" },
  SolcExpressions: { v: "counter" },
  SolcMappings: { s: "sBox", m: "sMap" },
  SolcMemory: { x: "outerX", inner: "innerS", data: "inners" },
};

/**
 * Functions that cannot be expressed, with the reason, where the reason is
 * a fact about the Lean model rather than about a line of the source.
 */
const UNSUPPORTED = {
  "SolcStructs.recursiveStructThroughAliases":
    "field-name overloading: Depth0.recursive and Depth1.recursive have " +
    "different types, and Semantics.structDef is one global name->fields table",
  "SolcStructs.nestedRecursiveStructSetAndCheck":
    "field-name overloading: as recursiveStructThroughAliases, plus " +
    "Flagged.y (bool) vs Sub.y/Triple.y (uint)",
};

/**
 * The `.key` suites. They are KeY problem files, not annotated Solidity, so
 * there is nothing to translate; the table accounts for every problem in
 * `expected.tsv`. `ported` maps a problem to the typed example that states
 * it; `unported` lists those the removed untyped layer had hand-written
 * (its Corpus/Wp/Rules module), still to be re-derived (`docs/kernel-port.md`).
 */
const KEY_SUITES = [
  {
    contract: "Net",
    suite: "net",
    dir: "net",
    ported: {
      "net-transfer-simple": ["net_transfer_simple", "Net.netTransferSimple"],
      "net-transfer-capture-argument":
        ["net_transfer_capture_argument", "Net.netTransferCapturedAmount"],
      "net-transfer-capture-receiver":
        ["net_transfer_capture_receiver", "Net.netTransferStorageReceiver"],
    },
    unported: {},
    reason: (name) =>
      name.includes("withcallback")
        ? "needs `transferWithCallback`: the typed syntax has no calls " +
          "(docs/kernel-port.md, Port later)"
        : name === "net-msg-value"
          ? "`msg.value` is not a program expression"
          : "assumes an uninterpreted CInv over a symbolic ledger and books " +
            "msg.value/msg.sender before the call; the fragment has no msg.*",
  },
  {
    contract: "Rules",
    suite: "rules",
    dir: "../keyext.solidity.core/src/test/resources/org/key_project/solidity/examples",
    ported: {},
    unported: Object.fromEntries(
      [
        "assignRuleExample", "contextAssignTest", "fieldAccessTest", "programRulesTest",
        "revert", "schemaVarExample", "simpleExpressionTest", "mainExamples", "problem1",
        "problem2", "simpleExample1", "simpleExample2", "simpleExample3", "simpleExample4",
        "simpleExample5", "simpleExample6", "simpleExample7", "simpleExample8",
        "simpleExample9", "simpleExample10", "storageExample1", "storageExample1-2",
        "storageExample2", "storageExample2-2", "storageExample3", "storageExample4",
        "storageExample4-2", "storageExample5", "memoryExample1", "memoryExample2",
        "memoryExample2-2", "memoryExample3", "memoryExample4", "memoryExample5",
      ].map((n) => [n, n.replace(/-/g, "_")]),
    ),
    reason: () =>
      "KeY loader/taclet machinery: ad-hoc taclets over `\\problem { true }`, " +
      "a sort condition, a list declaration or an empty problem — there is no " +
      "identity and no judgment to state",
  },
  {
    contract: "Rules",
    suite: "storage",
    dir: "storage",
    ported: {},
    unported: {},
    reason: () =>
      "storage-theory problem over a `MapField`: the mapping-preserving copy " +
      "is unreachable (solc ≥ 0.7 and solkey's parser reject a copy of a " +
      "mapping-carrying type) and `Theory/Storage.lean` does not model it",
  },
];

const UNPORTED_REASON =
  "hand-written in the removed untyped layer (its Corpus/Wp/Rules module); " +
  "not yet re-derived over the typed syntax (docs/kernel-port.md, Port later)";

/** The kernel stops at a well-founded definition; the run is `#eval`-pinned. */
const EVALUATED_REASON =
  "the run needs a well-founded definition the kernel does not unfold " +
  "(a struct default: `defaultForTy`, or the memory-to-storage copy " +
  "`copyMToSt`); pinned by `#eval`";

/** Lean keywords a Solidity local may be named. */
const LEAN_KEYWORDS = new Set([
  "at", "by", "do", "else", "end", "for", "from", "fun", "have", "if", "import",
  "in", "let", "match", "mut", "namespace", "open", "return", "show", "then",
  "where", "with", "deriving", "instance", "structure", "class", "section",
  "variable", "universe", "example", "theorem", "def", "axiom", "calc",
  "suffices", "obtain", "local", "private", "protected", "partial", "unsafe",
  "try", "catch", "finally", "break", "continue", "unless", "nomatch", "nofun",
  "Type", "Sort", "Prop", "λ", "fun", "this", "true", "false",
]);

/** Solidity value types, and their spelling in the Lean grammar. */
const VALUE_TYPES = { uint: "uint", uint256: "uint", int: "int", int256: "int",
                      bool: "bool", address: "address" };

// ─────────────────────────── the Lean side ─────────────────────────────

/** The state variables of each ported `Contract`, read off `Syntax.lean`. */
function leanContracts() {
  const src = readFileSync(join(ROOT, "Solidity/Syntax.lean"), "utf8");
  const out = {};
  for (const m of src.matchAll(/def (\w+) : Contract := contract!\{([^}]*)\}/g)) {
    out[m[1]] = new Set(
      m[2].split(";").map((d) => d.trim()).filter(Boolean)
        .map((d) => d.split(/\s+/).pop()),
    );
  }
  return out;
}

// ─────────────────────────── parsing the .sol ───────────────────────────

/**
 * Split a contract source into its state variables (name → type) and
 * functions: name, parameters, the `@custom:key box` tag, the doc comment,
 * the body text.
 */
function parseContract(source) {
  const lines = source.split("\n");
  const functions = [];
  const stateVars = new Map();
  let doc = [];
  let boxed = false;
  let depth = 0;

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const trimmed = line.trim();

    if (depth === 1 && !/^(struct|function|event|modifier|constructor)\b/.test(trimmed)) {
      const sv = trimmed.match(/^(.+?)\s+(\w+)\s*;$/);
      if (sv && !trimmed.startsWith("//")) stateVars.set(sv[2], sv[1].trim());
    }

    if (trimmed.startsWith("///")) {
      const text = trimmed.slice(3).trim();
      if (text === "@custom:key box") boxed = true;
      else doc.push(text);
      continue;
    }

    const header = trimmed.match(/^function\s+(\w+)\s*\(([^)]*)\)\s*public\s*\{/);
    if (!header) {
      const code = line.replace(/\/\/.*$/, "");
      depth += (code.match(/\{/g) || []).length - (code.match(/\}/g) || []).length;
      if (trimmed !== "") {
        doc = [];
        boxed = false;
      }
      continue;
    }

    const body = [];
    let level = 1;
    for (let j = i + 1; j < lines.length && level > 0; j++) {
      const code = lines[j].replace(/\/\/.*$/, "");
      level += (code.match(/\{/g) || []).length;
      level -= (code.match(/\}/g) || []).length;
      if (level > 0) body.push(lines[j]);
      i = j;
    }

    functions.push({
      name: header[1],
      params: header[2].split(",").map((p) => p.trim()).filter(Boolean).map((p) => {
        const parts = p.split(/\s+/);
        return { ty: parts[0], name: parts[parts.length - 1] };
      }),
      boxed,
      doc: doc.slice(),
      body: body.map((l) => l.replace(/\/\/.*$/, "")).join("\n")
        .replace(/\/\*[\s\S]*?\*\//g, ""),
    });
    doc = [];
    boxed = false;
  }
  const structs = new Map();
  for (const m of source.matchAll(/struct\s+(\w+)\s*\{([^}]*)\}/g)) {
    structs.set(m[1], new Map(
      m[2].split(";").map((f) => f.trim()).filter(Boolean)
        .map((f) => { const i = f.lastIndexOf(" "); return [f.slice(i + 1), f.slice(0, i).trim()]; }),
    ));
  }
  return { functions, stateVars, structs };
}

/**
 * The Solidity type of a storage path `root.f[i]…`, or null: what the
 * push a `require` on its length discharges into appends.
 */
function pathType(path, stateVars, structs) {
  const root = path.match(/^\w+/);
  let ty = root && stateVars.get(root[0]);
  let rest = path.slice(root ? root[0].length : 0);
  while (ty && rest.length > 0) {
    if (rest[0] === "[") {
      rest = rest.slice(matching(rest, 0));
      const map = ty.match(/^mapping\s*\(\s*\w+\s*=>\s*(.*)\)$/);
      ty = map ? map[1].trim() : ty.endsWith("[]") ? ty.slice(0, -2) : null;
    } else {
      const f = rest.match(/^\.(\w+)/);
      if (!f) return null;
      rest = rest.slice(f[0].length);
      ty = structs.get(ty)?.get(f[1]) ?? null;
    }
  }
  return ty;
}

/**
 * The push that grows the array at `path` by one element: `push(0)` or
 * `push(false)` for a value element, which is the default `push()` would
 * append spelt out — `push()` needs `defaultForTy`, which the kernel does not
 * unfold even at `uint` — and `push()` otherwise.
 */
function growBy1(path, stateVars, structs) {
  const ty = pathType(path, stateVars, structs);
  const elem = ty && ty.endsWith("[]") ? ty.slice(0, -2) : null;
  if (elem && /^(u?int\d*|address)$/.test(elem)) return `${path}.push(0)`;
  if (elem === "bool") return `${path}.push(false)`;
  return `${path}.push()`;
}

// ─────────────────────────── statements ────────────────────────────────

class Unsupported extends Error {}

/** The index just past the bracket matching the one at `i`. */
function matching(src, i) {
  const open = src[i];
  const close = { "(": ")", "{": "}", "[": "]" }[open];
  let depth = 0;
  for (let k = i; k < src.length; k++) {
    if (src[k] === open) depth++;
    else if (src[k] === close && --depth === 0) return k + 1;
  }
  throw new Unsupported(`unbalanced \`${open}\``);
}

const skipWs = (src, i) => {
  while (i < src.length && /\s/.test(src[i])) i++;
  return i;
};

const keywordAt = (src, i, kw) =>
  src.startsWith(kw, i) && !/[\w$]/.test(src[i + kw.length] || "");

/**
 * Parse a block into statements: `{ kind: "if", cond, thn, els }`,
 * `{ kind: "loop", text }`, `{ kind: "block", body }` or
 * `{ kind: "simple", text }` (without its `;`).
 */
function parseBlock(src) {
  const out = [];
  let i = skipWs(src, 0);
  while (i < src.length) {
    const [stmt, next] = parseStmt(src, i);
    out.push(stmt);
    i = skipWs(src, next);
  }
  return out;
}

function parseStmt(src, i) {
  if (keywordAt(src, i, "if")) {
    const open = skipWs(src, i + 2);
    const close = matching(src, open);
    const cond = src.slice(open + 1, close - 1).trim();
    const [thn, afterThen] = parseBody(src, skipWs(src, close));
    let j = skipWs(src, afterThen);
    let els = null;
    if (keywordAt(src, j, "else")) {
      const [e, afterElse] = parseBody(src, skipWs(src, j + 4));
      els = e;
      j = afterElse;
    }
    return [{ kind: "if", cond, thn, els }, j];
  }
  for (const kw of ["for", "while"]) {
    if (keywordAt(src, i, kw)) {
      const close = matching(src, skipWs(src, i + kw.length));
      const [, end] = parseBody(src, skipWs(src, close));
      return [{ kind: "loop", text: kw }, end];
    }
  }
  if (keywordAt(src, i, "do")) {
    const [, afterBody] = parseBody(src, skipWs(src, i + 2));
    const semi = src.indexOf(";", afterBody);
    return [{ kind: "loop", text: "do" }, semi + 1];
  }
  if (src[i] === "{") {
    const end = matching(src, i);
    return [{ kind: "block", body: parseBlock(src.slice(i + 1, end - 1)) }, end];
  }
  let depth = 0;
  for (let k = i; k < src.length; k++) {
    const c = src[k];
    if ("([{".includes(c)) depth++;
    else if (")]}".includes(c)) depth--;
    else if (c === ";" && depth === 0) {
      return [{ kind: "simple", text: src.slice(i, k).trim() }, k + 1];
    }
  }
  throw new Unsupported(`statement does not end in ';': ${src.slice(i).trim()}`);
}

/** A branch: a braced block, or one statement. */
function parseBody(src, i) {
  if (src[i] === "{") {
    const end = matching(src, i);
    return [parseBlock(src.slice(i + 1, end - 1)), end];
  }
  const [stmt, end] = parseStmt(src, i);
  return [[stmt], end];
}

// ─────────────────────────── expressions ───────────────────────────────

/**
 * Split an expression on a top-level binary operator (not inside brackets),
 * returning the operands, or null when it does not occur at the top level.
 */
function splitTopLevel(expr, op) {
  let depth = 0;
  const parts = [];
  let start = 0;
  for (let i = 0; i < expr.length; i++) {
    const c = expr[i];
    if (c === "(" || c === "[") depth++;
    else if (c === ")" || c === "]") depth--;
    else if (depth === 0 && expr.startsWith(op, i)) {
      parts.push(expr.slice(start, i));
      i += op.length - 1;
      start = i + 1;
    }
  }
  if (parts.length === 0) return null;
  parts.push(expr.slice(start));
  return parts.map((p) => p.trim());
}

/** `c ? t : e` split at the first top-level `?` and its matching `:`. */
function splitTernary(expr) {
  let depth = 0;
  let question = -1;
  let pending = 0;
  for (let i = 0; i < expr.length; i++) {
    const c = expr[i];
    if (c === "(" || c === "[") depth++;
    else if (c === ")" || c === "]") depth--;
    else if (depth === 0 && c === "?") {
      if (question < 0) question = i;
      else pending++;
    } else if (depth === 0 && c === ":" && question >= 0) {
      if (pending === 0) {
        return {
          cond: expr.slice(0, question).trim(),
          thn: expr.slice(question + 1, i).trim(),
          els: expr.slice(i + 1).trim(),
        };
      }
      pending--;
    }
  }
  return null;
}

/**
 * The grammar gives `c ? t : e` precedence 20 with the `then` branch at
 * 21, so a ternary nested in a branch needs its own parentheses.
 */
function fixTernary(expr) {
  const t = splitTernary(expr);
  if (!t) return expr;
  const branch = (b) => (splitTernary(b) ? `(${fixTernary(b)})` : b);
  return `${t.cond} ? ${branch(t.thn)} : ${branch(t.els)}`;
}

/** Why an expression cannot be written, or null. */
function exprGap(e) {
  if (/\b\d+\s*(wei|gwei|ether|seconds|minutes|hours|days|weeks)\b/.test(e)) {
    return "ether and time units (`1 gwei`, `2 days`) are not in the grammar";
  }
  if (/--/.test(e)) {
    return "decrement: `--` is Lean's comment token, and the grammar has no `x--`/`--x`";
  }
  if (/\.length\b/.test(e)) return "`.length` is not a program expression";
  if (/\*\*/.test(e)) return "exponentiation `**` is not in the sol_expr grammar";
  if (/\bnew\s+\w+/.test(e)) return "`new T[](n)` array allocation is not in the fragment";
  if (/\b(msg|block|tx)\.\w+|\bthis\b/.test(e)) return "`msg`/`block`/`this` are not expressions";
  if (/(^|[^&|])[&|](?![&|=])|\^|~|<<|>>/.test(e)) return "bitwise operators are not in the grammar";
  if (/\+\+/.test(e)) return "`++` inside an expression: the grammar has it as a statement only";
  const call = e.match(/\b([A-Za-z_]\w*)\s*\(/);
  if (call && !["push", "pop", "transfer"].includes(call[1])) {
    return VALUE_TYPES[call[1]] || /^u?int\d+$/.test(call[1]) || call[1] === "payable"
      ? `type conversion \`${call[1]}(…)\` is not an expression`
      : `a call of \`${call[1]}\`: the typed syntax has no calls`;
  }
  return null;
}

// ─────────────────────── require discharge ─────────────────────────────

/**
 * A top-level `require` that pins a parameter becomes its declaration; one
 * on an array length becomes the pushes that establish it. Returns the
 * statements to emit and the conjuncts to keep as a `require`.
 */
function dischargeRequire(condition, params, declared, pushes, grow) {
  const conjuncts = splitTopLevel(condition, "&&") || [condition.trim()];
  const emitted = [];
  const kept = [];
  const pin = (name, value) => {
    declared.add(name);
    emitted.push({ stmt: `${params.get(name)} ${name} = ${value}`, witness: `${name} = ${value}` });
  };
  const free = (name) => params.has(name) && !declared.has(name);

  for (const raw of conjuncts) {
    const conjunct = raw.replace(/^\((.*)\)$/, "$1").trim();
    const equality = conjunct.match(/^(\w+)\s*==\s*(-?\d+)$/);
    if (equality && free(equality[1])) {
      pin(equality[1], equality[2]);
      continue;
    }
    const lengthEq = conjunct.match(/^([\w.[\]]+)\.length\s*==\s*(\d+)$/);
    const lengthGt = conjunct.match(/^(\d+)\s*<\s*([\w.[\]]+)\.length$/);
    const target = lengthEq ? lengthEq[1] : lengthGt ? lengthGt[2] : null;
    if (target) {
      const need = lengthEq ? Number(lengthEq[2]) : Number(lengthGt[1]) + 1;
      const have = pushes.get(target) || 0;
      for (let k = have; k < need; k++) emitted.push({ stmt: grow(target) });
      pushes.set(target, Math.max(have, need));
      continue;
    }
    const paramBound = conjunct.match(/^(\w+)\s*<\s*([\w.[\]]+)\.length$/);
    if (paramBound && free(paramBound[1])) {
      pin(paramBound[1], 0);
      if ((pushes.get(paramBound[2]) || 0) < 1) {
        emitted.push({ stmt: grow(paramBound[2]) });
        pushes.set(paramBound[2], 1);
      }
      continue;
    }
    // `require(b == minusTwo)`: a local already in scope pins the parameter.
    const aliasEq = conjunct.match(/^(\w+)\s*==\s*([A-Za-z_]\w*)$/);
    if (aliasEq && free(aliasEq[1]) && declared.has(aliasEq[2])) {
      pin(aliasEq[1], aliasEq[2]);
      continue;
    }
    const lower = conjunct.match(/^(\w+)\s*(>=|>)\s*(\d+)$/);
    if (lower && free(lower[1])) {
      pin(lower[1], Number(lower[3]) + (lower[2] === ">" ? 1 : 0));
      continue;
    }
    kept.push(conjunct);
  }
  return { emitted, kept };
}

// ─────────────────────────── translation ───────────────────────────────

/**
 * An assertion no state satisfies: solkey writes one only after a statement
 * it expects to revert, in a `@custom:key box` function.
 */
function assertsUnsatisfiable(body) {
  return /\bassert\s*\(\s*false\s*\)/.test(body) ||
    /\bassert\s*\(\s*([A-Za-z_]\w*)\s*!=\s*\1\s*\)/.test(body);
}

/** A declaration `T [location] name [= init]`, or null. */
function parseDecl(text) {
  const m = text.match(
    /^([A-Za-z_]\w*(?:\s*\[\s*\d*\s*\])*|mapping\s*\(.*\))\s+(?:(memory|storage|calldata)\s+)?([A-Za-z_]\w*)\s*(?:=\s*([\s\S]*))?$/,
  );
  if (!m) return null;
  const [, ty, location, name, init] = m;
  const base = ty.match(/^[A-Za-z_]\w*/)[0];
  if (!(base in VALUE_TYPES) && !/^[A-Z]/.test(base) && !ty.startsWith("mapping")) return null;
  if (["delete", "return", "emit"].includes(base)) return null;
  return { ty: ty.replace(/\s+/g, ""), location, name, init: init?.trim() };
}

/** A Solidity type as the Lean grammar spells it, or throw. */
function leanType(ty) {
  if (/\[\d+\]/.test(ty)) throw new Unsupported(`fixed-size array type \`${ty}\` is not in the grammar`);
  if (ty.startsWith("mapping")) return ty;
  const base = ty.match(/^[A-Za-z_]\w*/)[0];
  if (base in VALUE_TYPES) return VALUE_TYPES[base] + ty.slice(base.length);
  if (/^(u?int\d+|bytes\d*|string)$/.test(base)) {
    throw new Unsupported(`type \`${base}\` is not in the fragment`);
  }
  return ty;
}

/** Spell out `2e3` and `1_000`: Lean's `num` has neither. */
const expandScientific = (e) =>
  e.replace(/\b(\d+)e(\d+)\b/g, (_, m, x) => (BigInt(m) * 10n ** BigInt(x)).toString())
    .replace(/\b(\d+(?:_\d+)+)\b/g, (n) => n.replace(/_/g, ""));

function translateFunction(fn, contract, sol, leanVars, unportedVars) {
  if (fn.boxed && assertsUnsatisfiable(fn.body)) {
    throw new Unsupported(
      "the function asserts that the program reverts (a box-only obligation): " +
        "the obligation is a diamond, which proves the opposite",
    );
  }
  const renames = RENAMES[contract] || {};
  const params = new Map(fn.params.map((p) => [p.name, leanType(p.ty)]));
  const declared = new Set();
  const pushes = new Map();
  const witnesses = [];
  const notes = new Set();

  const statements = parseBlock(fn.body);

  // Every name the function declares: a local shadows a state variable of
  // the same name, and is never renamed as one.
  const locals = new Set(fn.params.map((p) => p.name));
  (function collect(ss) {
    for (const s of ss) {
      if (s.kind === "simple") {
        const d = parseDecl(s.text);
        if (d) locals.add(d.name);
      } else if (s.kind === "if") {
        collect(s.thn);
        if (s.els) collect(s.els);
      } else if (s.kind === "block") collect(s.body);
    }
  })(statements);

  for (const name of locals) {
    if (leanVars.has(name) || LEAN_KEYWORDS.has(name) ||
        Object.values(renames).includes(name)) {
      notes.add(`local \`${name}\` renamed \`${name}_\``);
    }
  }
  const localName = (name) =>
    leanVars.has(name) || LEAN_KEYWORDS.has(name) || Object.values(renames).includes(name)
      ? `${name}_` : name;

  /** Names in `e` rewritten: locals first, then renamed state variables. */
  const names = (e) =>
    e.replace(/(?<![.\w])([A-Za-z_]\w*)\b/g, (whole, id) => {
      if (locals.has(id)) return localName(id);
      if (unportedVars.has(id)) {
        throw new Unsupported(
          `state variable \`${id}\` (\`${unportedVars.get(id)}\`) is not in the Lean contract ` +
            `\`${contract}\` (Syntax.lean)`,
        );
      }
      return Object.hasOwn(renames, id) ? renames[id] : id;
    });

  const expr = (e) => {
    const gap = exprGap(e);
    if (gap) throw new Unsupported(gap);
    return fixTernary(names(expandScientific(e.trim())));
  };

  const out = [];
  for (const s of statements) {
    if (s.kind === "simple") {
      const req = s.text.match(/^require\s*\(([\s\S]*)\)$/);
      if (req) {
        const cond = splitTopLevel(req[1], ",")?.[0] ?? req[1];
        const { emitted, kept } = dischargeRequire(cond.trim(), params, declared, pushes,
          (path) => growBy1(path, sol.stateVars, sol.structs));
        for (const e of emitted) {
          out.push(e.witness ? names(e.stmt) : expr(e.stmt));
          if (e.witness) witnesses.push(e.witness);
        }
        if (kept.length > 0) out.push(`require(${expr(kept.join(" && "))})`);
        continue;
      }
    }
    out.push(...translate(s));
    if (s.kind === "simple") {
      const d = parseDecl(s.text);
      if (d) declared.add(d.name);
    }
  }

  /** One statement, as the list of Lean statements it becomes. */
  function translate(s) {
    switch (s.kind) {
      case "loop":
        throw new Unsupported("loops have no rule in the calculus");
      case "block":
        throw new Unsupported("a bare block `{ … }` is not a statement of the grammar");
      case "if": {
        const block = (ss) => ss.flatMap(translate).map((t) => `${t}; `).join("");
        const thn = `{ ${block(s.thn)}}`;
        return [s.els === null
          ? `if (${expr(s.cond)}) ${thn}`
          : `if (${expr(s.cond)}) ${thn} else { ${block(s.els)}}`];
      }
    }
    const text = s.text;
    if (/\.push\(\)\s*=(?!=)/.test(text)) {
      throw new Unsupported("`b.push() = v` (a push as an lvalue) is not in the grammar");
    }
    if (/^return\b/.test(text)) throw new Unsupported("`return` is not in the fragment");
    if (/^(emit|unchecked)\b/.test(text)) throw new Unsupported(`\`${text.split(/\s/)[0]}\` is not in the fragment`);
    const guard = text.match(/^(require|assert)\s*\(([\s\S]*)\)$/);
    if (guard) {
      const cond = splitTopLevel(guard[2], ",")?.[0] ?? guard[2];
      return [`${guard[1]}(${expr(cond)})`];
    }
    if (/^revert\s*\(/.test(text)) return ["revert()"];
    const del = text.match(/^delete\s+([\s\S]*)$/);
    if (del) return [`delete ${expr(del[1])}`];

    const decl = parseDecl(text);
    if (decl) {
      const ty = leanType(decl.ty);
      const name = localName(decl.name);
      const loc = decl.location === "calldata" ? "memory" : decl.location;
      const head = loc ? `${ty} ${loc} ${name}` : `${ty} ${name}`;
      if (decl.init === undefined) return [head];
      const inc = decl.init.match(/^(\+\+)?\s*([^+]+?)\s*(\+\+)?$/);
      if (inc && (inc[1] || inc[3]) && !(inc[1] && inc[3])) {
        notes.add("`T r = x++;` split into `T r; r = x++;`");
        const target = expr(inc[2]);
        return [head, inc[1] ? `${name} = ++${target}` : `${name} = ${target}++`];
      }
      return [`${head} = ${expr(decl.init)}`];
    }

    // An expression statement: `l = r`, `l += r`, `x++`, `b.push(v)`, ….
    const incDec = text.match(/^(?:([\s\S]+?)\s*=\s*)?(\+\+)?\s*([^=+]+?)\s*(\+\+)?$/);
    if (incDec && (incDec[2] || incDec[4]) && !(incDec[2] && incDec[4])) {
      const lhs = incDec[1] ? `${expr(incDec[1])} = ` : "";
      const target = expr(incDec[3]);
      return [incDec[2] ? `${lhs}++${target}` : `${lhs}${target}++`];
    }
    const assign = text.match(/^([^=!<>+\-*/%]+?)\s*([+\-*/%]?=)(?!=)\s*([\s\S]+)$/);
    if (assign) return [`${expr(assign[1])} ${assign[2]} ${expr(assign[3])}`];
    return [expr(text)];
  }

  const unconstrained = [...params.keys()].filter((p) => !declared.has(p));
  if (unconstrained.length > 0) {
    throw new Unsupported(
      `parameter(s) ${unconstrained.join(", ")} are not pinned by any require, ` +
        "so no concrete witness is derivable",
    );
  }
  if (witnesses.length > 0) {
    notes.add(`concretized: solkey proves this for all parameters; ported at ${witnesses.join(", ")}`);
  }
  return { statements: out, note: [...notes].join("; ") };
}

// ─────────────────────────── pins and probe ────────────────────────────

const TSV = join(ROOT, "tests/solkey/expected.tsv");

/** The pinned verdicts: `Contract.function` → { status, reason }. */
function readPins() {
  const pins = new Map();
  if (!existsSync(TSV)) return pins;
  for (const line of readFileSync(TSV, "utf8").split("\n")) {
    const [suite, contract, fn, status, , reason] = line.split("\t");
    if (fn) pins.set(`${suite}.${contract}.${fn}`, { status, reason: reason ?? "" });
  }
  return pins;
}

const leanString = (s) => s.replace(/\n/g, " ");

/** `sol[C]{ … }`, one statement per line under `indent`. */
function program(contract, statements, indent) {
  return `sol[${contract}]{\n` +
    statements.map((s) => `${indent}  ${s};`).join("\n") + `\n${indent}}`;
}

/** Lean's name for a function: its own, escaped if it is a keyword. */
const declName = (fn) => (LEAN_KEYWORDS.has(fn) ? `«${fn}»` : fn);

/**
 * Elaborate every obligation of `jobs` (one probe file per contract), and
 * return `Contract.function` → { status, reason }.
 */
async function probe(jobs) {
  const dir = join(ROOT, ".lake/corpus-probe");
  rmSync(dir, { recursive: true, force: true });
  mkdirSync(dir, { recursive: true });
  const results = new Map();

  await Promise.all(jobs.map(({ contract, store, obligations }) => {
    const lines = [
      "import Solidity.Corpus.Basic",
      "open Solidity Solidity.Corpus Semantics",
      "set_option maxHeartbeats 8000000",
      "",
    ];
    const ranges = [];
    let count = lines.length;
    for (const { fn, statements } of obligations) {
      const prog = program(contract, statements, "  ");
      const text = [
        `example : Diamond State.${store}`, `    ${prog} := by`, `  corpus_decide ${store}_eq`,
        `#eval IO.println ("@@PROBE ${fn} " ++ outcome State.${store}`, `  ${prog})`, "",
      ].join("\n");
      const height = text.split("\n").length;
      ranges.push({ fn, start: count + 1, end: count + 1 + height });
      count += height;
      lines.push(text);
    }
    const file = join(dir, `${contract}.lean`);
    writeFileSync(file, lines.join("\n"));

    return new Promise((resolve, reject) => {
      const child = spawn("lake", ["env", "lean", "--tstack=131072", file], { cwd: ROOT });
      let output = "";
      child.stdout.on("data", (d) => (output += d));
      child.stderr.on("data", (d) => (output += d));
      child.on("error", reject);
      child.on("close", () => {
        const outcomes = new Map();
        for (const m of output.matchAll(/^@@PROBE (\S+) (\S+)$/gm)) outcomes.set(m[1], m[2]);
        const errors = new Map();
        let current = null;
        for (const line of output.split("\n")) {
          if (line.startsWith(`${file}:`) || line.startsWith("@@PROBE")) {
            current = null;
            const m = line.slice(file.length + 1).match(/^(\d+):\d+: error(?:\([^)]*\))?: (.*)$/);
            if (!m) continue;
            const at = Number(m[1]);
            const r = ranges.find((x) => x.start <= at && at < x.end);
            if (!r) {
              reject(new Error(`probe ${contract}: an error outside any obligation:\n${line}`));
              return;
            }
            if (!errors.has(r.fn)) errors.set(r.fn, []);
            current = { text: m[2] };
            errors.get(r.fn).push(current);
          } else if (current) {
            current.text += `\n${line}`;
          }
        }
        for (const { fn } of ranges) {
          const errs = (errors.get(fn) || []).map((e) => e.text.trim());
          const outcome = outcomes.get(fn);
          const key = `${contract}.${fn}`;
          const elab = errs.find((e) => !/^Tactic `decide`/.test(e));
          if (elab) {
            results.set(key, { status: "unsupported", reason: leanString(elab.split("\n")[0]) });
          } else if (outcome === undefined) {
            reject(new Error(`probe ${contract}: no outcome for ${fn}:\n${errs.join("\n")}`));
            return;
          } else if (errs.length === 0 && outcome === "ok") {
            results.set(key, { status: "proved", reason: "" });
          } else if (outcome === "ok") {
            results.set(key, { status: "evaluated", reason: EVALUATED_REASON });
          } else {
            results.set(key, { status: "open", reason: `the run from the initial store ends in \`${outcome}\`` });
          }
        }
        resolve();
      });
    });
  }));
  return results;
}

// ───────────────────────────── emission ─────────────────────────────────

function solkeyCommit() {
  try {
    return execFileSync("git", ["-C", SOLKEY, "rev-parse", "--short=10", "HEAD"]).toString().trim();
  } catch {
    return "unknown";
  }
}

/** A reason with its particulars dropped, for counting. */
function reasonClass(reason) {
  if (/^state variable/.test(reason)) {
    return "a state variable the Lean contract does not declare (`Syntax.lean`)";
  }
  if (/^fixed-size array type/.test(reason)) return "fixed-size array types (`T[n]`) are not in the grammar";
  if (/^parameter\(s\)/.test(reason)) {
    return "a parameter no `require` pins: solkey proves it for every value";
  }
  return reason;
}

const STATUSES = ["proved", "evaluated", "open", "unsupported", "unported"];

/**
 * Why an `open` run halts, where it has been traced to a statement: what the
 * interpreter does there that solc and solkey do not. For the scoreboard
 * only; the verdict itself is re-derived by `--probe`.
 */
const OPEN_CAUSES = {
  // None since solkey `f2eb3d98eb`: the five rows traced here (a write through
  // a reference to a popped element, `delete` of an array keeping its
  // elements' mapping entries) now run to the end (docs/solc-alignment.md,
  // "Arrays past their end").
};

/** `docs/corpus-parity.md`: the scoreboard, generated from the rows. */
function parityDoc(rows, commit) {
  const byContract = new Map();
  for (const [, contract, , status] of rows) {
    if (!byContract.has(contract)) byContract.set(contract, {});
    const t = byContract.get(contract);
    t[status] = (t[status] || 0) + 1;
  }
  const total = {};
  for (const t of byContract.values()) for (const k of STATUSES) total[k] = (total[k] || 0) + (t[k] || 0);
  const cell = (t, k) => String(t[k] || 0);
  const table = [
    `| Contract | ${STATUSES.join(" | ")} |`,
    `|---|${STATUSES.map(() => "---:").join("|")}|`,
    ...[...byContract].map(([c, t]) => `| ${c} | ${STATUSES.map((k) => cell(t, k)).join(" | ")} |`),
    `| **all** | ${STATUSES.map((k) => `**${total[k]}**`).join(" | ")} |`,
  ];

  const reasons = new Map();
  for (const [, contract, , status, , reason] of rows) {
    if (status !== "unsupported") continue;
    const r = reasonClass(reason);
    if (!reasons.has(r)) reasons.set(r, new Map());
    const m = reasons.get(r);
    m.set(contract, (m.get(contract) || 0) + 1);
  }
  const reasonTable = [
    "| Unsupported because | # | where |",
    "|---|---:|---|",
    ...[...reasons]
      .map(([r, m]) => [r, [...m.values()].reduce((a, b) => a + b, 0), m])
      .sort((a, b) => b[1] - a[1])
      .map(([r, n, m]) =>
        `| ${r.replace(/\|/g, "\\|")} | ${n} | ${[...m].map(([c, k]) => `${c} ${k}`).join(", ")} |`),
  ];

  const open = rows.filter((r) => r[3] === "open")
    .map(([, c, f, , , reason]) =>
      `- \`${c}.${f}\`: ${OPEN_CAUSES[`${c}.${f}`] ?? reason}.`);

  return [
    "# solkey corpus parity",
    "",
    `Generated by \`scripts/solkey-port.mjs\` from solkey \`${commit}\`; do not edit by`,
    "hand. One row per solkey obligation is in `tests/solkey/expected.tsv`;",
    "`scripts/check-corpus.sh` re-derives the verdicts and diffs them. The",
    "obligation form (solkey's `⟨ f() ⟩ true` at the contract's initial",
    "store) and the statuses are explained in `Solidity/Corpus/Basic.lean`",
    "and the script's header:",
    "",
    "- **proved**: a theorem, decided by the kernel;",
    "- **evaluated**: the run ends normally, but it needs a well-founded",
    "  definition the kernel does not unfold (a struct or `push()` default,",
    "  the memory-to-storage copy), so it is pinned by `#eval`;",
    "- **open**: solkey proves it, the interpreter's run from the initial",
    "  store does not end normally (pinned by `#eval`);",
    "- **unsupported**: no obligation, for the reason below;",
    "- **unported**: a `.key` problem the removed untyped layer had",
    "  hand-written, not yet re-derived.",
    "",
    "## By contract",
    "",
    ...table,
    "",
    "## Open",
    "",
    ...(open.length > 0 ? open : ["None."]),
    "",
    "## Unsupported, by reason",
    "",
    ...reasonTable,
    "",
  ].join("\n");
}

async function main() {
  const lean = leanContracts();
  const commit = solkeyCommit();
  const pins = readPins();
  const rows = [];
  const perContract = [];

  for (const { file, suite, store } of CONTRACTS) {
    const contract = basename(file, ".sol");
    const sol = parseContract(readFileSync(join(SOLKEY, file), "utf8"));
    const { functions, stateVars } = sol;
    const leanVars = lean[contract];
    if (!leanVars) throw new Error(`no contract ${contract} in Syntax.lean`);
    const renames = RENAMES[contract] || {};
    const unportedVars = new Map(
      [...stateVars].filter(([n]) => !leanVars.has(Object.hasOwn(renames, n) ? renames[n] : n)),
    );

    const entries = [];
    for (const fn of functions) {
      const key = `${contract}.${fn.name}`;
      if (UNSUPPORTED[key]) {
        entries.push({ fn, status: "unsupported", note: "", reason: UNSUPPORTED[key] });
        continue;
      }
      try {
        const { statements, note } = translateFunction(fn, contract, sol, leanVars, unportedVars);
        entries.push({ fn, statements, note });
      } catch (error) {
        if (!(error instanceof Unsupported)) throw error;
        entries.push({ fn, status: "unsupported", note: "", reason: error.message });
      }
    }
    perContract.push({ file, suite, store, contract, entries });
  }

  let verdicts;
  if (PROBE) {
    verdicts = await probe(perContract.map(({ contract, store, entries }) => ({
      contract,
      store,
      obligations: entries.filter((e) => e.statements).map((e) => ({
        fn: e.fn.name, statements: e.statements,
      })),
    })));
  }

  const corpusDir = join(OUT, "Solidity/Corpus");
  mkdirSync(corpusDir, { recursive: true });
  const modules = ["Solidity.Corpus.Basic"];

  for (const { file, suite, store, contract, entries } of perContract) {
    const blocks = [];
    const tally = {};
    for (const e of entries) {
      if (e.statements) {
        const v = PROBE
          ? verdicts.get(`${contract}.${e.fn.name}`)
          : pins.get(`${suite}.${contract}.${e.fn.name}`) ?? { status: "pending", reason: "" };
        e.status = v.status === "unsupported" && !PROBE && !v.reason ? "pending" : v.status;
        e.reason = v.reason;
      }
      tally[e.status] = (tally[e.status] || 0) + 1;
      rows.push([suite, contract, e.fn.name, e.status, e.note, e.reason]);
      if (!e.statements || !["proved", "evaluated", "open"].includes(e.status)) continue;

      const doc = [
        `solkey \`${contract}.${e.fn.name}\` (\`${file}\`).`,
        ...(e.fn.doc.length > 0 ? ["", ...e.fn.doc.map((l) => l.replace(/-\//g, "- /").replace(/\/-/g, "/ -"))] : []),
        ...(e.note ? ["", `${e.note}.`] : []),
        ...(e.fn.boxed
          ? ["", "solkey tags this `@custom:key box`; the port makes its assumptions true",
             "instead, so the diamond also proves that it does not revert."]
          : []),
      ];
      const prog = program(contract, e.statements, "    ");
      if (e.status === "proved") {
        blocks.push(
          `/-- ${doc.join("\n")} -/\ntheorem ${declName(e.fn.name)} :\n` +
            `    Diamond State.${store}\n    ${prog} := by\n  corpus_decide ${store}_eq`,
        );
      } else {
        const why = e.status === "evaluated"
          ? "The kernel stops at a well-founded definition; the run is pinned instead."
          : "solkey proves this; the run from the initial store does not end normally.";
        blocks.push(
          `/-! ${doc.join("\n")}\n\n${why} -/\n\n` +
            `/-- info: "${e.status === "evaluated" ? "ok" : e.reason.match(/`(\w+)`/)[1]}" -/\n` +
            `#guard_msgs in\n#eval outcome State.${store}\n  ${program(contract, e.statements, "  ")}`,
        );
      }
    }

    const summary = Object.entries(tally).map(([k, n]) => `${n} ${k}`).join(", ");
    const moduleName = `Solidity.Corpus.${contract}`;
    modules.push(moduleName);
    writeFileSync(
      join(corpusDir, `${contract}.lean`),
      [
        "import Solidity.Corpus.Basic",
        "",
        "/-!",
        `# solkey \`${file}\`, ported`,
        "",
        `solkey \`${commit}\`: ${entries.length} functions — ${summary}.`,
        "",
        "Generated by `scripts/solkey-port.mjs`; do not edit by hand. Each",
        "function is `Diamond σ sol[C]{ body }`, solkey's `⟨ f() ⟩ true` at the",
        "contract's initial store (`Corpus/Basic.lean` says why this form):",
        "a theorem where the kernel decides it, an `#eval` pin where it stops",
        "at a well-founded definition or the run does not end normally.  The",
        "functions with no obligation, and why, are the `unsupported` rows of",
        "`tests/solkey/expected.tsv`; `docs/corpus-parity.md` is the scoreboard.",
        "-/",
        "",
        `namespace Solidity.Corpus.${contract}`,
        "",
        "open Semantics",
        "",
        "set_option maxHeartbeats 8000000",
        "",
        blocks.join("\n\n"),
        "",
        `end Solidity.Corpus.${contract}`,
        "",
      ].join("\n"),
    );
  }

  // The `.key` suites: every problem accounted for.
  for (const { contract, suite, dir, ported, unported, reason } of KEY_SUITES) {
    const problems = readdirSync(join(SOLKEY, dir))
      .filter((f) => f.endsWith(".key"))
      .map((f) => basename(f, ".key"))
      .filter((name) => readFileSync(join(SOLKEY, dir, `${name}.key`), "utf8").includes("\\problem"))
      .sort();
    for (const name of problems) {
      if (ported[name]) {
        const [fn, example] = ported[name];
        rows.push([suite, contract, fn, "proved", `solkey ${name}.key`,
                   `\`Examples/Net.lean\` \`${example}\``]);
      } else if (unported[name]) {
        rows.push([suite, contract, unported[name], "unported", `solkey ${name}.key`, UNPORTED_REASON]);
      } else {
        rows.push([suite, contract, name.replace(/-/g, "_"), "unsupported", "", reason(name)]);
      }
    }
  }

  writeFileSync(join(OUT, "SolidityCorpus.lean"),
    "-- The root of the `SolidityCorpus` library: solkey's example suites, ported\n" +
    "-- by `scripts/solkey-port.mjs` (generated; do not edit).\n" +
    modules.map((m) => `import ${m}`).join("\n") + "\n");

  mkdirSync(join(OUT, "tests/solkey"), { recursive: true });
  writeFileSync(join(OUT, "tests/solkey/expected.tsv"),
    rows.map((row) => row.join("\t")).join("\n") + "\n");

  mkdirSync(join(OUT, "docs"), { recursive: true });
  writeFileSync(join(OUT, "docs/corpus-parity.md"), parityDoc(rows, commit));

  const tally = rows.reduce((acc, [, , , status]) => {
    acc[status] = (acc[status] || 0) + 1;
    return acc;
  }, {});
  console.log(`solkey ${commit}: ${rows.length} obligations:`, tally);
}

main().catch((error) => {
  console.error(error.message);
  process.exit(1);
});
