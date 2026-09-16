#!/usr/bin/env node
/**
 * solkey-port — translate the solkey `.sol` example suites into
 * dynamic-logic judgments.
 *
 * Source of truth: `~/projects/solkey/keyext.solidity.examples`.
 * There are no `.key` problem files for the `.sol` suites — KeY's
 * `SolidityProblemSynthesizer` makes one obligation per function,
 * `\<{ f(…)@C; }\>(true)`, and the whole specification is the `require`
 * and `assert` statements in the body. That maps onto a `sol!` judgment
 * `sol!{ < body > (true) }`: a failing `assert` halts with `.revert`,
 * which refutes a diamond exactly as it leaves KeY's diamond open.
 *
 * Two outputs per contract, from one pass so they cannot drift:
 *   - `Solidity/Examples/Solkey/<Contract>.lean`
 *     (one `theorem … := by sol_wp`, kernel-checked in `lake build`)
 *   - `Solidity/Examples/Derivations/Solkey/<Contract>/PartNN.lean`, for
 *     the contracts in `CALCULUS_CONTRACTS`: the *same* obligation proved by
 *     the rule table alone (`sol_calculus`), which is the artefact that
 *     corresponds to a KeY proof. `sol_wp` never reads `Rules.lean`, so
 *     the corpus above says the interpreter is right and says nothing
 *     about the calculus.
 * plus a row per function in `tests/solkey/expected.tsv` and, for the
 * calculus contracts, in `tests/solkey/expected-calculus.tsv`. Six
 * tab-separated columns: suite, contract, function, status, note, reason.
 * The *note* is this script's and says what the translation did; the
 * *reason* is the checker's and says why a verdict is what it is. They are
 * separate columns so that re-pinning is idempotent — with one column, a
 * second `--update` appends the checker's reason to the reason it wrote the
 * first time.
 *
 * ## Translation rules
 *
 * 1. **Modality.** Every port is a *diamond*. solkey tags a function
 *    `/// @custom:key box` when its `require`s must be read as
 *    assumptions about unconstrained parameters; this verifier evaluates
 *    from one concrete store, so the assumptions are instead *made true*
 *    (rule 2/3) and the judgment proves no-revert as well as every
 *    assert. A box judgment over an unsatisfied `require` is vacuously
 *    valid — it would report "proved" while proving nothing.
 *
 * 2. **Parameters are concretized.** `require(x == 5 && y == 7)` on
 *    parameters becomes `uint x = 5; uint y = 7;` and the conjuncts are
 *    dropped. This is strictly weaker than KeY, which proves the same
 *    assert for *all* `x`, `y`; such functions are recorded
 *    `concretized`, with the witness in the note.
 *
 * 3. **Storage bounds are established.** `require(1 < values.length)`
 *    becomes the `values.push()` statements that make it true, since each
 *    contract's store starts with every array empty.
 *
 * 4. **Syntax.** Comparisons exist only parenthesized in the `sol_expr`
 *    grammar (a bare trailing `>` would close the diamond), so every
 *    comparison is wrapped. `--` cannot be a Lean token, so `x--` and
 *    `--x` become `postdec(x)` / `predec(x)`.
 *
 * 5. **Renames.** Eight state variables collide across the seven ported
 *    contracts. The stores are per contract, but the *parser* resolves a
 *    name to a type through one global table
 *    (`SoliditySyntax.solkeyGlobalTy`), so the clashes still have to go;
 *    `RENAMES` below is the map, and every affected theorem says so in its docstring. Local
 *    *storage* aliases are emitted in the `name@Type` form so they need
 *    no entry in the alias table; local *memory* aliases are renamed to
 *    `mv`/`mv2`/… because `aliasKind` is a name→kind table and the same
 *    solkey name is a storage alias in one function and a memory alias
 *    in another.
 *
 * 6. **Anything else** produces no theorem: the function is recorded
 *    `unsupported` with the reason, which is what the parity report is
 *    for.
 *
 * Usage: node scripts/solkey-port.mjs [--solkey <dir>] [--out <repo>]
 */

import { readFileSync, readdirSync, writeFileSync, mkdirSync } from "node:fs";
import { join, basename } from "node:path";

const args = process.argv.slice(2);
const optionOf = (flag, fallback) => {
  const i = args.indexOf(flag);
  return i >= 0 && args[i + 1] ? args[i + 1] : fallback;
};

const SOLKEY = optionOf(
  "--solkey",
  join(process.env.HOME, "projects/solkey/keyext.solidity.examples"),
);
const REPO = optionOf("--out", process.cwd());

/**
 * The contracts to port, in report order, each with the initial state
 * its judgments run from. There is deliberately one store per contract
 * rather than one union store: the store is an association list the
 * interpreter scans on every access, so its length multiplies the cost
 * of every proof (see `Semantics.State.testSuiteStore`).
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
 * The contracts that also get a rule-table corpus. TestSuite is the one the
 * question was asked about; adding a name here is all it takes to extend the
 * exercise, at the cost of that contract's elaboration time in
 * `scripts/check-calculus-parity.sh`.
 */
const CALCULUS_CONTRACTS = new Set(["TestSuite"]);

/**
 * Obligations per rule-table module. One module of a whole contract's
 * `sol_calculus` commands is a single-threaded elaboration of tens of
 * thousands of pinned taclet applications; split into parts it is
 * a handful of independent
 * files over the same cached dependencies, which
 * `scripts/check-calculus-parity.sh` elaborates concurrently. The parts
 * reopen one namespace, so nothing about the corpus is split but its
 * elaboration.
 */
const CALCULUS_PART_SIZE = 24;

/**
 * The state variables `SoliditySyntax.rootExpr` already resolves. Anything
 * else is emitted as `name@@Type`, which carries the type at the use site
 * and so keeps the ported contracts out of that table — see
 * `SoliditySyntax.globalExpr` for why that matters (widening the table
 * makes *every* judgment more expensive to elaborate, not just the ones
 * using the new names).
 */
const BASELINE_ROOTS = new Set([
  "total", "age", "owner", "balance", "values", "balances", "flags",
  "folks", "matrix", "persons", "people", "alice", "bob", "wallet",
]);

/**
 * Types of the state variables that need the `@@` form, per contract.
 * The type names are those of `SoliditySyntax.typedVarTy`.
 */
const GLOBAL_TYPES = {
  TestSuite: {
    aux: "UintArray", valuesMap: "UintMap", accountMap: "AccountMap",
    ledger: "Ledger", tokens: "TokenArray", bucket: "TokenBucket",
    ledgerUses: "LedgerUseArray",
    // `flag` is a *stack* bool in `rootExpr` (the calculus's own examples
    // use it as one), so TestSuite's storage `flag` needs the `@@` form
    // like every other name that table does not already resolve.
    flag: "bool", flag2: "bool", boolFlags: "BoolArray",
    toggle: "Toggle", tok: "Token", buckets: "TokenBucketArray",
    basketA: "Basket", basketB: "Basket",
  },
  SolcExpressions: { counter: "uint" },
  SolcStructs: {
    data1: "Simple", withArray: "WithArray", triple: "Triple",
    neighbourBefore: "uint", neighbourAfter: "uint", source: "Pair",
    target: "Pair", pairs1: "PairArray", pairs2: "PairArray",
    campaigns: "SimpleMap",
  },
  SolcArrays: {
    storageArray: "UintArray", matrix: "UintMatrix", structs: "PairArray",
  },
  SolcMemory: {
    outerX: "Outer", innerS: "Inner", inners: "InnerArray",
    prims: "UintArray",
  },
  SolcMappings: {
    sBox: "S", withSub: "WithSub", sMap: "SMap", withSubMap: "WithSubMap",
    balances: "UintMap", arrayMap: "UintArrayMap", rows: "UintMatrix",
    ledger: "Ledger",
  },
  SolcControlFlow: {
    sx: "Pair", sy: "Pair", target: "Pair", values: "UintArray",
  },
};

/**
 * State-variable renames, keyed by contract. A handful of names mean
 * different things in different contracts and would otherwise collide
 * with a local, an alias name, or a `rootExpr` entry.
 */
const RENAMES = {
  TestSuite: {
    // `people` is already the `Person[]` of the worked examples.
    people: "folks",
    // `a` is a local `uint` in seven SolcExpressions functions.
    a: "aux",
  },
  SolcExpressions: {
    // `v` is a local `uint` in twelve functions across the suites.
    v: "counter",
  },
  SolcMappings: {
    // `s` is a local `Inner memory` in SolcMemory.
    s: "sBox",
    // `m` is an existing local storage-alias name.
    m: "sMap",
  },
  SolcMemory: {
    // `x` is the stack `uint` root.
    x: "outerX",
    // `inner` is a local storage alias in SolcStructs.
    inner: "innerS",
    // `data` is a `Depth0` state variable in SolcStructs.
    data: "inners",
  },
};

/**
 * Functions that cannot be expressed, with the reason for the report.
 * Recorded here rather than discovered by the translator because the
 * reason is a fact about the Lean fragment, not about the line.
 */
const UNSUPPORTED = {
  "SolcStructs.recursiveStructThroughAliases":
    "field-name overloading: Depth0.recursive and Depth1.recursive have " +
    "different types, and SoliditySyntax.fieldTy is one global name->type table",
  "SolcStructs.nestedRecursiveStructSetAndCheck":
    "field-name overloading: as recursiveStructThroughAliases, plus " +
    "Flagged.y (bool) vs Sub.y/Triple.y (uint)",
};

/**
 * The `.key` suites. They are KeY problem files, not annotated
 * Solidity, so there is nothing here to translate: the obligations that
 * *are* expressible are hand-written in `Examples/Solkey/Net.lean` and
 * `Examples/Solkey/Rules.lean`, and this table records which, so that
 * every one of solkey's obligations appears in `expected.tsv` — the
 * unported ones with the reason.
 *
 * Two entries may share a `contract`, and so a module: `storage` and
 * `rules` are different upstream directories whose obligations are both
 * term-level and both live in `Examples/Solkey/Rules.lean`.
 */
const KEY_SUITES = [
  {
    contract: "Net",
    suite: "net",
    dir: "net",
    ported: {
      "net-transfer-simple": "net_transfer_simple",
      "net-transfer-capture-argument": "net_transfer_capture_argument",
      "net-transfer-capture-receiver": "net_transfer_capture_receiver",
    },
    reason: (name) =>
      name.includes("withcallback")
        ? "needs `transferWithCallback`, which CallbackSemantics.lean gives a " +
          "relational meaning but the sol_stmt grammar cannot spell"
        : name === "net-msg-value"
          ? "`msg.value` is not in the sol_expr grammar"
          : "assumes an uninterpreted CInv over a symbolic ledger and books " +
            "msg.value/msg.sender before the call; sol_wp evaluates from a " +
            "concrete store and the fragment has no msg.*",
  },
  {
    contract: "Rules",
    suite: "rules",
    dir: "../keyext.solidity.core/src/test/resources/org/key_project/solidity/examples",
    ported: {
      assignRuleExample: "assignRuleExample",
      contextAssignTest: "contextAssignTest",
      fieldAccessTest: "fieldAccessTest",
      programRulesTest: "programRulesTest",
      revert: "revert",
      schemaVarExample: "schemaVarExample",
      simpleExpressionTest: "simpleExpressionTest",
      // Term-level: proved over `Theory/Storage.lean` and `Theory/Memory.lean`
      // rather than by `sol_wp`, since a heap-algebra identity is not a
      // dynamic logic judgment. Hand-written in the same module.
      mainExamples: "mainExamples",
      problem1: "problem1",
      problem2: "problem2",
      simpleExample1: "simpleExample1",
      simpleExample2: "simpleExample2",
      simpleExample3: "simpleExample3",
      simpleExample4: "simpleExample4",
      simpleExample5: "simpleExample5",
      simpleExample6: "simpleExample6",
      simpleExample7: "simpleExample7",
      simpleExample8: "simpleExample8",
      simpleExample9: "simpleExample9",
      simpleExample10: "simpleExample10",
      storageExample1: "storageExample1",
      "storageExample1-2": "storageExample1_2",
      storageExample2: "storageExample2",
      "storageExample2-2": "storageExample2_2",
      storageExample3: "storageExample3",
      storageExample4: "storageExample4",
      "storageExample4-2": "storageExample4_2",
      storageExample5: "storageExample5",
      memoryExample1: "memoryExample1",
      memoryExample2: "memoryExample2",
      "memoryExample2-2": "memoryExample2_2",
      memoryExample3: "memoryExample3",
      memoryExample4: "memoryExample4",
      memoryExample5: "memoryExample5",
    },
    reason: () =>
      "KeY loader/taclet machinery: ad-hoc taclets over `\\problem { true }`, " +
      "a sort condition, a list declaration or an empty problem — there is no " +
      "identity and no judgment to state",
  },
  {
    contract: "Rules",
    suite: "storage",
    dir: "storage",
    ported: { copyKeepsMapping: "copyKeepsMapping" },
    reason: () =>
      "storage-theory problem with no Lean statement yet — see " +
      "`Theory/Storage.lean`'s leaf of a write",
  },
];

/**
 * Names `SoliditySyntax.rootExpr` resolves to a *storage* or *memory*
 * root. A solkey function that declares a plain local with one of these
 * names (`uint p = a++;`) would have every later mention of it read as a
 * storage alias instead, so such locals are renamed. The stack roots
 * (`result`, `x`, `y`, `i`, `to`, `amount`, `flag`) are not listed: a
 * `uint` local of that name resolves correctly already.
 */
const RESERVED_ROOTS = new Set([
  "alice", "bob", "carol", "david", "mv", "people", "total", "age",
  "balance", "owner", "values", "balances", "flags", "folks", "matrix",
  "persons", "wallet", "p", "acc", "sp", "src", "tgt", "pv", "pp", "bp",
  "aliceAlias", "tokRef", "aliceAcc", "aliceTok", "m",
]);

/** Solidity value types that introduce a stack variable. */
const VALUE_TYPES = new Set(["uint", "int", "bool", "address"]);

/** Reference type spellings with no single-ident Solidity name. */
const ARRAY_TYPE_NAMES = {
  "uint[]": "UintArray",
  "Token[]": "TokenArray",
  "Pair[]": "PairArray",
  "Inner[]": "InnerArray",
};

// ─────────────────────────── parsing the .sol ───────────────────────────

/**
 * Split a contract source into functions: name, parameter list, the
 * `/// @custom:key box` tag, the preceding doc comment, and body lines.
 */
function parseContract(source) {
  const lines = source.split("\n");
  const functions = [];
  let doc = [];
  let boxed = false;

  for (let i = 0; i < lines.length; i++) {
    const line = lines[i];
    const trimmed = line.trim();

    if (trimmed.startsWith("///")) {
      const text = trimmed.slice(3).trim();
      if (text === "@custom:key box") {
        boxed = true;
      } else {
        doc.push(text);
      }
      continue;
    }

    const header = trimmed.match(/^function\s+(\w+)\s*\(([^)]*)\)\s*public\s*\{/);
    if (!header) {
      if (trimmed !== "") {
        doc = [];
        boxed = false;
      }
      continue;
    }

    // Collect the body up to the matching close brace.
    const body = [];
    let depth = 1;
    for (let j = i + 1; j < lines.length && depth > 0; j++) {
      const bodyLine = lines[j];
      depth += (bodyLine.match(/\{/g) || []).length;
      depth -= (bodyLine.match(/\}/g) || []).length;
      if (depth > 0) body.push(bodyLine);
      i = j;
    }

    functions.push({
      name: header[1],
      params: header[2]
        .split(",")
        .map((p) => p.trim())
        .filter(Boolean)
        .map((p) => {
          const [ty, name] = p.split(/\s+/);
          return { ty, name };
        }),
      boxed,
      doc: doc.slice(),
      body,
    });
    doc = [];
    boxed = false;
  }
  return functions;
}

/**
 * Body lines to *logical* statements, dropping comments and blank lines.
 * A statement spanning several lines — an `if`/`else` with a braced
 * block — is joined into one string, so the caller sees one entry per
 * statement whatever its layout.
 */
function statementsOf(bodyLines) {
  const out = [];
  let pending = "";
  let depth = 0;

  for (const raw of bodyLines) {
    const line = raw.replace(/\/\/.*$/, "").trim();
    if (line === "") continue;

    pending = pending === "" ? line : `${pending} ${line}`;
    depth += (line.match(/\{/g) || []).length;
    depth -= (line.match(/\}/g) || []).length;

    // Still inside a block, or an `else` is about to follow.
    if (depth > 0 || /\}$/.test(pending) === false) {
      if (depth > 0) continue;
    }
    if (depth === 0 && pending.endsWith("}")) {
      out.push(pending);
      pending = "";
      continue;
    }
    if (depth === 0 && pending.endsWith(";")) {
      out.push(pending);
      pending = "";
    }
  }
  if (pending !== "") out.push(pending);

  // `} else {` was joined into the preceding `if`; merge a dangling
  // `else` block onto the statement before it.
  const merged = [];
  for (const statement of out) {
    if (/^else\b/.test(statement) && merged.length > 0) {
      merged[merged.length - 1] += ` ${statement}`;
    } else {
      merged.push(statement);
    }
  }
  return merged;
}

/** Split `if (c) { … } else { … }` into its three parts. */
function parseIf(statement) {
  const head = statement.match(/^if\s*\(/);
  if (!head) return null;

  let depth = 0;
  let condEnd = -1;
  for (let i = statement.indexOf("("); i < statement.length; i++) {
    if (statement[i] === "(") depth++;
    else if (statement[i] === ")") {
      depth--;
      if (depth === 0) {
        condEnd = i;
        break;
      }
    }
  }
  if (condEnd < 0) return null;
  const condition = statement.slice(statement.indexOf("(") + 1, condEnd);

  // Solidity allows a braceless single-statement branch
  // (`if (x == 4) r = 1;`), which has no `{` to match.
  const readBlock = (from) => {
    const open = statement.indexOf("{", from);
    const semi = statement.indexOf(";", from);
    if (open < 0 || (semi >= 0 && semi < open)) {
      if (semi < 0) return null;
      // `from` points at the `)` closing the condition, or just past the
      // then-branch's `}` with `else` still ahead; skip both.
      let start = from;
      while (start < semi && /[)\s]/.test(statement[start])) start++;
      if (statement.startsWith("else", start)) start += 4;
      while (start < semi && /\s/.test(statement[start])) start++;
      return { body: statement.slice(start, semi + 1), end: semi };
    }
    let level = 0;
    for (let i = open; i < statement.length; i++) {
      if (statement[i] === "{") level++;
      else if (statement[i] === "}") {
        level--;
        if (level === 0) return { body: statement.slice(open + 1, i), end: i };
      }
    }
    return null;
  };

  const thenBlock = readBlock(condEnd);
  if (!thenBlock) return null;
  const rest = statement.slice(thenBlock.end + 1).trim();
  const elseBlock = /^else\b/.test(rest) ? readBlock(thenBlock.end + 1) : null;

  return {
    condition,
    thenBody: thenBlock.body,
    elseBody: elseBlock ? elseBlock.body : null,
  };
}

// ─────────────────────── expression transformation ──────────────────────

/**
 * Split an expression on a top-level binary operator (not inside
 * parentheses or brackets), returning the operand strings, or null when
 * the operator does not occur at the top level.
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

const COMPARISONS = ["==", "!=", "<=", ">=", "<", ">"];

/**
 * Split `c ? t : e` at the first top-level `?` and its matching `:`.
 * Returns null when the expression is not a ternary.
 */
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
          cond: expr.slice(0, question),
          thenBranch: expr.slice(question + 1, i),
          elseBranch: expr.slice(i + 1),
        };
      }
      pending--;
    }
  }
  return null;
}

/**
 * Wrap every comparison in parentheses: the `sol_expr` grammar has
 * comparisons only in the parenthesized form, because a bare trailing
 * `>` would be parsed as the closing bracket of the diamond modality.
 */
function parenthesizeComparisons(expr) {
  if (expr === undefined) return expr;
  const trimmed = expr.trim();

  for (const connective of ["||", "&&"]) {
    const parts = splitTopLevel(trimmed, connective);
    if (parts) {
      return parts.map(parenthesizeComparisons).join(` ${connective} `);
    }
  }

  // `c ? t : e`, possibly nested in any of the three positions. Split at
  // the *first* top-level `?` and pair it with its matching `:`, counting
  // intervening `?`/`:` so that `c1 ? c2 ? a : b : c` associates right.
  const ternary = splitTernary(trimmed);
  if (ternary) {
    // The grammar gives `c ? t : e` precedence 20 with both branches at
    // 21, so a ternary nested in a branch needs its own parentheses.
    const branch = (text) => {
      const rendered = parenthesizeComparisons(text);
      return splitTernary(text) ? `(${rendered})` : rendered;
    };
    return (
      `${parenthesizeComparisons(ternary.cond)} ? ` +
      `${branch(ternary.thenBranch)} : ${branch(ternary.elseBranch)}`
    );
  }

  for (const op of COMPARISONS) {
    const parts = splitTopLevel(trimmed, op);
    if (parts && parts.length === 2) {
      return `(${parts[0]} ${op} ${parts[1]})`;
    }
  }

  // A fully parenthesized subexpression: recurse inside.
  if (trimmed.startsWith("(") && trimmed.endsWith(")")) {
    let depth = 0;
    let wraps = true;
    for (let i = 0; i < trimmed.length - 1; i++) {
      if (trimmed[i] === "(") depth++;
      else if (trimmed[i] === ")") depth--;
      if (depth === 0 && i < trimmed.length - 1) wraps = false;
    }
    if (wraps) return `(${parenthesizeComparisons(trimmed.slice(1, -1))})`;
  }

  return trimmed;
}

/** `x--` / `--x` become `postdec(x)` / `predec(x)`; see AST.lean. */
function rewriteDecrements(expr) {
  return expr
    .replace(/--\s*([A-Za-z_][\w.[\]]*)/g, "predec($1)")
    .replace(/([A-Za-z_][\w.[\]]*)\s*--/g, "postdec($1)");
}

/** Apply an identifier rename map at word boundaries. */
function applyRenames(text, renames) {
  let out = text;
  for (const [from, to] of Object.entries(renames)) {
    out = out.replace(new RegExp(`(?<![.\\w])${from}\\b`, "g"), to);
  }
  return out;
}

/**
 * Rewrite state variables that `rootExpr` does not know into the typed
 * `name@@Type` form. Applied after renaming, so the names are the port's.
 */
function applyGlobals(text, globals) {
  let out = text;
  for (const [name, ty] of Object.entries(globals)) {
    if (BASELINE_ROOTS.has(name)) continue;
    out = out.replace(new RegExp(`(?<![.\\w])${name}\\b(?!@)`, "g"),
                      `${name}@@${ty}`);
  }
  return parenthesizeCallReceivers(out);
}

/**
 * `x@@T.push(42)` does not parse: Lean lexes `T.push` as a single dotted
 * identifier, so the type path of the `@@` form swallows the method name.
 * Parenthesizing the global makes the receiver a complete `sol_expr`.
 *
 * The receiver may be indexed on the way to the method — solkey's
 * receiver-and-index-both-impure group writes
 * `buckets[1].tokens.push()` — so the path alternates field selectors and
 * index brackets, not field selectors alone.
 *
 * The lookbehind is what keeps this from parenthesizing more than it has
 * to. The problem is the *lexer*, not the grammar: a dot after an
 * identifier glues into a dotted identifier, so `tokens.push` and
 * `TokenBucketArray.push` are one token and the `(` after them has nothing
 * to attach to. A dot after `]` does not glue, and `rows@@M[0].push()`
 * parses as written — parenthesizing it too would be a gratuitous
 * difference from the solkey source.
 */
function parenthesizeCallReceivers(text) {
  return text.replace(
    /([A-Za-z_]\w*@@[A-Za-z_]\w*(?:\[[^\][]*\]|\.[A-Za-z_]\w*)*?)(?<=[A-Za-z0-9_])(\.(?:push|pop|transfer)\()/g,
    "($1)$2",
  );
}

// ─────────────────────── require/bound handling ─────────────────────────

/**
 * A `require` that constrains a *parameter* to a literal becomes that
 * parameter's declaration; a `require` on an array *length* becomes the
 * `push`es that establish it, since every array in the contract's store starts
 * empty. Returns the statements to emit in place of the require, or null
 * when the require has no such reading (it is then kept verbatim, and
 * has to hold on its own).
 */
function dischargeRequire(condition, params, declared, pushes) {
  const conjuncts = splitTopLevel(condition, "&&") || [condition.trim()];
  const emitted = [];
  const kept = [];

  for (const conjunct of conjuncts) {
    const equality = conjunct.match(/^(\w+)\s*==\s*(-?\d+)$/);
    if (equality && params.has(equality[1]) && !declared.has(equality[1])) {
      declared.add(equality[1]);
      emitted.push({
        stmt: `${params.get(equality[1])} ${equality[1]} = ${equality[2]}`,
        witness: `${equality[1]} = ${equality[2]}`,
      });
      continue;
    }

    // `require(<array>.length == N)` / `require(N < <array>.length)`
    const lengthEq = conjunct.match(/^([\w.[\]]+)\.length\s*==\s*(\d+)$/);
    const lengthGt = conjunct.match(/^(\d+)\s*<\s*([\w.[\]]+)\.length$/);
    const target = lengthEq ? lengthEq[1] : lengthGt ? lengthGt[2] : null;
    if (target) {
      const need = lengthEq ? Number(lengthEq[2]) : Number(lengthGt[1]) + 1;
      const have = pushes.get(target) || 0;
      for (let k = have; k < need; k++) emitted.push({ stmt: `${target}.push()` });
      pushes.set(target, Math.max(have, need));
      continue;
    }

    // A bound on a parameter: pick the smallest witness and grow the
    // array to match.
    const paramBound = conjunct.match(/^(\w+)\s*<\s*([\w.[\]]+)\.length$/);
    if (paramBound && params.has(paramBound[1]) && !declared.has(paramBound[1])) {
      declared.add(paramBound[1]);
      emitted.push({
        stmt: `${params.get(paramBound[1])} ${paramBound[1]} = 0`,
        witness: `${paramBound[1]} = 0`,
      });
      const have = pushes.get(paramBound[2]) || 0;
      if (have < 1) {
        emitted.push({ stmt: `${paramBound[2]}.push()` });
        pushes.set(paramBound[2], 1);
      }
      continue;
    }

    // `require(b == minusTwo)`: the bound is a local already in scope
    // (solkey uses one when a negative literal cannot appear directly in
    // the condition), so the parameter is declared as a copy of it.
    const aliasEquality = conjunct.match(/^(\w+)\s*==\s*([A-Za-z_]\w*)$/);
    if (
      aliasEquality &&
      params.has(aliasEquality[1]) &&
      !declared.has(aliasEquality[1]) &&
      declared.has(aliasEquality[2])
    ) {
      declared.add(aliasEquality[1]);
      emitted.push({
        stmt: `${params.get(aliasEquality[1])} ${aliasEquality[1]} = ${aliasEquality[2]}`,
        witness: `${aliasEquality[1]} = ${aliasEquality[2]}`,
      });
      continue;
    }

    const paramPositive = conjunct.match(/^(\w+)\s*>\s*(\d+)$/);
    if (paramPositive && params.has(paramPositive[1]) && !declared.has(paramPositive[1])) {
      declared.add(paramPositive[1]);
      const witness = Number(paramPositive[2]) + 1;
      emitted.push({
        stmt: `${params.get(paramPositive[1])} ${paramPositive[1]} = ${witness}`,
        witness: `${paramPositive[1]} = ${witness}`,
      });
      continue;
    }

    kept.push(conjunct);
  }

  return { emitted, kept };
}

// ───────────────────────── statement translation ────────────────────────

/**
 * Translate one function body into the statement list of a judgment.
 * Throws `Unsupported` with a reason when a construct has no
 * counterpart in the `sol_stmt` grammar.
 */
class Unsupported extends Error {}

/**
 * An assertion no state satisfies: `assert(false)`, or `assert(e != e)`.
 *
 * solkey writes one only after a statement it expects to *revert* — an
 * out-of-bounds index, a `require(false)` — and tags the function
 * `@custom:key box`, under which the reverting execution discharges the
 * obligation vacuously. That is precisely what this port cannot express:
 * rule 1 makes every judgment a diamond, so the program must also not
 * revert, and the whole content of such a function is that it does. It is
 * not a gap in the calculus and it is not a proof that failed, so it is not
 * `open` — recording it as one would put four rows in the scoreboard that
 * no amount of work on the rules could ever move.
 */
function assertsUnsatisfiable(body) {
  return /\bassert\s*\(\s*false\s*\)/.test(body) ||
    /\bassert\s*\(\s*([A-Za-z_]\w*)\s*!=\s*\1\s*\)/.test(body);
}

function translateFunction(fn, contract) {
  if (fn.boxed && assertsUnsatisfiable(fn.body)) {
    throw new Unsupported(
      "the function asserts that the program reverts (a box-only obligation): " +
        "every judgment here is a diamond, which proves the opposite",
    );
  }
  const renames = RENAMES[contract] || {};
  const globals = GLOBAL_TYPES[contract] || {};
  const params = new Map(fn.params.map((p) => [p.name, p.ty]));
  const declared = new Set();
  const pushes = new Map();
  const memoryAliases = new Map();
  const storageAliases = new Map();
  const localRenames = new Map();
  const witnesses = [];
  const out = [];

  /** Translate a `;`-separated run of statements (an `if` block body). */
  const translateBlock = (body) =>
    body
      .split(";")
      .map((s) => s.trim())
      .filter(Boolean)
      .map((s) => translateStatement(`${s};`, true))
      .join("; ");

  for (const rawStatement of statementsOf(fn.body)) {
    const emitted = translateStatement(rawStatement, false);
    if (emitted !== null) out.push(emitted);
  }

  /**
   * Translate one statement, returning the judgment text or null when
   * the statement produced its output directly (a `require` expands into
   * declarations and `push`es appended to `out`, or into nothing).
   */
  function translateStatement(rawStatement, inBranch) {
    if (!rawStatement.endsWith(";") && !rawStatement.endsWith("}")) {
      throw new Unsupported(`statement does not end in ';': ${rawStatement}`);
    }
    if (/\bnew\s+\w+\[\]/.test(rawStatement)) {
      throw new Unsupported("`new T[](n)` array allocation is not in the fragment");
    }
    if (/^(for|while|do)\b/.test(rawStatement)) {
      throw new Unsupported("loops have no rule in the calculus");
    }
    if (/^return\b/.test(rawStatement)) {
      throw new Unsupported("`return` is not in the fragment");
    }

    // `if (c) { … } else { … }` — the branches are translated with the
    // same rules and rejoined with the `;` separator the grammar uses.
    const branch = parseIf(rawStatement);
    if (branch) {
      const condition = parenthesizeComparisons(
        applyRenames(branch.condition, renames),
      );
      const thenPart = translateBlock(branch.thenBody);
      return branch.elseBody === null
        ? `if (${condition}) { ${thenPart} }`
        : `if (${condition}) { ${thenPart} } else { ${translateBlock(branch.elseBody)} }`;
    }

    const statement = applyRenames(rawStatement.replace(/;$/, ""), renames);

    // require(...)
    const require_ = statement.match(/^require\((.*)\)$/);
    if (require_) {
      if (inBranch) {
        throw new Unsupported("`require` inside an `if` branch is not handled by the port");
      }
      const { emitted, kept } = dischargeRequire(require_[1], params, declared, pushes);
      for (const e of emitted) {
        out.push(e.stmt);
        if (e.witness) witnesses.push(e.witness);
      }
      return kept.length > 0
        ? `require(${parenthesizeComparisons(kept.join(" && "))})`
        : null;
    }

    // assert(...)
    const assert_ = statement.match(/^assert\((.*)\)$/);
    if (assert_) {
      return `assert(${parenthesizeComparisons(rewriteDecrements(assert_[1]))})`;
    }

    // Declarations: `T [memory|storage] name = expr` or `T [memory] name`.
    const decl = statement.match(
      /^([\w[\]]+)(?:\s+(memory|storage))?\s+(\w+)(?:\s*=\s*(.*))?$/,
    );
    if (decl && (VALUE_TYPES.has(decl[1]) || decl[2] || /^[A-Z]/.test(decl[1]))) {
      const [, rawTy, location, name, init] = decl;
      const ty = ARRAY_TYPE_NAMES[rawTy] || rawTy;

      if (location === "memory" && !VALUE_TYPES.has(rawTy)) {
        // Memory locals are renamed to `mv`/`mv2`/…: `aliasKind` is a
        // name→kind table, and only those names resolve to `Kind.memory`.
        // Their *uses* take the `mv@Type` form, like storage aliases —
        // `rootExpr` hardwires a type to each bare name (`carol` is a
        // `Person`), so a bare `mv` would be read at the wrong type.
        const alias = ["mv", "mv2", "mv3", "mv4"][memoryAliases.size];
        if (!alias) throw new Unsupported("more memory locals than `aliasKind` names");
        memoryAliases.set(name, { alias, ty });
        // As for storage: the binder is protected from the alias rewrite,
        // only uses take the `mv@Type` form.
        return init === undefined
          ? { protect: `${ty} memory ${alias}`, rest: "" }
          : { protect: `${ty} memory ${alias} = `,
              rest: parenthesizeComparisons(init) };
      }

      if (location === "storage") {
        // The declaration binds the name; only *uses* take the `name@Type`
        // form, so the binder is protected from the alias rewrite.
        storageAliases.set(name, ty);
        return { protect: `${ty} storage ${name} = `,
                 rest: parenthesizeComparisons(init) };
      }

      const local = RESERVED_ROOTS.has(name) ? `v_${name}` : name;
      if (local !== name) localRenames.set(name, local);
      declared.add(local);
      return init === undefined
        ? `${ty} ${local}`
        : `${ty} ${local} = ${renameLocals(rewriteDecrements(parenthesizeComparisons(init)))}`;
    }

    if (/^delete\s+/.test(statement)) {
      return `delete ${renameLocals(statement.slice(7).trim())}`;
    }

    return renameLocals(rewriteDecrements(parenthesizeComparisons(statement)));
  }

  /**
   * Rewrite references to locals into the typed-alias form `name@Type`,
   * which carries the type explicitly instead of looking it up in
   * `rootExpr`'s hardwired name→type table.
   */
  function renameLocals(expr) {
    if (expr === undefined) return expr;
    let out = applyGlobals(expr, globals);
    for (const [from, to] of localRenames) {
      out = out.replace(new RegExp(`(?<![.\\w])${from}\\b(?![@\\w])`, "g"), to);
    }
    for (const [from, { alias, ty }] of memoryAliases) {
      out = out.replace(new RegExp(`(?<![.\\w])${from}\\b(?!@)`, "g"),
                        `${alias}@${ty}`);
    }
    for (const [name, ty] of storageAliases) {
      out = out.replace(new RegExp(`(?<![.\\w])${name}\\b(?!@)`, "g"),
                        `${name}@${ty}`);
    }
    return out;
  }

  // Late pass, so that a name declared as an alias is rewritten in the
  // statements emitted before the declaration was seen as well. Binders
  // carry their `protect` prefix through untouched.
  const statements = out.map((s) =>
    typeof s === "string" ? renameLocals(s) : s.protect + renameLocals(s.rest),
  );

  const unconstrained = [...params.keys()].filter((p) => !declared.has(p));
  if (unconstrained.length > 0) {
    throw new Unsupported(
      `parameter(s) ${unconstrained.join(", ")} are not pinned by any require, ` +
        "so no concrete witness is derivable",
    );
  }

  return { statements, witnesses };
}

// ───────────────────────────── emission ─────────────────────────────────

function leanName(contract, fn) {
  return `solkey_${contract.replace(/^Solc/, "solc_")}_${fn}`;
}

function main() {
  const tsvDir = join(REPO, "tests/solkey");
  const leanDir = join(REPO, "Solidity/Examples/Solkey");
  const calculusDir = join(REPO, "Solidity/Examples/Derivations/Solkey");
  mkdirSync(tsvDir, { recursive: true });
  mkdirSync(leanDir, { recursive: true });
  mkdirSync(calculusDir, { recursive: true });

  const expected = [];
  const expectedCalculus = [];
  const modules = [];
  const calculusModules = [];

  for (const { file, suite, store } of CONTRACTS) {
    const contract = basename(file, ".sol");
    const source = readFileSync(join(SOLKEY, file), "utf8");
    const functions = parseContract(source);

    const theorems = [];
    const calculusTheorems = [];
    const wantsCalculus = CALCULUS_CONTRACTS.has(contract);

    for (const fn of functions) {
      const key = `${contract}.${fn.name}`;
      if (UNSUPPORTED[key]) {
        expected.push([suite, contract, fn.name, "unsupported", UNSUPPORTED[key], ""]);
        if (wantsCalculus) {
          expectedCalculus.push([suite, contract, fn.name, "unsupported",
                                 UNSUPPORTED[key], ""]);
        }
        continue;
      }

      let translated;
      try {
        translated = translateFunction(fn, contract);
      } catch (error) {
        if (!(error instanceof Unsupported)) throw error;
        expected.push([suite, contract, fn.name, "unsupported", error.message, ""]);
        if (wantsCalculus) {
          expectedCalculus.push([suite, contract, fn.name, "unsupported",
                                 error.message, ""]);
        }
        continue;
      }

      const { statements, witnesses } = translated;
      const judgment = `< ${statements.join(";\n  ")} > (true)`;
      const note =
        witnesses.length > 0
          ? `concretized: solkey proves this for all parameters; ported at ${witnesses.join(", ")}`
          : "";
      // The verdict is not the translator's to decide: `pending` is
      // replaced by the observed `proved`/`open` by
      // scripts/check-solkey-parity.sh --update.
      expected.push([suite, contract, fn.name, "pending", note, ""]);

      const docLines = [
        `solkey \`${key}\` (${file}).`,
        ...(fn.doc.length > 0 ? ["", ...fn.doc] : []),
        ...(note ? ["", note + "."] : []),
        ...(fn.boxed
          ? ["", "solkey tags this `@custom:key box`; the port makes the assumptions", "true instead, so the diamond also proves that it does not revert."]
          : []),
      ];
      theorems.push(
        `/-- ${docLines.join("\n")} -/\ntheorem ${leanName(contract, fn.name)} :\n` +
          `    (sol!{ ${judgment.replace(/\n  /g, "\n             ")} }).Holds\n` +
          `      State.${store} := by\n  sol_wp`,
      );

      if (wantsCalculus) {
        expectedCalculus.push([suite, contract, fn.name, "pending", note, ""]);
        calculusTheorems.push(
          `/-- ${docLines.join("\n")} -/\n` +
            `sol_calculus ${leanName(contract, fn.name)} from State.${store}\n` +
            `  { ${statements.join(";\n    ")} }`,
        );
      }
    }

    const moduleName = `Solidity.Examples.Solkey.${contract}`;
    modules.push(moduleName);
    writeFileSync(
      join(leanDir, `${contract}.lean`),
      [
        "import Solidity.Wp.Verifier",
        "",
        "/-!",
        `# solkey \`${file}\`, ported`,
        "",
        "Generated by `scripts/solkey-port.mjs` from the solkey source of",
        "truth; do not edit by hand. See that script for the translation",
        "rules and `docs/solkey-parity.md` for the functions that are not",
        "here and why.",
        "-/",
        "",
        "namespace Solidity",
        "namespace Solkey",
        `namespace ${contract}`,
        "",
        "open Semantics Wp",
        "",
        "set_option maxHeartbeats 8000000",
        "",
        theorems.join("\n\n"),
        "",
        `end ${contract}`,
        "end Solkey",
        "end Solidity",
        "",
      ].join("\n"),
    );
    if (wantsCalculus) {
      const parts = [];
      for (let i = 0; i < calculusTheorems.length; i += CALCULUS_PART_SIZE) {
        parts.push(calculusTheorems.slice(i, i + CALCULUS_PART_SIZE));
      }
      const partDir = join(calculusDir, contract);
      mkdirSync(partDir, { recursive: true });
      parts.forEach((part, index) => {
        const partName = `Part${String(index + 1).padStart(2, "0")}`;
        calculusModules.push(
          `Solidity.Examples.Derivations.Solkey.${contract}.${partName}`,
        );
        writeFileSync(
          join(partDir, `${partName}.lean`),
          [
            "import Solidity.Examples.Common",
            "import Solidity.Semantics",
            "",
            "/-!",
            `# solkey \`${file}\`, by the rule table alone — ${partName}`,
            "",
            `Obligations ${index * CALCULUS_PART_SIZE + 1}-${index * CALCULUS_PART_SIZE + part.length} of ${calculusTheorems.length}.`,
            "",
            "The same obligations as `Solidity/Examples/Solkey/" + contract +
              ".lean`,",
            "proved without the interpreter doing the symbolic execution:",
            "`sol_calculus` drives each program with the taclets of `Rules.lean`",
            "until no line of the frontier has a statement left, and decides the",
            "frontier reached.",
            "",
            "That is the difference worth the second corpus. `sol_wp` never reads",
            "the rule table, so the corpus beside this one says the *interpreter*",
            "agrees with solkey; a chain here says the *calculus* does, which is",
            "the artefact that corresponds to a KeY proof.",
            "",
            "What is left at the end is first-order: the accumulated update",
            "applied to the store, and one obligation line per `assert` — KeY's",
            "own shape, since `Rules.assertGoals` leaves the violated branch as",
            "an obligation rather than a revert.",
            "",
            "The split into parts is an elaboration cost, nothing else: they",
            "reopen one namespace and are independent files over the same cached",
            "dependencies, so `scripts/check-calculus-parity.sh` runs them",
            "concurrently.",
            "",
            "Generated by `scripts/solkey-port.mjs` from the solkey source of",
            "truth; do not edit by hand. Verdicts are pinned in",
            "`tests/solkey/expected-calculus.tsv`, and `docs/calculus-parity.md`",
            "is the scoreboard.",
            "-/",
            "",
            "namespace Solidity",
            "namespace Calculus",
            `namespace ${contract}`,
            "",
            "open Semantics SoliditySyntax StandardExample Rules",
            "",
            "set_option maxHeartbeats 8000000",
            "",
            part.join("\n\n"),
            "",
            `end ${contract}`,
            "end Calculus",
            "end Solidity",
            "",
          ].join("\n"),
        );
      });
    }
  }

  // The `.key` suites: hand-written modules, but every obligation is
  // accounted for in expected.tsv.
  for (const { contract, suite, dir, ported, reason } of KEY_SUITES) {
    const problems = readdirSync(join(SOLKEY, dir))
      .filter((f) => f.endsWith(".key"))
      .map((f) => basename(f, ".key"))
      .filter((name) =>
        readFileSync(join(SOLKEY, dir, `${name}.key`), "utf8").includes("\\problem"),
      )
      .sort();

    for (const name of problems) {
      expected.push(
        ported[name]
          ? [suite, contract, ported[name], "pending", `solkey ${name}.key`, ""]
          : [suite, contract, name.replace(/-/g, "_"), "unsupported", reason(name), ""],
      );
    }
    const module = `Solidity.Examples.Solkey.${contract}`;
    if (!modules.includes(module)) modules.push(module);
  }

  writeFileSync(
    join(REPO, "SolidityCorpus.lean"),
    modules.map((m) => `import ${m}`).join("\n") + "\n",
  );

  writeFileSync(
    join(tsvDir, "expected.tsv"),
    expected.map((row) => row.join("\t")).join("\n") + "\n",
  );

  writeFileSync(
    join(REPO, "SolidityCalculus.lean"),
    calculusModules.map((m) => `import ${m}`).join("\n") + "\n",
  );

  writeFileSync(
    join(tsvDir, "expected-calculus.tsv"),
    expectedCalculus.map((row) => row.join("\t")).join("\n") + "\n",
  );

  const tally = expected.reduce((acc, [, , , status]) => {
    acc[status] = (acc[status] || 0) + 1;
    return acc;
  }, {});
  console.log(`${expected.length} obligations:`, tally);
  console.log(`${expectedCalculus.length} of them also as rule-table chains`);
}

main();
