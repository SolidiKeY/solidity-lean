# Proving solkey's TestSuite by `⊢`

The goal: every obligation of solkey's `TestSuite.sol`, stated as solkey's
`SolidityProblemSynthesizer` states it and derived with `⊢`, checked by the
kernel, at close to KeY's speed. No dependencies, no `native_decide`, no
`maxHeartbeats` override, and a `?` twin that prints a cheap replay for every
searching tactic.

**Status.** `TestSuite/Report.lean` pins it (`#solkey_obligations`): at
solkey `473da8944c`, 617 functions, 552 derived, none pending; the 65 others
are internal helpers, two `skip` rows, one excluded and the refuted ones
(`TestSuite/Refuted.lean`). `node scripts/check-automatic.mjs --strict` is
the gate that every obligation is closed by `sol_prove` or `sol_refute`
(`docs/automation.md`).

## Decisions

- **Box meaning.** A failed `assert` is a Panic halt (`THalt.panic`, solc's
  `Panic(0x01)`), distinct from a `require` revert, and no modality holds of
  it. solc's other panics (overflow, a zero divisor, an index out of bounds,
  `pop` of an empty array) stay reverts, as in KeY, where a box accepts them.
  Only an `assert` panics (`Prog.run_noPanic`, `Semantics/NoPanic.lean`).
- **The obligations** (`Problem.fml`, `Calculus/Problem.lean`): box
  `∀x̄. wt(storage) → [ f(x̄); ] true` (KeY's "Violated" obligation, no cut
  needed) and diamond `∀x̄. wt(storage) → ⟨ f(x̄); ⟩ true`; a specified
  function or constructor as `spec!` states it.
- **The `wt(storage)` premise.** solkey's `storage` is a free `Struct` term;
  here it is any state of the interpreter, so the premise says it is one the
  contract can be in: the model's own reachability assumption, not KeY's.
  Both modalities carry it, so neither is read over storages the contract
  can never be in. A derived obligation therefore need not imply solkey's: `assert(total >= 0)` on a `uint total` holds under `wt`. It is one
  atomic symbol (`Op1.wt`, `Fml.wt`), read as `Storage.wtB`
  (`Semantics/StorageWt.lean`, a fold the kernel evaluates: every root
  canonical and tight, every mapping key in range); `wt_iff_reachable`: for
  TestSuite's roots it holds exactly of the reachable storages. An `Op1` and not a formula: a
  new `Fml` constructor touches every traversal, and an expanded layout
  (`∀` per root and member) gives every leaf quantifiers to instantiate.
  `initState_wt`: the initial state passes it.
- **Parameters** are `Fml.all` binders over the type's range (`uint`
  `[0, 2²⁵⁶)`, `int` the signed 256-bit range, `bool`); KeY's `int` is
  unbounded. The width is not bound: an `int8` parameter ranges over the
  256-bit range, which makes the obligation stronger than Solidity's.
- **One front end.** solc's JSON AST → normalized `sol` text → the
  `contract!`/`sol_raw!` macros. The printer normalises what the grammar
  spells differently (folded literals and units, `payable(…)` stripped,
  `−−`, `bool` keys as `b ? 1 : 0`). A function the model has no
  counterpart for is `excluded` (`Gap.excluded`: the struct recursive
  through a mapping, `recursiveStructMapping`); one the printer or grammar
  lacks is `unsupported`.
- **What counts as derived.** `N.f.proved : ⊢ N.f.problem`, compared as an
  expression, using no axiom but `propext`, `Classical.choice` and
  `Quot.sound` (`standardAxioms`, `Frontend/Problems.lean`; otherwise listed
  "unsound"); refuted: `N.f.refuted : ¬ (⊢ N.f.problem)`. A pending
  obligation has no theorem and no `sorry`.
- **A replay fits one declaration.** Each leaf try of a search runs with its
  own heartbeats, so a search can succeed where the replay does not:
  `Derive.replayFits` compares their sum with `maxHeartbeats`, and
  `#solkey_derive?` reports such a statement pending. An obligation whose
  leaves each close but together pass the limit is declared by
  `sol_auto_theorem` instead (`TestSuite/Derived20.lean`).
- **The length delta.** The model's `push` never panics (at `2^256 - 1`
  elements it is out of gas, which every modality accepts) and `wt` bounds no
  length, while solc's `push` panics (0x41) at length `2^64`.
  `storagePushLengthPositive`, `storagePopUnknownLength` and
  `arrayOfMappingsIndex` push with no bound before them: derived, true of
  solkey, false of solc from such a storage. Closing it is a bound in `wt`
  and the panic in the push, a semantic change of its own
  (`docs/solc-alignment.md`, "No bound on a dynamic array's length").

## The pipeline

| Step | Where | Command |
|---|---|---|
| the fixture: soljson 0.8.34 (sha256 checked against solkey's `build.gradle`) on `TestSuite.sol` of the snapshot, trimmed, with a header naming compiler, source sha256 and solkey commit | `tests/solc/TestSuite.ast.json` | `node scripts/solc-ast.mjs --solkey <checkout> --soljson <dir>` (rewrites the hash literal of the importing module; `--source`/`--out`/`--wrapper` for another fixture); `./scripts/check-solc-ast.sh [--compare-cache]` re-derives and diffs it |
| the import: the contract and every body, one `evalExpr` | `Solkey/TestSuite.lean` | `solc_import "…" hash 0x… as Solkey.TestSuite renaming Triple => FixedTriple`; a fixture of another hash is refused |
| the statements `N.f.problem : Fml _ []` on the scoped programs | `TestSuite/ScopedProblems.lean`, `TestSuite/Problems.lean` | `solc_scoped_problems`; `#solkey_problem` prints one in solkey's `--print-problem` syntax |
| the theorems | `TestSuite/Derived*.lean`, `TestSuite/Refuted.lean` | `#solkey_derive? N [only f] [from i] [count k] [timed] [pending]` prints each `N.f.proved` with its replay; `#solkey_scan N [walk]` lists the leaves of the walk |
| the pin | `TestSuite/Report.lean` | `#solkey_obligations N` |
| `#solkey_derive?` pins | `TestSuite/Suggestions.lean` | imported only by the library root, so its searches run beside the `Derived` modules |
| the corpus table and corollaries | `tests/solkey/expected.tsv`, `Corpus/TestSuite.lean`, `docs/corpus-parity.md` | `node scripts/solkey-port.mjs` (generated, never hand-edited) |
| the audit | | `./scripts/check-testsuite.sh [--complete] [--solkey <examples>]` |

`lake build SolkeyTestSuite` builds the fixture's chain; `./run-lean.sh`
runs it. A body that exhausts its heartbeats or recursion depth is a row,
not a failed import. Bodies are elaborated with info trees off (the server
would otherwise keep every expansion, anchored at the command).

## The corpus table (M7 integration)

The corpus and the `⊢` derivations tell one story.

- `scripts/solkey-port.mjs` does not translate `TestSuite.sol`: it reads the
  rows off two pins with no Lean run, `Report.lean` and the import's summary
  in `Solkey/TestSuite.lean`, finds the theorems in `Solidity/TestSuite/`,
  and fails when the pins disagree with the source or each other, or when
  the source's sha256 is not the fixture's `sourceSha256`.
- `Corpus/TestSuite.lean` states each derived obligation with no parameters
  at `Solkey.TestSuite.initState`, as `diamond_of_proved`/`box_of_proved` of
  its theorem and `initState_wt` (`Corpus/Imported.lean`); those with
  parameters are checked by `Report.lean`'s pin. They are not stated at the
  hand-written contract's store, which lacks some roots and fails `wt`.
  `testSuite_agrees` (`decide +kernel`, no axioms) checks that every root of
  the hand-written `TestSuite` is a root of `Solkey.TestSuite` at the same
  type.
- The other corpus suites (`Corpus/Solc*.lean`) are runs decided by the
  kernel at the default heartbeats: each `corpus_decide` takes about 100 ms
  (the `rw`, the `Decidable` instance and the kernel, 30–40 ms each).
- `check-testsuite.sh` checks, with node only: no `native_decide`,
  `decide +native`, `sorry`, `admit`, `maxHeartbeats` or `skipKernelTC` in
  the code of `Solidity/TestSuite/` and `Solidity/Solkey/`; no
  `unsound`/`mismatched`/`unstated` theorem in the pin; and parity: the
  stated rows are solkey's `testSuiteFunctions` (every public or external
  function not tagged `skip`, as `SolidityOutline.functionsOf` reads the
  header), and the table is what the generator writes. `--complete` also
  fails while a row is pending.

## How a derivation is checked

`sol_prove` is reflective (`Calculus/ProvesDerive.lean`): the walk of the
strategy is a function (`Seq.residue`), run as compiled code (one
`evalExpr`), and the kernel checks one auxiliary equation by `Eq.refl` (the
residue is `some [leaves]`), which `Proves.of_residue`/`of_residueWithin`
turn into `⊢ φ`. The leaves are closed by the closer inside the residue or
left as goals `leafᵢ` for a leaf tactic. The proof term is assembled
directly, so the elaborator never unfolds the program.

- **Keep the head out of the elaborator's reach.** `Proves` is an inductive,
  so `⊢ φ` is safe; a reducible wrapper over a closed program must not be
  the target of `apply` or of an elaborated term (see "Measured costs").
- **Budgets.** The compiled run and the kernel check are out of reach of
  `maxHeartbeats`, so the walk carries its own: `Derive.budget` (20000
  steps, every branch counted). A leaf is admitted to the closer only within
  the size bounds of `Calculus/ReadBounds.lean`
  (`docs/solkey-migration.md`, "Read bounds"); a leaf past them is left for
  a tactic, not attempted.
- **Ground splits are pruned.** A split whose branch the context refutes
  under its updates keeps only the other branch; the refuted one is closed by
  `Proves.closeFalse` (`refuteLanded`). `closeFalse` is a deviation in shape
  from KeY's (`dl{ ..Γ ⟹ false }` gives any `φ`): solkey derives it by `cut`
  on `false`, so `Proves.toSolkey` keeps it. `sol_derive` and the proof tree
  do not prune.

## Measured costs

How to measure: copy the file to a scratch module with
`set_option Elab.async false`, time it by `IO.monoMsNow` (or
`IO.getNumHeartbeats`) at its first and last command or around each
declaration, interleave runs against master, and record the load average.
Heartbeats are the regression criterion; wall clock under other lanes' load
is only informative (two master runs differed by 22%). `Elab.async false`
sometimes crashes a worker; repeat under a fresh file name.

- **The kernel is not the cost; the elaborator's `whnf` is.** A 10-statement
  run decided against a reducible `Diamond` target took 2.2 s and 169k
  heartbeats in `apply`'s `whnf` (the program run in `Meta.whnf`); behind an
  `@[irreducible]` head the same proof took 38 ms.
- **Kernel work counts toward the heartbeat counter but the limit does not
  stop it** (v4.24): a `decide +kernel` of 12.1k passes at `maxHeartbeats
  5000`; elaborator work after it in the same declaration still sees the
  higher count.
- **`decide +kernel` caches by proposition**: a second proof of the same
  proposition costs 1 ms, so a measurement needs a fresh term.
- **The import.** `sol[C]{…}` costs 20–25 ms per program (one `evalExpr`
  each); `solc_import` does one for all bodies: about 8 s for 417 bodies at
  M2, 3.6 s of it compiling the programs, which `sol_prove` evaluates.
- **Reductions grow with storage writes.** `count = 0;` then `n` times
  `count += 1;`: the tree after `toL` is 310, 1374, 5678, 22942, 92046 nodes
  for `n` = 2, 4, 6, 8, 10, its reduction 1071 to 2.5 million, the kernel
  check 0.8 s at 4 and 49.5 s at 10. Below a `delete` the tree grows
  linearly while the reduction triples per delete. Hence two bounds, the
  tree a cheap first test and the reduction second.
- **Strict arguments in compiled code are exponential.** An elimination arm
  that passes two recursive calls on the same storage as strict arguments
  does `2^k` calls for `k` array operations (twelve interleaved pushes onto
  two arrays: 106 s); computing them only where the relation reads them took
  it to 7 ms. The kernel and the proofs see the plain definitions.
- **Literal powers** fold only with an exponent at most `256`
  (`Calculus/Decide.lean`): `Int.pow` recurses once per unit of the
  exponent, compiled and in the kernel, heeding no heartbeats.
- **Axiom collection.** `#solkey_obligations` collects axioms once for all
  theorems (one shared traversal), per theorem only when the union is not
  standard. A `do` that hoisted `← collectAxioms t` out of an `||` ran it
  for every theorem: nine minutes instead of about 1 s.
- **Speed commits in the closer** (`7541cad`, `2ff6a0f`, `16d0a9b`,
  `02f363b`): check `git log` before changing a representation they touch.
