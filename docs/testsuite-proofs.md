# Proving solkey's TestSuite by `⊢`

The goal: every obligation of solkey's `TestSuite.sol` (418 functions, 2 more
tagged skip), stated as solkey's `SolidityProblemSynthesizer` states it and
derived with `⊢`, checked by the kernel, at close to KeY's speed. No
dependencies, no `native_decide`, no new `maxHeartbeats` override, and a `?`
twin that prints a cheap replay for every searching tactic.

Today the corpus (`Corpus/TestSuite.lean`) decides each function's run at one
concrete store (`corpus_decide`); none is proved by `⊢`.

## Decisions (2026-10-05)

- **Box meaning.** Follow Solidity and solkey exactly: a failed `assert` is a
  Panic halt, distinct from a `require` revert, and the box does not hold on
  it. This is a semantic change, made even though many files move.
- **Diamond premise.** One atomic `wt(storage)` symbol (canonical and tight
  storage, KeY's `wellFormed(heap)`), not an expanded layout.
- **Front end.** solc's JSON AST → normalized `sol` text → the existing
  `contract!`/`sol_raw!` macros: one lowering path.
- **Scope.** M0 and M1, then M2 (done, below).

## Measurements (2026-10-05)

One scratch module importing `Corpus/Basic.lean` and the Counter and Mapping
benchmarks, `Elab.async false`, each command or tactic wrapped in an
`IO.monoNanosNow`/`IO.getNumHeartbeats` timer. Heartbeats are in
`maxHeartbeats` units (thousands of raw heartbeats); the default limit is
200000. Times are wall clock on this machine, warm.

| What | Where | Time | Heartbeats |
|---|---|---:|---:|
| corpus, 5 statements (`additionStorageWrite`), default limit | `corpus_decide`, whole theorem | 140 ms | 3.5k |
| corpus, 10 statements (`testStorageStructDeleteSkipsMappingMember`), default limit | `corpus_decide`, whole theorem | 2.56 s | 172.5k |
| ⤷ its `rw [testSuiteStore_eq]` | | 1 ms | 0.02k |
| ⤷ its `apply diamond_of_isOk` | elaborator `whnf` of the `Diamond` target | 2.2 s | 169.4k |
| ⤷ the same, as a term `@diamond_of_isOk … h` | elaborator `whnf` of the expected type | 2.4 s | 169.5k |
| same shape, fresh program, target behind an `@[irreducible]` head | `diamondI_of_isOk (by decide +kernel)` | 38 ms | 0.54k |
| ⤷ the same at `maxHeartbeats 1000` | | passes | 0.54k |
| a false run (`assert` flipped) | `decide +kernel` rejects it | 41 ms | 0.54k |
| kernel only: `(List.replicate 20000 1).foldl (·+·) 0 = 20000` | `decide +kernel` | 0.9 s | 12.1k |
| ⤷ the same at `maxHeartbeats 5000` | | passes | 12.1k |
| `sol[TestSuite]{…}`, 5 statements | one `evalExpr` + quote | 20 ms | 0.49k |
| `sol[TestSuite]{…}`, 10 statements | one `evalExpr` + quote | 24 ms | 0.71k |
| `dl!{…}` over Counter's `inc()` | | 12 ms | 0.29k |
| Mapping `set_frame`, `⊨`: `sol_symex` | `symex_valid 200` | 10 ms | 0.26k |
| ⤷ `inL` check | `decide +kernel` | 18 ms | 0.25k |
| ⤷ `sol_reduce` | | 3 ms | 0.13k |
| ⤷ the leaf by `LFml.syn` | `decide +kernel` | 58 ms | 0.86k |
| ⤷ whole theorem | | 133 ms | 2.2k |
| Mapping `set_frame`, `⊢`: `sol_derive` + leaves | 76 + 20 ms | 143 ms | 3.1k |
| Counter `spec!{dec}`, `⊨`: `sol_symex; sol_decide` | 12 + 93 ms | 152 ms | 2.4k |
| Counter `spec!{dec}`, `⊢`: `sol_derive` + leaves | 63 + 24 ms | 139 ms | 2.9k |
| Counter `c == count → [inc();] count == c + 1`, `⊨`: `sol_symex; sol_decide` | `LFml.syn` says no (36 ms), `sol_decide_cons` closes | 691 ms | 19.0k |
| ⤷ the same with `sol_close` | | 939 ms | 27.8k |
| ⤷ `⊢`: `sol_derive` + leaves | 48 + 623 ms | 735 ms | 19.7k |

What they say:

- **The kernel is not the cost.** Deciding a 10-statement run in the kernel
  takes about 40 ms. The 2.5 s of the corpus theorem is the elaborator
  unfolding the reducible `Diamond` target to see whether it is a `∀`
  (`apply`'s argument count, the term elaborator's implicit-lambda check),
  which runs the program in `Meta.whnf`. Behind an irreducible head the
  same proof costs 38 ms. This is what the corpus's file-wide
  `maxHeartbeats 8000000` pays for.
- **Kernel work counts toward the heartbeat counter but the limit does not
  stop it** (v4.24): a `decide +kernel` that allocates 12.1k passes at
  `maxHeartbeats 5000`. Elaborator work after it, in the same declaration,
  still sees the higher count.
- **`decide +kernel` caches by proposition.** A second proof of the same
  proposition in a file costs 1 ms; a measurement needs a fresh term.
- **`sol[C]{…}` costs 20–25 ms per program**, so 418 programs cost about
  10 s. Avoiding the per-program `evalExpr` is worth doing but is not the
  bottleneck.
- **`⊢` by `sol_derive` costs the same as `⊨` by `sol_symex`** on these
  obligations. Where `LFml.syn` closes the leaf, a whole obligation is about
  140 ms; where it falls back to `sol_decide_cons`, about 700 ms, nearly all
  in the fallback.

## Milestones

- **M0.** Measure (this section); re-pin the corpus at solkey `100f7f24c3`
  with `modality`/`bucket` columns in `tests/solkey/expected.tsv`.
- **M1.** A reflective driver, `Derive.residue` with `Proves.of_residue`: one
  kernel evaluation runs the strategy and the closer per obligation;
  `sol_prove` replays, `sol_prove?` searches the residue's leaves.
- **M2.** solc JSON front end at elaboration time: pinned soljson 0.8.34, a
  checked-in fixture, `solc_import` defining the whole TestSuite contract
  with one `evalExpr`.
- **M3.** Obligation forms: diamond under `wt(storage)`, box with the Panic
  halt, parameters as `∀` over their type's range.  **M3a** (the Panic halt)
  is done, below; M3b (`wt`, the obligation statements) is next.
- **M4.** Closer for locals, plain storage and `try`/`transfer`: ground
  arithmetic, `applyEq`, bool case splits, difference bounds, `wt` facts.
- **M5.** Push, pop, `delete` and storage copies in the closer.
- **M6.** Memory in the closer: allocation, reads and writes, `mlen`,
  defaults, copies to storage.
- **M7.** The remaining functions; a `derived` status in the corpus table;
  retire `corpus_decide`, the `#eval` rows and the 8M override.

## For M1

- Keep the obligation's head out of the elaborator's reach: `Proves` is an
  inductive, so `⊢ φ` is safe, but a reducible wrapper over a closed program
  (like `Diamond`) must not be the target of `apply` or of an elaborated term.
  `exact Proves.of_residue (by decide +kernel) …` elaborates against
  `Proves …` and never unfolds the program.
- Per leaf, the closer as a kernel `decide` costs 50–60 ms and under 1k
  heartbeats; a whole residue of a handful of leaves is well inside the
  budget, and the kernel part is not limited by it anyway. Deciding the
  whole residue at once is feasible; the risk is elaboration around it, not
  the kernel.
- The `sol_decide_cons` fallback (about 600 ms and 18k heartbeats per leaf)
  is the slow path to keep off the common case.

## M1 results (2026-10-05)

`Calculus/Derive.lean`. `Derive.residue n close b Γ φ` is `sol_derive`'s walk
as a function. It numbers fresh names per goal (`Hyp.fresh Γ φ`, as the
`Proves` constructors do), takes any number of `branches` outcomes, and
drops a leaf the closer accepts. `Proves.of_residue` is the soundness
theorem. The closer is `Derive.synClose`: modal-free, in `Fml.inL`, and
`LFml.syn` on the reduction.

`sol_prove` computes the residue with compiled code (one `evalExpr`). It
then has the kernel check one auxiliary lemma, as `decide +kernel` does:
`Derive.proves Γ φ = true` when nothing is left, or
`Derive.residue … = some [leaves]` (by `Eq.refl`) otherwise. It leaves one
goal per leaf (`leaf1`, …). It assembles the proof term directly, so the
elaborator never unfolds the program. `sol_prove?` adds one tactic per leaf
and suggests the replay. It tries `sol_decide`'s step after `LFml.syn`
(`sol_decide_cons`), then `sol_decide_heuristic`, `sol_close` and
`sol_spec_close`, each with its own heartbeats.

The compiled run and the kernel check are out of reach of `maxHeartbeats`,
so the walk carries a budget of its own: `b` counts the steps of the whole
derivation, every branch included, and `Derive.budget` (20000) stops it.
A function of 22 sequential `if`s (about 4 million paths) fails with
"the derivation takes more than 20000 steps" in about ten seconds. The
budget bounds the walk, not the closer: a leaf whose reduction grows with
its sequential storage writes (each `count += 1` reads the storage it
writes, so the reduced term doubles per write) is still unbounded inside
`LFml.syn`.

Setup: each benchmark theorem was stated twice in a scratch module, the
`sol_prove` replay first, the old `sol_derive` proof second, with
`Elab.async false`. Times are whole declarations (elaboration and kernel),
warm, in ms. Running the replay first gives the old proof any
`decide +kernel` cache hits.

| File | Theorems moved to `sol_prove` | `sol_prove` | `sol_derive` | Speed-up |
|---|---:|---:|---:|---:|
| Counter | 3 of 5 | 299 | 535 | 1.8× |
| Coin | 9 of 10 | 3438 | 5843 | 1.7× |
| ERC20 | 13 of 13 | 2837 | 5024 | 1.8× |
| Mapping | 11 of 14 | 2594 | 5553 | 2.1× |
| Purchase | 5 of 5 | 1781 | 4583 | 2.6× |
| EtherWallet | 4 of 4 | 1268 | 1756 | 1.4× |
| SimpleStorage | 4 of 4 | 255 | 578 | 2.3× |
| **total** | 49 of 55 | 12472 | 23872 | 1.9× |

Where `LFml.syn` closes every leaf, the speed-up is 1.6–4.6×: an obligation
takes 30–340 ms instead of 80–960 ms, at a fifth to a half of the
heartbeats. For
example, Counter `get_spec` takes 40 ms instead of 103, ERC20
`transfer_self` 110 instead of 247, Purchase `abort_spec` 237 instead of
787.

A leaf that needs `sol_decide_heuristic` gains from the replay naming that
step. Where the old proof closed it by `sol_decide`, the replay no longer
retries `sol_decide_cons` first: Mapping `remove_spec` takes 415 ms instead
of 719, `nested_remove_spec_true` 679 instead of 1530. EtherWallet
`withdrawOwner` closed its leaf by `sol_close`, which never tries
`sol_decide_cons`; it takes 562 ms instead of 688, from the residue's one
kernel evaluation and the named step in place of `sol_close`.

The six that keep `sol_derive` are dominated by their leaf, and `sol_prove`
does not beat them by more than about 5%:

| Theorem | `sol_prove` replay | `sol_derive` |
|---|---:|---:|
| Counter `inc_spec`, `dec_spec` (`sol_decide_cons` leaf) | 771, 764 | 755, 759 |
| Mapping `spec_set` (`sol_close` leaf) | 5352 | 5385 |
| Mapping `spec_remove` (`sol_spec_close` leaf) | 3614 | 3608 |
| Mapping `spec_nested_remove` (`sol_spec_close` leaf) | 5729 | 5929 |
| Coin `spec_mint` (hand-written leaf script) | 12644, 12588 | 13304, 13360 |

Coin `spec_mint` was measured under its existing 400k override for both,
in both orders (the second number with `sol_derive` first). The replay
gains 5–6%, inside the noise of the 12–13 s its leaves take, so the
theorem keeps `sol_derive`.

No heartbeat override was added. The aux-lemma kernel check stays far below
the limit, at about 0.5–5k heartbeats for a whole obligation.

`#print axioms` on `Proves.of_residue`, `Proves.of_proves`,
`Proves.of_synResidue`, Counter `spec_dec` and Counter `get_spec` gives
`propext`, `Classical.choice` and `Quot.sound`. There is no
`Lean.ofReduceBool` and no `sorryAx`.

## M2 results (2026-10-05)

The front end: `scripts/solc-ast.mjs` runs the soljson solkey pins
(0.8.34, its sha256 checked against solkey's `build.gradle`) under node on
`TestSuite.sol` at solkey `100f7f24c3` and writes the trimmed AST,
`tests/solc/TestSuite.ast.json` (1.8 MB, one line per statement), with a
header naming the compiler, the source's sha256 and the solkey commit.
`scripts/check-solc-ast.sh` regenerates and diffs it; given
`--compare-cache`, the script also compares it with solkey's own cached
solc output when solkey has compiled the same source (the cache key, the
sha256 of `SolcWrapper`'s input, was checked against an older cached
`TestSuite.sol`: the trimmed ASTs are identical).

`Solidity/Solkey/TestSuite.lean` is one command,
`solc_import "…" hash 0x… as Solkey.TestSuite renaming Triple => FixedTriple`
(`Frontend/Import.lean`), and the pinned report:

- 420 functions: 316 diamond, 102 box, 2 skip (solkey's tags, read from the
  NatSpec text);
- **417 elaborated**: `Solkey.TestSuite.f : Prog Solkey.TestSuite` for each,
  its parameters free locals of their types (the report row carries them);
- 2 skipped (`tryCalleeGet`, `tryCalleePing`, tagged `skip`);
- 1 excluded: `recursiveStructMapping`, whose struct `Tree` is recursive
  through a mapping (its state variable `tree` is left out of the contract).

No syntax had to be added: every construct of the file (`new T[](n)`,
`.length`, `**`, fixed arrays, `int8`, `try`/`catch`, `transfer`, `++`/`−−`
inside expressions, units) already elaborates.  Most of the corpus's
`unsupported` reasons for TestSuite are stale.  The printer normalises what
the grammar spells differently: folded literals and units, `payable(…)`
and contract conversions stripped, `−−`, `bool` keys as `b ? 1 : 0` (the
mapping declared with a `uint` key), `x.push().f` read through a
`T storage pushRef1 = x.push();` (the three sites are an assignment of a
constant and a declaration's whole initial value, the only positions where
that is solc's order).  The printer also renames a local named like a state
variable or a Lean keyword with a trailing `_`, but no local or parameter of
TestSuite is so named (`balance`, `age`, `balances`, `ledger`, `tokens` are
struct members, left alone): the fixture does not exercise that path.

After the M2 review, the import refuses what it used to read past and would
change a function's meaning: a modifier, a `constant` or `immutable` state
variable, an overloaded name or one named `report`, an inheriting contract;
expressions of literals only are folded in exact rational arithmetic, as
solc does (`7 / 2 * 2` is `7`); named arguments go in parameter order; a
pushed member is hoisted only where that keeps solc's order; a struct
recursive through an array is `unsupported`, not `excluded`.  None of these
occurs in TestSuite: the fixture and its hash are unchanged.  A body that
exhausts its heartbeats or recursion depth is a row, not a failed import.
`./run-lean.sh` now builds `SolkeyTestSuite` too (about 8 s, the import's
cost below), so its pinned report is checked.

Cross-check against the old corpus: of the 212 corpus bodies that were not
concretized, 182 print the same program (`Prog.toStr`, up to spacing,
parentheses and the old renames `folks`/`aux`); the 30 others differ only
where the corpus discharged a `require` by pushes, or where the source
changed since `f2eb3d98eb` (`storageLocalDeclSkip`,
`parenthesizedCondition`).

Cost of the import, one module, `Elab.async false`, warm:

| Step | Time |
|---|---:|
| read and parse the fixture, print, elaborate the contract | 0.5 s |
| the macros on 417 bodies (`sol_raw!{ … }` to `List RawStmt` terms) | 0.8 s |
| one `evalExpr` of the contract and all bodies | 0.5 s |
| the typed elaborator on each, quoting, kernel check of 417 definitions | 2.7 s |
| compiling the 417 programs | 3.6 s |
| **total** | about 8 s |

`sol[C]{ … }` would have cost about 10 s for the elaboration alone (one
`evalExpr` per program).  The programs are compiled because `sol_prove`
evaluates its sequent with compiled code; if the obligations of M3 do not
name the program constants, the 3.6 s can go.  The default build is not
slowed: `SolkeyTestSuite` is its own library, and `Frontend/` is two small
modules.

## M3a results (2026-10-05): a failed `assert` panics

Decision A is in: a failed `assert` is `Halt.panic` (`assertOk`,
`Semantics.lean`), solc's `Panic(0x01)`, distinct from `require`'s revert.
solc's other panics (overflow, a zero divisor, an index out of bounds, `pop`
of an empty array) stay reverts, as in KeY, where a box accepts them.

- **Meaning.** A program's formula reads its run with `Modality.afterRun`
  (`Update.lean`): `Modality.after` and the run is not a panic.  So no
  modality holds of a panic; `revert` and `stuck` keep their meaning (box
  true, diamond false).  An update keeps `Modality.after`: a term never
  panics (`Calculus/NoPanic.lean`, `Upd.apply_ne_panic`), so the two
  readings agree on it, and the closers, `Decide` and the chains, which read
  updates, did not change.  Only an `assert` panics
  (`Semantics/NoPanic.lean`: `Prog.run_noPanic` for a program with no
  `assert`, by a lemma per operation and the `no_panic` tactic).
- **The taclet.** `Taclet.assertSimple` is KeY's: `⟨[ assert(se); ]⟩ ⇝
  se = true ⟹ ⟨[ ]⟩ ; se = true`, "Holds" and "Violated" (the new premise
  `Premise.check`, `Proves.check` with goals `thn` and `els`, `checkRule`,
  in `sol_derive`, `Derive.residue`, the proof tree, `SolkeyFragment`,
  `Termination`).  Its soundness is `Taclet.sound_check`.
- **Soundness.** `SameOk` now asks two halts to agree on whether they are a
  panic; an update rule's premise and its statement reach their halts
  through different reads, which `res_split` closes by `no_panic_iff`
  (neither is a panic).  `Premise.Correct` asks a branch's uncovered halt,
  a closed goal and a `try`'s halt not to be a panic.  `Proves.sound` holds
  with only `propext`, `Classical.choice`, `Quot.sound`.
- **Callbacks.** `COut.after` of a panic is false; a `transfer` and a `try`'s
  call never panic.
- **EVM.** `StmtOut.panic`: the interpreter panics where the machine
  reverts.  `compile_correct`'s second case is "both revert", the
  interpreter's halt a revert or a panic; `Theorems.lean`'s `(P, σ) ↯` says
  the same.
- **Regression** (`Examples/Tactics/Revert.lean`): `¬ ⊨ [ assert(false); ] true`
  and so `¬ ⊢` (`assertFalse_box_not_valid`, `assertFalse_box_not_derivable`),
  while `⊢ [ require(false); ] true` (`requireFalse_box`).  The examples that
  relied on the old reading now state the precondition the box needs
  (`assertBox`, `assertConditionCaptured`) or the refutation
  (`StorageSuite.assertFails`); the `assert` chains run under any modality
  (`ChainNotation.assertTrace`, `StorageCoverage.assert*`).

Cost: no new `maxHeartbeats` and none raised.  The default build passes; the
slowest modules take what they took before (`Examples/Tactics/Calls.lean`
81 s, `Memory.lean` 78 s, `CrossDomain.lean` 77 s, `Decide.lean` 66 s, wall
clock with the build's parallelism), so no slowdown was measured.  A modal
formula's meaning has one more conjunct, which `decide +kernel` never meets:
the kernel decides runs (`corpus_decide`) and the `LFml` reduction, not
`holds` of a modality.

Review fixes: `#difftest` takes an interpreter panic against a machine
revert as agreement (`DiffTest.runOnce`, pinned by `Examples/Tools.lean`'s
`Asserting`); `#verify` reports a panic as a counterexample with no clause
blamed (`SpecProblem.try`, pinned by `Examples/Verify.lean`'s `Guarded`);
the `check` paths of `#proof_tree`, `sol_derive?` and `sol_prove?` are
pinned in `Examples/ProofTree.lean`; the docs and conventions that stated
the old reading (`solc-alignment.md`, `compiler-verification.md`,
`solc-validation.md`, the soundness rules, the walk steps) now state this
one.

