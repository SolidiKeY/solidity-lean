# Proving solkey's TestSuite by `⊢`

The goal: every obligation of solkey's `TestSuite.sol` (418 functions, 2 more
tagged skip), stated as solkey's `SolidityProblemSynthesizer` states it and
derived with `⊢`, checked by the kernel, at close to KeY's speed. No
dependencies, no `native_decide`, no new `maxHeartbeats` override, and a `?`
twin that prints a cheap replay for every searching tactic.

Today 391 of the 418 are derived by `⊢` (`TestSuite/Report.lean`), and the
corpus rows (`Corpus/TestSuite.lean`) are corollaries of those theorems.

## Decisions (2026-10-05)

- **Box meaning.** Follow Solidity and solkey exactly: a failed `assert` is a
  Panic halt, distinct from a `require` revert, and the box does not hold on
  it. This is a semantic change, made even though many files move.
- **Diamond premise.** One atomic `wt(storage)` symbol (canonical and tight
  storage, the model's own reachability assumption: solkey states no
  premise), not an expanded layout.  The M3b
  review put it on the box too, and added words in range.
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
- **M3.** Obligation forms: both under `wt(storage)`, box with the Panic
  halt, parameters as `∀` over their type's range.  **M3a** (the Panic halt)
  and **M3b** (`wt`, the 417 statements, 111 derived) are done, below.
- **M4.** Closer for locals, plain storage and `try`/`transfer`: ground
  arithmetic, `applyEq`, bool case splits, difference bounds, `wt` facts.
  Done (below; bounds by constants, not differences of terms): 237
  derived.
- **M5.** Push, pop, `delete` and storage copies in the closer.  Done
  (below): 300 derived; the 6 pending outside memory are listed with
  their reasons.
- **M6.** Memory in the closer: allocation, reads and writes, `mlen`,
  defaults, copies to storage.  Done (below), but for the copies between
  memory and storage: 391 derived.  Being reworked into solkey's
  `memoryRules.key`/`structMemoryRules.key` taclets.
- **M7.** The remaining functions; a `derived` status in the corpus table;
  retire `corpus_decide`, the `#eval` rows and the 8M override.  Done
  (below), but for the remaining functions: the table reads the `Report.lean`
  pin, and `TestSuite`'s `corpus_decide` theorems and `#eval` rows, and the
  8M override, are gone.

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
  NatSpec text as `KeyNatspec` reads it: a `@custom:key` tag starts a line,
  and a `requires`/`ensures`/`invariant` clause, the function's or the
  contract's, makes the tag `specified`, a function neither `public` nor
  `external` `internal`; neither gets a plain `N.f.problem`, and a clause
  solkey refuses is `malformed`, an unsupported row. TestSuite has none of
  the three, so the summary omits them);
- **417 elaborated**: `Solkey.TestSuite.f : Prog Solkey.TestSuite` for each,
  its parameters free locals of their types (the report row carries them);
- 2 skipped (`tryCalleeGet`, `tryCalleePing`, tagged `skip`);
- 1 excluded: `recursiveStructMapping`, whose struct `Tree` is recursive
  through a mapping (its state variable `tree` is left out of the contract).

The bodies are elaborated with info trees off: the language server would
otherwise keep all 417 expansions, every one anchored at the command.

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
  readings agree on it.  The closers, `Decide` and the chains read updates;
  their one change is the revert case of a modality (`holds_revert` in
  `Calculus/Close.lean`, the modal case of `Fml.toL_holds` in
  `Calculus/Decide.lean`), whose `simp only` now unfolds
  `Modality.afterRun`.  Only an `assert` panics
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

Cost: no new `maxHeartbeats` and none raised.  **M3a slowed the two
soundness theorems under a heartbeat override**, measured in heartbeats (the
`IO.getNumHeartbeats` difference around the declaration, `Elab.async`
off, in thousands, the unit of `maxHeartbeats`), at the commit before M3a
(`d6a4b65`), after its review (`947dd28`), and after the fixes below:

| Theorem | Override | before M3a | after M3a | after the fixes |
|---|---|---|---|---|
| `Taclet.sound_unfold` (`Calculus/SoundUnfold.lean`) | 1000000 | 551392 | 641806 (+16%) | 631932 |
| `Taclet.sound_update` (`Calculus/SoundUpdate.lean`) | 1000000, now none | 109127 | 119744 (+10%) | 121185 |

The growth is the panic cases: `res_split`'s `no_panic_iff` on every
split, and the new `pushAt` and short-circuit cases of `sound_unfold`.
`sound_unfold` keeps 37% of its margin; `sound_update` fits the default
200000, so its override is gone.  The examples did not move measurably
(`Examples/Tactics/Calls.lean` 81 s, `Examples/Tactics/Memory.lean` 78 s,
`Examples/Tactics/CrossDomain.lean` 77 s, `Examples/Tactics/Decide.lean`
66 s, wall clock with the build's parallelism, against the 75–90 s the
`lean-verify` skill records), but they do not run the soundness proofs.
A modal formula's meaning has one more conjunct, which `decide +kernel`
never meets: the kernel decides runs (`corpus_decide`) and the `LFml`
reduction, not `holds` of a modality.

Second review fixes: the `*_noPanic` lemmas are in the simp set
`no_panic_simp` (`Semantics/NoPanicSimp.lean`), not the default one, and
`Semantics/NoPanic.lean` closes with `simp only`; `no_panic`,
`no_panic_iff` and `sound_unfold`'s panic cases use `simp only` /
`simp_all only`.  `NoPanic.ne_of_eq` is the one proof that a halt of a
computation that does not panic is not a panic.  `#verify` runs the
update and the call once per candidate (`SpecProblem.try`), not once more
per postcondition.

Review fixes: `#difftest` takes an interpreter panic against a machine
revert as agreement (`DiffTest.runOnce`, pinned by `Examples/Tools.lean`'s
`Asserting`); `#verify` reports a panic as a counterexample with no clause
blamed (`SpecProblem.try`, pinned by `Examples/Verify.lean`'s `Guarded`);
the `check` paths of `#proof_tree`, `sol_derive?` and `sol_prove?` are
pinned in `Examples/ProofTree.lean`; the docs and conventions that stated
the old reading (`solc-alignment.md`, `compiler-verification.md`,
`solc-validation.md`, the soundness rules, the walk steps) now state this
one.


## M3b results (2026-10-05): the obligations

`Calculus/Problem.lean` states solkey's obligations (`Problem.fml`); the
`SolkeyTestSuite` library states all of `TestSuite`'s and proves what
`sol_prove` and its leaf tactics close.

- **Box**: `∀x̄. wt(storage) → [ f(x̄); ] true`.  With M3a a failed
  `assert` falsifies it, so no cut is needed: this is KeY's "Violated"
  obligation; a `require` that fails reverts, which the box accepts, as in
  KeY.
- **Diamond**: `∀x̄. wt(storage) → ⟨ f(x̄); ⟩ true`.  solkey states no
  premise: its `storage` is a free `Struct` term with unbounded integer
  fields, and no solidity taclet mentions a well-formed heap.  Here the
  storage is any state of the interpreter, so the premise says it is one
  the contract can be in: the model's own Solidity-reachability assumption,
  not KeY's.  Both modalities carry it (M3b review): a box over every
  storage is false of some functions Solidity runs safely (below).  So a
  derived obligation need not imply solkey's: `assert(total >= 0)` on a
  `uint total` holds under `wt`, where solkey's free `total` can be
  negative.
- **Parameters**: `Fml.all` binders over the type's range: `uint`
  `[0, 2²⁵⁶)`, `int` the signed 256-bit range, `bool`.  KeY's `int` is
  unbounded.  The width is not bound (`solc_problems` keeps only the
  `PrimTy`): the one narrow parameter (`signedUnaryMinusInRange(int8)`)
  ranges over `[-2²⁵⁵, 2²⁵⁵)`, neither solc's `[-128, 128)` nor KeY's every
  integer.  That makes the obligation stronger than Solidity's (more
  inputs), never weaker; its `require(x == 5)` keeps it derivable.  No `TestSuite`
  function returns a value but the skipped `tryCalleeGet`.
- **`wt` is one atomic term**, `Op1.wt vs` applied to `storage`, stated as
  `defined(wt(storage))` (`Fml.wt`).  The interpreter reads it as a test,
  `storageWtB` (`Semantics/WellFormed.lean`): every root there, in order,
  each `SVal.canon` and `SVal.tight` at its type, clause for clause as
  `canonB`/`tightB`, the default compared by `SVal.isDfltB` since the
  kernel does not reduce the well-founded `defaultForTy`; and every word in
  its type's range, every mapping key in its key type's (`SVal.wordsB`).
  So `shape_iff_reachable`: for `TestSuite`'s roots (no duplicate,
  `Ty.okDeep`) a storage passes the shape test exactly when a checked
  program reaches it; `wt_iff_reachable`: it passes `wt` exactly when it is
  reachable and its words fit.  The words are a test of their own because
  the AST admits unchecked literals (`.lit (i : Int)`), so a program the
  AST runs can store a `uint` of `-1`, which solc never does.  Why an
  `Op1` and not a formula: a new `Fml` constructor touches every formula
  traversal, and an expanded layout (`∀` per root and member) gives every
  leaf quantifiers the closer has to instantiate.  The `Op1` cost one case
  in `Op1.eval`/`denote` and their frame, bridge, refinement and
  state-part lemmas, the quoter, the printer and the `dl{}` reader
  (`wt(storage)`).  The closer sets the premise aside
  (`Derive.dropWt`: only a weakening, `Derive.wrap_dropWt`); a leaf
  tactic does the same through `Proves.close_dropWt`, which `sol_prove?`
  picks for a leaf under `wt`.
- **Satisfiable**: `Solkey.TestSuite.initState_wt`, the initial state passes
  `wt`.  The plan asked for `decide +kernel` on the initial store; the
  kernel cannot evaluate `C.initStorage` (it is built by `defaultForTy`), so
  the theorem is `initStorage_wt` — the empty program reaches the initial
  storage, and its words are defaults — with its two side conditions (`nodupKeysB`, `okDeep` of the
  roots) by `decide +kernel`.

**The statements.**  `solc_problems Solkey.TestSuite`
(`Frontend/Problems.lean`) defines `Solkey.TestSuite.f.problem : Fml _` for
each of the 417 programs, compiled for `sol_prove`.  `#solkey_problem`
prints one in solkey's `--print-problem` syntax (same modality, same
parameters as program variables of their KeY sort, plus `wt(storage) ->`);
two are pinned in `TestSuite/Problems.lean`; the `#solkey_derive?`
suggestions are pinned in `TestSuite/Suggestions.lean` (two leaves under
`wt`).

**The theorems.**  `#solkey_derive? N from i count k` runs `sol_prove?` on
each statement and prints, for those whose leaves all close, the theorem
`N.f.proved : ⊢ N.f.problem` with its replay (`sol_prove`, then one leaf
tactic sequence per leaf; nothing searched on re-check).  The three
`TestSuite/Derived*.lean` modules hold the 111 it found (37 each), the
search run at `maxHeartbeats 50000` per leaf try.  `#solkey_obligations`
reads the environment, and `TestSuite/Report.lean` pins it; a theorem
counts as derived only when its type is `⊢ N.f.problem`, compared as an
expression (a `N.f.proved` of another statement is listed "mismatched"):

| | Box | Diamond | Total |
|---|---:|---:|---:|
| derived | 36 | 75 | 111 |
| pending | 66 | 240 | 306 |
| no statement | | | 3 (1 excluded, 2 skipped) |

A pending obligation is no theorem and no `sorry`.  What keeps them
pending (from `#solkey_scan`, which lists the leaves of the walk, and the
first leaf the search leaves open):

- **Diamond storage writes and reads** (most of the 240): a diamond update
  must return, and `store(storage, age, 34)` returns only where `age` is a
  root; that is what `wt(storage)` gives, and the closer does not read it
  yet (M4: "returns" facts at statically typed paths).
- **Memory** (`memory*`, `testMemory*`): the closer has no memory layer (M6).
- **Push, pop, copies** (`storagePush*`, `test*Push*`, `testCopy*`): M5.
- Ground arithmetic and key splits the syntactic closer does not do (M4).

Derived diamonds are the locals-only and the literal-condition ones
(`additionSimple`, `ifElseSplit`, `requireTrueLiteral`, …); derived boxes
include the reverting ones (`storageIndexArrayReadOutOfBoundsReverts`,
`transferToOwner`, …).

**Cost.**  Each derived theorem, elaborated alone (`Elab.async false`,
warm): 9 ms to 2.2 s, median 380 ms; 50.4 s for all 111 (11.4, 23.4 and
15.6 s for the three modules).  No `maxHeartbeats` override.  The walk
alone (`#solkey_scan … walk`) takes 0–6 ms per statement; with
`LFml.syn` on its leaves 0–110 ms.  The most storage writes in one leaf is
9 (`testArrayCopyClearsOldElements`), so the closer's unbounded reduction
did not blow up on this file.  The search (`#solkey_derive?`) took about
7 minutes for the 417 statements.

**What changed below.**  `Op1.wt` is a new symbol, so `Update.lean` and the
modules that match on `Op1` (`Theory/Bridge/Denote.lean`,
`Calculus/TermRules.lean`, `Calculus/UpdateRules.lean`,
`Calculus/StateParts.lean`, `Calculus/Decide.lean`,
`Calculus/ChainRewrites.lean`, `Calculus/Quote.lean`,
`Calculus/RuleSyntax.lean`, `Calculus/Notation.lean`) gained one case each;
`Derive.synClose` filters the context first (a `List.filter` in the kernel
check, for every `sol_prove`).  The default build passes; the benchmark
modules that use `sol_prove` built in 6.8 s (ERC20), 24 s (Coin) and 25 s
(Mapping) with the build's parallelism.  The filter's own cost was not
measured apart; it is linear in the context, beside a reduction that is
not.

`#print axioms` on `Solkey.TestSuite.additionSimple.proved`,
`additionStorageWrite.proved`, `initState_wt`, `wt_iff_reachable` and
`Proves.of_proves`: `propext`, `Classical.choice`, `Quot.sound`.

## M3b review (2026-10-05)

- **Box premise.**  The box obligations had no `wt(storage)`, so they
  ranged over every storage, and some were false in the model: with the
  `uint[3]` root `fixedValues` stored as a mapping (which fails `wt`),
  `testFixedArrayDeleteKeepsLength` writes `7` through `delete` (a
  `.map` has no bound to check, and `defaultOf` leaves it), so its
  `assert(fixedValues[1] == 0)` panics.  `testStructWithFixedArrayDeleteKeepsLength`
  and `testFixedStructArrayDeleteResetsElements` fail the same way.  Both
  modalities now carry the premise (`Problem.fml`), so these three are
  true and pending, like solkey's.  The 36 derived boxes' leaves set it
  aside (`Proves.close_dropWt` in place of `Proves.close`); every replay
  still checks and the counts are unchanged (111 / 306 / 3).  The replays'
  times were not measured again: the change is one `List.filter` of the
  context per leaf.
- **Words in range.**  `wt` now asks `SVal.wordsB` too (see above); a
  diamond such as `total = total + 0` from `total = -1` reverted, which made
  its obligation false where solkey's holds.
- **One copy each.**  `nodupKeysB` and `Ty.numericKey` moved to `AST.lean`,
  below both the typing modules and `Semantics/WellFormed.lean`, which
  had copies; `Frontend/Import.lean`'s `paramTy?` is the one reading of a
  parameter type, for `paramCtx` and for `solc_problems`, which now warns
  and skips a function whose parameter it cannot bind (listed "unstated")
  instead of failing the command.
- **Pins.**  `#solkey_derive?` prints times only with `timed`, so its
  suggestion is pinned (`TestSuite/Suggestions.lean` since the M3b review 2: the `case leafᵢ =>`
  layout and `close_dropWt`); it resolves the leaf tactics with
  `Solidity` open, as a `Derived` module does.


## M4 results (2026-10-05): the closer

`Calculus/Closer.lean`.  `sol_prove`'s default closer (`Derive.synClose`) is
now `LFml.close`, one `Bool` over the leaf's reduction proved sound once
(`LFml.close_holds`); `LFml.syn` stays as `sol_decide`'s first try, which
the new closer subsumes (`Facts.retsW` accepts what `LTerm.rets` does,
an operation on operands equal to a known one's included).  Each KeY first-order or arithmetic taclet it
replaces has a row in `docs/lean-key-rule-map.md` ("The closer's clauses").

- **Ground evaluation** (`foldBin`, `foldUn`, `foldIte`, `foldKite`,
  `foldSame`, `foldZeroT`): a node on literals is evaluated by the
  interpreter's own checked operation (so `/`, `%` truncate and an
  overflow is left unfolded), `t == t` is `true`.
- **`applyEq`** (`Eqs`, `substE`, `Facts.eqnK`): a premise `t ≐ 5` or
  `alice.age ≐ v` rewrites `t` (`alice.age`) to the literal (the local)
  after it; a premise is decomposed through `&&`, `||`, `==`, `!=`, `!`
  and guards (`Facts.decomp`).
- **Case split on a `bool`** (`Facts.split`): on a `bool` parameter, or a
  condition compared with a literal, where a branch's cover needs it
  (`se ≐ true ∨ se ≐ false`).
- **`wt` facts** (`LPath.ty`, `LPath.ty_find`, `Facts.retsW`,
  `Facts.halts`): `Derive.topWt` reads the obligation's `wt(storage)` as
  the layout a well-formed storage holds (`Decide.LayoutOk`); a read of the
  initial storage at a path the layout types (members, mapping entries, a
  fixed-size array's elements in range) returns, of its type's kind, and
  a test for a shape the layout says is not there halts (the guards a
  `delete` leaves).  Proved from `SVal.canonB` clause by clause.
- **Parallel updates** (`Fml.seqUpd`, `peel_sound`): `{ x := x + 1 ‖ r :=
  x + 1 }` of `r = ++x;` is split into single updates where its last
  element binds a local the others do not mention.
- **Bounds by constants** (`Facts.range`, `Facts.bnds`, `foldCmp`,
  `Facts.fitsArith`): a local's type gives its range, a premise comparing a
  term with a literal narrows it, `+` and `-` add intervals; a checked `+`
  or `-` that fits returns, a comparison the intervals decide folds
  (`Examples/ProofTree.lean` pins two).  Differences of two terms (`y - x`
  with both symbolic) are not bounded: no obligation of buckets A, B or E
  needed them (each one the closer leaves is push, pop, memory or a
  copy).

**The size guard.**  A leaf's formula with its updates pushed in shares
subterms: a storage written from a read of the one before it appears
twice in the next.  The tree after `toL` and its reduction (`LFml.elim`,
what the closer walks) grow at different rates, so neither bounds the
other.  Measured on `count = 0;` and `n` times `count += 1;` (kernel check
of the whole `sol_prove`; first two columns from M4):

| `n` | tree after `toL` | `okE` reduction | kernel |
|---:|---:|---:|---:|
| 2 | 310 | 1071 | |
| 4 | 1374 | 7736 | 0.79 s |
| 6 | 5678 | 53531 | 2.1 s |
| 8 | 22942 | 367531 | 8.2 s |
| 10 | 92046 | 2519836 | 49.5 s |

The ratio of the two grows from 3.5 to 27 there.  A `delete` widens it
further: the tree grows linearly while the reduction triples, since a read
below a deleted location carries the read before it two or three times
(`delBelow`).  `n` deletes of `ledgerUses[aᵢ]` then a read of
`ledgerUses[k].ledger.balances[m]` (`TestSuite`'s layout), counted with
`LFml.fits`:

| `n` | tree after `toL` | `LFml.elim` |
|---:|---:|---:|
| 2 | 131 | 1002 |
| 4 | 295 | 8104 |
| 6 | 523 | 68894 |
| 8 | 815 | 619172 |
| 10 | 1171 | 5624250 |

So `synClose` asks two bounds (`Derive.fitsClose`): the tree within
`Derive.closeSize` (2000), a cheap first test, and the reduction within
`Derive.elimSize` (8000).  Each count stops at its bound, so the test
costs at most their sum in steps; in compiled code the reduction is built
first, but as a graph sharing the reads it repeats (ten deletes are
refused in 5 ms), and the kernel builds only the nodes the count visits.
A leaf past either is left open for a tactic, not attempted.
`sol_prove?` (and `#solkey_derive?`, through `Derive.searchLeaf`) asks the
same bounds (`Derive.leafFits`, which `Derive.synClose_fits` ties to
`synClose`) before its reducing steps (`sol_reduce`, then
`sol_decide_cons` or `sol_decide_heuristic`), whose evaluation, quoting
and kernel check heed no heartbeats: a leaf past them gets only
`sol_close` and `sol_spec_close`.  `Examples/ProofTree.lean` pins both
sides (four writes close in the residue, six leave one leaf past the
tree's bound, ten deletes one past the reduction's).  Of the leaves
`synClose` closes in `TestSuite`, the largest tree has 1674 nodes
(`testStorageMapStructCopy`) and the largest reduction 6079
(`testStorageIndexWriteImpureIndexRefRhs`); the second bound refuses none
of them.  The growth itself is not removed: `okE` re-guards every read by
the writes before it, and sharing it would change `LFml.elim_holds`
(`Calculus/Decide.lean`).

**Cost of the second bound.**  Counting the reduction is a second walk
of it in the kernel.  The whole residue of four obligations checked by
`decide +kernel` (`Elab.async false`), before and after:
`testNestedIndexWriteImpureReceiverAndIndex` 9.11 → 9.22 s,
`testStorageStructDeleteSkipsMappingMember` 2.80 → 3.03 s,
`testDeleteArrayDoesNotResetElementMappingMember` 5.48 → 5.83 s,
`testStorageIndexWriteImpureIndexRefRhs` 1.52 → 2.07 s; 18.9 → 20.2 s in
all (+7%), most on the largest reductions.

**Literal powers.**  The closer folds `**` on two literals (`foldBin`)
only with an exponent at most `256` (`Decide.powBig`): `Int.pow` recurses
once per unit of the exponent, compiled and in the kernel, heeding no
heartbeats.

**The counts** (`TestSuite/Report.lean`, pinned):

| | Box | Diamond | Total |
|---:|---:|---:|---:|
| derived | 51 | 186 | 237 |
| pending | 51 | 129 | 180 |
| no statement | | | 3 (1 excluded, 2 skipped) |

233 of the 237 close inside the residue (`sol_prove` alone); 4 leave
leaves a tactic closes (`storageIndexArrayAddAssignOutOfBoundsReverts`,
`storageIndexArrayReadOutOfBoundsReverts`, `testStorageArrayReadWrite`,
`storagePopUnfold`: a dynamic array's bounds, which the layout does not
give).  No obligation derived before is pending now.
Every pending one is outside buckets A, B and E's fragment:

| Reason | Pending |
|---|---:|
| memory (`memory` locals, `new`): M6 | 111 |
| `push` / `pop` on a storage array: M5 | 52 |
| a copy between storage locations (`alice = bob;`, `a.f = tok;`): M5 | 17 |

**Cost.**  The six `TestSuite/Derived*.lean` modules (40, 40, 40, 40,
40, 37 theorems) checked in 5.5, 6.9, 17.1, 16.1, 5.3 and 8.1 s (wall
clock, `Elab.async false`, measured with the language server running them
side by side, so these are upper bounds); M3b's three modules of 37 took
11.4, 23.4 and 15.6 s for 111 theorems.  The slowest single theorem is
`storageMatrixNseIndex` (6.7 s): its `require(i == 1 && j == 2 && …)`
splits into 43 leaves, each reduced and closed apart, about 150 ms each.
`testStorageStructDeleteSkipsMappingMember`, the largest leaf, takes 2.4 s.
No `maxHeartbeats` override.  The benchmark modules built in 17 s (Coin),
18 s (Mapping), 5.0 s (ERC20), 5.4 s (Purchase), against 24, 25 and 6.8 s
at M3b: no slowdown measured.  Four benchmark proofs and three pinned
suggestions lost a leaf the closer now proves (`EtherWallet.withdrawOwner`,
`Coin.mintMinter`, `Mapping.nested_remove_spec_*`; `Examples/ProofTree.lean`),
and are now `sol_prove` alone; Counter's `inc_spec` and `dec_spec`, two of
the six M1 kept on `sol_derive`, close by `sol_prove` alone too (the premise
`c == count` rewrites `count`).

`#print axioms` on `Derive.synClose_sound`, `Proves.of_proves` and
`Solkey.TestSuite.storageMatrixNseIndex.proved`,
`testStorageArrayReadWrite.proved`, `storageFieldPostdecrementAssign.proved`:
`propext`, `Classical.choice`, `Quot.sound`.


## M5 results (2026-10-05): push, pop and storage copies

`sol_decide`'s target language (`Calculus/Decide.lean`) has two more
storage writes, and the closer reads past them.

- **`LStor.arr op s q w`**: an operation on the array at `q` (`AOp`):
  `values.push(w)`, `persons.push()` (the slot `pushSlot E` gives), and
  `values.pop()` (`keep` for an array of mappings).  `AOp.apply` is the
  interpreter's `pushOn`/`popOn` on the node alone, so the bridge to
  `Tm.eval` is one lemma per symbol (`pushOn_slot`, `pushOn_word`,
  `popOn_pop`, `write_bridge`).  `tokens.push(tok)` of a struct is a
  `push()` of a `uint` slot with the source copied over it
  (`pushCopy_bridge`).
- **`LStor.copy s q src sq`**: the subtree at `sq` of `src` written over
  `q` (`alice = bob;`, `SVal.overlay`), the source read where the program
  reads it (`read_bridge`).
- **The elimination** (`LStor.readU`, `hasU`, `lenU`, `mapU`, `okE`, and
  `slotU`) peels both.  Below a pushed or popped array a read compares its
  index with the old length (`arrKey`): the pushed word, or a primitive
  default, at it; the old element below it; nothing past it, or at the
  last index after a `pop`.  The length is the old one plus or minus one,
  counted unchecked (`lenSucc`, `lenPred`: `bool` arithmetic, which never
  reverts; a storage array's length has no bound).  The slot a `push()` of
  a struct, an array or a mapping recycles is read where the storage below
  says what it is (`LStor.slotU`): after a `pop` at the same array the
  element it popped, cleared (as below a `delete`) or kept; after a
  `delete` of the array its old first element, cleared.  An element of
  such a push at an index up to the old length exists exactly where the
  index is in range (`inRange`).  A copy is read through its source key by
  key (`copyKeys`, `overlay_findLive_nomap`): where the source has a
  mapping at a key the read is kept whole (a mapping met in both keeps the
  target's entries; a copy of a well-typed program has none).  A read kept
  whole is a term over the written storage, still exact.
- **Soundness**, case by case outside the mutual proof: the elimination's
  `save` and `delete` cases moved out too (`save_readU_sim`, …,
  `copy_mapU_sim`, `pop_slotU_sim`, `del_slotU_sim`), so the mutual proof
  only dispatches; with `termination_by structural` on each of its
  theorems, its `maxHeartbeats 400000` override is gone (it now checks at
  the default).
- **The alias a push returns** (`Derive.pushAlias?`, `Calculus/Derive.lean`):
  `T storage x = arr.push();` leaves `{ storage := extend(storage, arr) ‖ x
  := arr[arr.length] }`, the alias past the old end; `Fml.seqUpd` reads it
  as the push, then `x := arr[arr.length - 1]` after it (`lastSlot`), where
  the path to the array reads the storage only to check indices
  (`Tm.stablePath`, `stable_eval`).
- **The closer** (`Calculus/Closer.lean`):
  - a bound below alone (`Facts.lo`, `cmpDecideO`): a length is at least
    `0`, so `values.length > 0` after a `push`, and `pop` after `push`
    returns; unchecked `+`/`-` return on integers (`Facts.fitsArith`); a key
    compared with itself takes its first branch (`foldKite`:
    `values[values.length + 1 - 1]`);
  - a read below the slot a `push()` of the initial storage's array takes,
    or of that array after its `delete`, is typed by the element type
    (`Facts.slotTy`, `Facts.slot_find`): under `wt(storage)` the elements
    and the slots past the end are canonical (`SVal.canonB` checks the
    shadow too), and a default is canonical where the type's structs are
    (`defaultForTy_canonB`, in the new `Typing/CanonTest.lean`, with
    `canonB_iff`/`tightB_iff` moved there from `Calculus/Problem.lean`).  So
    its shape and kind follow the type, and it returns where the index is at
    most the old length (`Facts.slotIn`).

**The counts** (`TestSuite/Report.lean`, pinned):

| | Total |
|---|---:|
| derived | 300 (237 + 63) |
| pending | 117 |
| no statement | 3 (1 excluded, 2 skipped) |

The 63 new theorems are `TestSuite/Derived7.lean` (40) and
`TestSuite/Derived8.lean` (23), in the order of the source; all but
`testStorageNestedPushReturnAlias` (two leaves `sol_close` closes) are
`sol_prove` alone.  `testStorageArrayReadWrite` and `storagePopUnfold`
(M4: leaves left for a tactic) now close in the residue.
`memoryToStorageIndexArrayCopyRootExample` is derived by the search (two
`sol_close` leaves, 9 s) but its replay runs past 200000 heartbeats as one
declaration; it stays pending, for M6.

Of the 117 pending, 111 use memory (M6).  The other 6, and why:

| Function | Why it stays pending |
|---|---|
| `storagePushReadBack` (diamond) | `values[values.length - 1]` after `values.push(42)`: the `- 1` is a checked `uint` subtraction of a length with no bound, which reverts where the length is past `2²⁵⁶`; KeY's `int` has no range.  Not valid in the model (overflow, as the plan expects): solc keeps a length at most `2⁶⁴` (`push` panics, 0x41, on an array already that long), but `wt(storage)` does not bound lengths (`docs/solc-alignment.md`, "Remaining deltas"). |
| `testDanglingReferenceSurvivesPush`, `testArrayCopyClearsOldElements`, `testArrayCopyKeepsDestinationTail`, `testDeleteArrayLeavesDataPastLength`, `testDanglingInnerArrayReappearsAfterPush` (diamonds) | an alias bound through an index (`Token storage r = tokens[0];`) used after a `pop` made it dangle: the fragment drops such an alias at the next write (`SymB.onWrite`), and the write through it lands past the live end, which the reduction's live storage does not reach. |

**Cost.**  `Derived7.lean` (40 theorems) takes 58 s, `Derived8.lean` (23)
26 s (`Elab.async false`, the sum of the profiler's per-declaration
times); the slowest theorem is `testNestedIndexWriteImpureReceiverAndIndex`
(8.3 s: four pushes, two of them into the elements of the first two, and
two impure indices).  The closer's leaves stay within `Derive.closeSize`.
The default build passes with the same module times as at M4 (ProofTree
5.4 s, Coin 17 s, Mapping 18 s, `Examples/Tactics/Decide.lean` 40 s): no
slowdown measured from the new constructors.  `Calculus/Closer.lean` now
imports `Typing/CanonTest.lean`, so it waits for the typing modules in a
parallel build (they were built before `Calculus/Problem.lean` anyway).

`#print axioms` on `testStoragePushReturnAlias.proved`,
`storagePushValueCopySource.proved`, `storagePushLengthPositive.proved`,
`Derive.synClose_sound` and `Fml.valid_iff_reduce`: `propext`,
`Classical.choice`, `Quot.sound`.

`#solkey_derive? N … pending` runs the search on the statements no
theorem derives yet.

**Three diamonds hold only up to the length delta.**  The model's `push`
never panics and `wt(storage)` does not bound a length, while solc's
`push` panics (0x41) on an array of length `2^64`, a length a deployed
contract can hold.  `storagePushLengthPositive`, `storagePopUnknownLength`
(`TestSuite/Derived7.lean`) and `arrayOfMappingsIndex`
(`TestSuite/Derived8.lean`) push with no bound on the length before them:
derived, and true of solkey (its `int` is unbounded), but false of solc
from that storage.  The other derived diamonds that push start with a
`delete` of the array.  Closing the delta is a bound in `wt` and the panic
in `pushOn` (`docs/solc-alignment.md`, "Remaining deltas").


## M3b review 2 (2026-10-05): what counts as derived

- **Axioms.**  `#solkey_obligations` counts `N.f.proved` as derived only
  when its proof uses no axiom but `propext`, `Classical.choice` and
  `Quot.sound` (`Frontend/Problems.lean`, `standardAxioms`); one that uses
  `sorryAx` (a pasted `sol_prove?` suggestion with a `sorry` leaf) or
  `Lean.ofReduceBool` is listed "unsound".  The axioms are collected once
  for all 300 theorems (one shared `CollectAxioms` traversal), and per
  theorem only when the union is not standard: the command stays under the
  profiler's 100 ms threshold.  Checked by hand with a scratch `sorry`
  theorem (`unsound storagePushReadBack`); not pinned, since a pin would
  need a `sorry` in a checked file.
- **A replay that fits.**  Each leaf try runs with heartbeats of its own,
  so a search could succeed where the replay, one declaration, does not.
  `Derive.proveSearch` adds up the heartbeats of `prove` and of each
  closing try, and `Derive.replayFits` compares the sum with
  `maxHeartbeats`: `#solkey_derive?` reports such a statement pending ("its
  replay is past maxHeartbeats as one declaration"), and `sol_prove?`
  warns.  `memoryToStorageIndexArrayCopyRootExample` needs about 264k
  heartbeats against 200k and is pinned as that case.  The sum is
  approximate: it leaves out the statement's elaboration and the `case`
  lines.
- **Pins off the critical path.**  The `#solkey_derive?` pins moved from
  `TestSuite/Problems.lean`, which every `Derived` module imports, to
  `TestSuite/Suggestions.lean`, which only the library root imports, so
  their searches (about 9 s for the replay-too-long pin) run beside the
  `Derived` modules.  They pick the statement by name (`only f`), not by
  position.
- **One builder, one loop.**  `Derive.provesNil` is the one builder of
  `⊢ φ` (`sol_prove`, `#solkey_derive?`, `#solkey_obligations`), and
  `Derive.proveSearch` the one leaf loop of `sol_prove?` and
  `#solkey_derive?`.


## M5 review (2026-10-05)

- **The length delta cuts both ways.**  `storagePushLengthPositive`,
  `storagePopUnknownLength` and `arrayOfMappingsIndex` are derived diamonds
  that solc breaks from a storage of length `2^64` (`push` panics, 0x41);
  they hold in the model and in solkey.  `Calculus/Problem.lean`,
  `docs/solc-alignment.md` ("No bound on a dynamic array's length") and the
  M5 section above say so, and that solc's lengths reach `2^64` (not
  "below").  Not fixed in the model: it needs a bound in `wt` and the panic
  in `pushOn`, a semantic change of its own.
- **The elimination as compiled code** (`Calculus/Decide.lean`).  The
  `.arr` cases of `readU`, `hasU`, `lenU` and `mapU` passed the old length
  and the old value as strict arguments: two recursive calls on the same
  storage, so compiled code (`Derive.leafFits` through `evalExpr`, which
  heeds no heartbeats) did `2^k` calls for `k` array operations.  Measured
  on the reduction alone: twelve pushes onto `values`, 23 ms; twelve onto
  each of `values` and `persons`, interleaved, 106 s.  `LTerm.elimF` and
  its mutual copies compute a leaf's arguments only where the relation
  reads them (`CaseTree.toTermLazy`), proved equal to the definitions
  (`LTerm.elimF_eq`, …) and installed with `@[csimp]`: 1 ms and 7 ms on
  the same leaves.  The kernel and the proofs see the old definitions, so
  nothing checked changes.  Pinned in `Examples/ProofTree.lean`
  (`pushes22`: a leaf within `closeSize` whose reduction is past
  `elimSize`, refused in milliseconds).
- **What stays slow.**  The closer itself (`LFml.close`) on the reduction
  of `n` pushes onto one array, within the bounds: 0.1 s at 8, 0.9 s at 12,
  2.0 s at 14, 4.5 s at 16; at 20 the reduction is past `elimSize` and the
  leaf is refused (4 ms).  So `sol_prove`'s compiled residue can spend a
  few seconds on a leaf the bounds accept; no TestSuite function comes
  near (the most pushes and pops in one is six,
  `testNestedIndexWriteImpureReceiverAndIndex`, over several arrays).
- **`simp only`.**  The 336 bare `simp`/`simpa`/`simp_all` calls of
  `Calculus/Decide.lean` (not only M5's) and the 7 of `Calculus/Derive.lean`
  are now `simp only` with the lemmas `simp?` printed (the union, where a
  `<;>` fan printed several), and three unused arguments the linter
  reported are gone.
- **Docs and pins.**  The module docstrings of `Calculus/Decide.lean`
  (recycled slots, `copyKeys`) and `Calculus/Closer.lean` (`Facts.slotTy`)
  and `docs/lean-key-rule-map.md` (copies below keys, recycled slots) say
  what fd4430d added.  `Examples/Tactics/Decide.lean` had a pin that called
  copies outside the fragment; it now proves a push, a push read back, a
  `pop` after a `push` and a copy (`pushLength`, `pushReadBack`,
  `pushPopLength`, `copyReadsSource`), and keeps the unguarded copy as a
  formula that is not valid over every state.  `Examples/ProofTree.lean`
  pins `sol_prove?` on a push, a `pop`, a copy, and under `wt(storage)` a
  push and `pop`, a write through an index into a pushed struct, and one
  through the alias `push()` returns: the default targets now exercise
  the M5 closer paths.
- **Checked.**  `Derived7.lean` and `Derived8.lean` re-check with no
  errors after the change.


## M7 integration (2026-10-05)

The old corpus and the `⊢` derivations now tell one story.

- **The table.**  `scripts/solkey-port.mjs` no longer translates
  `TestSuite.sol`.  It reads the rows off two pins, with no Lean run:
  `TestSuite/Report.lean` (`#solkey_obligations`) and the import's summary
  in `Solidity/Solkey/TestSuite.lean`.  It also finds the theorems
  `Solkey.TestSuite.f.proved` in `Solidity/TestSuite/`, and fails when the
  pins disagree with the source or with each other.
  - `tests/solkey/expected.tsv` has one row for each of the 420 functions:
    391 `derived`, 25 `pending` (19 copies between memory and storage, 5
    dangling aliases, and the replay past its budget), 1 `divergent`
    (`storagePushReadBack`, the length delta), 1 `excluded` and 2 `skip`.
    Each row's note gives the modality and the parameters.  (Before M6:
    300 derived, 116 pending.)
  - `docs/corpus-parity.md` has a TestSuite section, by modality and by
    reason.
  - Re-running the generator re-pins all of it with no hand edit, as it did
    after M6.
  - It refuses a `TestSuite.sol` whose sha256 is not the fixture's
    `sourceSha256` (`tests/solc/TestSuite.ast.json`), and a `DIVERGENT` or
    `PENDING` entry that `Report.lean` does not list pending.
- **The generator, re-synced.**  The function header now accepts
  `pure`/`view`, `external` and `returns (…)`, and reads the `skip` tag.
  The solkey checkout is at `78f42fde33`, where solkey's "fixed some
  warnings" made the header refuse about half of the functions.  Run with
  that refusal, the generator dropped them from every suite; now the `Solc*`
  modules come out unchanged, but for the commit line.
  - The `Net` rows follow the checkout's renamed `.key` files (unsupported,
    as before).
  - The fixture's header says `solkeyCommit 100f7f24c3`, but its
    `sourceSha256` is the file at `78f42fde33`, which adds
    `localPreincrementAssign`.  That file is the one with 420 functions
    (`scripts/solc-ast.mjs` is not this lane's).
- **The corpus rows are corollaries.**  `Corpus/TestSuite.lean`
  (generated) states each of the 371 derived obligations with no
  parameters at `Solkey.TestSuite.initState`, as `diamond_of_proved` or
  `box_of_proved` of its theorem and `initState_wt` (`Corpus/Imported.lean`).
  The 20 derived ones with parameters have no corollary; `Report.lean`'s
  pin, which the corpus imports, checks them.
  - The 186 `corpus_decide` theorems, the 51 `#eval` pins of this module
    and its `maxHeartbeats 8000000` are gone.
  - The corollaries are not stated at `State.testSuiteStore`: that is the
    hand-written contract's store, without the roots `fixedByKey` and
    `boolKeyed`, so it is no storage of the imported contract and `wt`
    fails there.
  - Rows the old corpus decided at that store and `⊢` has not derived yet
    (the copies between memory and storage) have no corpus theorem yet.
- **The two contracts agree.**  `testSuite_agrees` (`decide +kernel`, no
  axioms) checks that every root of the hand-written `TestSuite` is a root of
  `Solkey.TestSuite` at the same type, up to `folks`/`people` and
  `aux`/`a`.  Structs are the shared `structDef`.  `Syntax.lean` is
  unchanged.
- **No override left in the corpus.**  The `Solc*` modules check at the
  default heartbeats: each `corpus_decide` takes about 100 ms (the
  `rw`, the `Decidable` instance and the kernel, 30–40 ms each).  The
  generator and its probe no longer write `maxHeartbeats`.  The 2.5 s
  theorem of the Measurements section was a 10-statement `TestSuite` body,
  and those are no longer decided here.
- **Audit.**  `scripts/check-testsuite.sh` checks three things with node
  only:
  - no `native_decide`, `decide +native`, `sorry`, `admit`,
    `maxHeartbeats` or `skipKernelTC` in the code (comments and strings
    stripped) of `Solidity/TestSuite/` and `Solidity/Solkey/`;
  - the `Report.lean` pin lists no `unsound`/`mismatched`/`unstated` theorem
    (`#solkey_obligations` already rejects any axiom but Lean's three);
  - the parity: the stated rows are exactly solkey's `testSuiteFunctions`
    (418, every function not tagged skip), the skip rows are the 2 tagged
    ones, and the table is what the generator writes today.

  `--complete` also fails while a row is pending.  Today:
  `418 = 391 derived + 25 pending + 1 divergent + 1 excluded; 2 skip`.

**Times** (`Elab.async false`, warm; wall clock includes the tool round trip):

| Module | Time |
|---|---:|
| `Corpus/TestSuite.lean`, 281 corollaries (before M6) | under 3 s; no declaration reaches 3 ms |
| `Corpus/Imported.lean` | about 0.4 s (`testSuite_agrees`: 218 ms in the kernel) |
| `Corpus/SolcExpressions.lean` … `SolcControlFlow.lean`, no override | 2.6–4.6 s each |

Loading `Corpus/TestSuite.lean`'s imports (`TestSuite/Report.lean`, so all
the `Derived` modules) took about 140 s the first time.  `lake build
SolidityCorpus` now builds the `SolkeyTestSuite` derivations too.

**Still to do:**
- the final full `lean_build`;
- the `#print axioms` sweep over `Solkey.TestSuite.*`;
- `scripts/check-testsuite.sh --complete`, which fails while 25 rows are
  pending.

The generator was re-run after M6 (`scripts/check-testsuite.sh` passes).
`#print axioms` on `testSuite_agrees` (none) was checked by hand; the
corollaries' are pinned: `diamond_of_proved` and `box_of_proved` in
`Corpus/Imported.lean`, one corollary (for `initState_wt`) in
`Corpus/TestSuite.lean`, and each `⊢` theorem by `Report.lean`'s pin.

## M6 results (2026-10-05): memory

This memory support is being reworked into solkey's `memoryRules.key`/
`structMemoryRules.key` taclets; what follows is the closer as merged.

- **The closer reads memory.**  `Calculus/DecideMem.lean` keeps the
  objects the updates allocate as `SObj`s over `sol_decide`'s terms: the
  `k`-th allocation is the identity `nextId + k` of the starting state, so
  no heap premise is needed, and `MemRel` relates the symbolic heap to the
  interpreter's.  `Calculus/Decide.lean` runs the updates on that heap
  (`readL`, `mlenL`, `writeL`, `kchainL` for an index that is no literal)
  with a guard that returns exactly where the interpreter's operation does.
- **An allocation one element at a time** (`Calculus/Derive.lean`).
  `{ x := freshId(addM(memory)) ‖ memory := addM(memory) }` is split into
  `x` first and then the memory where the allocation does not read `x`
  (`memAlloc?`, `peelMem_sound`), so `Fml.toL` sees the identity before the
  object.
- **Counts.**  91 more obligations derived, in `TestSuite/Derived9.lean` to
  `TestSuite/Derived11.lean` (40, 40, 11), all `sol_prove`: 391 derived, 25 pending,
  one divergent, one excluded, two skipped (`Report.lean` counts the
  divergent one pending: 26).  `Report.lean` pins it and finds no theorem
  that uses an axiom beyond Lean's three.
- **Times.**  Language-server checks with the imports built: `Derived9`
  16 s, `Derived10` and `Derived11` about 5 s each.
- **Pending (25, and 1 divergent).**  The 19 copies between memory and
  storage, in either direction, through a root, a field or an index
  (`storageNewIntoField`, `memoryToStorage`,
  `memoryToStorageIndexMappingCopyRootExample`,
  `memoryToStorageIndexArrayCopyRootOutOfBoundsReverts`, `storageToMemory`,
  `testMemoryToStorageCopyComplexSource`,
  `testMemoryToStorageCopyComplexTarget`, `testMemoryToStorageCopyField`,
  `testMemoryToStorageCopyRoot`, `testMemoryToStorageIndexCopyImpureIndex`,
  `testStorageToMemoryCopyComplexPath`, `testStorageToMemoryCopyField`,
  `testStorageToMemoryCopyRoot`, `memoryAssignForms`,
  `storageIndexWriteRefSourceImpureIndex`,
  `storageFieldWriteRefSourceImpureReceiver`,
  `memoryToStorageIndexImpureReceiver`, `indexWriteBothImpureMemToStorage`,
  `mappingEntryThroughMemoryToMappingEntry`): the closer does not reduce
  `copySt` of a memory object or `copyStToM` of a storage path inside a
  leaf yet.  `memoryToStorageIndexArrayCopyRootExample`: the search derives
  it, but its replay is past the budget (M3b review 2).  The five
  dangling-alias functions (`testDanglingReferenceSurvivesPush`,
  `testArrayCopyClearsOldElements`, `testArrayCopyKeepsDestinationTail`,
  `testDeleteArrayLeavesDataPastLength`,
  `testDanglingInnerArrayReappearsAfterPush`) and `storagePushReadBack`
  (divergent, M7) are as before.


## M6b

The memory closer is being rebuilt from solkey's `memoryRules.key` and
`structMemoryRules.key` taclets. Each step is timed against this baseline.

### Baseline (step 0, M6 closer at `8c6ac5a`)

**How it was measured.** A scratch module, not committed, imports
`TestSuite/Problems.lean`. For each of the 91 theorems of `Derived9` to
`Derived11` it elaborates `theorem … : ⊢ f.problem := by sol_prove` with
`Elab.async` off, timed with `IO.monoMsNow` in the language server. These
times are serial and per theorem. They leave out loading the file's imports,
which is why they do not add up to the M6 file times above.

For each leaf of the residue (`residue budget (fun _ _ => false)`, the
leaves `synClose` is asked about), the module computes three numbers on
`(Hyp.wrap (dropWt Γ) φ).seqUpd`:

- the nodes `LFml.fits` counts in its `toL`;
- the nodes `LFml.fits` counts in its `elim`;
- **W**, the number of `write`, `addM` and `copySt` nodes on the spines of
  its `memory := …` updates.

A second run was within 1% of the first.

| File | Theorems | `sol_prove` total | Slowest | Largest `l.fits` | Largest `l.elim.fits` | Largest W | Most leaves |
|---|---|---|---|---|---|---|---|
| `Derived9` | 40 | 7.9 s | `memoryIndexWriteNse` 2.48 s | 534 | 534 | 5 | 19 |
| `Derived10` | 40 | 10.1 s | `indexWriteBothImpureMemRef` 0.73 s | 159 | 175 | 9 | 4 |
| `Derived11` | 11 | 2.3 s | `memoryIndexArrayPreincrementAssignment` 0.24 s | 93 | 93 | 5 | 3 |
| all | 91 | 20.2 s | | 534 | 534 | 9 | 19 |

- **The slowest theorem by far** is `memoryIndexWriteNse`. It is the only
  one whose index is not a literal, so it goes through `kwriteL`/`kchainL`.
  It has 19 leaves of up to 534 nodes, against at most 4 leaves and 159
  nodes anywhere else.
- **The next slowest**, from 0.3 s to 0.73 s, are:
  - `indexWriteBothImpureMemRef` 725 ms
  - `indexWriteBothImpureMemoryValue` 628 ms
  - `memoryIndexWriteMemRefImpureReceiver` 482 ms
  - `testMemoryTokenArrayAuxiliaryCases` 461 ms
  - `testMemoryUintArray{Predecrement,Postincrement,Postdecrement}` 370–390 ms
  - `memoryDelete` 382 ms
  - `testMemoryStructFixedMemberLength` 350 ms
  - `memoryFieldWriteMemRefImpureReceiver` 337 ms
  - `testMemoryFieldShallowCopy` 312 ms
  - `testMemoryEvaluationOrder` 308 ms

  Every other theorem takes 34–280 ms.
- **The reduction is the size of the leaf** except in
  `memoryFieldAsMappingKey`, where it grows from 106 nodes to 175.
- **W is small.** Of the 91 theorems, 48 have W = 3 and only
  `testMemoryTokenArrayAuxiliaryCases` reaches 9. A `memSize` of 400
  nodes, as the plan sets it, is more than 40 times the largest W.
- **Computing these numbers is cheap.** Running the residue and `toL` for
  every leaf of a theorem took at most 5 ms, against 34 ms to 2.5 s for the
  theorem itself.
- **Later steps warn at 20% slower.** A later step that is more than 20%
  slower than this, per file total or on `memoryIndexWriteNse`, gets a
  warning here.

### Step 1: the interpreter lemmas

`Calculus/MemNames.lean` (about 1,560 lines) holds the facts the memory
clauses rest on. It builds in 2.2 s (`lake build`), well under the 20–60 s
the plan estimated. Nothing in `Decide`, `Closer` or `Derive` changed, so
`Derived9`–`11` are as in the baseline. `DecideMem.lean` does not import the
module yet; the clauses of step 3 are its first users.

### Step 2: the syntax beside M6

The target language gains solkey's memory (`LMem`: `addM`, `newArr`,
`copySt`, `write`), its selectors and values (`LSel`, `LMV`), names
(`LId`: a root ordinal and a literal path), a view of a memory object as
storage (`LStor.view`), the copy guard `LTerm.cpok` and `LVal.mem`.
Nothing produces them yet; every exhaustive match keeps them whole
(`.find (.view ..) Q`, `.sok (.view ..)`, `cpok` itself), and `fits` counts
`LMem` nodes. `DecideMem.lean` now imports `Calculus/MemNames.lean`.

**Measured.** All 91 theorems still prove; `Derived9`–`11` check clean.

| | Baseline | Step 2 | Change |
|---|---|---|---|
| `Calculus/Decide.lean`, serial (`Elab.async` off) | 37.2 s | 42.8 s | +15% |
| `Derived9`, `sol_prove` total | 7.9 s | 9.0 s | +14% |
| `Derived10` | 10.1 s | 11.4 s | +13% |
| `Derived11` | 2.3 s | 2.5 s | +10% |
| `memoryIndexWriteNse` | 2.48 s | 2.89 s | +16% |

Two runs agreed within 2%. Every theorem is slower by about the same
fraction, and `memoryIndexWriteNse` spends 2.83 s of its 2.87 s in the
kernel (`profiler`), so the cost is the kernel's, not the search's: the
reductions recurse over a six-type mutual block, and each step of a
recursor now carries 6 motives and 39 minor premises where it carried 3 and
27. No figure is past the 20% warning line, and the `Calculus/Decide.lean` gate
(40%) leaves the derived `DecidableEq`/`ToExpr` in place, but
`memoryIndexWriteNse` is 4 points from the warning: step 4 should
re-measure it first.

### Step 3: the clauses, not yet produced

The memory clauses are defined and proved, and nothing produces them yet:

- **Where they are.** The target language moved out of `Calculus/Decide.lean`
  into `Calculus/DecideLang.lean`, so that the readers
  (`Calculus/MemRead.lean`) sit between the language and the translation
  that will use them. `docs/lean-key-rule-map.md` has one row per clause,
  under "The closer's memory clauses".
- **The readers, at translation.** These are `LMem.readT`, `readI`, `lenT`,
  `nameG`, `structG`, `writeG` and `refDesc`, each exact under the run of
  the memory (`LMem.readT_sim` and the others).
- **The readers, in the elimination.** These are `LMem.readU`, `objU` and
  `LSel.idxU`, with lazy `F` twins and `@[csimp]`. Each is proved to agree
  with its translation-level reader (`LMem.readU_sim`, `LMem.objU_sim`).
- **The view arms.** `readU`, `hasU`, `lenU` and `mapU .map` of an
  `LStor.view` now read memory along the path (`view_read_sim` and the
  others). `okE` of a view is still kept whole, because it needs the run
  guard of the memory.
- **Constants are folded where a term is built.** `Op2.toL`/`Op1.toL` build
  `LTerm.mkBin`/`mkUn`, so `LTerm.ground?` is a test for a literal. This
  closes the earlier review's exponential walk of shared terms. A power past
  `powBig` is not folded.

The pins are in `Examples/Tactics/Decide.lean`, section `MemoryClauses`.

**Measured.** All 91 theorems of `Derived9`–`11` still prove, and so do the
theorems of `Derived1`–`8`. `Derived7`'s language-server worker crashed
when the file was checked whole, so its 40 theorems were checked in two
halves of 20.

| | Baseline | Step 3 | Change |
|---|---|---|---|
| `Derived9`, `sol_prove` total | 7.9 s | 8.2 s | +4% |
| `Derived10` | 10.1 s | 9.5 s | −6% |
| `Derived11` | 2.3 s | 2.2 s | −3% |
| `memoryIndexWriteNse` | 2.48 s | 2.90 s | +17% |

The leaves are smaller than at step 0 where constants are folded:
`memoryDeclDefault` goes from 27 nodes to 21, while `memoryIndexWriteNse`
stays at 534. `memoryIndexWriteNse` is still the
one figure near the 20% line, and the step-2 kernel cost of the six-type
mutual block is all of it.

### Step 3c: the copy guard and the run guard

The step-3 clauses are completed by two guards that Lean needs and KeY does
not. Nothing produces them yet.

- **The copy guard.** `LTerm.cpok` is now eliminated: a word written over a
  word keeps whether a copy into memory succeeds (`save_cpok_sim`), so
  `LStor.cpokU` passes such writes down to `cpok init q`. The closer then
  closes `cpok init q` where the layout types `q` at a type with no
  mapping (`Facts.cpokInit`). It tests `Ty.mapFree`, which the kernel
  evaluates, not `tyHasMapping`, which it cannot; `Ty.mapFree_sound` links
  the two, one struct at a time.
- **The run guard.** `LMem.okU` returns exactly where the memory's run does
  (`LMem.okU_sim`). `okE` of a view is that guard plus `nameG` of the name
  wherever every reference written names an older root (`view_okE_sim`),
  and is kept whole elsewhere.

Both have pins in `Examples/Tactics/Decide.lean`, which now imports
`Calculus/Closer.lean` for the `Facts.cpokInit` pin.

**Measured.** All 91 theorems of `Derived9`–`11` still prove. The new arms
are not reached yet, so the times are those of step 3.

| | Baseline | Step 3c | Change |
|---|---|---|---|
| `Derived9`, `sol_prove` total | 7.9 s | 8.2 s | +4% |
| `Derived10` | 10.1 s | 9.5 s | −6% |
| `Derived11` | 2.3 s | 2.2 s | −3% |
| `memoryIndexWriteNse` | 2.48 s | 2.90 s | +17% |
