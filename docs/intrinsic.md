# Making the model intrinsic

The record of the intrinsic refactor (branch `intrinsic`, 2026-10-07 to
2026-10-09): locals scoped in the syntax (`Stmt C Γ Γ'`, positions `Idx`), a
state typed by its context, a run with no `stuck`, a compiler total on the
scoped syntax, and the calculus over scoped formulas.  Done but for the closer
(M6c, "What is left").  `docs/module-map.md` says where each part lives now.

The full lane notes (M1–M6, W0–W5: what each lane did, its pins, timings and
review), the spike behind Gate G0 and the original design are in this file at
`ad728b16` (`git show ad728b16:docs/intrinsic.md`); docstrings that cite a
section of this record by name ("M6a lane", "W4 item 11", "Decision 17',
implemented", "how `dl{ … }` will write a scoped taclet", …) cite that
version.  It names files by the paths they had at each step, which is why
`scripts/check-doc-paths.sh` skips this record (decision 68).

## What changed

| | Before | After |
|---|---|---|
| Syntax | `Stmt C`, locals by name, unscoped (a branch's local outlived it), a locals check `Stmt.wt` beside it | `Stmt C Γ Γ'` (`Syntax/Scoped.lean`): a local is a position `Idx Γ t` carrying its type (`Scope.lean`), branches, loop bodies and blocks are scopes, a call's body is closed over its own frame; the elaborator emits `Surface.Stmt` (no run, no rule, no `wt`; decision 11), which `resolve` scopes and checks (`Syntax/Resolve.lean`) |
| State | untyped `Semantics.State`: values, storage and heap by name, with junk | `State C Γ` (`Semantics/State.lean`): typed values (`PrimTy.Denote`, a `uint` an `Int` in range), typed storage (`SVal T` over `structDef`, `Storage C`), a typed heap (`HRef H R`, no mapping object), locals computed from the context (`TEnv`) |
| Run | `Stmt.run` on the untyped state, halting by `revert`, `panic`, `diverge` or `stuck` | `Stmt.run` (`Semantics/Run.lean`) on the typed state, halting by `revert`, `panic`, `diverge` or `exhausted` (a push at the bound, decision 15): never stuck; the only run of a statement (W4) |
| Untyped side kept | | the state's operations (`Semantics.lean`), which the typed ones erase to (`StorageErase`, `HeapErase`, `StepErase`), and the erased state `EState C Γ` (`Semantics/Erased.lean`): what the closer's terms read |
| Compiler | `compileStmt` with `wtStmt`, `not_stuck` | over the scoped syntax, locals at their level (`Evm/Compile.lean`), `inFrag` the fragment alone, `compile_correct` over the typed run (`Evm/Correct.lean`), no `not_stuck` |
| Formulas | `Fml C` with modalities over `Stmt C` | `Fml C Γ` (`Calculus/Fml.lean`) with frames (`seq`, `pop .block`/`.capture`) and the hidden binder `bind`; `Update.lean`'s formulas without the modality are `NFml`, the closer's input; `Surface.Fml` is `dl!{}`'s text before the scoped reading |
| Rules | `Taclet C k m s p` on `Stmt C`, `Taclet.sound` by case | the same 159 lines read scoped (`Calculus/Rules.lean`, `open scoped Solidity.Schema`); `Taclet.toStep` (`Calculus/Taclet.lean`) says each is the rule `Stmt.step` fires, so soundness is `Stmt.sound` (`Calculus/Sound.lean`) with no proof per taclet; `blockEmpty` and `functionFrameEmpty` claimed; no cover goal (KeY's two goals); the step rules read the rule set (`⊢ₖ`, decision 36) |
| Sequent | `Proves` over `Hyp` | `Proves C R Γ₀ H φ` over a telescope `Hyps` (`Calculus/Proves.lean`); `Proves.valid` with no hypothesis; a leaf closed by its erasure (`Proves.close`, `Calculus/CloseErase.lean`) |
| Tools | on `Fml C` | `sol_symex`, `sol_prove`, `sol_derive?`, chains, `#chain`, the proof tree, `#wp`, `#step`, specs, contracts, callbacks on `Fml C Γ`; the same text through `open scoped Solidity.Scoped` (`Calculus/Surface.lean`) |
| Names (W5) | `Solidity.Core.X`, `Calculus/Core/*`, `TState`, `trun` | `Solidity.X`, `Calculus/*`, `State`, `run`; the old side's clashing names under `Surface`, `NFml`, `Semantics` (decision 62) |
| SolKey reader | `Corresp.LeanShape` over `Stmt.*` | ported on its branch `intrinsic` (decisions 51–54, 73, 74) |

What stays extrinsic, on purpose: the EVM fragment (`inFrag`, a fact about
the target); function and modifier bodies in `Contract` (typed at each call);
taclet soundness and the closer's completeness (theorems by nature); storage
canonicity beyond shape (`canon`, `tight`: lemmas, so `decide +kernel` keeps
association-list stores); narrow integer widths (the elaborator's); the
fresh-name numbering (`Taclet C k`: labels only, so pins keep `se1`, `sp1`).

## Milestones and waves

| | Status | Work |
|---|---|---|
| M0 | done 2026-10-07 | baselines, the scratch spike, Gate G0 (passes under conditions, below) |
| M1 | done | stuck causes that need no index: a negative `**` exponent or payment reverts, `Simple.lit` in range, `memOk` in the syntax, captures declared, the reference conditional, `Binding.unset` |
| M2 | done 2026-10-07 | `Ctx`/`Idx`/`Thin`, the scoped syntax, `resolve`, the quoter, the lint (`solc_scoped`); elaboration within 10% |
| M3 | done 2026-10-07 | the scoped run over `Env Γ`, the locals checker deleted (M3's run itself went at decision 40) |
| M4 | done (lane `intrinsic-values`, wired at W1–W4) | typed values (4a), storage (4b), heap (4c); `stuck` deleted; the old `Stmt` retired to `Surface` |
| M5 | done 2026-10-07 | the EVM on the scoped syntax, `Sim` by position, `compile_correct`; `wtStmt`, `not_stuck` deleted |
| M6a | done; gate passed (decision 9) | the scoped calculus: `Fml C Γ`, `Frames`, `Premise`, `Stmt.step`, symex, chains, ProofTree |
| M6b | done 2026-10-07 | formula frontends: `cdl!{}`, specs, obligations, callbacks |
| M6c | **in progress** | the closer and `Decide` on `Fml C Γ` ("M6c", "What is left"); 6a parts 1 and 2, 6b (`Decide.lean`) and 6c part 1 (`NFmlUpdateRules`, `StateParts`) partial 2026-10-09 |
| M7 | done 2026-10-09 | the docs; the review pass ("M7 review"; proposals 75–77) |
| W0 | done | the four M6 lanes merged; `Proves.valid` unconditional; `resolve`'s output `Fresh` |
| W1 | done 2026-10-08 | off M3's run: typed-run lemmas (`runlemmas`), typing (`typing`), the EVM (`evm`), the rule table read scoped (`rules`) |
| W2 | done 2026-10-08 | soundness over the typed run (`sound`), the strategy (`symex`), chains (`chains`), the tree (`tree`) |
| W2.5 | done 2026-10-08 | typed soundness of the arms and blocks (`tsoundA`, `tsoundB`); decisions 12–17' implemented (CORE 1, CORE A, CORE B) |
| W3 (a–d) | done 2026-10-08 | the flip: tactics, TestSuite, tree and chains onto the scoped calculus; captures by provenance; the W3 gates |
| W4 | done 2026-10-09 | prep (`theorems`, `contracts`, `moves`), then `sem-del` (the untyped run), `calc-del` (the untyped calculus), `modal` (the modality off `Update.lean`'s formulas), `reader-dry`; W4b: `run40` (decisions 40, 50), `rules36` (36, 53), `printers` (item 14) |
| W5 | done 2026-10-09 | the rename (`scripts/w5-rename.sh`, since deleted), its pins, review fixes, the reader ported |
| W6+ | **left** | M6c |

## Checks at the end (W5)

`lean_build` of `Solidity`, `solkeycheck`, `SolidityCorpus` and
`SolkeyTestSuite`: green.  `check-orphans` (300 reachable), `check-doc-paths`,
`check-rule-text`: OK.  `check-testsuite.sh` against solkey `1b4341a303`: 438
= 435 derived + 1 pending + 1 divergent + 1 excluded (2 skip).  `sorry` 19,
`axiom` 1, `maxHeartbeats` overrides 30, as before the rename; no rule name,
branch label or fresh name changed by W5.  Pins moved only for the reasons
allowed by the plan and decision 20 (each lane section at `ad728b16` lists
them).

## M7 review (2026-10-09)

The read-only finder/skeptic pass of M7; its confirmed findings applied
but for two left as proposals (75, 76):

- **Docstrings to the current design**: the surface syntax's names and
  `resolve` (`Syntax.lean`, `AST.lean`), `Stmt.wk`/`Prog.wk`/`Idx.wk` as the
  documented kernel exceptions to condition 1 (`Scope.lean`,
  `Syntax/Scoped.lean`), `Surface.Prog.quote` (`Syntax/Splice.lean`,
  `Syntax/Quote.lean`), the elaborators of each tactic
  (`Calculus/TacticSyntax.lean`, `module-map`), `Surface.Fml.quoteAuto`
  and `NFml.eqD`/`NFml.eq` (`Calculus/SurfaceNotation.lean`), the typed run
  (`Semantics/Run.lean`, `StepErase`), W5 self-citations
  (`Calculus/{Step,Completeness,RuleExists,Rules,Callback}.lean`),
  `Theorems.lean`'s two statements not restated, the rule table's untyped
  rationales (`whileInvariantBox`, `Premise.inv`,
  `memoryIndexWriteCaptureAllNonSimpleIndex` and its rule-map row: kept as
  a deviation in shape, the rule text and fresh names unchanged),
  `Seq.ground`/`Seq.refutes` for `Derive.splitRes`, `TRun.send` for
  `Semantics.sendAt`, `NFml.Chain.groupSteps`, `Rule.premise_unique`,
  `Modality.onTHalt`/`afterRunTR`; the examples that called a formula "not
  valid" over untyped states now say the leaf is closed on its erasure
  (until M6c: `Examples/{ProofTree,Tactics/Decide,Benchmark/Mapping,
  Tactics/UpdateRules,Tactics/Calls,Tactics/Loops}.lean`); the EVM's
  docstrings and `docs/compiler-verification.md`.
- **Dead code deleted**: `Semantics.lean`'s untyped evaluators over
  `Surface` syntax (`Surface.Src.value`, `MLoc.write`, `MSrc.mval`,
  `MLoc.addr`, `OpLoc.store`, `OpLoc.bump`, `Src.pushVal`,
  `ExtCall.key`, `Semantics.sendAt`/`guardOk`/`assertOk`/`opLocal`/
  `bumpLocal`) with their `_frame` (`Agree`) and `_noPanic` (`NoPanicOps`)
  lemmas; `bindData_induct` and the `Counter` witness (`Reachability`),
  `kernelRefl`, `Semantics.State.valueOf`, `bind_bind_ok`/`_error`,
  `sidePreds`/`clear_side`, `CLTy`.
- **Types carry what they can**: `defaultOk` premises (decision 16),
  `Invariant.fo` (decision 24), `inFrag` no longer re-checks
  `p != .bool` (the `*_sim` lemmas take `p.isNumeric`, `numeric_of_ne`
  replaced by `ne_bool_of_numeric`).
- **Weakened statements**: `Problem.deploy_of_valid` restated for any
  parameters (decision 23); `reachable_iff`'s `FitsStorage` recorded
  (proposal 77, `module-map`).
- **Tools**: `side_cond` reads the scoped predicates (`Calculus/Rules.lean`);
  the walk line `apply unfoldStep` takes no argument (was
  `apply unfoldRule (Stmt.step _ _ _).rule`, whose argument was never
  read); `#chain`/`#derivation` on an unscoped formula say so
  (`notScopedNotation`); `Evm/Examples`' `rejects`, and `compiles`
  conjuncts on the runs the empty program would also satisfy.
- **`simp only`**: the bare `simp`s the branch added
  (`Constructibility`, `Reachability.Canon.init`, `Agree`, `Syntax.lean`'s
  four `simp [hd]`) replaced by `simp?`'s lists.

Checks: `lean_build` of `Solidity`, `solkeycheck`, `SolidityCorpus` and
`SolkeyTestSuite` green, no pin moved; `dups.py` reports only false
positives (`as`, and `Delab.delabFml`/`delabProves`, which the script
places in `Solidity` because a docstring line of `Calculus/Delab.lean`
starts with `end`); `check-orphans` (300 reachable; the four orphans are
the git-excluded `Scratch/` modules), `check-doc-paths`, `check-rule-text`:
OK; `check-testsuite.sh` against solkey `1b4341a303` (read-only
`git archive`): 438 = 435 derived + 1 pending + 1 divergent + 1 excluded
(2 skip).  `sorry` 19, `axiom` 1, `maxHeartbeats` overrides 30, as before.
Not re-timed: no kernel-evaluated function changed (`inFrag` lost a
conjunct; `Evm/Examples` gained three `compiles` checks).

## Gates

**G0 (M0), passes under conditions.**  The positional design against the
named one, on a 43-statement spike checked by the kernel:

The spike (the scratch module `Solidity/Scratch/IntrinsicSpike`, not committed) has seven
statements (`assignLocal`, `declLocal`, `declStorage`, `write`, scoped `ite`,
`loop`, `call` over a closed frame), `Prog Γ Γ'` with a variable output
index, `Frames` with `pop .capture`/`.block`, `storageFieldRead_unfold_rightFst`
as a capture and `ifElseSplit` into `pop .block`, a typed run, `resolve` from
the named toy, hand quoters, and a symex checked by the kernel (`Eq.refl` of
the compiled-and-quoted result, `Environment.addDeclCore`, timed). The program
has 43 top-level statements (five blocks; the symex variant drops the loop
and the call). U is today's shape: names, unscoped locals, `stuck`,
`thn ++ ω`.

| Variant | symex, kernel | run, kernel | result DAG (hash-consed) |
|---|---|---|---|
| U, names (reference) | 3.8–3.9 s (500 steps) | 164–184 ms | 1170 |
| I, `(Var × LTy)` contexts, `match` | 51.8 s | 380 ms | |
| J, `LTy` contexts, `match` | 45.1 s | 293 ms | |
| K, `LTy` contexts, `casesOn` + structural | 6.5 s (686 steps) | 44 ms | 1566 |
| **K, `Fml.rec` step + `implemented_by`** | **3.0–3.3 s (0.8×)** | **44 ms (0.25×)** | **1566 (1.34×)** |

- Kernel ≤ 1.3×: yes for K with the recursor step (0.8× symex, 0.25× run).
  The literal's own check is 0.8 ms against 0.15 ms (5×, negligible).
- Quoted size ≤ 2×: yes as a hash-consed DAG (result 1.34×, literal 1.96×);
  unshared trees are 26–37× larger, because every node carries its contexts.
- No `Meta.reduce` fallback: the quoter covers every constructor of the
  closed term, `Idx`/`Ext`/`Frames` included.
- `cases` with no generalisation: works on `Prog Γ Γ'`, `Prog Γ Γ`,
  `Prog [] [t]` and `Stmt Γ (t :: Γ)` (the cyclic index is closed by
  acyclicity); `induction` on `Idx` and a structural proof of `run_append`
  work too.

The named-scope retry was not needed. The conditions, which M2–M6 follow:

1. **No `match` on an indexed family in kernel-evaluated code.** The equation
   compiler casts every index (`x = a → x₁ ≍ x₃ → motive`, then `Eq.ndrec`)
   even for `_` patterns, and the kernel pays a context comparison per cast:
   11–13× on symex, 4× on a fold. Hot functions use `T.casesOn`/`T.rec` with
   the motive generalising the indices and the dependent arguments passed
   after it (`Prog.casesOn (motive_2 := fun Γ Γ₁ _ => Frames Γ₁ Γ₀ → …) P … κ`).
   `match` stays fine on parameter-only families (`Expr Γ`, `SPath Γ`) and on
   elaboration-time code (`resolve`, quoters).  `Stmt.wk`/`Prog.wk` are not
   elaboration-time only: `ifElseUnfold` runs `Prog.wk up` in the kernel
   (`Calculus/Core/Step.lean`); a rule's expression schema variables use
   `Val.up` and its kin instead, which match only on parameter-only
   families.
2. **The fastest form is `T.rec` + an `@[implemented_by]` twin** written with
   `casesOn` + structural recursion (the code generator rejects `T.rec`),
   linked by a theorem (`stepR_eq`, by induction, `show`/`rw`/`rfl`).
   `casesOn` + structural alone compiles and costs 1.7×.
3. **Labels stay out of the index**: `Ctx := List LTy`, the name on the
   binder (`declLocal x`, `Args.cons x`). With `(Var × LTy)` the literal is
   three times larger (tree 206k against 67k) and symex 15% slower.
   `resolve` and printers keep the names beside the context
   (`List (Var × LTy)` and its `map (·.2)`).
4. **`Env Γ` is computed from Γ** (`Unit`, `t.Denote × Env Γ`), not an
   inductive family: `get`/`set`/`drop` are recursions on `Idx`/`Ext` over
   projections, no casts. That is the 0.25× run.
5. **Scope ends are suffixes** (`Ext Γ Δ`: `refl`, `push`) rather than the
   general `Thin`; `Prog.ext` and `Ext.trans` recurse on one argument.
   `Thin` with `keep` is only for `Stmt.wk`/`Prog.wk`.
6. **No administrative steps**: `Premise.fml` takes the rest ω and the frames
   κ apart, so an update continues into `box ω κ φ`, not into
   `box nil (seq ω κ)` (that doubled the steps and cost 1.23×).
7. **The quoter hash-conses contexts** (`ShareCommon`, or a per-context cache).

Pitfalls met: a `casesOn`-style definition has no per-constructor equations
(`simp [f]` loops on `f.eq_1`), so the rule lemmas are stated by hand and
proved by `rfl`; mutual `casesOn` motives are `motive_1`/`motive_2`; Lean
promotes a uniform first index to a parameter (`Premise`, `Ext`), which
changes the motive and breaks structural recursion unless that argument is
bound before the colon; inside `if x = y then match u, t with …` the
fall-through arm loses the refinement of `t`, so compute it before the
`match`. `Stmt.wk` is stated as
`Thin Γ Δ → Stmt Γ Γ' → (Δ' : Ctx) × Thin Γ' Δ' × Stmt Δ Δ'` (mutual with
`Prog.wk`) and elaborates as is.

**M6a (decision 9)**: the scoped symex about 2.9× faster on aggregate,
outside 20% on three small programs by 3–23 ms; ruled passed.  **M2**:
`sol{}` sites within 10%.  **M3**: Typing within 20% (10% faster).
**M4**: the concrete stores and the typed run within 20%.  **M5**: `stmt_sim`
within its heartbeats (now `10000`), `Evm/Examples` within 20%.

The **W3 gates** at the W4 preparation (limits M0 + 20%; `bcbaa0b` against
`31951be`, each file copied under `Solidity/Scratch/` and opened in a fresh
worker, wall from its start to its last CPU, the minimum of two runs; the
last column on the W3d integration's scale):

| Module | Limit | `31951be`, raw (min) | merged, raw (min) | ratio | merged, on the integration's scale |
|---|---|---|---|---|---|
| Derived9–11 | 22.9 s | 23.68 s (7.80 + 12.03 + 3.85) | 23.53 s (7.81 + 11.86 + 3.86) | 0.99 | about 22.3 s, within |
| `TestSuite/Problems` (`legacy`) | 1.44 s | CPU 0.67 s | CPU 0.64 s | 0.96 | 1.03 s |
| `TestSuite/CoreProblems` | 1.44 s | CPU 1.23 s | CPU 1.22 s | 0.99 | 1.33 s |
| `Examples/ProofTree` | 12.1 s | 13.37 s | 10.90 s | 0.82 | about 10.5 s, **within** (was 12.9 s, over) |
| `Examples/Chains/Storage` | 9.0 s | 8.09 s | 8.05 s | 1.00 | 7.6 s |
| `Solkey/TestSuite` | 12.5 s | 11.54 s | 11.43 s | 0.99 | 10.1 s |
| `Examples/Benchmark/Syntax` | 1.44 s | CPU 1.52 s | CPU 1.48 s | 0.97 | 1.44 s, at the limit (file and imports unchanged: as W3d) |

`ProofTree` is back within: `w4-contracts` moved its chain sections to
`Tactics/CoreChains` (the lead's approval), the 0.9 s the W3d gates lane
attributed to them.  The aggregate is about 53.0 s against 59.4 s of
limits (54.3 against 60.8 with `CoreProblems`): **under by about 6.4 s**
(W3d: 3.7 s).  Every row within or at its limit; nothing slowed by the
three lanes.

The **M0 rows** re-timed at the W4b integration (`64d115c` against
`78182e5`, the same method; the wall includes the worker's wait for `lake
setup-file`, so the CPU column is the steadier):

| M0 row | M0 | `78182e5` | merged | ratio | CPU, `78182e5` → merged |
|---|---|---|---|---|---|
| `TestSuite/Derived9` | 7.0 s | 7.96 s | 7.96 s | 1.00 | 8.68 → 8.65 s |
| `TestSuite/Derived10` | 9.3 s | 12.07 s | 12.08 s | 1.00 | 12.98 → 12.99 s |
| `TestSuite/Derived11` | 2.8 s | 4.00 s | 3.97 s | 0.99 | 3.44 → 3.44 s |
| `TestSuite/Problems` (`legacy`) | 1.2 s | 1.60 s | 1.55 s | 0.97 | 0.68 → 0.66 s |
| `TestSuite/CoreProblems` | — | 2.14 s | 2.15 s | 1.00 | 1.24 → 1.23 s |
| `Solkey/TestSuite` | 10.4 s | 11.80 s | 11.84 s | 1.00 | 11.19 → 11.11 s |
| `Examples/Benchmark/Syntax` | 1.2 s | 2.17 s | 2.18 s | 1.00 | 1.54 → 1.52 s |
| `Examples/ProofTree` | 10.1 s | 10.53 s | 10.63 s | 1.01 | 9.80 → 9.93 s |
| `Examples/Chains/Storage` | 7.5 s | 8.34 s | 8.23 s | 0.99 | 8.03 → 7.90 s |
| `Evm/CoreExamples` (`Evm/Examples`' row) | 9.5 s | 8.42 s | 8.52 s | 1.01 | 7.95 → 8.05 s |
| `Evm/CoreCorrect` (`Evm/Correctness`' rows; changed by `run40`) | 25.6 s | 2.45 s | 2.40 s | 0.98 | 6.02 → 6.05 s |

Nothing slowed: every row within ±1.5% of the tree before the lanes, in
wall and in CPU.  Only `Evm/CoreCorrect` of these files changed (`run40`).

Not re-timed after W5 (a rename changes no elaboration); the W6 baselines
below re-time them.

**W6 baselines** (2026-10-09, `8761bbde`, no code change): the erased
form's timings that M6c's gates compare against.  Method: the file copied
under `Solidity/Scratch/` and opened in a fresh worker through the Lean MCP
(`lean_diagnostic_messages`), one worker at a time, every import built
beforehand (a warm-up module importing all of them), `/proc` sampled every
20 ms, the worker killed after each run.  Two passes of three runs each:
pass 1 measures the wall from the worker's start to its last CPU (the
integration's method); pass 2 also keeps the CPU series and measures the
wall to the *end of work*, the first sample at which the worker's CPU is
within 50 ms of its final value.  The two differ because the worker
spends a tick of CPU (10 ms) at whole seconds after its start
(x.04–x.07 s) while the MCP is still polling it: 50 of the 144 runs ended
on such a tick, 0.4–7.4 s after the end of work.  The minimum of three
filters most of them out, but not pass 1's `Derived1` (8.05 s against
7.32), `Problems` (1.05 against 0.81) and `ScopedProblems` (2.04 against
1.39).  **The gate column is the end of work**, pass 2's
minimum; a ported module is timed the same way.  CPU is the worker's
user + system time, the minimum of the six runs (above the wall where
Lean elaborates declarations in parallel).

Machine: Intel i9-13900 (32 threads), 64 GB, the 32 GiB session cgroup at
9.0–11.0 GB throughout.  Load average (1 min) at each worker's start:
pass 1 (06:45–07:09) 0.43–3.98, median 0.76, its first six runs
(`Derived9`, `Derived10`) at 2.0–4.0 while another session's work wound
down (pass 2's end of work, at load under 1.3: 7.16 and 11.11 s against
pass 1's 7.17 and 11.33); pass 2 (07:10–07:35) 0.24–1.24, median 0.76.

| Module | wall, last CPU (pass 1 min) | **wall, end of work** (pass 2 min; the three runs) | gate (1.2×) | CPU (min) | peak RSS |
|---|---|---|---|---|---|
| `TestSuite/Derived1` | 8.05 s | **7.32 s** (7.38, 7.39, 7.32) | 8.78 s | 8.98 s | 3.2 GB |
| `TestSuite/Derived2` | 8.77 s | **8.63 s** (8.69, 8.63, 8.76) | 10.36 s | 10.38 s | 4.1 GB |
| `TestSuite/Derived3` | 13.05 s | **13.01 s** (13.03, 13.03, 13.01) | 15.61 s | 14.48 s | 4.8 GB |
| `TestSuite/Derived4` | 17.56 s | **17.57 s** (17.75, 17.66, 17.57) | 21.08 s | 19.61 s | 5.4 GB |
| `TestSuite/Derived5` | 7.07 s | **6.95 s** (6.97, 6.97, 6.95) | 8.34 s | 8.23 s | 3.4 GB |
| `TestSuite/Derived6` | 11.47 s | **11.42 s** (11.49, 11.42, 11.43) | 13.70 s | 13.00 s | 4.8 GB |
| `TestSuite/Derived7` | 50.45 s | **50.43 s** (50.53, 50.66, 50.43) | 60.52 s | 52.88 s | 7.8 GB |
| `TestSuite/Derived8` | 26.27 s | **26.38 s** (26.43, 26.38, 26.44) | 31.66 s | 27.50 s | 6.3 GB |
| `TestSuite/Derived9` | 7.17 s | **7.16 s** (7.16, 7.23, 7.19) | 8.59 s | 8.62 s | 3.4 GB |
| `TestSuite/Derived10` | 11.33 s | **11.11 s** (11.21, 11.28, 11.11) | 13.33 s | 12.75 s | 4.6 GB |
| `TestSuite/Derived11` | 3.23 s | **3.16 s** (3.24, 3.22, 3.16) | 3.79 s | 3.36 s | 2.2 GB |
| `TestSuite/Derived12` | 13.27 s | **13.17 s** (13.17, 13.35, 13.29) | 15.80 s | 14.01 s | 4.3 GB |
| `TestSuite/Derived13` | 6.33 s | **6.36 s** (6.36, 6.39, 6.36) | 7.63 s | 6.38 s | 2.9 GB |
| `TestSuite/Derived14` | 11.05 s | **10.89 s** (10.89, 10.92, 11.00) | 13.07 s | 11.50 s | 3.8 GB |
| Derived1–14, sum | 195.1 s | **193.6 s** | 232.3 s | 211.7 s | |
| `Examples/Tactics/Decide` | 49.42 s | **49.14 s** (49.14, 49.75, 49.40) | 58.97 s | 49.97 s | 2.0 GB |
| `Examples/ProofTree` | 9.89 s | **9.81 s** (9.81, 9.95, 9.97) | 11.77 s | 9.85 s | 1.6 GB |
| `Examples/Chains/Storage` | 7.51 s | **7.45 s** (7.45, 7.49, 7.55) | 8.94 s | 7.86 s | 1.6 GB |
| `Examples/ChainRewrites` | 6.34 s | **6.36 s** (6.36, 6.37, 6.36) | 7.63 s | 7.24 s | 1.6 GB |

The M0 rows, the same runs (M0's limit is M0 + 20%; W4b's wall is the
merged column of the table above, and its CPU):

| M0 row | M0 limit | W4b wall | **W6, end of work** (last CPU, pass 1) | W4b CPU → W6 CPU |
|---|---|---|---|---|
| `TestSuite/Derived9` | 8.4 s | 7.96 s | **7.16 s** (7.17) | 8.65 → 8.62 s |
| `TestSuite/Derived10` | 11.2 s | 12.08 s | **11.11 s** (11.33) | 12.99 → 12.75 s |
| `TestSuite/Derived11` | 3.4 s | 3.97 s | **3.16 s** (3.23) | 3.44 → 3.36 s |
| `TestSuite/Problems` (`legacy`) | 1.44 s | 1.55 s | **0.81 s** (1.05) | 0.66 → 0.63 s |
| `TestSuite/ScopedProblems` (was `CoreProblems`) | — | 2.15 s | **1.39 s** (2.04) | 1.23 → 1.21 s |
| `Solkey/TestSuite` | 12.5 s | 11.84 s | **10.83 s** (10.92) | 11.11 → 10.95 s |
| `Examples/Benchmark/Syntax` | 1.44 s | 2.18 s | **1.41 s** (1.44) | 1.52 → 1.49 s |
| `Examples/ProofTree` | 12.1 s | 10.63 s | **9.81 s** (9.89) | 9.93 → 9.85 s |
| `Examples/Chains/Storage` | 9.0 s | 8.23 s | **7.45 s** (7.51) | 7.90 → 7.86 s |
| `Evm/Examples` (was `CoreExamples`) | 11.4 s | 8.52 s | **7.75 s** (7.81) | 8.05 → 8.00 s |
| `Evm/Correct` (was `CoreCorrect`) | 30.7 s | 2.40 s | **1.68 s** (1.73) | 6.05 → 5.92 s |

Nothing slowed since W4b: the CPU of every M0 row is within −5% to 0% of
W4b's.  The walls are 0.7–1.0 s lower throughout, the share of W4b's wall
that was the worker's wait for `lake setup-file` (here every import was
built and traced before the first run).  Every M0 row is within its
M0 + 20% limit, raw (`Derived10` by 0.05 s, `Benchmark/Syntax` by 0.03 s).

## Decisions

1–10 are the user's (2026-10-07: "implement all of them"); 11–21 the
lead's.  Proposals 22–74 were the lanes', each "the lead's call":
**approved** 22–29 (2026-10-09: 27 and 28 together, explicit `∀`s marked by
`cdl!` keep their range and `allRight` line, `Seq.pick` on the parameters
only), 30–32 (30 a recorded deviation, 31 interim until W4 `contracts`),
33–53 (36 implemented at W4b `rules36`; 40 and 50 at W4b `run40`; 53 before
W5); **no recorded call yet**: 54–74, implemented as proposed.

1. If a speed gate (G0, M6a) fails, the calculus takes Church-typed program
   variables (KeY's `\programVariables`); every other layer stays intrinsic.
2. Locals are block-scoped (popped at the end of `if`/loop/`try`/block), as
   solc; each changed behaviour gets a `docs/solc-alignment.md` row.
3. `uint` values are `{n : Int // p.admits n}` (keeps 56642ee's kernel path).
4. Storage is typed (`SVal : Ty → Type` over `structDef`, M4b).
5. The SolKey reader (side-projects `lean/solkey`) is regenerated on a branch
   there when M6a breaks it.
6. The closer and Decide are ported (M6c); `Fml.erase` is a bridge only.
7. All milestones run; a failed gate takes its stated fallback, not a stop.
8. The bridge (typed `Core` beside the untyped `Stmt`) ends at M4, not M7.
   *Replaced by 11: it ended at W4.*
9. **The M6a gate counts as passed.**  The scoped symex is about 2.9×
   faster on e1×5 and e3×10 (3.2 s against 9.0 s in total); it is outside
   the 20% gate on e2 (1.42×), e4 (1.27×) and e2×10 (1.23×), each by
   3–23 ms, a cost to reduce (the kernel's comparison of contexts) rather
   than a trigger for Decision 1's fallback.  The calculus stays
   positional.
10. **A `bool` mapping key follows solc**: it is hashed as the word `0`/`1`,
   so the typed path takes the key as the `Int` `0`/`1`
   (`docs/solc-alignment.md`, "`bool` mapping keys").

11. *The untyped `Stmt`* (lead, 2026-10-08, open to the user's override
    before W4; replaces Decision 8: the bridge ends at W4): the
    untyped `Stmt` survives only as `Surface.Stmt`, the elaborator's output and
    the printers' target, with no run, no taclet and no `wt`; every
    semantics is on Core.  `NFml` (today's `Fml` with `.modal` removed)
    stays the closer's input until M6c.

12. *Hidden binder at a memory type*: option (c). `Fml.bind` takes the
    modality; under the diamond it asks for an inhabitant of the binder's
    typed domain, under the box it stays universal. Printed as today; memory
    locals stay non-dangling.  *Superseded by 17'.*
13. *Array length past `uint`'s range*: bounded by the type. A dynamic
    array's typed value carries `length < 2^256` (push at the bound
    reverts, as an out-of-gas stand-in, with a solc-alignment row), so the
    typed run never diverges on a length read and `len` on an erasure is in
    range.  *Amended by 15: the push at the bound is `exhausted`.*
14. *`bool` mapping key*: `Update.lean`'s key read (and M3's run) hash a
    `bool` as 0/1, as solc and the typed run do; `bridgeOk` drops its
    bool-key exclusion.

15. *Push at the bound*: resource exhaustion, read as KeY reads gas (not at
    all). The typed run's push at the bound ends in a new halt `exhausted`
    that both modalities accept, like solkey, which models no gas; the
    TestSuite's pushing diamond obligations stay provable. solc-alignment
    row: solc panics (0x41) on a storage array past 2^64 elements; Lean's
    bound is 2^256 and an exhausted run proves any modality. The `NoDiv`
    hypotheses of the push arms go.
16. *Copy off the bridge*: the elaborator rejects a struct with a repeated
    member name, as solc does ("Identifier already declared"); `BadDup`
    becomes a pinned elaboration error; `bridgeOk` and `Ty.nodupS`
    hypotheses go.  *M7 review:* so does `defaultOk`, which existed for the
    same reason: `defaultOk_true` (from `structDef_nodup`, now in
    `AST.lean`), so `defaultForTy_hasTy`, `defaultForTy_canon`,
    `pushSlot_hasTy`/`_canon`, `pushPlaceAt_wt`/`_canon`,
    `allocDefault_typed`/`_canon`, `StateWT.init`, `RunWT.init`,
    `Canon.init` and `reachable_canon` lose the premise, and
    `defaultOk_of_defaultOkS`/`defaultOk_struct_of_mem` are deleted.  The
    closer's `defaultForTy_canonB` keeps its (now vacuous) `okDeep` premise
    for its callers in `Closer`/`Decide` until M6c.
17. *`memoryLocalDeclInitDrop` under the box*: change the typed reading, not
    the rule text: the hidden binder at a memory type ranges over the
    references of the heap grown by the initializer's allocations (or any
    heap extension), so the premise is not vacuous where the conclusion
    allocates. Existing box derivations must keep closing. If that proves
    infeasible, `Proves.tsound` threads `Stmt.TArmOk` as an invariant of
    reachable states instead; record which.  *Infeasible
    (`Stmt.not_tsound`); replaced by 17'.*

17'. *Memory locals may be unset*, as storage aliases already are (M1e):
    `LTy.TDenote (.mem R)` is `Option (HRef H R)`; a read of an unset memory
    local reverts; the typed run's `declMem` always binds `some`. The hidden
    binder then has an inhabitant at every type, so Decision 12's diamond
    inhabitant clause and `LTy.inhabited` go, `Stmt.TSound C` becomes
    provable unconditionally and `Proves.tvalid` loses its hypothesis.
    solc-alignment/rule-map rows as for `unset` aliases.
18. `Proves.close` on diamond updates that keep `bool` locals (`Upd.boolB`)
    is approved as the interim M3 closer; the typed reading replaces it.
19. `CallRet.isRets` follows solkey's rule map (rows 54/55): a memory
    return steps by `internalCallExpand`, not `functionBodyExpand`.
20. Two more pin reasons are allowed: (7) a `#check` printing the flip's
    type (`Fml C` → `Core.Fml C []`); (8) `blockEmpty` on an inlined
    callee's body (solkey's `blockEmpty`, now claimed).
21. `Derived7`'s `case leaf2` may go (one fewer residual leaf), recorded as
    the one deviation from "Derived1–14 text unchanged".
22. *Proposed (CORE B), the lead's call:* an update's typed reading asks the
    typed states it reads past it to extend the heap typing it is applied
    in (`σ.H <+: σ'.H`), as a typed run's end state does; it makes the
    `TokenCopy` merge across a memory binder sound.
23. *Proposed (CORE B), the lead's call:* `Problem.deploy_of_valid_nil`
    takes a typed transaction and asks the typed run to end (`TRes.Ends`);
    `Problem.deploy_of_valid_typed` states the typed deployment with no
    hypothesis.  *M7 review:* master's `Problem.deploy_of_valid` is restated
    for any parameter list (`Calculus/Deploy.lean`: for every typed value
    of the parameters, `State.deploy` with them bound, via
    `holds_closeN`); `_typed` is its case of none.
24. *Proposed (W3c `tactics`), the lead's call:* `ProvesC.valid` asks the
    invariant first-order (`Fml.FO`, KeY's `CInv` of the storage and the
    ledger): "the invariant holds" is then a fact of the erasure, which the
    callee's havocked state and the updates read; today's asks it closed.
    *M7 review:* `Invariant` carries it (`fo := by rfl`, as master's carried
    `closed`), `noTransfer` is a lemma of it (`Fml.hasTransfer_of_FO`), and
    `ProvesC.valid`/`Main.callback_soundness` take no hypothesis.
25. *Proposed (W3c `tactics`), the lead's call:* `Core.Proves.closeHolds`,
    today's semantic `Proves.close` over the typed reading (modal-free), is
    a rule of the scoped sequent beside the erasure's `close`; the steps
    after the program (`eqDSplit`, `applyOnRigidBox`, `simplify`, the goal's
    `rewrite`, `assumeInv`, `openInv`) are derived from it, as today's are
    from its `close`, and only `merge` and `updRw` are rules of their own.
26. *Proposed (W3c `testsuite`), the lead's call:* `Core.Proves.closeFalse`
    (today's rule) and the scoped walk's pruning of a ground split whose
    branch the closer refutes (`Seq.ground`, `Seq.refutes`).
27. *Proposed (W3c `testsuite`), the lead's call:* a leaf's leading `∀`s
    (parameters and explicit ones alike) are kept, with their ranges, only
    where stripping them leaves the leaf open and keeping them closes it
    (`Seq.pick`).
28. *Proposed (W3c `tree`), the lead's call:* mark the parameters in
    `cdl!`'s output, so an explicit `∀` always keeps its range and gets its
    `allRight` line in the short walk.
29. *Proposed (W3c `tree`), the lead's call:* `#verify` is scoped whatever
    the caller's scope, and a witness's after-line drops `\result`.
30. *Proposed (captures by provenance), the lead's call:* `captureExpr`
    skips a fresh name only outside the inlined ranges (`ElabScope.inlined`);
    a program's own fresh-shaped local is still read as a written-out
    capture (`uint se1 = 0; y = se1++ + se1;` stays as before), since a pure
    provenance set would re-capture every written line's captures.  See
    "Captures by provenance" below.
31. *Proposed (W3d `w3rest`), the lead's call:* the scoped contract rule
    (`Calculus/Core/FunContract.lean`) reads `requires`/`ensures` at the
    callee's frame (the parameters, then the return variables), "post"
    reads the parameters at the arguments' values, so the body may write
    its return variables only (`writesRets`, by `rfl`); `\old` is not read
    (no `old`/`oldNet` snapshot in the obligation); a call that leaves
    several results or a memory return has the goal `false`; an `ensures`
    that is not first-order weakens to `true` (`Fml.wkD`).  Today's rule
    read the parameters at their values after the body, with a freshness
    side condition (`CallRet.freshFor`), and took `\old` and every return
    shape.  These interim limits are lifted by W4 `contracts`
    (`Calculus/Core/FunContract.lean`; proposal 33).
32. *Proposed (W4 preparation), renumbered from 31 at the W3d integration, the lead's call:* the corpus reads the typed
    run.  An obligation is `Corpus.Diamond (Core.TState.init C) P`, the
    program resolved and `⟨ Q ⟩ true` read by `Core.holds` (`Runs`), so an
    exhausted run counts as solkey's (decision 15: the docstrings say "ends
    normally, or is exhausted"; `corpus_decide` proves only a normal end,
    so the probe still marks an exhausted run `open`, and no row is one); a
    `TestSuite` corollary is `Obligation.Diamond`/`Box` of the obligation `N.f.problem` (its
    program is the one `⊢` derived; the surface `N.f` cannot be tied to it
    in the kernel: `rfl` fails at elaboration and `Core.Prog` has no
    `DecidableEq`); and the 16 `evaluated` rows, which `corpus_decide`
    proves since W1 `evm` made it typed, are `proved` (their `#eval` pins
    replaced by theorems).  See "W4 preparation" above.
33. *Proposed (W4 `moves`), the lead's call:* `Calculus/SurfaceNotation.lean` and
    `Calculus/SurfaceSpec.lean` leave `calc-del`'s list: the elaborator's frontends
    (`dl!{ … }`, `spec[C]{f}`), which use no deleted module and which the
    scoped reader reads; the `modal` lane types their output.  See "W4 lane
    `moves`".
34. *Proposed (W4 `moves`), the lead's call:* `Calculus/NFmlLogic.lean` and
    `Calculus/NFmlDerive.lean` leave `calc-del`'s list: today's `Proves` is the
    closer's sequent calculus on the erasure (`Rewrite`, `TheoryRewrite`,
    `Derive.residue`, `Proves.of_residue`) until M6c; the `modal` lane trims
    their program rules (and the program-rule soundness modules with them).
    Keeping them keeps 9 of `calc-del`'s 21 modules reachable: `Logic`,
    `Derive`, `RuleSoundness`, `SoundUpdate`, `SoundKit`, `SoundUnfold`,
    `SoundLoop` (through `Logic`), `Symex`, `Completeness` (through
    `Derive`'s `Proves.closeTrue`), and today's `Rules` body; `ProofTree`,
    `Sequents`, `Chains` are cut from it.  See "W4 lane `moves`".
35. *Proposed (W4 `moves`), the lead's call:* `Calculus/Core/RuleText`
    (the scoped rule lines against today's) goes with today's rule table.
36. *Proposed (W4 `theorems`), the lead's call:* the scoped `Core.Proves`'
    step rules read the rule set, so that under `.solkey` the step's rule
    must be a `Taclet` (a low-module edit to `Calculus/Core/Proves.lean`);
    then the judgement-level `solkey_eq_calculus` and `solkey_lt_calculus`
    are restated and `Taclet.premise_inSolkey` ported.  Until then
    `solkey_eq_calculus` is dropped (it holds of every formula) and
    `solkey_soundness` is `soundness'`.  See "W4 lane `theorems`".
37. *Proposed (W4 `theorems`), the lead's call:* the scoped sequent input
    notation lives in its own scope `Solidity.Core.Sequent`; W5 may fold it
    into `Surface`.  See "W4 lane `theorems`".
38. *Proposed (W4 `contracts`), the lead's call:* `ensures` always
    stands at the snapshots (`rs ++ Olds ++ ps`), as today's rule always
    took them, so a contract with no `\old` still lists `old, oldNet` in
    its `cdlIn`; the obligation is
    `requires → {old := storage ‖ oldNet := net} [ T r; { body } ] ensures`,
    the body printed as a block; a memory return is declared in "post"
    (`[ T memory r; ]`) rather than bound by `∀` (no binder ranges over an
    object not yet in the heap).  See "W4 lane `contracts`" below.
39. *Proposed (W4 `sem-del`), the lead's call:* today's interpreter
    (`Stmt.run`/`Prog.run`/`Loop` of `Semantics.lean`), `Halt.stuck`, the
    old run's frame lemmas (`Stmt.run_frame`/`Prog.run_frame`,
    `Semantics/Agree.lean`) and `Semantics/Mutability`'s frame lemmas
    stay until the `modal` lane: they are the reading of today's
    `Fml.modal` (`Update.lean`'s `holds`, `holds_frame`) and of the program
    rules of today's `Proves`, which decision 34 keeps past `calc-del`
    (`Logic`'s `Proves.valid` through `RuleSoundness`, `SoundLoop`, …).
    `sem-del` before `modal` cannot delete them without deleting those
    rules; the `modal` lane deletes them with `.modal`.  `Halt.stuck`
    becomes the term model's `undef` then, when no run produces it.  See
    "W4 lane `sem-del`" below.
40. *Proposed (W4 `sem-del`), the lead's call:* M3's scoped run
    (`Semantics/Core.lean`'s `Run.*`, `Stmt.run`/`runR`/`runC`, `Loop`) and
    `Semantics/Core/TypedRunErase` stay, for a lane of their own
    after W4: they are the bridge every update arm's soundness goes through
    (`Premise.sound_update_run`, `Calculus/Core/SoundKit.lean`: an arm is an
    equation `U.apply σ.erase = s.run σ.erase`, carried to the typed run by
    `Stmt.trun_erase`), and the run `Typing/` reads (`ReachableS`, the
    builder's `Prog.keeps_canon`/`run_tight` carried to the typed run by
    `Prog.trun_of_run`, `Stmt.run_wt` read by `SortCheck/Faithfulness`).
    Its deletion is a re-proof, not a move: each update arm against the
    typed step (`TRun.*`, through the per-step erasure lemmas of
    `TypedRunErase`), the builder over the typed run, `Faithfulness` over
    `TState`.  M3's `State C Γ`/`Env` stay regardless: they are the erased
    state the closer's untyped terms read (`TState.erase`), until M6c.
41. *Proposed (W4 `calc-del`), the lead's call; amends 34:* `Calculus/NFmlLogic.lean`
    and `Calculus/NFmlDerive.lean` are trimmed in `calc-del`, not deleted and
    not left whole: today's `Proves` keeps its connective, update, rewrite
    and close rules (the closer's sequent calculus on a leaf's erasure) and
    loses its program rules (`update` … `invLean`, their soundness
    `RuleSoundness`/`Sound*`, `Proves.unfoldRule`); `Derive.residue` keeps
    moving the connectives in front into the context and loses the program
    step (a program left in a leaf stays a leaf).  So today's strategy
    (`Symex`, `Completeness`, today's `Rules`) and the program rules'
    soundness go now, with nothing of `Core` reading them.  `RuleSet` is
    still the index (now a parameter: no rule restricts it).
42. *Proposed (W4 `calc-del`), the lead's call:* today's chains split
    (blocker 9): the rewrite half, on `Update.lean`'s lines, is
    `Calculus/RewriteChains.lean` (`Link` with `rw`/`rwAny` only, `Fml.Via`,
    `Fml.Leads`, `Post`, the chain notation and `sol_chain` on rewrites)
    and `Calculus/RewriteChainGen.lean` (`#last_line` on rewrites, the
    rewrite search, `groupSteps`, `sol_chain?` on `~~>`, `sol_rws`); a step
    of the strategy (`~>`, `~*>`, `~[rule]~>`) on today's formulas is an
    error that names the scoped chains, and `#chain`/`#chain_rest`/
    `#derivation` are syntax only here, elaborated by the scoped chains.
43. *Proposed (W4 `calc-del`), the lead's call:* the rule tables
    (`RuleShapes`, `PrintedRules`) are keyed by the scoped constructors
    (`` ``Core.Taclet.r ``) and hold the scoped claims (`blockEmpty`, and
    `functionFrameEmpty` merged into the two call expansions); their scoped
    twins (`Core/RuleShapes`, `Core/PrintedRules`) are deleted, and with
    `Rules.lean` gone `scripts/check-rule-text.sh` checks that every
    constructor of `Calculus/Core/Rules.lean` is a `dl{ … }` line but the
    two stated by hand (`scripts/core-rules.mjs` and the copy markers are
    deleted).
44. *Proposed (W4 `calc-del`), the lead's call:* `SortCheck/Faithfulness`
    reads the scoped taclets: a read is a `CRead` over the statement's
    context, erased under any names to today's `Read` (so `Read.sortOk` and
    the semantic half are unchanged), and the 36 `faithful_<ctor>`
    theorems are stated by `faithful_theorem r dom cls`, which reads the
    binders and the statement off `Core.Taclet.r`'s type (the hygienic
    binder names of the schema macros cannot be written in the file); the
    domain and class of each are today's.
45. *Proposed (W4 `calc-del`), the lead's call:* `#solkey_scan` reads the
    scoped statement (`N.f.problem.core`, or `N.f.problem` under `main`;
    `Core.Seq.scanLeaves`, the scoped walk with today's residue at the
    leaves), since today's walk on the legacy statement is gone.
46. *Proposed (W4 `modal`), the lead's call:* the formula **as written** is
    `Surface.Fml` (`Update.lean`): today's `Fml` with its modality over
    `Surface.Prog`, and no reading, as decision 11 makes `Surface.Stmt` the
    statement as written.  It is `dl!{ … }`'s output when a modality is in
    it (`Surface.Fml.quoteAuto`; the closer's `NFml` otherwise), today's
    obligations (`Problem.fml`, `ctorFml`, `specObligation`,
    `solc_problems`' statements), and the printers' target
    (`Core.Fml.eraseS`; `RuleSyntax.lean`'s `ppFml` prints both families,
    `whnfF`, so no second printer).  `Core.Fml.resolveN` reads it.  A
    schema `dl{ … }` with a modality (today's sequents) is an error that
    names the scoped calculus.
47. *Proposed (W4 `modal`), the lead's call:* `Core.Fml.erase` (the
    closer's input) erases a modality to `false`: `NFml` has none, and the
    closer takes only a formula with none (`Fml.Closable`), so nothing
    reads it; `Fml.eraseS` keeps it for the printers and the chains' lines
    (`Fml.erasedQuoted`).  `#wp` shows a reduction only of a formula with
    no modality left (`!ψ.active`).
48. *Proposed (W4 `modal`), the lead's call:* the examples' runs of today's
    interpreter (`Prog.run`, `Prog.localAfter`, `Contract.deploy`) run the
    typed run: `Surface.Prog.runT`/`localAfterT`/`Contract.deployRun`
    (`Tools/Run.lean`: resolved, read at the contract's types
    (`typedState?`), `Core.Prog.trun`, the end named back by
    `TState.toSem`).  The `#eval` pins are unchanged.  *Amended (W4
    review):* the 28 kernel checks (`rfl`, `simp …; rfl`) of today's run
    stay theorems, over the typed run itself: each block is resolved and
    declared at elaboration (`Core.Prog.defineCore`), so the kernel never
    meets `Prog.resolve`, and each claim is `Core.Prog.trun (TState.ofStorage
    …)`/`TState.init C` or `Core.Contract.deployT`, by `decide +kernel`
    (`Mini.deployRun … = .error .revert := rfl` stays as it was).  Where the
    kernel is stuck the claim is restated, not dropped to a `#guard`: the
    erasure of a typed storage (`SFields.erase`) and `Semantics.SVal`'s
    `DecidableEq` do not reduce, so a storage claim compares typed values
    (`SFields.beq` against the expected storage, `SVal.find` for a mapping
    entry: `Coin`, both `Constructors`); a loop (`TLoop.run`, classical)
    runs with fuel (`Core.Prog.trunF_approx`: `Loops.countTo3Run`).  No
    `#guard` of the list is kept.
49. *Proposed (W4 `modal`), the lead's call:* a rewrite link on a line
    whose program is still open (`Examples/ChainRewrites`' §Literals,
    `⟨[ revert(); ]⟩ φ` in a check's branch) is gone: the rewrites run on
    the erasure, which has no modality.  The four examples stand a
    postcondition `ψ` for the reverting branch; rewrites under an open
    program come back with M6c's scoped rewrites.
50. *Proposed (W4 `modal`), the lead's call:* `Halt.stuck` stays, not yet
    `undef`: M3's scoped run (decision 40) still produces it on an
    ill-typed state, so decision 39's condition ("when no run produces it")
    is not met; the rename goes with decision 40's lane.
51. *Proposed (W4 `reader-dry`), the lead's call:* the reader's dry-run
    branch starts from side-projects' unmerged
    `solkey-reader-solidity-names` (`a4d4cb8`, the reader as it last built,
    against `86f89d9`), not from `main` (`7a32e13`'s reader, against a
    sibling of 2026-09-27), and re-vendors its corpus to solkey
    `1b4341a303`, the sibling's pin: `Corpus.keyTaclets_eq_corpus` fails
    otherwise (323 names against 313), and `functionFrameEmpty` has no row
    without it.  The re-pin adds ten rows (`internalCallExpand`,
    `blockReturn`, `functionFrameReturn`, `functionFrameEmpty`, the six
    `send…` taclets), new rather than moved.
52. *Proposed (W4 `reader-dry`), the lead's call:* one row moves beyond the
    three the plan allows: `storageLocalDeclSkip`, from `agrees` to
    `findOnly`.  The scoped rule binds the alias to `unset` (`{ lsv :=
    unset }`, M1, the rule's own "Lean only" comment), where solkey binds
    nothing; the reader reads that update as written rather than as
    `⟨[ ]⟩`, which would claim an agreement the rule disowns.  Its theorem
    becomes `storageLocalDeclSkip.find` (`FindAgrees`).
53. *Proposed (W4 `reader-dry`), the lead's call:* the reader reads a
    scoped constructor through `Core.Delab`'s erasure (`withTwins`, `tr`),
    so it imports `Calculus/Core/Delab` beside `Core.Rules` and
    `KeyTaclets`: 68 sibling modules instead of 29, among them
    `Core.Taclet`, `Core.Proves` and part of `Typing/` (the delaborators'
    imports).  Moving `tr`/`withTwins` into a module below the
    delaborators (`Core/Rules` and `RuleKit` only) would take them off the
    reader's path; a sibling refactor, left for W5 or the lead.
54. *Proposed (W4 `reader-dry`), the lead's call:* a mapping key's lowering
    (`Simple.keyLower`/`Val.keyLower`, decision 10's `bool` key hashed as
    `0`/`1`) is read as a value's lowering (`lowerV`), as the sibling
    prints it (as the index): the key's type is one of the type details the
    common form leaves out.  Read as an unknown symbol, it moved the 18
    mapping rows (`storageIndex…Mapping…`, the mapping `OpAssign` and
    increment families) from `agrees`/`merged` to `findOnly`/`candidates`.

55. *Proposed (W4 `run40`), the lead's call:* the per-step erasure lemmas
    stay, with their right-hand sides written out: `TRun.x_erase :
    StepAgrees (TRun.x …) (fun τ => …)` (`Semantics/Core/TypedStepErase.lean`),
    the body each deleted `Run.x` had, as a lemma's statement, not a
    definition; `StepAgrees.erased ha` names it for the update arms'
    equations (`save_run : U.apply τ = (TRun.assign_erase l r).erased τ`).
    Decision 40 asked the arms "against the typed step, through the
    per-step erasure lemmas"; no untyped step or run is defined any more.
56. *Proposed (W4 `run40`), the lead's call:* the non-reachability witnesses
    (`map_default_not_reachable` and its kin, `dirty_word_not_reachable`,
    `fixed_past_end_not_reachable`) are stated as `¬ Reachable` (the typed
    run's): they were `¬ ReachableS`, the stronger claim about M3's run,
    which is gone with that run.
57. *Proposed (W4 `run40`), the lead's call:* type soundness of the typed run
    is by construction alone (`TState.erase_wt`): `Stmt.run_wt`/`Prog.run_wt`
    and the wt leaves (`keeps_assign` …) are deleted, not moved;
    `Read.sortOk_after_run` (`SortCheck/Faithfulness`) becomes
    `Read.sortOk_typed` (any typed state, given `nodupKeysB C.vars`).  The
    canonical and tight invariants are carried along the typed run on its
    erasure (`RunInv.TKeeps`, `Typing/TypedRunInv.lean`), each leaf through
    its erasure lemma (`TKeeps.of_agrees`), so their leaf proofs are the old
    ones read on the erased step.
58. *Proposed (W4 `run40`), the lead's call:* `Halt.stuck` is `Halt.undef`,
    the term model's ill-sorted value, and the term model's own `.stuck`s
    are `.undef` (`Term.undef`, `PTerm.undef`, `ITerm.undef`, `STerm.undef`,
    `LPath.undef`, `*.undef_eval`, `NoPanic.undef`); `Surface.Prog.runT`
    (`Tools/Run.lean`) returns `.error .undef` where the program does not
    resolve or the state is not of the contract's types (no typed run
    starts).  The identifiers that said "stuck" in another sense are renamed
    so that `rg stuck` finds prose only: `#verify`'s outcome `gaveUp`
    (`Tools/Verify.lean`), the chains' `Run.modalStop`/`modalStopNote`
    (`Calculus/Core/Chains.lean`), `rule_exists`'s `Blocker`/`blockerOf`
    (`Calculus/Core/RuleExists.lean`, a blocked `whnf`).
59. *Proposed (W4b `rules36`):* the rule set is read by a last,
    default-proved argument of each step rule (`hR : R.admits m s = true`,
    `rule_admits`), not by its premise (`Stmt.stepIn R`): the walks'
    `apply Proves.update (Taclet.step_eq .r)` stays as written, and `hR` is
    read off the statement alone (`Stmt.keyStep`), which the kernel
    decides.  Under `.solkey` a statement whose rule could be a
    `LeanTaclet` (a call with an argument to capture, a `try` or a payment
    under the diamond, a loop) is not admitted.
60. *Proposed (W4b `rules36`):* the judgement-level `solkey_lt_calculus`
    is witnessed by a loop (`[ while (false) { } ] true`) rather than
    today's call with an argument to capture (`[ f(x + 1); ] true`): a
    scoped call needs a function body over its frame, and the loop is the
    statement the rule-level row already names.  `Premise.inSolkey` is
    `false` for `branches` and `inv` (neither `try` nor a loop is in the
    fragment), where today's read a `try`'s blocks.
61. *Proposed (W4b `rules36`):* `sol_prove` on `⊢ₖ` walks solkey's rules
    only (`Seq.run R`, `Stmt.stepIn`), and fails where a statement is not
    admitted, rather than proving `⊢` and failing in the kernel.
62. *Proposed (W5 preparation), the lead's call:* the old side of every
    clash W5 would create moves into the namespace it belongs to, and the
    scoped one keeps the plain name: today's term syntax as written is
    `Surface`'s (`Surface.Val`, `Simple`, `SPath`, `Loc`, `MPath`, `MLoc`,
    `Src`, `ARhs`, `MRhs`, `NewLhs`, `MSrc`, `OpLoc`, `CallRet`, `ExtArg`,
    `ExtCall`, `LoopAnn`, `Tm`, `MAddr`, `UpdElem`, `Upd`, the holes `Hole`,
    `MHole`, `VHole`, `Premise`, the obligations `Problem.*` and
    `specObligation`, `primName`, `cmpParts?`); the closer's is `NFml`'s
    (`NFml.holds`, `holds_conj`, `Valid`, `Proves`, `Post`, `Link`, the
    rewrite chains' `Chain.*`, `Derive.*`, `instSoundRelLeads`); the untyped
    semantics' is `Semantics`' (the lemma namespaces `State.*`, `SVal.*`,
    `MVal.*`, `MObj.*`, `Value.*`, `Res.*`, and `SE`, `Tight`,
    `lookupBy_map_snd`, `writeLoc_eq`, `aliasPath`, `assertOk`, `guardOk`,
    `bumpLocal`, `opLocal`, `sendAt`); `Calculus/SurfaceNotation`'s path
    reader `elemTy` is `Surface.elemTy`.  See "W5 preparation" below.
63. *Proposed (W5 preparation), the lead's call:* M3's erased state
    `Core.State` is `Core.EState` (with its namespace), the one scoped name
    renamed: W5's `TState` → `State` takes the plain name.
64. *Proposed (W5 preparation), the lead's call:* the switch
    `Solidity.Core.Surface` (`open scoped`, the scoped reading of `dl!{}`,
    `⊨`, the walks' `apply`) is `Solidity.Core.Scoped`: W5 would merge it
    into the old side's `Surface`, and every `def Surface.X …` (which opens
    its prefix) would read its formulas scoped.
65. *Proposed (W5 preparation), the lead's call:* the old modules W5's
    moves would overwrite are renamed by their side:
    `Calculus/{Close,Derive,Logic,Quote,UpdateRules}.lean` →
    `Calculus/NFml{Close,Derive,Logic,Quote,UpdateRules}.lean`,
    `Calculus/{Notation,Spec}.lean` → `Calculus/Surface{Notation,Spec}.lean`.
66. *Proposed (W5 preparation), the lead's call:* the script's scope beyond
    the plan's list: `Solidity.Evm.Core` folds into `Solidity.Evm` with its
    files; `Semantics/Core/TypedX` → `Semantics/X` (the plan's
    "`TypedRun` → `Semantics`": `Semantics/Run`),
    `Semantics/Core/X` → `Semantics/X`, `Semantics/Core.lean` →
    `Semantics/Erased`; `Syntax/Core*.lean`,
    `Examples/Tactics/Core*.lean` and `TestSuite/CoreProblems.lean` keep
    their paths (two would overwrite `Examples/Tactics/Callback.lean` and
    `TestSuite/Problems.lean`).  *Superseded by decision 72* (review fix):
    they lose `Core` too.
67. *Proposed (W5 preparation), the lead's call:* two exact duplicates go
    instead of being renamed: `Core.Res.bind_eq_ok` and `Core.Res.ok_bind`
    (`Calculus/Core/SoundArms`, `SoundCalls`) are `SemanticsProperties`'
    `Res.bind_eq_ok`/`Res.ok_bind`, which their users now name.
68. *Proposed (W5 preparation, review fix), the lead's call:* the script
    leaves this record alone (`':!:docs/intrinsic.md'`): it describes the
    rename, which its rules would rewrite into nonsense (`Solidity.Core.X`
    → `Solidity.X` would read `Solidity.X` → `Solidity.X`).  The record cites
    files by the paths they had at each step, so after W5
    `check-doc-paths` reports its 96 citations of moved modules: W5
    exempts the record there (it is history, like `git log`) rather than
    editing it.
69. *Proposed (W5), the lead's call:* with the prefix `Solidity.Core`
    gone, a scoped family is one with an erased twin (`legacyName?`) or one
    of `Delab.untwinnedFamilies` (`Idx`, `Args`, `Binders`, `CodeBinder`,
    `SHole`, `Prog`, `Frames`, `LTy`): `Delab.isScopedFamily`, which
    `trArg` now tests.  No name of the erased side or of the shared
    vocabulary has a twin (checked over the environment of `Solidity`
    before the rename), so the test admits no shared name; the scoped
    families it no longer admits (propositions, the tools' structures)
    are ones `tr` left as they were but for unfolding a definition.
70. *Proposed (W5), the lead's call:* `#check_rule_text` prints a rule
    line with full names, and an escape `‹…›` fails the line when a name
    in it, or a namespace it is in, is a scoped family
    (`Tools.isScopedName`): `‹Solidity.Val.…›`, `‹(Solidity.Upd.…).snd›`,
    `‹@Solidity.Idx.…›` fail, `‹Solidity.Surface.…›` and
    `‹Solidity.Term.bumped …›` pass (checked on these five strings).
    *Review fix*: a family with no twin that `Solidity.Core` alone kept
    apart (`Ext`, `Thin`, `Hyps`, `Tms`, `Env`, `TEnv`, …) fails it too:
    `Tools.scopedOnlyRoots`, the roots of every type or namespace declared
    under `Solidity.Core` that is neither twinned nor in `untwinnedFamilies`,
    but the shared vocabulary that only gained lemmas there (`Contract`,
    `PrimTy`, `BinOp`, `Op0`–`Op3`, `Srt`, `Binds`, `Res`, `Value`,
    `Delab`); kept apart from `Delab.isScopedFamily`, so `trArg` is
    unchanged.  `‹Solidity.Ext.push e›` and `‹Solidity.Tms.STerm.save a b›`
    fail (checked with the five above).
    `Delab.isUp` keeps the prefix `Solidity`: the one other name ending
    in `up` is the theorem `Wrote.up`, which no term heads.
71. *Proposed (W5), the lead's call:* the script's scope beyond the
    preparation's: a backticked `Core/X` relative to `Calculus/` loses
    `Core/` (`Examples/Chains/EvaluationOrder`'s gains `Calculus/`),
    `tests/solkey/expected.tsv` takes the path rules (its notes are what
    `scripts/solkey-port.mjs` writes, which the rules change), and
    `check-doc-paths` skips this record (decision 68).
72. *Proposed (W5 review fix), the lead's call:* the paths decision 66 kept
    lose `Core`: `Syntax/Core.lean` → `Syntax/Scoped.lean` (its title, "the
    typed syntax, scoped"), `Syntax/CoreQuote.lean` → `Syntax/Quote.lean`,
    `Examples/Tactics/CoreX.lean` → `Examples/Tactics/X.lean` for the twelve
    that clash with nothing, with their namespaces
    (`Solidity.Examples.CoreChains` → `Solidity.Examples.Tactics.Chains`),
    and the two that would clash renamed rather than merged:
    `CoreCallback` → `Examples/Tactics/CallbackRuns.lean` (the callback
    reading on typed runs, beside `Callback`'s worked withdrawals),
    `TestSuite/CoreProblems.lean` → `TestSuite/ScopedProblems.lean` (what
    `solc_scoped_problems` declares; merging it into `Problems.lean` would
    put that module past its timing gate, W3b lane `testsuite`).
73. *Proposed (W5 reader), the lead's call:* the SolKey reader erases a
    constructor as the taclet printer does (`withTwins (schema := true)`),
    so a call whose parts are schema variables is read as one variable,
    `call(args, ret, body)` (the printer's `fbs`/`ic`, KeY's
    `FunctionBody`/`InternalCall` variable), and its premise as
    `expand_function_body` of it; the side condition `CallRet.isRets` on
    that variable is now compared against KeY's sort (`FunctionBody`
    returns to targets, `InternalCall` does not), where it was recorded
    and not compared.  `Args.firstNonSimple = none` stays uncompared (KeY's
    `internalCallExpand` binds `T p = arg` as written, the rule map's
    deviation).
74. *Proposed (W5 reader), the lead's call:* the reader excuses two more
    rows: `functionFrameEmpty` (a call's body is inlined as a block and its
    frame ends with the expansion; `RuleShapes` claims it merged into
    `internalCallExpand`/`functionBodyExpand`, a pairing the shapes cannot
    see, since the erasure prints a frame's end as nothing) and
    `tryCallWithCallbackBox` (callbacks, as the `transfer`/`send` ones;
    `CallbackTaclet.tryCallWithCallbackBox`, which the reader does not
    import).  `tryCallNoCallbackBox` stays `differs`: the scoped `try`
    binds its return locals and `Panic` code in the statement
    (`try call returns (rets) … catch Panic (code) …`), KeY's statement
    variables do not.

75. *Proposed (M7 review), the lead's call:* the canonicity invariant keeps
    its store typing on the erasure for now (`canonInv.glob` is
    `StateWT ∧ Canon`, `Prog.run_canon`/`Prog.run_tight` take
    `hwt : RunWT C H σ.erase`).  Tying it to the typed state
    (`RunInv.TKeeps` over `HTy.toHeapTy 0 σ.H`, the leaf obligation
    `State.erase_wt hnd σ`, `canonInv.glob := CanonStorage`) rewrites every
    `keepsC_*` leaf, `TypedRunInv` and the tightness invariant of
    `Constructibility` (about 120 sites): its own lane, after M6c, which
    moves the closer onto the same states.
76. *Proposed (M7 review), the lead's call:* `Stmt.step` keeps its `Option`
    result.  `Stmt.rule_exists` proves it never `none`, but making it total
    changes the kernel-evaluated strategy (every arm, `shortStep`, the
    `apply_toStep` dispatch) and every `Proves` program rule, `Premise.Sound`
    and `Stmt.Sound` (about 70 sites); AGENTS.md asks that such a change be
    timed against `TestSuite/Derived9–11` and `Examples/ProofTree` before
    and after, so it is a lane of its own with those gates.
77. *Proposed (M7 review), the lead's call:* `Reachable C st ↔ Canon ∧
    Tight` (`reachable_iff`, `shape_iff_reachable`, `wt_iff_reachable`)
    holds for a storage that fits (`FitsStorage C st`): a consequence of
    M1's in-range literals, since a word, key or slot out of range is
    canonical and tight but no literal writes it.  `Reachable → FitsStorage`
    is not proved here.

**Lead, 2026-10-09 (4):** proposals 54–77 are approved. 75 (store typing
tied to the typed state), 76 (`Stmt.step` total, behind the Derived9–11
and ProofTree gates) and 77 (`Reachable → FitsStorage`) are W6 lanes beside
the closer port.

78. *Proposed (M6c 6a, `w6-closer`; renumber at the merge if another lane
    took 78–80), the lead's call:* on a scoped leaf `sol_decide` keys the
    reduction's atoms by the leaf's context, not by its names, as far as
    the modules below allow: the leaf's parameters (its leading `∀ p x`,
    the positions of the context its body is read in) stay quantifiers
    through the erasure, are the reduction's leading `LFml.all`s
    (`LFml.alls`), and are read at their types (`Typed`: a `uint` an
    integer in range, a `bool` a boolean), where the erased leaf stripped
    them to free names (`Derive.stripAlls`) and split each three ways.
    `LTerm.var` itself keeps a name: `DecideLang` is a symbol library that
    does not port, and the reduction (`Decide.lean`, wave 6b) is what
    reads the erasure; a hidden binder's local stays a name split as
    before.
79. *Proposed (M6c 6a), the lead's call:* the constraints' step on a
    scoped leaf (`LFml.valid_alls_of_cons`) is sound, not an equivalence:
    the parameters are typed, the storage is still read untyped, so a
    leaf it does not close may be valid (the two `fail_if_success`
    examples of `Examples/Tactics/Decide` that hold in typed states stay
    open).  `NFml.valid_iff_cons`, the equivalence, stays for today's
    leaves (`sol_prove`'s, `NFmlDerive`'s leaf search).
80. *Proposed (M6c 6a), the lead's call:* `Closers.lean`'s erased
    elaborator of `sol_decide` (`Derive.onErased`) is deleted; the scoped
    one is `DecideComplete.lean`'s.  The parts (`sol_decide_cons`,
    `sol_reduce`, `sol_reads`, `sol_decide_heuristic`,
    `sol_decide_unconstrained`) keep their erased elaborators: a written
    proof that calls them names today's steps.
81. *Proposed (M6c 6a part 2, `w6-closer`; renumber at the merge), the
    lead's call:* `Closer.lean` does not port in wave 6a.  It reads only
    `LFml`, the reduction's output (`LFml.close`, `Facts`), never `Fml`
    or `NFml`: its input is `Decide.lean`'s (wave 6b), and under decision
    78 its atoms stay name-keyed until the reduction lowers scoped terms by
    position.  On a scoped leaf it already reads the parameters typed:
    `sol_prove`'s residue moves each `∀ p x` into the context
    (`NFml.Derive.residue`), and the closer binds it at its type
    (`Facts.bind`).  Its layout (`LayoutOk`) stays read off `wt(storage)`:
    a typed storage is not canonical (`SVal.map`'s default is any value of
    its type, its entries may repeat a key), so the typed state does not
    give it until decision 75's lane ties canonicity to the typed state.
    `Closer` moves to wave 6b with `Decide.lean`; it is not the fallback
    (nothing was ported and timed).
82. *Proposed (M6c 6a part 2), the lead's call:* the scoped
    `sol_close_unwrap` (`Calculus/Derive.lean`, the first step of
    `sol_close`, `sol_close_mt`, `sol_spec_close`) erases the leaf with
    its parameters kept as quantifiers (`Derive.eraseLeaf … (typed :=
    true)`), so `NFmlClose`'s `sol_close` introduces each with its type's
    range (`Close.holds_all`, `PrimTy.admits`), as it already did an
    explicit `∀` (decision 28).  The other closers on a scoped leaf
    (`Closers.lean`'s `sol_close_eval`, `sol_apply_upd`, …) keep the
    stripped leaf: a written proof that calls them names today's steps, as
    decision 80 keeps `sol_decide`'s parts.  `NFmlClose` keeps its name and
    its simp set over the untyped interpreter: a scoped term reads its
    symbols on the erasure (`Calculus/Logic.lean`), so a `sol_close` over
    the typed state would restate the whole `close_rw` set for symbols
    that are still untyped.

83. *Proposed (M6c 6b, `w6-closer`; renumber at the merge), the lead's
    call:* `Decide.lean` ports as a scoped front end,
    `Calculus/DecideScoped.lean`: `sol_decide` reduces the leaf itself
    (`Fml.reduceS`), its updates pushed in by position (`SymS`: one entry
    per position of the context, a pop or a frame's drop popping or
    dropping entries) and the fragment checked on it (`Fml.inLS`).  Its
    soundness is the commutation with the erased reduction, exactly
    (`Fml.toLS_eq`: the scoped reduction and fragment are the erasure's,
    for every leaf `Fml.posB` takes), then `NFml.valid_iff_reduce` and
    `Valid.of_erase` (`Valid.of_reduceS`), not a re-proof of
    `NFml.toL_holds` and the elimination over the typed state: those
    read the scoped terms' symbols on the erasure anyway
    (`Calculus/Logic.lean`), so the 9k lines of term lemmas would restate
    the untyped interpreter by position for no new theorem.  `NFml` stays
    `Decide.lean`'s IR for its proofs (decision 7's documented IR), not for
    the computation: no erasure is computed or checked by the kernel.
    `Valid.of_reduce` (the erasure computed and quoted) is deleted.
    The kernel-evaluated functions keep G0's conditions 1 and 2 (review
    fix): `Fml.toLS`, `Fml.inLS`, `Fml.peelS`, `Upd.view`, `Upd.replayS`,
    `Thin.sel`, `Tm.toLS`, `Tm.inLS` and `Idx.toNatR` are written by the
    recursor, each with its `match` form as the `implemented_by` twin
    (`Fml.toLSM`, …) and a link theorem (`Fml.toLS_eq_toLSM`, …); the
    proofs are stated on the twins and carried across by the links, and
    `sameAt`/`allocPairS?` compare `Tm.eraseR`.  Still by `match`, the
    lead's call: the helpers that take one `Tm C Γ s` (or `Rhs C Γ t`)
    apart at fixed constructors (`Tm.storLocalS`, `Tm.slotPathS`,
    `Tm.sameShapeS`, `Op2.toLAtS`, `Rhs.actS`, …): the context is that
    family's parameter, so their casts compare a `Srt` or `LTy`, not a
    context; not timed apart from the module.
84. *Proposed (M6c 6b), the lead's call:* the positional state keeps,
    beside the positions, the erased reduction's `Sym` (its bindings by
    name, newest first), read only by the two checks that ask about names
    the scope no longer has: a quantifier's local is read by no binding so
    far, a popped local's included (`Sym.vars`), and a hidden binder's
    local starts at its name's last binding (`SymS.push`), as the erasure
    reads it (a hidden binder erases to nothing).  That keeps
    `Fml.toLS_eq` an equality with no side condition beyond `Fml.posB`'s
    freshness (`Fml.FreshS`).  An equation `eqD a b` is recognised
    through the two constructors the erasure drops, an update of pops and
    a hidden binder (`Fml.peelS`), and two syntactic tests compare terms
    by their erasures under the context's names (`sameAt`, an equation's
    two readings; `allocPairS?`, an allocation's pair): the erased
    reduction compares names there.
85. *Proposed (M6c 6b), the lead's call:* `Examples/Tactics/Decide`'s
    fragment pins read `Fml.inLS` on scoped formulas; the second pin, a
    memory local no update binds (`{ x := read(memory, carol.age) }`),
    has no scoped spelling (a free name is a `uint` parameter, a memory
    local is in scope only through a binder) and is replaced by a read of
    the ledger (`{ y := net(a) }`), also outside the fragment.  Both still
    print `false`.

86. *Proposed (M6c 6c, `w6c-upd`; renumber at the merge if another lane
    took 86–88), the lead's call:* the update rules on scoped formulas are
    **one way** (`UpdRuleS.sound`: `holds σ ψ → holds σ φ`, the direction
    a derivation uses), where the erased ones are equivalences.  The
    converse fails on the typed state: `{U} φ` reads `φ` in every typed
    state the update's result erases to, and a merged update can reach a
    typed state the two updates in turn do not (`{x := 300}{x := 1} φ`
    for a `uint8` local holds vacuously, its merge only where `φ` does).
    So a rule applies at the positive positions only (`Fml.rwAtS`: under
    an update, a conjunction, the right of an implication, a binder,
    `{havoc}`, `{anon}`, a modality's postcondition), not under a negation
    or on the left of an implication, where `NFml.updAt` rewrites.  The
    scoped sequent's rules (`merge`, `simplify`, `applyOnRigidBox`) were
    already one way.
87. *Proposed (M6c 6c), the lead's call:* the scoped rules transcribe
    solkey's as far as positions allow: `sequentialToParallel` is
    `Upd.seqPar` (Graft's, unchanged); `simplifyUpdate`
    (`\dropEffectlessElementaries`) drops what the update pops later
    (`Upd.simp`, under the box, as `Proves.simplify`), not a write
    shadowed by a later one nor a local in scope that the formula does not
    read, which the erased form drops by name (a gap, not a deviation in
    soundness); `applySkip` asks a formula with no modality (`{}` reads it
    in every typed state of the same erasure and heap typing,
    `holds_congr_erase`); `applyOnRigid` under the diamond asks an update
    that cannot halt (`Upd.totalB`: what the erased `Upd.total` admits, a
    literal and an alias to a root and its fields, `sp1 := alice.account`,
    and also a local, `unset` and the ledger's saves, which cannot halt on
    the typed state; review fix: the alias was missing), under the box
    any update (`Fml.substU`).  `elimSelfUpdate`, commented out in solkey
    and theorems only in the erased form, is not ported.
88. *Proposed (M6c 6c), the lead's call:* `StateParts`' two merges port
    as one graft through a term map read where a write looks
    (`Upd.graftF`, `GraftOK`: `Srt.AgreePart`, the erased form's), beside
    Graft's exact one, which the sequent and the scoped chains run and
    which stays as timed: `{L ‖ storage := S}{V}` (`Upd.mergeSt?`, memory
    reads kept, an index check and a push slot read in `S`, a storage
    variable `U` sets read as what it is set to) and `{memory := M}{V}`
    (`Upd.mergeMem?`, a lone memory write, as `mergeMemory_holds`; the
    locals-then-memory merge is `ChainRewrites`', which ports with it).
    `NFmlUpdateRules` and `StateParts` stay: `Rewrite`, `TheoryRewrite`,
    `ChainRewrites`, `ChainBranches`, `NFmlLogic`, `RewriteChains`,
    `Decide` and `Hyp` still read `NFml`; they go when those port.  This
    is not decision 7's fallback (the gate rows did not move).

## M6c

**Wave 6a, part 1 (2026-10-09, `w6-closer`): `DecideSyn`, `DecideComplete`
on the scoped leaf; Gate: partial.**  `sol_decide` on `Valid φ`
(`φ : Fml C []`) erases only to call the reduction below it
(`Valid.of_reduce`, `Calculus/DecideSyn.lean`: `Fml.posB` and the
fragment checked by the kernel, the erasure computed once and quoted),
then tries, on the reduction `alls xs body`:

* `LFml.syn_valid_alls`: `syn` with the parameters' locals known to return;
* `LFml.valid_alls_of_cons` (`Calculus/DecideComplete.lean`): the
  constraints, the parameters read at their types (`Typed`,
  `sol_decide_atoms`), the other locals split as before;
* `LFml.valid_alls_of_body`, then `sol_decide_heuristic` on the body.

Decisions 78–80.  Two examples added (`parameterReturns`,
`parameterInRange`): valid in typed states, not on the erased leaf, closed
now.  No pin moved; no `sorry`, `axiom` or `maxHeartbeats` added.

Gate (the W6 baselines' method: each file copied under
`Solidity/Scratch/`, a fresh worker, the end of work, the minimum of three
runs; load 0.6–6.8 at the starts, the Decide runs the highest):

| Module | W6 end of work | 6a part 1 (three runs) | ratio | CPU (min) |
|---|---|---|---|---|
| `TestSuite/Derived1` | 7.32 s | **7.38 s** (7.39, 7.38, 7.38) | 1.01 | 9.07 s |
| `TestSuite/Derived2` | 8.63 s | **8.68 s** (8.71, 8.69, 8.68) | 1.01 | 10.41 s |
| `TestSuite/Derived3` | 13.01 s | **12.93 s** (12.93, 13.04, 13.19) | 0.99 | 14.54 s |
| `TestSuite/Derived4` | 17.57 s | **17.42 s** (17.58, 17.42, 17.60) | 0.99 | 19.53 s |
| `TestSuite/Derived5` | 6.95 s | **6.96 s** (7.03, 7.04, 6.96) | 1.00 | 8.22 s |
| `TestSuite/Derived6` | 11.42 s | **11.48 s** (11.48, 11.53, 11.52) | 1.01 | 13.07 s |
| `TestSuite/Derived7` | 50.43 s | **50.41 s** (50.57, 50.41, 50.45) | 1.00 | 52.84 s |
| `TestSuite/Derived8` | 26.38 s | **26.32 s** (26.52, 26.43, 26.32) | 1.00 | 27.69 s |
| `TestSuite/Derived9` | 7.16 s | **7.13 s** (7.14, 7.13, 7.16) | 1.00 | 8.61 s |
| `TestSuite/Derived10` | 11.11 s | **11.20 s** (11.21, 11.20, 11.27) | 1.01 | 12.89 s |
| `TestSuite/Derived11` | 3.16 s | **3.21 s** (3.21, 3.24, 3.26) | 1.02 | 3.43 s |
| `TestSuite/Derived12` | 13.17 s | **13.22 s** (13.38, 13.23, 13.22) | 1.00 | 14.16 s |
| `TestSuite/Derived13` | 6.36 s | **6.31 s** (6.44, 6.31, 6.36) | 0.99 | 6.40 s |
| `TestSuite/Derived14` | 10.89 s | **10.95 s** (10.95, 10.97, 11.06) | 1.01 | 11.57 s |
| Derived1–14, sum | 193.6 s | **193.6 s** | 1.00 | |
| `Examples/Tactics/Decide` | 49.14 s | **37.59 s** (37.59, 37.65, 37.96) | 0.77 | 38.43 s |

The Derived files call `sol_decide` only through today's leaves
(`sol_prove`, then `sol_decide_cons` on `NFml`), which did not change:
they are where they were.  `Examples/Tactics/Decide` (with its two new
examples; 37.57–38.13 s without them) is 23% faster: a parameter is one
case where the erased leaf split it into three, each unfolded and closed
by `omega`/`grind`.  **Gate: partial** (timings within 1.2×; atoms not
re-keyed by `Idx`, decision 78; the Derived rows do not exercise the
changed path), for both modules (ported together, timed together).

**Wave 6a, part 2 (2026-10-09, `w6-closer`): `NFmlClose`, `Closer`;
Gate: partial.**  `NFmlClose`: the scoped `sol_close`, `sol_close_mt` and
`sol_spec_close` erase the leaf with its parameters kept as quantifiers
(decision 82), so a parameter is a `uint` in range where the erased leaf
read a name bound to anything: three examples added to
`Calculus/CloseTests.lean` (`[ uint x = a; ] x >= 0`, `⟨ uint x = a; ⟩
x == a`, `a < 100 → ⟨ uint y = a + 1; ⟩ y <= 100`; open before).  No other
proof or pin moved (the whole build, `SolidityCorpus` and
`SolkeyTestSuite` included, green on the first run); no `sorry`, `axiom`
or `maxHeartbeats` added.  `NFmlClose` keeps its name: its simp set reads
the untyped interpreter, as the scoped terms' symbols still are.
`Closer`: not ported, moved to wave 6b with `Decide.lean` (decision 81).

Gate (the W6 baselines' method, measured at `702df6bf`; load 0.5–1.7 at
the starts of the Derived runs; the `Decide` runs 6.8, 3.6, 2.4; after the
build):

| Module | W6 end of work | 6a part 2 (three runs) | ratio | CPU (min) |
|---|---|---|---|---|
| `TestSuite/Derived1` | 7.32 s | **7.33 s** (7.35, 7.33, 7.38) | 1.00 | 9.01 s |
| `TestSuite/Derived2` | 8.63 s | **8.79 s** (8.79, 8.85, 8.79) | 1.02 | 10.51 s |
| `TestSuite/Derived3` | 13.01 s | **13.06 s** (13.15, 13.06, 13.07) | 1.00 | 14.61 s |
| `TestSuite/Derived4` | 17.57 s | **17.49 s** (17.49, 17.57, 17.71) | 1.00 | 19.58 s |
| `TestSuite/Derived5` | 6.95 s | **7.03 s** (7.07, 7.04, 7.03) | 1.01 | 8.36 s |
| `TestSuite/Derived6` | 11.42 s | **11.46 s** (11.47, 11.46, 11.50) | 1.00 | 13.03 s |
| `TestSuite/Derived7` | 50.43 s | **50.27 s** (50.41, 50.45, 50.27) | 1.00 | 52.85 s |
| `TestSuite/Derived8` | 26.38 s | **26.31 s** (26.38, 26.35, 26.31) | 1.00 | 27.64 s |
| `TestSuite/Derived9` | 7.16 s | **7.10 s** (7.12, 7.12, 7.10) | 0.99 | 8.55 s |
| `TestSuite/Derived10` | 11.11 s | **11.21 s** (11.21, 11.22, 11.25) | 1.01 | 12.77 s |
| `TestSuite/Derived11` | 3.16 s | **3.16 s** (3.20, 3.18, 3.16) | 1.00 | 3.34 s |
| `TestSuite/Derived12` | 13.17 s | **13.26 s** (13.31, 13.26, 13.33) | 1.01 | 14.22 s |
| `TestSuite/Derived13` | 6.36 s | **6.26 s** (6.43, 6.37, 6.26) | 0.98 | 6.38 s |
| `TestSuite/Derived14` | 10.89 s | **10.91 s** (10.91, 11.01, 10.98) | 1.00 | 11.49 s |
| Derived1–14, sum | 193.6 s | **193.6 s** | 1.00 | |
| `Examples/Tactics/Decide` | 49.14 s | **34.79 s** (34.98, 34.79, 34.90) | 0.71 | 35.64 s |

Only `Derived7` (one) and `Examples/Tactics/Decide` (nine) call
`sol_close` on a scoped leaf; the Derived rows are where they were.
`Examples/Tactics/Decide` is 7% faster than after part 1 (37.59 s), 29%
faster than the baseline: a `uint` parameter read at its value, not a
binding split by `sol_close`'s `simp` and `grind`.  **Gate: partial**
(timings within 1.2×; `NFmlClose` reads its parameters typed but its
`simp` set is the untyped interpreter's, decision 82; `Closer` not
ported, decision 81).

**Wave 6b (2026-10-09, `w6-closer`): `Decide.lean`; Gate: partial.**
`Calculus/DecideScoped.lean` (new, 1,700 lines, no `sorry`; `Valid.of_reduceS` on `propext`, `Classical.choice`, `Quot.sound` only): the
reduction on `Fml C Γ` by position (decisions 83–85).  `sol_decide` on a
scoped leaf checks `Fml.posB` and `Fml.inLS` in the kernel and reduces
`Fml.reduceS φ` (compiled and quoted, as before), where it used to
compute and quote the erasure and check `φ.erase [] = ψ`, `ψ.inL`.  No
proof or pin moved but the two fragment pins (decision 85); no `sorry`,
`axiom` or `maxHeartbeats` added (`sorry` in 12 files, 30 overrides, as
before).  The build (`Solidity`, `solkeycheck`, `SolidityCorpus`,
`SolkeyTestSuite`) green, no module OOM-killed.

Gate (the W6 baselines' method, measured at `38bd6a24`, one dead definition and two docstrings before the commit that records it; load 0.4–2.3 at
the starts, the `Decide` runs the highest, right after the build):

| Module | W6 end of work | 6b (three runs) | ratio | CPU (min) |
|---|---|---|---|---|
| `TestSuite/Derived1` | 7.32 s | **7.33 s** (7.35, 7.33, 7.38) | 1.00 | 8.94 s |
| `TestSuite/Derived2` | 8.63 s | **8.71 s** (8.71, 8.74, 8.74) | 1.01 | 10.38 s |
| `TestSuite/Derived3` | 13.01 s | **12.95 s** (13.13, 13.02, 12.95) | 1.00 | 14.44 s |
| `TestSuite/Derived4` | 17.57 s | **17.45 s** (17.66, 17.45, 17.56) | 0.99 | 19.72 s |
| `TestSuite/Derived5` | 6.95 s | **6.93 s** (6.99, 6.93, 7.10) | 1.00 | 8.27 s |
| `TestSuite/Derived6` | 11.42 s | **11.39 s** (11.43, 11.39, 11.54) | 1.00 | 12.98 s |
| `TestSuite/Derived7` | 50.43 s | **50.22 s** (50.61, 50.22, 50.70) | 1.00 | 52.59 s |
| `TestSuite/Derived8` | 26.38 s | **26.21 s** (26.21, 26.34, 26.25) | 0.99 | 27.54 s |
| `TestSuite/Derived9` | 7.16 s | **7.11 s** (7.18, 7.15, 7.11) | 0.99 | 8.59 s |
| `TestSuite/Derived10` | 11.11 s | **11.21 s** (11.24, 11.21, 11.27) | 1.01 | 12.86 s |
| `TestSuite/Derived11` | 3.16 s | **3.19 s** (3.23, 3.30, 3.19) | 1.01 | 3.44 s |
| `TestSuite/Derived12` | 13.17 s | **13.22 s** (13.22, 13.40, 13.30) | 1.00 | 14.15 s |
| `TestSuite/Derived13` | 6.36 s | **6.35 s** (6.39, 6.35, 6.45) | 1.00 | 6.46 s |
| `TestSuite/Derived14` | 10.89 s | **10.90 s** (10.90, 10.96, 10.97) | 1.00 | 11.45 s |
| Derived1–14, sum | 193.6 s | **193.2 s** | 1.00 | |
| `Examples/Tactics/Decide` | 49.14 s | **35.35 s** (35.50, 35.35, 35.46) | 0.72 | 36.17 s |

The Derived files reach `sol_decide` only through `sol_prove`'s leaves
(`sol_decide_cons` on `NFml`), which did not change: they are where they
were.  `Examples/Tactics/Decide` is where 6a part 2 left it (34.79 s,
+1.6%): the positional reduction costs the kernel what the erasure and
its check did.  **Gate: partial** (timings within 1.2×; the reduction's
entry, push-in and fragment run on `Fml C Γ` by position, but its
soundness is the commutation with the erased reduction, whose proofs stay
on `NFml` and the untyped state, decision 83; the atoms keep the
binders' names, decision 78; `Closer` not ported, decision 81).

Review fix (2026-10-09): the 6b functions the kernel evaluates broke G0's
condition 1 (`match` on `Fml C Γ`, `Upd C Γ Δ`, `Thin Γ Δ`, `Idx Γ t`);
they are now recursors with `match` twins (decision 83).  Re-timed by the
same method (load 0.6–0.8 at the starts): `Examples/Tactics/Decide`
**34.32 s** (34.50, 34.32, 34.40), CPU 35.32 s: 0.97 of 6b, 0.70 of the
W6 baseline.  Only that module's leaves reach the scoped reduction; the
Derived files were not re-timed (their path, `sol_decide_cons` on `NFml`,
did not change).  The build (`Solidity`, `solkeycheck`, `SolidityCorpus`,
`SolkeyTestSuite`) green; no pin moved; no `sorry`, `axiom` or
`maxHeartbeats` added.

**Wave 6c, part 1 (2026-10-09, `w6c-upd`): `NFmlUpdateRules`,
`StateParts`; Gate: partial.**  Two new modules on `Fml C Γ` and
`Upd C Γ Δ`, read over the typed state (decisions 86–88):

* `Calculus/UpdRuleScoped.lean` (`NFmlUpdateRules`' port): `UpdRuleS`
  (`sequentialToParallel` by `Upd.seqPar`, `simplifyUpdate` by `Upd.simp`
  under the box, `applySkip` before a formula with no modality,
  `applyOnRigid` by `Fml.substU`, under the diamond for `Upd.totalB`),
  `UpdRuleS.sound` one way; `Fml.rwAtS` (a rewrite at the first positive
  position where it fits), `Fml.updAtS`, `Fml.simpUpdsS` and
  `Valid.of_updAtS`/`Valid.of_simpUpdsS`; `holds_congr_erase` (a formula
  with no modality reads the typed state by its erasure and heap typing),
  `holds_upd_of_apply` (Graft's `holds_upd_graft` for any update that
  runs as two), `holds_upd_mono`.
* `Calculus/StatePartsScoped.lean` (`StateParts`' port): `Upd.graftF`, a
  graft through a term map read where a write looks (`GraftOK`,
  `Srt.AgreePart`), with `Upd.apply_graftF`; the storage merge
  `Upd.mergeSt?` (`Tm.substStS`: locals and `storage` substituted, memory
  reads kept, `p[p.length]@S`, `p[i]@S`) and the memory merge
  `Upd.mergeMem?` (`Tm.withMemS`), `holds_upd_mergeSt`,
  `holds_upd_mergeMem`, `Fml.mergeAtS`.
* `Examples/Tactics/UpdRulesScoped.lean`: the functions computed by the
  kernel (`rfl`) on `dl!{ … }` leaves, the three entry points
  (`Valid.of_simpUpdsS`, `Valid.of_updAtS`, `Valid.of_mergeAtS`) each used
  on a `⊨` goal; a rule
  refused under a negation, `Upd.seqPar` refusing a memory term after a
  storage write that the storage merge reads.

`NFmlUpdateRules` and `StateParts` stay, their consumers (`Rewrite`,
`TheoryRewrite`, `ChainRewrites`, `ChainBranches`, `NFmlLogic`,
`RewriteChains`, `Decide`, `Hyp`) still on `NFml`; no consumer switched,
no existing file but `Solidity.lean` and `docs/module-map.md` edited.  The
build (`Solidity`) green; `check-orphans` (304 reachable),
`check-doc-paths` OK; no pin moved; no `sorry`, `axiom` or `maxHeartbeats`
added (`Fml.simpUpdsS_holds`, `Fml.updAtS_sound`, `Fml.mergeAtS_sound` on
`propext`, `Classical.choice`, `Quot.sound`).

Review fixes: the functions the kernel evaluates keep G0's conditions 1
and 2, as `DecideScoped` does (decision 83), rather than claim Graft's
exemption, which was granted to Graft and UpdateRules as timed: the walks
over a whole formula or update (`Fml.rwAtS`, `Fml.simpUpdsS`,
`Upd.graftF`, `Upd.totalB`, `Upd.size`) are written by the recursor with
their `match` twins as `implemented_by` (`Fml.rwAtSM`, …) and link
theorems (`Fml.rwAtS_eq_rwAtSM`, …), the proofs on the twins; a head is
read by `Fml.casesOn`/`Upd.casesOn` (`Fml.updHead?`, `Upd.skipS`,
`Upd.mergeMem?`), so `UpdRuleNameS.top`, `MergeNameS.top`, `Fml.mkUpdS`
and `Fml.cleanS` match on no indexed family; `match` stays on one `Tm`,
`Rhs` or `UpdElem` (decision 83's helpers).  `Upd.totalB` admits an alias
to a root and its fields (`Tm.totalP`, `Tm.totalP_eval`), as the erased
`Upd.total` does, so `applyOnRigid` fires under the diamond on
`{ sp := alice.account }` (pinned).  The example module uses
`Valid.of_updAtS` and `Valid.of_mergeAtS` on a `⊨` goal each, beside
`Valid.of_simpUpdsS`.

Gate: no gate file imports the new modules (checked on the import
closure of `TestSuite/Derived1–14` and `Examples/Tactics/Decide`), and
none of their imports changed, so their elaboration is the same by
construction.  Re-timed as a check of the machine (the W6 baselines'
method, measured at `8eca1996`; another session's build ran beside, load
1.7–3.4 at the starts, two `Derived9` runs at load 2–11 left out):

| Module | W6 end of work | 6c part 1 (runs) | ratio | CPU (min) |
|---|---|---|---|---|
| `TestSuite/Derived9` | 7.16 s | **7.53 s** (7.78, 7.53, 8.18) | 1.05 | 9.04 s |
| `TestSuite/Derived10` | 11.11 s | **11.49 s** (11.49, 11.69, 11.82) | 1.03 | 13.40 s |
| `TestSuite/Derived11` | 3.16 s | **3.28 s** (3.28, 3.38, 3.32) | 1.04 | 3.49 s |
| `Examples/Tactics/Decide` | 49.14 s | **36.20 s** (36.48, 36.20, 37.54) | 0.74 | 37.04 s |
| `Examples/Tactics/UpdRulesScoped` (new) | — | **0.75 s** (0.76, 0.80, 0.75) | — | 0.63 s |

Every row within 1.2×; the 3–5% over the earlier lanes' (`Decide` 34.32 s
at the 6b review fix) is the load, as the CPU column shows on files that
did not change.  **Gate: partial**: the rules and merges run on
`Fml C Γ`, but nothing calls them yet (the scoped `sol_upd`/`sol_merge`
still erase the leaf, `Closers.lean`'s `Derive.onErased`, and the chains'
rewrite links read the erasure: `Rewrite`, `ChainRewrites`), and
`simplifyUpdate` drops less than the erased form (decision 87).

## What is left

**M6c: the closer on `Fml C Γ`**, gated.  Today a leaf is erased
(`Fml.erase`) to `NFml` and closed over the untyped state.
- **The boundary moves top-down.** A ported module takes `Fml C Γ` and
  erases only before calling the modules below it.
- **Scope is smaller than 25k lines.** The symbol libraries never port,
  since scoped terms share `Op0`–`Op3`: `ReadWrite`, `TermRules`,
  `TermTaclets`, `MemRead`, `MemNames`, `MemTheory`, `SlotLemmas`,
  `KeyNotation`, `DecideLang`, `Literals` and `Theory/**`.  Only modules
  that handle locals, updates or formula structure port.
- **Waves:** 6a `Closer`, `DecideSyn`, `DecideComplete`, `NFmlClose`, with
  symbolic atoms keyed by `Idx` (`DecideSyn`, `DecideComplete`: the scoped
  entry `Valid.of_reduce`, replaced at 6b by `Valid.of_reduceS`, and
  typed parameters only; their atoms stay
  name-keyed `LFml`, decision 78, pending the lead's call; `NFmlClose`:
  the scoped `sol_close` with typed parameters only, its `simp` set the
  untyped interpreter's, decision 82; `Closer` moved to 6b, decision 81);
  6b `Decide.lean` with `Closer` (10k and 3.7k lines, one agent;
  `Decide.lean` ported as a scoped front end, `Calculus/DecideScoped.lean`,
  its proofs on `NFml` through the commutation, decision 83; `Closer` not
  yet); 6c `NFmlUpdateRules`, `StateParts` (scoped ports beside them,
  `Calculus/UpdRuleScoped.lean`, `Calculus/StatePartsScoped.lean`, one
  way, decisions 86–88; unused until `Rewrite` and `ChainRewrites` port),
  `Rewrite`, `TheoryRewrite`, `ChainRewrites`, `ChainBranches`, then
  `NFmlDerive`, `NFmlLogic`, `RewriteChains`.
- **Gate per module:** the `TestSuite/Derived*` files and
  `Examples/Tactics/Decide` within 1.2× of the erased form's timings
  (the W6 baselines, Gates: the end-of-work column and its gate).
- **Fallback (decision 7):** a module that fails its gate stays on `NFml`
  for good, documented as the decision procedure's IR.  When nothing uses
  `NFml`, `NFml`, `Fml.erase` and `Semantics/Erased.lean` go.

**Besides M6c:**
- The lead's calls on proposals 78–88; the user's on decision 11 (whether
  `Surface.Stmt`, an IR with no semantics, counts as "deleting the untyped
  `Stmt`").
- At the merge into `master`: the SolKey reader's require back to
  `../../../solidity-lean` (side-projects `lean/solkey`, branch
  `intrinsic`) and that branch merged.
- Not run since W4: `check-corpus.sh` (its probes need `lake`), the
  `solkeycheck` executable (built only; no rule name or annotation changed),
  the reader's `keycheck` executable as a target and the VS Code extension's
  tests.
- From the M7 review: proposals 75 (the canonicity invariant on the typed
  state) and 76 (`Stmt.step` total), each a lane with its gates.
- Lean docstrings still call the erased side "today's" in places and cite
  this record's sections (at `ad728b16`).
- `Delab.withTwins` (`Calculus/DelabErase.lean`) does not pass `schema` on
  its `frames = true` path; nothing calls it with both set.
