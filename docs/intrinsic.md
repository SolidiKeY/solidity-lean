# Making the model intrinsic

The record of the intrinsic refactor (branch `intrinsic`, 2026-10-07 to
2026-10-11): locals scoped in the syntax (`Stmt C Γ Γ'`, positions `Idx`), a
state typed by its context, a run with no `stuck`, a compiler total on the
scoped syntax, and the calculus over scoped formulas.  Done but for the rest
of the closer (M6c, "What is left").  `docs/module-map.md` says where each
part lives now.

The full lane notes are in this file's history: M1–M6 and W0–W5 (what each
lane did, its pins, timings and review), the spike behind Gate G0 and the
original design at `ad728b16`; W6 (the M7 review in full, the W3 and W4b
gate tables, and each M6c wave's lane notes with its gate table) at
`b8565d23` (`git show b8565d23:docs/intrinsic.md`).  Docstrings that cite a
section of this record by name ("M6a lane", "W4 item 11", "Decision 17',
implemented", "how `dl{ … }` will write a scoped taclet", …) cite those
versions.  It names files by the paths they had at each step, which is why
`scripts/check-doc-paths.sh` skips this record (decision 68).

## What changed

| | Before | After |
|---|---|---|
| Syntax | `Stmt C`, locals by name, unscoped (a branch's local outlived it), a locals check `Stmt.wt` beside it | `Stmt C Γ Γ'` (`Syntax/Scoped.lean`): a local is a position `Idx Γ t` carrying its type (`Scope.lean`), branches, loop bodies and blocks are scopes, a call's body is closed over its own frame; the elaborator emits it directly, a local by `NCtx.find` (`Syntax/Elab.lean`), and the printers print it (`Calculus/PrintStmt.lean`): the untyped `Surface.Stmt` and `resolve` went at W8 (decision 11) |
| State | untyped `Semantics.State`: values, storage and heap by name, with junk | `State C Γ` (`Semantics/State.lean`): typed values (`PrimTy.Denote`, a `uint` an `Int` in range), typed storage (`SVal T` over `structDef`, `Storage C`), a typed heap (`HRef H R`, no mapping object), locals computed from the context (`TEnv`) |
| Run | `Stmt.run` on the untyped state, halting by `revert`, `panic`, `diverge` or `stuck` | `Stmt.run` (`Semantics/Run.lean`) on the typed state, halting by `revert`, `panic`, `diverge` or `exhausted` (a push at the bound, decision 15): never stuck; the only run of a statement (W4) |
| Untyped side kept | | the state's operations (`Semantics.lean`), which the typed ones erase to (`StorageErase`, `HeapErase`, `TypedErase`), and the erased state `EState C Γ` (`Semantics/Erased.lean`): what the closer's terms read |
| Compiler | `compileStmt` with `wtStmt`, `not_stuck` | over the scoped syntax, locals at their level (`Evm/Compile.lean`), `inFrag` the fragment alone, `compile_correct` over the typed run (`Evm/Correct.lean`), no `not_stuck` |
| Formulas | `Fml C` with modalities over `Stmt C` | `Fml C Γ` (`Calculus/Fml.lean`) with frames (`seq`, `pop .block`/`.capture`) and the hidden binder `bind`; `Update.lean`'s formulas without the modality are `NFml`, the closer's input; a `dl!{}` with a modality reads scoped, one without reads as `NFml` (`Surface.Fml` went at W8) |
| Rules | `Taclet C k m s p` on `Stmt C`, `Taclet.sound` by case | the same 159 lines read scoped (`Calculus/Rules.lean`, `open scoped Solidity.Schema`); `Taclet.toStep` (`Calculus/Taclet.lean`) says each is the rule `Stmt.step` fires, so soundness is `Stmt.sound` (`Calculus/Sound.lean`) with no proof per taclet; `blockEmpty` and `functionFrameEmpty` claimed; no cover goal (KeY's two goals); the step rules read the rule set (`⊢ₖ`, decision 36) |
| Sequent | `Proves` over `Hyp` | `Proves C R Γ₀ H φ` over a telescope `Hyps` (`Calculus/Proves.lean`); `Proves.valid` with no hypothesis; a leaf closed by its erasure (`Proves.close`, `Calculus/CloseErase.lean`) |
| Tools | on `Fml C` | `sol_symex`, `sol_prove`, `sol_derive?`, chains, `#chain`, the proof tree, `#wp`, `#step`, specs, contracts, callbacks on `Fml C Γ`; the same text through `open scoped Solidity.Scoped` (`Calculus/Surface.lean`) |
| Names (W5) | `Solidity.Core.X`, `Calculus/Core/*`, `TState`, `trun` | `Solidity.X`, `Calculus/*`, `State`, `run`; the old side's clashing names under `Surface`, `NFml`, `Semantics` (decision 62) |
| Closer (W6) | a leaf erased to `NFml`, closed over the untyped state | in part on `Fml C Γ`: `sol_decide` reduces a scoped leaf by position (`Calculus/DecideScoped.lean`), `sol_close` reads parameters at their types, `sol_prove`'s leaves on `⊢` are scoped sequents with `rw` (`Calculus/SeqRewrite.lean`), the chains rewrite while the program is open (`Calculus/RewriteScoped.lean`), the update rules and merges have scoped ports (`UpdRuleScoped`, `StatePartsScoped`; W7: `sol_upd`, `sol_merge` and the chains' links while the program is open use them); below that `NFml` stays the decision procedure's IR (decisions 83, 88, 91, 93) |
| SolKey reader | `Corresp.LeanShape` over `Stmt.*` | ported on its branch `intrinsic` (decisions 51–54, 73, 74) |

Not restated from master: termination (`symex_terminates`,
`symex_normalizes`) and progress (`Fml.active_iff_step`,
`Fml.step_wellFounded`), retired at W2 `symex`/W4 `calc-del` because the
scoped strategy is fuelled; `never_stuck`, because the typed run has no
stuck outcome.

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
| M6c | **done with IR** (W6–W7, merged 2026-10-11; gates passed) | the closer on `Fml C Γ`: 6a (`DecideSyn`, `DecideComplete`, `NFmlClose`), 6b (`Decide.lean` as a scoped front end), 6c (update rules, merges, `⊢`/`⊨` leaves, the chains' rewrites while the program is open); W7: atoms by position and the closer on the scoped reduction, the `⊨` route on the walk, the scoped update rules given their consumers.  `NFml`, `Fml.erase` and `Semantics/Erased.lean` stay as decision 7's IR, every reader listed ("M6c", W7 merge); `NFml` and `Fml.erase` deleted at W9.5a ("W9.5a `delete` record") |
| M7 | done 2026-10-09 | the docs; the review pass ("M7 review"; proposals 75–77) |
| W0 | done | the four M6 lanes merged; `Proves.valid` unconditional; `resolve`'s output `Fresh` |
| W1 | done 2026-10-08 | off M3's run: typed-run lemmas (`runlemmas`), typing (`typing`), the EVM (`evm`), the rule table read scoped (`rules`) |
| W2 | done 2026-10-08 | soundness over the typed run (`sound`), the strategy (`symex`), chains (`chains`), the tree (`tree`) |
| W2.5 | done 2026-10-08 | typed soundness of the arms and blocks (`tsoundA`, `tsoundB`); decisions 12–17' implemented (CORE 1, CORE A, CORE B) |
| W3 (a–d) | done 2026-10-08 | the flip: tactics, TestSuite, tree and chains onto the scoped calculus; captures by provenance; the W3 gates |
| W4 | done 2026-10-09 | prep (`theorems`, `contracts`, `moves`), then `sem-del` (the untyped run), `calc-del` (the untyped calculus), `modal` (the modality off `Update.lean`'s formulas), `reader-dry`; W4b: `run40` (decisions 40, 50), `rules36` (36, 53), `printers` (item 14) |
| W5 | done 2026-10-09 | the rename (`scripts/w5-rename.sh`, since deleted), its pins, review fixes, the reader ported |
| W6 | done 2026-10-09 | lanes `w6-canon` (decision 75 implemented, 77 recorded false), `w6-step` (76: `Stmt.step` total), `w6-closer` (M6c 6a, 6b, and 6c's lanes `w6c-upd`, `w6c-rw`, `w6c-chain`); merged in that order into `intrinsic`; the final gates ("Gates") |
| W7 `w7-route` | done 2026-10-11 | the `⊨` route on the `⊢` walk; only an `assert` panics, typed; decision 77's conditional form; bare `simp`s (proposals 95–98) |
| W7 `w7-closer` | done 2026-10-11 | the closer core: atoms by position, `LFml.closeS` on the scoped reduction, its soundness over the typed state (proposals 99–100) |
| W7 `w7-rewrites` | done 2026-10-11 | the scoped update rules and merges given their consumers; the open-program links scoped; decision 49's examples restored (proposals 101–105) |
| W7 merge | done 2026-10-11 | `w7-route`, `w7-closer`, `w7-rewrites` merged in that order (proposals renumbered 95–105); vestigial `open NFml.Proves` and four dead lemmas deleted; the IR's readers listed; the final W7 gate ("M6c") |
| W8 | done 2026-10-11 (W8.1–W8.5, close-out) | decision 11 resolved: `Surface.Stmt`, `Surface.Prog`, `Surface.Fml` removed, the elaborator and printers on the scoped syntax ("W8 plan", "W8 result") |
| left | — | the lead's calls on proposals 106–117 (W8.2–W8.3) and 118–128 (W8.4); at the merge, the reader's require back to `../../../solidity-lean`; optional ports on the IR and the IR's rename ("What is left") |

## Checks at the end (W6)

The merge of `w6-canon`, `w6-step` and `w6-closer` into `intrinsic`
(2026-10-09, `b8565d23`): one conflict, in this record's "What is left";
none in code.  `w6-step` made `Stmt.step` total; the merged tree built
with no fix.
`lean_build` of `Solidity`, `solkeycheck`, `SolidityCorpus` and
`SolkeyTestSuite` green on the first run (320 jobs, no module
OOM-killed).  `check-orphans` (306 reachable; the four orphans are the
git-excluded `Scratch/` modules), `check-doc-paths`, `check-rule-text`:
OK; the duplicate-name scan reports only `as` (`Evm/Repr`,
`Examples/Verify`) and `delabFml`/`delabProves`, false positives already
at `77c6e047`.  `sorry` 19 lines, `axiom` 1, `maxHeartbeats` overrides 30,
as at W5.  Not run since W4: `check-corpus.sh`, `check-testsuite.sh`, the
`solkeycheck` executable (built only; no rule name or annotation changed)
and the SolKey reader's build (its only mention of `Stmt.step` is a
comment, `SolKey/Shape.lean`).

## M7 review (2026-10-09)

The read-only finder/skeptic pass of M7 (in full at `b8565d23`):
docstrings brought to the current design, the untyped evaluators over
`Surface` syntax and their lemmas deleted as dead code, types made to
carry what they could (`defaultOk`, `Invariant.fo`, `inFrag`), weakened
statements restated (`Problem.deploy_of_valid`) or recorded
(`reachable_iff`'s `FitsStorage`), the tools' scoped readings
(`side_cond`, `apply unfoldStep`, `notScopedNotation`), and the bare
`simp`s it found replaced by `simp only`.  Three findings were left as
proposals 75–77, all three W6 lanes (Decisions).

## Final review (2026-10-09)

The confirmed findings of the final review, applied:
- *chains*: `Fml.StepBy.unique` concludes `r = r'` again
  (`StepRule.eq_of_focus`: the premise by `Rule.premise_unique`, the
  derivation by proof irrelevance); `Fml.Steps.measure_le`,
  `Fml.Steps.eq_of_measure` ported; `Fml.OneStep.stepBy` in
  `Calculus/ChainRules.lean` (`Focus.rule`, by `Stmt.rule_exists`).
  Master's `Fml.StepBy.ofOneStep` (from `Fml.rule`, which the scoped side
  does not have) is not ported: `OneStep.stepBy` and `StepBy.unique`
  cover it.
- *Gate G0, condition 2*: the six twins without a link theorem have one
  (`Upd.freshB_eq_freshBM`, `Fml.foFreshB_eq_foFreshBM`,
  `Fml.bindsB_eq_bindsBM`, `Upd.freshK_eq_freshM`, `Fml.plainB_eq_plainM`,
  `Fml.posB_eq_posM`).
- *soundness premise*: `symex_sound`, `symex_valid`, `Fml.step_valid`,
  `Valid.of_proves`, `Valid.of_residue` take no `Stmt.Sound C`
  (`Stmt.sound` inside; `Symex.soundName` deleted).
- *canonicity*: `canonInv.ekeeps` asks a leaf for canonical storage only;
  the memory writes are storage frames (`memWriteField_storage` …
  `writeAddr_storage`, `MLoc.write_storage`), their heap halves deleted.
- *dead code*: the per-statement `StateWT` preservation layer
  (`Typing/Soundness.lean`, `Typing/State.lean`'s copy typing,
  `Typing/StoragePreservation.lean`'s `save_hasTy` and kin, with the
  `strip_hasTy`/`defaultOf_hasTy` chains), `Semantics/ToSem.lean`'s
  lemmas (the definitions stay, for `#run`), five `Agree.lean` lemmas,
  nine calculus lemmas (`Premise.sound_of_halt`, `sound_unfoldH`, …) and
  the duplicate `Stmt.sound_block`.
- *docs*: `sol_close` cited at `Calculus/Close.lean`; master's arms
  and strategy cited at `ad728b16` (`Step`, `Arms`, `Blocks`,
  `SoundLoops`); `docs/README.md` indexes this record; `AGENTS.md` names
  `Solidity.Calculus.SolSpec` for `sol_spec`; `.claude/rules/typing.md`
  states `reachable_iff` under `FitsStorage`; termination and progress
  recorded as not restated ("What changed"); `docs/loops.md`'s
  `Proves.check` and `NFml.inL`.
- *bare `simp`*: the 33 lines this branch wrote in
  `Typing/Constructibility.lean` are `simp only`/`simpa only`.

Left: "Only an `assert` panics" over the typed run ("What is left"); the
bare `simp`s that predate the branch (`Typing/Constructibility.lean`,
`Semantics/Properties.lean`, `Typing/StoragePreservation.lean`,
`Typing/Storage.lean`, `Semantics/Storage.lean`; no more than master's).
Checks: `lean_build` of `Solidity`, `solkeycheck`, `SolidityCorpus` and
`SolkeyTestSuite` green (321 jobs); `check-orphans`, `check-doc-paths`,
`check-rule-text` OK; the duplicate-name scan as at W6; `sorry` 19 lines,
`axiom` 1, as before.

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

The W3 gates and the M0 rows re-timed at W4b are at `b8565d23`: every row
within its limit then, nothing slowed by W3–W4b.

**W6 baselines and the final gate.**  The baselines (2026-10-09,
`8761bbde`, before W6) are the erased form's timings M6c's gates compare
against; the final column re-times every row on the merged tree
(`b8565d23`, 2026-10-09).  Method, both times: the file copied under
`Solidity/Scratch/` and opened in a fresh worker through the Lean MCP
(`lean_diagnostic_messages`), one worker at a time, every import built
beforehand, `/proc` sampled every 20 ms, the worker killed after each run.
The time is the *end of work*: the first sample at which the worker's CPU
is within 50 ms of its final value (the wall to the last CPU can end on a
tick the worker spends while the MCP polls it, 0.4–7.4 s later); the
minimum of three runs.  CPU is the worker's user + system time, the
minimum of the runs.  Machine: Intel i9-13900 (32 threads), 64 GB, the
32 GiB session cgroup at 8.7–11.0 GB.  Load (1 min) at the starts:
baselines 0.24–1.24 (median 0.76); final, pass 1 4.8 falling to 1.0 (the
build had just ended; KDE's file indexer at nice 19), passes 2 and 3
0.9–2.1.  The baselines' per-run figures are at `b8565d23`.

| Module | W6 baseline | gate (1.2×) | **final** (three runs) | ratio | CPU, baseline → final | peak RSS |
|---|---|---|---|---|---|---|
| `TestSuite/Derived1` | 7.32 s | 8.78 s | **7.41 s** (7.41, 7.50, 7.43) | 1.01 | 8.98 → 9.02 s | 3.3 GB |
| `TestSuite/Derived2` | 8.63 s | 10.36 s | **8.72 s** (8.85, 8.75, 8.72) | 1.01 | 10.38 → 10.46 s | 4.3 GB |
| `TestSuite/Derived3` | 13.01 s | 15.61 s | **13.02 s** (13.02, 13.03, 13.03) | 1.00 | 14.48 → 14.51 s | 5.1 GB |
| `TestSuite/Derived4` | 17.57 s | 21.08 s | **17.57 s** (17.57, 17.62, 17.61) | 1.00 | 19.61 → 19.61 s | 5.5 GB |
| `TestSuite/Derived5` | 6.95 s | 8.34 s | **6.99 s** (7.04, 6.99, 7.06) | 1.01 | 8.23 → 8.32 s | 3.6 GB |
| `TestSuite/Derived6` | 11.42 s | 13.70 s | **11.43 s** (11.84, 11.50, 11.43) | 1.00 | 13.00 → 12.98 s | 5.1 GB |
| `TestSuite/Derived7` | 50.43 s | 60.52 s | **50.80 s** (50.99, 50.80, 50.80) | 1.01 | 52.88 → 52.91 s | 7.8 GB |
| `TestSuite/Derived8` | 26.38 s | 31.66 s | **26.31 s** (26.44, 26.31, 26.57) | 1.00 | 27.50 → 27.64 s | 6.5 GB |
| `TestSuite/Derived9` | 7.16 s | 8.59 s | **7.11 s** (7.11, 7.23, 7.14) | 0.99 | 8.62 → 8.62 s | 3.7 GB |
| `TestSuite/Derived10` | 11.11 s | 13.33 s | **11.24 s** (11.24, 11.30, 11.24) | 1.01 | 12.75 → 12.90 s | 4.9 GB |
| `TestSuite/Derived11` | 3.16 s | 3.79 s | **3.18 s** (3.18, 3.23, 3.25) | 1.01 | 3.36 → 3.39 s | 2.4 GB |
| `TestSuite/Derived12` | 13.17 s | 15.80 s | **13.25 s** (13.29, 13.37, 13.25) | 1.01 | 14.01 → 14.10 s | 4.7 GB |
| `TestSuite/Derived13` | 6.36 s | 7.63 s | **6.33 s** (6.33, 6.36, 6.39) | 1.00 | 6.38 → 6.45 s | 3.1 GB |
| `TestSuite/Derived14` | 10.89 s | 13.07 s | **10.91 s** (10.91, 11.09, 10.92) | 1.00 | 11.50 → 11.43 s | 4.0 GB |
| Derived1–14, sum | 193.6 s | 232.3 s | **194.3 s** | 1.00 | 211.7 → 212.3 s | |
| `Examples/Tactics/Decide` | 49.14 s | 58.97 s | **34.51 s** (34.64, 34.51, 34.69) | 0.70 | 49.97 → 35.36 s | 2.0 GB |
| `Examples/ProofTree` | 9.81 s | 11.77 s | **9.74 s** (9.94, 9.74, 10.01) | 0.99 | 9.85 → 9.73 s | 1.8 GB |
| `Examples/Chains/Storage` | 7.45 s | 8.94 s | **7.41 s** (7.60, 7.41, 7.42) | 0.99 | 7.86 → 7.81 s | 1.7 GB |
| `Examples/ChainRewrites` | 6.36 s | 7.63 s | **7.30 s** (7.47, 7.30, 7.34) | 1.15 | 7.24 → 8.50 s | 1.7 GB |
| `Examples/ChainRewrites` without §3⁗ | 6.36 s | 7.63 s | **6.33 s** (6.34, 6.41, 6.33) | 1.00 | 7.24 → 7.31 s | 1.7 GB |

The M0 rows, the same runs (M0's limit is M0 + 20%):

| M0 row | M0 limit | W6 baseline | **final** (three runs) | CPU, baseline → final |
|---|---|---|---|---|
| `TestSuite/Derived9` | 8.4 s | 7.16 s | **7.11 s** | 8.62 → 8.62 s |
| `TestSuite/Derived10` | 11.2 s | 11.11 s | **11.24 s** | 12.75 → 12.90 s |
| `TestSuite/Derived11` | 3.4 s | 3.16 s | **3.18 s** | 3.36 → 3.39 s |
| `TestSuite/Problems` (`legacy`) | 1.44 s | 0.81 s | **0.85 s** (0.88, 0.85, 0.85) | 0.63 → 0.68 s |
| `TestSuite/ScopedProblems` | — | 1.39 s | **1.40 s** (1.41, 1.40, 1.44) | 1.21 → 1.23 s |
| `Solkey/TestSuite` | 12.5 s | 10.83 s | **10.82 s** (10.94, 10.82, 10.84) | 10.95 → 10.94 s |
| `Examples/Benchmark/Syntax` | 1.44 s | 1.41 s | **1.42 s** (1.45, 1.45, 1.42) | 1.49 → 1.52 s |
| `Examples/ProofTree` | 12.1 s | 9.81 s | **9.74 s** | 9.85 → 9.73 s |
| `Examples/Chains/Storage` | 9.0 s | 7.45 s | **7.41 s** | 7.86 → 7.81 s |
| `Evm/Examples` | 11.4 s | 7.75 s | **7.84 s** (7.87, 7.84, 7.93) | 8.00 → 8.10 s |
| `Evm/Correct` | 30.7 s | 1.68 s | **1.70 s** (1.70, 1.70, 1.71) | 5.92 → 6.08 s |

**Final gate: passed.**  Every row within its 1.2× gate; the Derived
files and the M0 rows within 1% of the baselines (0.99–1.01, the sum
1.00), as each lane measured them: their path (`sol_prove`'s leaves, then
`sol_decide_cons` on `NFml`) barely changed.  `Examples/Tactics/Decide`
is 30% faster (a parameter read at its type, one case where the erased
leaf split three; 6a part 2).  `Examples/ChainRewrites` is 1.15× only by
its new section (§3⁗, four chains with eleven rewrites while the program
is open, `w6c-chain`): without it, 1.00.  One raw M0 limit is crossed by
noise: `Derived10` at 11.24 s against 11.2 s (0.4%; the baseline was
0.09 s under it, the 6a–6b lanes measured 11.20–11.21 s, the file and its
path unchanged), within its W6 gate (13.33 s).

**W7 `w7-rewrites`** (2026-10-11, after the review fixes at `6f24cbc4`;
the method above, the 32 GiB cgroup at 7.4–7.9 GB, load 0.3–1.4; the other
W7 lanes idle; three runs where a row is gated, one otherwise):

| Module | W6 baseline | gate (1.2×) | **W7 `w7-rewrites`** | ratio | CPU |
|---|---|---|---|---|---|
| `Examples/ChainRewrites` (§3⁗ moved out, proposal 102) | 6.36 s | 7.63 s | **6.88 s** (6.88, 6.88, 6.85) | 1.08 | 8.07 s |
| `Examples/ChainRewritesOpen` (new) | — | — | 3.48 s | — | 3.90 s |
| `Examples/Chains/Storage` | 7.45 s | 8.94 s | **7.58 s** (7.60, 7.58, 7.55) | 1.02 | 8.21 s |
| `Examples/ProofTree` | 9.81 s | 11.77 s | 10.04 s | 1.02 | 10.26 s |
| `Evm/Correct` (control, untouched) | 1.68 s | — | 1.74 s | 1.04 | 6.31 s |
| `Examples/Tactics/UpdateRules` (`sol_upd`, `sol_merge` scoped) | — | — | 2.89 s | — | 2.99 s |

**The unchanged content, timed against this lane's base.**  `intrinsic`'s
copy of `Examples/ChainRewrites` (at `1616405c`, the base of this lane),
whole and without §3⁗, three runs each on the base checked out in this
worktree and on this branch, same cgroup and load:

| Checkout | whole | without §3⁗ |
|---|---|---|
| `1616405c` (base) | 7.43, 7.50, 7.43 s | 6.46, 6.42, 6.40 s |
| `9d1f186f` (before the fixes) | 7.97, 7.92 s | 6.88, 6.89, 6.87 s (+7%) |
| `6f24cbc4` (after) | 7.45, 7.43 s | 6.44, 6.44, 6.48 s (+0.5%) |

The +7% on identical text was **this lane's**, not `intrinsic`'s post-W6
commits (the record said otherwise at `83ec42c4`, untimed; the base is
within 2% of W6's final run, 7.30 and 6.33 s).  Bisected (without §3⁗, one
or two runs each): `fa3e54fa` 6.69–6.73 s (`openRwPath` in `leads%` and
`leadsSteps`: the `~~>` statement `headlineWrite` alone took 0.12 s more,
the depth-3 search run from every open line of a derivation before the
past-program reading), `8052d96d` 6.69–6.75 s, `df08c553` 6.99–7.05 s
(`applyOnPV` and three `stateMerge`s per update widened that search),
`7af11076` 7.78 s (scoped links past the program, off from `445c76f3`).
Fixed at `6f24cbc4`: the search is breadth first with each line expanded
once, bounded (`openRwNodes`, its own heartbeats per line), and not run
where the line written keeps no program (`Written.mayBeOpen`; on the proof
side `openRwFrom`, a line with no `Fml.modal`), since a rewrite while the
program is open keeps it.  Every row passes its gate.
`Examples/Chains/*` against `w6c-chain`'s runs, at `445c76f3` (not re-timed
after the fixes; the scratch builds of all thirteen pass): `Arithmetic`,
`CheckedArithmetic`, `EvaluationOrder`, `Memory`, `MemoryArrays`,
`MemoryCoverage`, `MemoryDelete`, `MemoryToStorage`, `StorageToMemory`,
`Payment`, `StorageArrays`, `StorageCoverage`, `StorageDelete`: 1.02,
1.25, 1.04, 4.86, 6.26, 11.81, 9.15, 5.49, 2.55, 1.09, 3.51, 14.16, 7.24 s,
0.96–1.06 of them.
`TestSuite/Derived*` and the M0 rows were not re-timed: no module on
their path changed but `DelabErase` (printing).

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
    *Overridden by the user (below): `Surface.Stmt`, `Surface.Prog` and
    `Surface.Fml` removed at W8 ("W8 result").*

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
    *Superseded at W8 (decision 11 overridden): `Surface.Fml`,
    `quoteAuto`, `eraseS` and `resolveN` removed; a modality reads scoped,
    the printers print `Fml C Γ` (`Calculus/PrintStmt.lean`), and the
    obligations are `Fml N []` (`solc_scoped_problems`).*
47. *Proposed (W4 `modal`), the lead's call:* `Core.Fml.erase` (the
    closer's input) erases a modality to `false`: `NFml` has none, and the
    closer takes only a formula with none (`Fml.Closable`), so nothing
    reads it; `Fml.eraseS` keeps it for the printers and the chains' lines
    (`Fml.erasedQuoted`).  `#wp` shows a reduction only of a formula with
    no modality left (`!ψ.active`).
    *Superseded at W8: `Fml.eraseS` and `Fml.erasedQuoted` removed; the
    printers print `Fml C Γ` (`Calculus/PrintStmt.lean`).*
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
    *Superseded at W8: `Surface.Prog` removed; the runs are
    `Prog.runT`/`Prog.localAfterT`/`Contract.deployRun` on the scoped
    block (`Tools/Run.lean`).*
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
    ones read on the erased step.  *2026-10-12 (W9.6.1):* `Read.sortOk_typed`
    and `TKeeps.of_agrees` are gone: `Read.sortOk` reads a typed state with
    no hypothesis, and `TKeeps` the typed step (`RunInv.HoldsT`).
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
    *Implemented (W6 lane `canon`):* `RunInv.TKeeps` reads the invariant
    under `HTy.toHeapTy 0 σ.H` before and after the step; a leaf's
    obligation (`RunInv.EKeeps`, `TKeeps.of_agrees hnd`) is read on the
    erasure of a typed state, so it is given `RunWT` by `State.erase_wt hnd
    σ`; a call's entry is read on the typed state (`tkeeps_call`'s
    `henter`, `CallRet.enterT_ok`).  `canonInv.glob` is `CanonStorage` and
    its locals carry nothing: the heap is canonical by construction
    (`State.erase_canonHeap`), so `canonInv.ekeeps` hands each leaf
    `Canon` and asks for the storage's.  `tightInv` is `canonInv` and
    `Semantics.Tight` on the global part, `LTy.Keys` on the locals.
    `Prog.run_canon hnd P hc h` and `Prog.run_tight hd hnd P hc ht h` take
    `hc : CanonStorage C σ.erase.storage` and no `hwt`; the `tight_*`
    leaves are unchanged (`tkeepsT_of hnd` instantiates their `RunWT` and
    `Canon` from the typed state).  `RunInv.Keeps`, the erased obligation,
    is deleted (`Typing/Soundness.lean`); `RunCanon.ofCopyOutC` is
    `CopyOutC.wtCanon` and `MRhs.eval_canon` returns `RunWT ∧ Canon`, the
    old `RunCanon`.  No statement outside `Typing/` moved; no pin moved.
76. *Proposed (M7 review), the lead's call:* `Stmt.step` keeps its `Option`
    result.  `Stmt.rule_exists` proves it never `none`, but making it total
    changes the kernel-evaluated strategy (every arm, `shortStep`, the
    `apply_toStep` dispatch) and every `Proves` program rule, `Premise.Sound`
    and `Stmt.Sound` (about 70 sites); AGENTS.md asks that such a change be
    timed against `TestSuite/Derived9–11` and `Examples/ProofTree` before
    and after, so it is a lane of its own with those gates.
    *Implemented (W6 lane `w6-step`, 2026-10-09):* `Stmt.step` returns
    `Premise C Γ Γ'`, every arm of `Calculus/Arms.lean` and
    `Calculus/Blocks.lean` too (`OpLoc.unfoldRecv`, `Args.capture` and
    `Prog.frame` stay `Option`: they are tests, not rules).  The one arm
    that returned `none`, `shortStep` off `&&`/`||`, is unreachable
    (`localStep` calls it only where `op.shortCircuits`) and now returns
    `.done false`, sound for any statement (`sound_done_false`).  The
    program rules of `Proves` take `d : s.step … m = .update U` (and kin),
    `Taclet.toStep` is `s.step k m = p`, `Stmt.Sound` and the arms'
    `…_sound` take `hs : …Step … = q`; `Fml.modalStep` (and
    `Fml.modalFocus`) wrap the premise in `some` once, where they used
    `Option.map`; `Stmt.stepIn R` stays `Option` (`.solkey` refuses a
    `LeanTaclet`'s statement).  `Stmt.rule_exists` is now
    `Rule C k m s (s.step k m)` (`Main.rule_exists`: `s ⇝[k, m] s.step k m`;
    `Stmt.solkey_rule_exists`: `Taclet C k m s (s.step k m)`).  Its replay
    table changed in two rows, both re-derived by `#derive_ruleExists?`:
    `assignLocal` gains a `!` per unreachable `shortStep` leaf (the
    `contradiction` that closed a `none`), and `deleteMem` loses its
    `/Ty` and `/ArrTy` splits (the step now reduces through
    `Premise.clearMem`'s match on the type, which `some` had hidden from
    `whnf`).  No pin changed.
    **Gates** (end of work, as the W6 baselines; the minimum of the runs
    kept, baseline in parentheses): `Derived9` 7.06 s (7.16; 0.99×), runs
    7.23, 7.22, 7.06, the first at load 3.6; `Derived10` 11.33 s (11.11;
    1.02×), runs 11.58, 11.33, 12.02, the first at load 3.2; `Derived11`
    3.20 s (3.16; 1.01×), runs 4.88, 3.28, 3.20, the first at load 4.0,
    after an aborted run (2.26 s, 1.66 GB against about 2.18 GB for a full
    one) that was dropped; `Examples/ProofTree` 9.93 s (9.81; 1.01×), runs
    10.05, 9.93, the minimum of two, a first run discarded (load 6.8 rising
    to 24.6 under another lane's build, 43.3 s).  CPU 8.48, 12.94, 3.42,
    9.92 s against 8.62, 12.75, 3.36, 9.85.  Every row within 1.2×, none
    slower beyond noise: kept.
77. *Proposed (M7 review), the lead's call:* `Reachable C st ↔ Canon ∧
    Tight` (`reachable_iff`, `shape_iff_reachable`, `wt_iff_reachable`)
    holds for a storage that fits (`FitsStorage C st`): a consequence of
    M1's in-range literals, since a word, key or slot out of range is
    canonical and tight but no literal writes it.  `Reachable → FitsStorage`
    is not proved here.
    *Recorded (W6 lane `canon`), not proved, because it is false:*
    `huge_reachable_not_fits` (`Typing/Constructibility.lean`): the contract
    `Huge`, one `uint[2^256 + 1]` root, reaches its initial storage by the
    empty program, and that root has more elements than `FitsStorage`
    allows a fixed-size array (`≤ 2^256`, each written at a literal index
    by the builder).  So the three theorems keep their `FitsStorage`
    premise.  With a premise on the contract instead (every fixed size at
    most `2^256`, which solc's "type too large for storage" check
    implies), `Reachable → FitsStorage` would need a third run invariant
    beside `canonInv` and `tightInv`, which the typed state does not give
    by construction: every mapping key in its key type's range
    (`SMap` keys are `Int`, written through `Value.keyAt` and alias paths)
    and every dynamic array's live and recycled slots together fewer than
    `2^256` (`SVal.array` bounds the live ones only; `push`, `pop`,
    `delete` and the overlay copies keep the sum).  Its leaves would
    mirror `tight_*` (about 20, with `save`/`overlay`/`copyMToSt`
    lemmas for the sum and the keys); left as a proposal for the lead.

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
    *Implemented (W7 lane `w7-closer`):* an atom is `Atom` (`DecideLang`):
    `pos k`, the local at the position `k` of a scoped leaf's context
    counted along its binders, or `name x`, an erased leaf's local (the `⊨`
    route and `sol_prove`'s leaves, until `NFml` goes).  The scoped
    reduction reads no name: every binder's local is held under its
    position's key (`slotVar k`), a quantifier's local is the atom `pos k`,
    and a hidden binder (at any type) pushes a position bound to nothing
    until an update binds it: a value-typed hidden local read before its
    update is outside the fragment (`Tm.inLS`), where the erased route read
    it at its name's last binding, so the fragment is narrower there.  The closer
    reads an atom at its key (`Atom.key`, `Facts.vars`), so it runs
    unchanged on both.  Printed as `pos(k)` (`key{}`) or the key
    (`#wp`'s `LTerm.fmt`): the binders' names are not carried (proposal
    99).
79. *Proposed (M6c 6a), the lead's call:* the constraints' step on a
    scoped leaf (`LFml.valid_alls_of_cons`) is sound, not an equivalence:
    the parameters are typed, the storage is still read untyped, so a
    leaf it does not close may be valid (the two `fail_if_success`
    examples of `Examples/Tactics/Decide` that hold in typed states stay
    open).  `NFml.valid_iff_cons`, the equivalence, stays for today's
    leaves (`sol_prove`'s, `NFmlDerive`'s leaf search).  master's
    `negativeKey` pin (`values[-1]` forcing a mapping) is now a
    `#guard_msgs` pin of its refusal: the typed elaborator rejects `-1`
    as a `uint`, as solc does, so a negative key is unrepresentable.
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
    *Implemented (W7 lane `w7-closer`):* `sol_decide` on a scoped leaf
    tries the closer on the scoped reduction (`LFml.closeS`,
    `Calculus/DecideComplete.lean`: `LFml.close` within `LFml.fits`, no
    layout), between the syntactic closing and the constraints; the
    parameters are bound at their types by the reduction's leading
    `LFml.all`s (`Facts.bind`).  No layout: proposal 100.
    Its bound is `NFml.Derive.elimSize`, moved to `Calculus/Closer.lean`
    so both routes read one constant.  Pinned in `Examples/Tactics/Decide`:
    `closerOnReduction` (a leaf `syn` does not close and the closer does)
    and `closerFallsThrough` (one past both, closed by the constraints).
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
    *Superseded in part (W7 lane `w7-closer`):* the scoped reduction's
    soundness no longer goes through the erasure.  `Fml.toLSM_sound`
    (`Calculus/DecideTyped.lean`) follows the leaf's binders, updates and
    connectives as `holds` reads them, over the typed state, at a polarity
    (the fragment `Fml.inLS pos` takes updates, hidden binders and
    modalities only in positive positions), and `Valid.of_reduceS` puts it
    together with the elimination (`LFml.elim_holds`); `Fml.toLS_eq` (the
    formula's commutation with the erased reduction) and its lemmas are
    deleted.  A term still reads its symbols on the erasure (`Tm.toLS_eq`
    under the keys, `Tm.eval_eraseB`): the symbols are untyped, as this
    decision says.  The G0 forms are kept: `Fml.toLS`, `Fml.inLS`,
    `Fml.peelS`, `Upd.view`, `Upd.replayS`, `Thin.sel`, `Tm.toLS`,
    `Tm.inLS` and `Idx.toNatR` by the recursor, each with its `match`
    twin and link.
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
    *Superseded in part (W7 lane `w7-closer`):* the bindings beside the
    positions are kept by each position's key (`slotVar k`), not by name,
    so a hidden binder's local is a fresh position bound to nothing, and a
    quantifier's is read by no binding so far (`Sym.vars`, `SymS.key`);
    `sameAt`/`allocPairS?` compare erasures under the keys.  With no
    commutation to keep, `Fml.FreshS` is gone.
85. *Proposed (M6c 6b), the lead's call:* `Examples/Tactics/Decide`'s
    fragment pins read `Fml.inLS` on scoped formulas; the second pin, a
    memory local no update binds (`{ x := read(memory, carol.age) }`),
    has no scoped spelling (a free name is a `uint` parameter, a memory
    local is in scope only through a binder) and is replaced by a read of
    the ledger (`{ y := net(a) }`), also outside the fragment.  Both still
    print `false`.

86. *Proposed (M6c 6c, `w6c-upd`), the lead's call:* the update rules
    on scoped formulas are **one way** (`UpdRuleS.sound`:
    `holds σ ψ → holds σ φ`, the direction a derivation uses), where the erased ones are equivalences.  The
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
89. *Proposed (M6c 6c, `w6c-rw`; 86–88 at the lane, renumbered at the
    merge), the lead's call:* `sol_prove` on a scoped sequent leaves
    the walk's own sequents (`Seq.SLeaf`, `Seq.leafS`), not today's
    sequents of their erasures: the closer still reads the erasure
    (`Derive.residue`, `synClose`, the decision procedure's IR), and a leaf
    it does not close is the scoped goal `H ⊢ φ`.  Its first line erases it
    to the goal today's leaf had (`Proves.close_leaf`,
    `Proves.close_leaf_dropWt`: `Fml.closeErase`, the first `np` `∀`s
    stripped, the connectives in front peeled into today's context), so the
    lines after it are unchanged; that line keeps today's text (`refine
    NFml.Proves.close_dropWt ?_`, `refine NFml.Proves.close ?_`: a global
    macro tries `core_leaf_close` first, today's rule on today's goal
    after), as decisions 80 and 82 keep written proofs' steps, so no replay
    of `Derived1`–`14`, `Suggestions` or `#solkey_derive?` moves.  The
    walk's spelling `refine close ?_` stays `Proves.close` on the whole
    erasure (a leaf of `sol_derive`), so `Benchmark/Mapping`'s
    `remove_spec`, which wrote it after `sol_prove`, now writes today's
    `refine NFml.Proves.close ?_` (one line; the leaf it closes is the
    same).  The `⊨` route (`Derive.lean`'s `sol_prove` on `Valid φ`) keeps
    today's leaves: it has no sequent, its leaf is the erasure of the
    strategy's whole output, and moving it to `⊢`'s walk changes the leaves
    of the `⊨` examples (`Constructors`, `LoopsImport`, `Purchase`, …).
90. *Proposed (M6c 6c), the lead's call:* the scoped `Proves` has today's
    `Proves.rewrite` as a rule: a Theory equation (`TermTaclet.sound`, or a
    law's `Term.Theq`) in every equation of the sequent, the context's
    preconditions and the goal (`Hyps.rwEqC`, `Fml.rwEqC`,
    `Calculus/SeqRewrite.lean`), through updates, quantifiers, hidden
    binders and the postcondition of a modality still open; sound over the
    typed state (`Fml.rwEqC_holds`, `Hyps.wrap_rwEqC`) and kept by
    `Proves.toAll`/`toSolkey`/`solkey_blocked` (`Fml.inSolkey_rwEqC`).  It
    replaces the derived `Proves.rewrite` (by `closeHolds`, no modality
    left, the goal's top equations only); `Proves.rewrite'` writes the
    result out, and `rw`/`sol_rw` on a scoped goal reach every side it
    rewrites (`Walk.eqSides`, `Walk.hypSides`).  This is decision 49's
    "rewrites under an open program come back" for the sequent
    (`SelectOnSaveConsr`'s two new examples).  Decision 49's four chain
    examples (`Examples/ChainRewrites`, §Literals) stay on `ψ`: their links
    (`applyOnRigid` through the connectives, `NFml.push`; `concrete`;
    `simplifyUpdate`) are `Calculus/ChainBranches.lean`'s and
    `Calculus/ChainRewrites.lean`'s on `Update.lean`'s lines, and a scoped
    line takes only `~[sequentialToParallel]~>` while its program is open
    (`Calculus/Chains.lean`, `Fml.MergeBy`); they come back with the chain
    port of those modules (the scoped update rules of lane `w6c-upd`,
    `UpdRuleS`, are their base), not here.
91. *Proposed (M6c 6c), the lead's call:* `NFmlLogic` and `NFmlDerive`
    stay, as the decision procedure's IR (decision 7's documented IR), not
    as a failed gate (their gate passed): every rule of `NFml.Proves` has
    its scoped twin, and `NFml.Proves` is what a scoped leaf erases to,
    the leaves of the `⊨` route, and the sequents written over today's
    terms (`Examples/Tactics/TermTaclets.lean`, `Calculus/CloseTests.lean`);
    `Derive.residue`/`synClose` are the closer on the erasure.
    `TheoryRewrite.lean` is a symbol library (`theoryRewrite` reads a closed
    term's erasure; the scoped `rw` calls it on the erasures of closed
    scoped terms, `Walk.rwTheory`); `Rewrite.lean`'s tactics stay
    `NFml.Proves`'s, the scoped ones are `Calculus/RewriteSyntax.lean`'s
    with the same text.

92. *Proposed (M6c 6c, `w6c-chain`; 86–88 at the lane, renumbered at
    the merge), the lead's call:* a chain's rewrite links on `Fml C Γ` are a
    new module, `Calculus/RewriteScoped.lean` (`FmlRw`, `Fml.RwBy`, the
    link `Link.rw`), each rewrite sound on the typed reading itself
    (`holds`), not by commutation with the erasure as `Decide.lean` is
    (decision 83): a `Leads` link needs both directions between a line
    and its erasure, and they hold only of a first-order formula
    (`holds_erase_fo`); an update reads the typed states it ends in, a
    modality erases to `false`.  Ported: a literal law in an update's
    right-hand sides under any modality (`FmlRw.lit`, exact:
    `Upd.rwC_apply_eq`), a term taclet onto a term that cannot halt in a
    box update's (`FmlRw.lawUpd`, `holds_upd_rwC`), `applyOnRigid` along
    the skeleton under an update that cannot halt or the box
    (`FmlRw.applyOnRigid`, `Fml.pushS_sound`: one direction, the
    first-order parts applied by `Fml.substU`), `concrete`
    (`FmlRw.concrete`, an equivalence); `sequentialToParallel` was already
    `Calculus/Merge.lean`'s.  The functions use `match` on the indexed
    families (G0 condition 1), the exemption `Calculus/Merge.lean` has:
    they run once a link.
93. *Proposed (M6c 6c), the lead's call:* a scoped rewrite is tried only
    while the program is open (the strategy still has a line to give), as
    the scoped merge is; a line with no program left goes on on its
    erasure as before (`Fml.ViaE`, `Calculus/ChainRewrites.lean`,
    `ChainBranches.lean`, `RewriteChains.lean`), so no existing chain's
    statement, line or pin changes.  Those three modules stay on `NFml`
    past the program, decision 7's fallback, as the rewrites' IR: porting
    them restates on scoped updates the merges that substitute a storage or
    memory write (`withStM`, `Upd.mergeStL`, `Upd.mergeMem`), the
    `simplifyUpdate` that asks a postcondition's fresh variables, the
    member-wise and covered laws (`Upd.covers`, `Term.base?`, `EvalLaw`)
    and `applyOnPV`, about 4k lines of soundness over the untyped
    interpreter, for no line a chain past the program does not already
    reach.
94. *Proposed (M6c 6c), the lead's call:* the scoped `applyOnRigid`
    applies a first-order antecedent under the box too, where
    `NFml.pushBox` keeps it whole: a first-order formula reads only the
    state's erasure (`Fml.substU_holds`), so `a[U] → [U]B` gives
    `[U](a → B)` wherever `U` returns, and `[U]` is true where it halts.
    Under the diamond it asks `U` to return in every state
    (`Upd.totalS`: locals and literals), and refuses otherwise.

**Lead, 2026-10-09 (5):** proposals 78–94 are approved. M6c continues (W7):
the closer's atoms by position and `Closer` on scoped formulas, the scoped
update rules and merges given their consumers, the open-program links
scoped, decision 49's four examples restored, the `⊨` route on the `⊢`
walk; then `NFml`, `Fml.erase` and `Semantics/Erased.lean` go wherever
nothing reads them, and what stays is recorded as decision 7's IR.

95. *Proposed (W7 `w7-route`), the lead's call:*
    `sol_prove` on `⊨ φ` is `Proves.valid` at `.all` and then the `⊢`
    walk (`evalSolProveValid`, `Calculus/ProvesDerive.lean`), decision 89
    extended: its leaves are the walk's sequents `H ⊢ ψ`, closed as a `⊢`
    leaf is (`refine NFml.Proves.close_dropWt ?_`, read as
    `core_leaf_close_wt` there).  The erased route (`Derive.proves`,
    `Derive.residueOf`, `Valid.of_proves`, `Valid.of_residue`) is deleted.
    Pins moved, each re-derived: `Examples/Tactics/LoopsImport`'s three
    invariant obligations leave one sequent per branch where the erased
    residue left one formula, so their leaf script runs under `all_goals`;
    `Examples/Tactics/Constructors`' `miniProblem` reads its parameter `a`
    typed, which the walk's first line strips (`Seq.leafErase`, decision
    28), so its first line is the walk's own `Proves.close` on the whole
    erasure (`refine Proves.close [] rfl List.nodup_nil ?_`, what
    `sol_derive?` writes); the residue pins of `Examples/Tactics/Dangling`
    and `Examples/ProofTree` (`rounds2`/`4`/`6`, `pushes22`, `writes4`/`6`,
    `deletes10`) read the walk's leaves (`Seq.residue`, `Seq.leafErase`)
    where they read the erased residue, and print the same.  The `⊨`
    route's step bound moved from `Derive.fuel` (5000) to the walk's
    `Seq.fuel` (`NFml.Derive.budget`); `Derive.fuel` now bounds only
    `sol_derive`'s walk.
96. *Proposed (W7 `w7-route`), the lead's call:* "only an `assert`
    panics" is `Prog.run_noPanic` over the typed run
    (`Semantics/NoPanic.lean`: `P.asserts = false → (P.run σ).NoPanic`,
    `Prog.run_ne_panic`), by the run's recursor and one lemma per `TRun`
    step; `Stmt.asserts`/`Prog.asserts` moved there from `Evm/Stmt.lean`
    (same definitions, now `Solidity.Stmt.asserts`), and the module's
    `MSrc.mvalT_noPanic` is private, since `Calculus/SoundMem.lean` states
    the same lemma above it.
97. *Proposed (W7 `w7-route`), the lead's call:* decision 77's
    conditional form is `reachable_fits` (`Typing/Fits.lean`) under
    `FixedFits C`: every fixed-size array type a path reaches from a root
    has at most `2^256` elements (stated with `tyAtSegs`, so no new
    recursion over `structDef`; `Huge` fails it, `huge_not_fixedFits`).
    The third run invariant `fitsInv` is on the erasure as `canonInv` and
    `tightInv` are, but carries only what the types do not give
    (`SVal.bnd`: live and recycled slots of a dynamic array below
    `2^256`, every mapping key in its key type's range; aliases bound
    along keys in range, `LTy.KeysFit`), and its storage leaves read the
    typed step (`TRun.*`) through `Semantics/StorageErase.lean`, so the
    reference's keys come from `PrimTy.key` of a typed index
    (`Loc.resolveT_keysFit`) and a push's bound from `Storage.full`
    (`Storage.len_of_full`); words in range and fixed lengths come from the
    typed state at the end (`SVal.erase_fits`).  `reachable_iff_fits`
    states the characterisation with no premise on the storage;
    `reachable_iff` keeps its `FitsStorage` form for a contract that fails
    `FixedFits`.
98. *Proposed (W7 `w7-route`), the lead's call:* `no_hidden_invariant`'s
    step premise reads the typed state: `CanonStorage C σ.erase.storage →
    prog.run σ = .ok o → P σ.erase.storage → P o.st.erase.storage`, with
    no `RunWT` or heap `Canon` on the erasure (both hold of every typed
    state, `State.erase_wt`, `State.erase_canonHeap`).
99. *Proposed (W7, `w7-closer`), the lead's call:* the reduction's atoms keep a second constructor for
    names (`Atom.name`) while `NFml.toL` reads erased leaves; it goes with
    `NFml`.  A scoped reduction is printed by positions (`pos(2)`), not by
    the binders' names: `LFml` carries no names, and the printers
    (`KeyNotation`'s delaborator, `LTerm.fmt`) have no context to read
    them from.  Printing the names would take the leaf's context to the
    printer (`Delab.withTwins`-style), not a change to the terms.
100. *Proposed (W7, `w7-closer`), the lead's call:* the closer
    on a scoped reduction runs with no layout (`LFml.closeS`), and "its
    layout (`LayoutOk`) from the typed state" (decision 81) is withdrawn:
    `Valid φ` reads every typed state, and a typed storage is not
    canonical (`SVal.map`'s default is any value of its type, its entries
    may repeat a key), so the typed state does not give `LayoutOk`;
    decision 75 ties canonicity to the *reachable* typed states, which
    `Valid` does not restrict to.  A leaf with a `wt(storage)` premise
    could give the layout as `NFmlDerive` does on the erasure (`topWt`,
    `LayoutOk` from `holds σ (.defined wt)`); not done, since the scoped
    `sol_decide`'s leaves (`Examples/Tactics/Decide`) have none, and the
    TestSuite's go through `sol_prove`'s erased closer.
101. *Proposed (W7 `w7-rewrites`), the
    lead's call (decision 93 revisited):* past the program a chain's
    `~[sequentialToParallel]~>` merges the scoped line where that gives the
    line written (the spine's merge, `Fml.mergeRun`, or one over a state
    write, `FmlRw.stateMerge`), behind `set_option sol_chain.scopedPast
    true`, **off by default**; every other rewrite past the program, and a
    line written `_`, stays on the erasure (`Fml.ViaE`).  Measured and
    tried: on, it costs 0.44 s on `Examples/ChainRewrites`' content (8.38
    against 7.94 s, 5.5%), for no line the erasure does not reach; the
    strategy's line past a declaration keeps a hidden binder `bind` between
    the two updates, which no scoped merge crosses, so most chains fall back
    anyway (`ageWriteReadValue`); the scoped `simplifyUpdate` keeps the
    hidden binders of the locals it drops, and today's closer on that
    line's erasure fails (`sol_close`, "simp made no progress", tried on
    `ChainNotation`'s `headline_valid`), so a chain gone scoped past the
    program could not be closed as today; a law's line reads the same on
    the erasure.  `~~>` past the program stays `Fml.LeadsE`, and
    `sol_chain?` writes `set_option sol_chain.scopedPast false in` in the
    chain for it when the option is on.  To turn it on: a scoped
    `simplifyUpdate` dropping unread locals with their binders (the
    formula strengthened out of the local's scope), a merge across a
    hidden binder (`bind x ({x := e} φ) ⇝ {x :=decl e} φ` where `e` does
    not read `x`), then the laws.
102. *Proposed (W7 `w7-rewrites`), the lead's call:* the rewrites
    while the program is open (W6's §3⁗ and this lane's additions, 26
    examples) move to their own module, `Examples/ChainRewritesOpen.lean`,
    so that the W6 gate row `Examples/ChainRewrites` times the content it
    was baselined on (plus decision 49's four examples, restored) and the
    new section has a row of its own; no pin changed by the move.
103. *Proposed (W7 `w7-rewrites`), the lead's call:* decision
    49's fourth example (the check's trace) ends at `concrete`, one link
    short of master's: master's last link, `simplifyUpdate`, drops the
    capture `se1` with the revert still to run, and on the scoped line
    `se1` is still in the reverting branch's scope until the revert runs
    (the line's frames drop it), so it is an unread local in scope, which
    the scoped `simplifyUpdate` keeps (decision 87).  The dropped capture
    is a separate example past the program, on the erasure.
104. *Proposed (W7 `w7-rewrites`, review), the lead's call:*
    decision 92's exemption from G0 condition 1 (`match` on the indexed
    families, since they run once a link) extends to the walks this lane
    added to `Calculus/RewriteScoped.lean`: `Fml.lawAlongS`,
    `Fml.lawFiresS`, `Fml.lawAtom`, `Fml.lawAtomFires`, `Fml.stepIn`,
    `Fml.atPath`, `Tm.litPV`, `Tm.litPVFires`, `Fml.litPVAlong`,
    `Fml.litPVFires`, `Fml.applyOnPVTop` (named in its module docstring).
    It does not extend to what `sol_upd` and `sol_merge` run on a whole
    leaf: `Upd.unsetAt`, `Upd.redecl` and `Upd.shadow` are recursors with
    `match` twins and link theorems (`Upd.shadow_eq_shadowM`, …), the
    declaration's `Idx` read by `Idx.casesOn` with no cast
    (`Upd.declAt`).
105. *Proposed (W7 `w7-rewrites`, review), the lead's call:*
    while the program is open, `~[applyOnRigidBox]~>` is
    `FmlRw.applyOnRigid` (under the box any update, under the diamond or
    `m` one that cannot halt), which is how the erasure reads the same
    link (`NFml.applyOnRigidBoxTop`: `U.total || m = .box`, the example
    "`applyOnRigidBox` too applies under `m`" in `Examples/ChainRewrites`)
    and how KeY's `applyOnRigidFormula` applies (its updates cannot
    halt); refusing it off the box would make the open and the closed
    reading of one link disagree.  `~[applyStorageBox]~>` is the box's
    only and asks an update of the storage and locals
    (`FmlRw.applyStorageBox`, `Upd.stOnly`); both refusals pinned under
    the diamond in `Examples/ChainRewritesOpen.lean`.  It is wider than
    the erasure's `NFml.applyStorageBoxTop`, which asks a lone
    `{storage := s}`: on `[{x := 1 ‖ storage := s}] φ` the link applies
    while the program is open and is refused past it (final review; the
    scoped form kept, since narrowing it loses a sound step).

**Lead, 2026-10-11:** proposals 95–105 are approved. The refactor is
complete on `intrinsic` with M6c done with IR (decision 7). Open for the
user: decision 11 (`Surface.Stmt`), the merge into `master`, and the SolKey
reader branch (side-projects `intrinsic`), whose require goes back to
`../../../solidity-lean` at that merge.

**User, 2026-10-11, decision 11:** "you can remove it". The untyped
`Surface.Stmt` goes, with `Surface.Prog` and the formula as written
(`Surface.Fml`): the elaborator emits the scoped syntax directly, the
printers print it, and `resolve`/`erase` to the surface go (W8).

## M6c

The closer on `Fml C Γ`, in W6's lanes (each with its gate table and
review fixes at `b8565d23`).  Every wave **partial**, every gate passed
(timings within 1.2×; the final gate above); no pin moved but those named;
no `sorry`, `axiom` or `maxHeartbeats` added.

- **6a part 1** (`DecideSyn`, `DecideComplete`): `sol_decide` on a scoped
  leaf reads its parameters at their types (`Typed`,
  `LFml.valid_alls_of_cons`); two examples closed that the erased leaf
  could not (`parameterReturns`, `parameterInRange`).  Atoms stay
  name-keyed `LFml` (decision 78; 79–80).
- **6a part 2** (`NFmlClose`): the scoped `sol_close`, `sol_close_mt`,
  `sol_spec_close` keep a leaf's parameters as quantifiers at their types
  (decision 82; three `CloseTests` examples closed); its `simp` set stays
  the untyped interpreter's.  `Closer` moved to 6b (decision 81) and is
  not ported.
- **6b** (`Decide.lean`): `Calculus/DecideScoped.lean`, the reduction by
  position (`Fml.reduceS`, `Fml.inLS`, `Valid.of_reduceS`), sound through
  its commutation with the erased one (`Fml.toLS_eq`), so `Decide.lean`'s
  proofs stay on `NFml` (decision 83; 84–85, two fragment pins;
  superseded by W7 `w7-closer`: `Fml.toLS_eq` is gone, `Valid.of_reduceS`
  is proved over the typed state, `Fml.toLSM_sound`).  The
  kernel-evaluated functions are recursors with `match` twins (G0's
  conditions 1 and 2).
- **6c `w6c-upd`** (`NFmlUpdateRules`, `StateParts`): scoped ports beside
  them, `Calculus/UpdRuleScoped.lean` (`UpdRuleS`: `sequentialToParallel`,
  `simplifyUpdate` under the box, `applySkip`, `applyOnRigid`) and
  `Calculus/StatePartsScoped.lean` (`Upd.graftF`, `Upd.mergeSt?`,
  `Upd.mergeMem?`), sound one way; no consumer yet (decisions 86–88).
- **6c `w6c-rw`** (`Rewrite`, `TheoryRewrite`, `NFmlDerive`, `NFmlLogic`):
  `sol_prove`'s leaves on `⊢` are scoped sequents (`Seq.SLeaf`,
  `Proves.close_leaf`), and the scoped `Proves` has the `rewrite` rule
  (`Calculus/SeqRewrite.lean`) while a modality is open; one pin moved
  (`Benchmark/Mapping`'s `remove_spec`, decision 89; 90–91).
- **6c `w6c-chain`** (`ChainRewrites`, `ChainBranches`, `RewriteChains`):
  rewrite links on the scoped line while the program is open
  (`Calculus/RewriteScoped.lean`, `Examples/ChainRewrites` §3⁗), so a step
  and a rewrite are links of one chain again; past the program the chains
  stay on `NFml` (`Fml.ViaE`; decisions 92–94).
- **W7 `w7-route`** (2026-10-11, proposals 95–98): the `⊨` route runs
  the `⊢` walk, its leaves scoped sequents (`evalSolProveValid`; the
  erased route deleted, four pin files re-derived, decision 95); "only an
  `assert` panics" over the typed run (`Semantics/NoPanic.lean`,
  `Prog.run_noPanic`); decision 77's conditional form
  (`Typing/Fits.lean`: `reachable_fits` under `FixedFits`,
  `reachable_iff_fits`, the third run invariant `fitsInv`);
  `no_hidden_invariant`'s step on the typed state; the bare `simp`s of
  `Semantics/Properties.lean`, `Typing/Storage.lean`,
  `Typing/StoragePreservation.lean` and `Typing/Constructibility.lean`
  replaced by the `simp only` lists `simp?` printed (`Semantics/Storage.lean`
  had none).
  **Gates** (2026-10-11, the W6 method: end of work, one fresh worker at
  a time, load 1.5–2.7, the cgroup at 9–16 GB; one run each, two for the
  rows furthest from 1.0, the minimum kept; ratio to the W6 baseline):
  `Derived1` 7.80 s (1.07), `Derived2` 8.91 (1.03), `Derived3` 13.32
  (1.02), `Derived4` 17.92 (1.02), `Derived5` 7.27 (1.05; runs 7.64,
  7.27), `Derived6` 12.26 (1.07; 12.68, 12.26), `Derived7` 54.09 (1.07),
  `Derived8` 27.45 (1.04; 29.00, 27.45), `Derived9` 7.59 (1.06),
  `Derived10` 11.61 (1.05), `Derived11` 3.35 (1.06), `Derived12` 13.66
  (1.04), `Derived13` 6.61 (1.04), `Derived14` 11.34 (1.04); the sum
  203.2 s (1.05; gate 232.3).  `Examples/Tactics/Decide` 35.87 s (0.73;
  W6 final 34.51), `Examples/ProofTree` 10.34 (1.05),
  `Examples/Chains/Storage` 7.75 (1.04), `Examples/ChainRewrites` 7.51
  (1.18 of the baseline, 1.03 of W6's final 7.30, which §3⁗ set; gate
  7.63).  Controls this lane does not reach, the same session:
  `Examples/Benchmark/Syntax` 1.46 s (1.04) and `Solkey/TestSuite` 11.18
  (1.03), so the machine ran 3–4% slower than at W6; the Derived files'
  path (`sol_prove` on `⊢`) is unchanged by the lane (`evalSolProveValid`
  answers only a `Valid` goal).  Dropped: two runs killed when another
  session took the cgroup past 32 GiB (`Derived6`, `Derived10`), and two
  control runs under another lane's build (load 4.9–20).  Every row
  within 1.2×: passed.
- **W7 `w7-rewrites`** (2026-10-09 to 2026-10-11; `UpdRuleScoped`,
  `StatePartsScoped`, `RewriteScoped` given their consumers): `sol_upd` and
  `sol_merge` rewrite the scoped leaf (`Valid.of_updAtSD`,
  `Valid.of_simpUpdsS`; `Closers.lean`), merging past hidden binders
  (`Fml.mergeB`); `simplifyUpdate` drops shadowed writes (`Upd.shadow`,
  `Upd.redecl`, `Upd.simpS`; decision 87's first half, under either
  modality); while the program is open the chain links are scoped for
  the laws in a line's equations (`FmlRw.litEq`, `FmlRw.lawEq`),
  `simplifyUpdate` (`FmlRw.simplifyUpdate`), `sequentialToParallel` under
  a branch (`FmlRw.mergeIn`) and over a storage write, a memory write and
  `ChainRewrites`' locals-then-memory (`FmlRw.stateMerge`,
  `Upd.mergeMemL?`), `applyOnPV` (`FmlRw.applyOnPV`), `applyStorageBox`
  and `applyOnRigidBox` (`FmlRw.applyOnRigid` under the box), `~=>`
  (`openRwSteps`), `~~>` up to three rewrites (`openRwPath`) and `calc`
  steps (`pendingLines` with `Fml.RwBy`); decision 49's four examples
  restored on the scoped line (one ends a link short, proposal 103);
  past the program, scoped merges behind an option, off (proposal 101);
  the open-program examples in `Examples/ChainRewritesOpen.lean`
  (proposal 102).  The reported elaboration failure of
  `dl![m]{ { se1 := false } ((se1 ≐ true → φ) ∧ (se1 ≐ false → ⟨[ revert(); ]⟩ φ)) }`
  was its print: `↑φ` under the capture, which `DelabErase` printed
  ill-typed (fixed at `8052d96d`, and a defined postcondition, `xDefined`,
  at `422e8fe4`); it elaborates, prints and is a chain's line under either
  modality, pinned in `Examples/ChainRewritesOpen.lean`.  Pins moved:
  `Examples/Tactics/UpdateRules` (the rules now rewrite the scoped leaf:
  `copyLocal_merge` keeps `x := 1`, a parameter in scope, decision 87;
  `selfAssign` closes with no lemma, a typed local always holds a value;
  the `applySkip` example replaced, a scoped line keeps a declaration);
  `Examples/ChainRewrites`' `~~>` refusal lists `applyOnPV`.  Gate:
  "W7 `w7-rewrites`" below.  Review fixes (`f4bd70a5`, `6f24cbc4`):
  `UpdRuleS.sequentialToParallel` and `UpdRuleS.simplifyUpdate` back in
  the taclets' `\find`/`\replacewith` shape, the binder-crossing merge
  and the pop absorption separate Lean-only constructors
  (`UpdRuleS.mergeHidden`, `absorbPops`, `trans`; `UpdRuleNameS.top_rule`
  builds from them); `Upd.unsetAt`, `Upd.redecl`, `Upd.shadow` by the
  recursor (proposal 104); `openRwPath` breadth first, bounded
  (`openRwNodes`, heartbeats and runtime errors caught per line), not run
  for a written line with no program, and written out by `sol_chain?` as
  `~[r]~>` links (`openRwFrom`, `Gen.openRws`), so the two `~~>` examples
  replay it (`Examples/ChainRewrites`, `Examples/ChainRewritesOpen`); the
  suggestion pinned in `Examples/Tactics/Chains.lean`, where
  `Examples/ProofTree.lean`'s docstring puts the chains' suggestions (it
  does not import the chain tactics, and importing them would load its
  gated row); `applyStorageBox` box-only (proposal 105);
  `simplifyUpdate`'s absorbing candidate only over an update.
- **W6 lanes beside it**: `w6-canon` tied the canonicity invariant to the
  typed state (decision 75) and found 77 false (`huge_reachable_not_fits`);
  `w6-step` made `Stmt.step` total (decision 76, two replay rows
  re-derived, no pin moved).
- **W7 `w7-closer`** (closer core): the reduction's atoms by position
  (`Atom.pos`, decision 78 implemented), the closer on the scoped
  reduction (`LFml.closeS`, decision 81 implemented with no layout), the
  scoped reduction sound over the typed state (`Calculus/DecideTyped.lean`,
  `Fml.toLSM_sound`, `Valid.of_reduceS`; decision 83's rest; 84 in part
  superseded), the G0 forms kept (recursors with `match` twins and links);
  proposals 99 and 100.  No pin's output moved (the fragment pins
  take the polarity, `Fml.inLS true`; `key{}`'s examples spell
  `Atom.name`); no `sorry`, `axiom` or `maxHeartbeats` added (19, 1, 30).
  Checks: `lean_build` of `Solidity`, `solkeycheck`, `SolidityCorpus` and
  `SolkeyTestSuite` green (322 jobs); `check-orphans` (308 reachable, the
  one orphan the git-excluded `Scratch/W7Dec`), `check-doc-paths`,
  `check-rule-text` OK; the duplicate-name scan as at W6.

  Gate (2026-10-11, at `3ba674c4`; W6's method, the minimum of three runs
  or more; a run whose load rose above 2 while it ran is repeated, the
  machine shared with two other W7 lanes).  The Derived files' path
  (`sol_prove`, the erased closer) reads `Atom.name` where it read a name;
  `Derived7`'s kernel time at `1616405c` and here, by `profiler`, 48.8 s
  and 49.2 s, and its end of work 51.45–51.61 s at `1616405c` and
  51.60 s here, so the CPU column's 2–4% over W6 is the machine's, not
  this lane's.

  | Module | W6 baseline | gate (1.2×) | **W7 `w7-closer`** (runs) | ratio | CPU, baseline → now |
  |---|---|---|---|---|---|
  | `TestSuite/Derived1` | 7.32 s | 8.78 s | **7.53 s** (7.68, 7.53, 7.60) | 1.03 | 8.98 → 9.38 s |
  | `TestSuite/Derived2` | 8.63 s | 10.36 s | **8.89 s** (8.93, 8.89, 8.95) | 1.03 | 10.38 → 10.86 s |
  | `TestSuite/Derived3` | 13.01 s | 15.61 s | **13.18 s** (13.57, 13.33, 13.18) | 1.01 | 14.48 → 14.92 s |
  | `TestSuite/Derived4` | 17.57 s | 21.08 s | **17.78 s** (18.26, 17.98, 17.78) | 1.01 | 19.61 → 20.20 s |
  | `TestSuite/Derived5` | 6.95 s | 8.34 s | **7.11 s** (7.22, 7.14, 7.11) | 1.02 | 8.23 → 8.63 s |
  | `TestSuite/Derived6` | 11.42 s | 13.70 s | **11.71 s** (11.71, 11.72, 11.83) | 1.03 | 13.00 → 13.51 s |
  | `TestSuite/Derived7` | 50.43 s | 60.52 s | **51.60 s** (55.90, 55.75, 51.60, 54.83) | 1.02 | 52.88 → 54.36 s |
  | `TestSuite/Derived8` | 26.38 s | 31.66 s | **26.99 s** (28.39, 28.13, 27.88, 26.99) | 1.02 | 27.50 → 28.51 s |
  | `TestSuite/Derived9` | 7.16 s | 8.59 s | **7.21 s** (7.46, 7.28, 7.21) | 1.01 | 8.62 → 8.94 s |
  | `TestSuite/Derived10` | 11.11 s | 13.33 s | **11.47 s** (12.71, 11.47, 11.50) | 1.03 | 12.75 → 13.34 s |
  | `TestSuite/Derived11` | 3.16 s | 3.79 s | **3.28 s** (3.76, 3.28, 3.32) | 1.04 | 3.36 → 3.69 s |
  | `TestSuite/Derived12` | 13.17 s | 15.80 s | **13.59 s** (20.58†, 13.94, 13.59) | 1.03 | 14.01 → 14.79 s |
  | `TestSuite/Derived13` | 6.36 s | 7.63 s | **6.51 s** (83.81†, 6.68, 6.51) | 1.02 | 6.38 → 6.87 s |
  | `TestSuite/Derived14` | 10.89 s | 13.07 s | **11.08 s** (11.62, 11.19, 11.08) | 1.02 | 11.50 → 11.87 s |
  | Derived1–14, sum | 193.6 s | 232.3 s | **197.9 s** | 1.02 | 211.7 → 219.9 s |
  | `Examples/Tactics/Decide` | 49.14 s | 58.97 s | **36.06 s** (36.67, 36.20, 36.06) | 0.73 | 49.97 → 37.09 s |

  † another session's build ran beside it (load 6.7 and 14–26, the
  cgroup at 31.9 GB); repeated.  **Gate passed**: every row within 1.2×.

- **W7 merge** (2026-10-11): `w7-route`, `w7-closer` and `w7-rewrites`
  merged into `intrinsic` in that order, conflicts only in this record
  (the lanes' proposals renumbered 95–98, 99–100 and 101–105, their
  references in the Lean sources and `docs/lean-key-rule-map.md` with
  them).  The deletion step: no module, and neither `NFml`, `Fml.erase`
  nor `Semantics/Erased.lean`, is unread (the list below).  What nothing
  read went: `open NFml.Proves` in 51 files whose tactics are the scoped
  macros (`Calculus/WalkSyntax.lean`, `Calculus/RewriteSyntax.lean`, whose
  fallbacks name `NFml.Proves` in full; kept in `Calculus/NFmlLogic.lean`
  and `Examples/Tactics/TermTaclets.lean`, which use its names bare), and
  four lemmas nothing cited (`anonRead_eq_ok`, `SubstAgree.abs_eq`,
  `State.alloc_heapEq`, `State.Keeps.heapEq`); two unused `simp`
  arguments of `Calculus/DecideScoped.lean` too.  Checks: `lean_build`
  with `SolidityCorpus` and `SolkeyTestSuite` among the default targets
  green (325 jobs, no error); `check-orphans` (311 reachable, the orphans
  only the git-excluded scratch modules, since deleted),
  `check-doc-paths`, `check-rule-text` OK; the duplicate-name scan at its
  three known false positives (`as`, `delabFml`, `delabProves`).
  `check-testsuite.sh` stops at its input check: the checkout `../solkey`
  holds another `TestSuite.sol` than the imported AST (sha `4150e0a8…`
  against `2fe50a03…`), a stale checkout, not a change here.  No pin
  moved at the merge.

  **Final W7 gate** (2026-10-11, at the merge; the W6 method: each file
  copied under `Solidity/Scratch/`, one fresh worker at a time through the
  MCP, end of work sampled every 20 ms, the worker killed after the run;
  two runs a row, three for the rows furthest from 1.0, one for the M0
  controls, the minimum kept; load 0.7–1.9, the cgroup at 7.4–13.8 GB.
  The CPU column is left out: this run killed the worker before reading
  the sample, so its CPU counts the idle polling after the work):

  | Module | W6 baseline | gate (1.2×) | **W7 merge** (runs) | ratio |
  |---|---|---|---|---|
  | `TestSuite/Derived1` | 7.32 s | 8.78 s | **7.65 s** (7.81, 7.71, 7.65) | 1.05 |
  | `TestSuite/Derived2` | 8.63 s | 10.36 s | **8.91 s** (9.00, 9.05, 8.91) | 1.03 |
  | `TestSuite/Derived3` | 13.01 s | 15.61 s | **13.36 s** (13.36, 13.47) | 1.03 |
  | `TestSuite/Derived4` | 17.57 s | 21.08 s | **17.87 s** (17.87, 18.10) | 1.02 |
  | `TestSuite/Derived5` | 6.95 s | 8.34 s | **7.20 s** (7.29, 7.24, 7.20) | 1.04 |
  | `TestSuite/Derived6` | 11.42 s | 13.70 s | **11.79 s** (11.80, 11.79) | 1.03 |
  | `TestSuite/Derived7` | 50.43 s | 60.52 s | **51.41 s** (51.41, 51.57) | 1.02 |
  | `TestSuite/Derived8` | 26.38 s | 31.66 s | **26.83 s** (26.83, 26.99) | 1.02 |
  | `TestSuite/Derived9` | 7.16 s | 8.59 s | **7.31 s** (7.50, 7.31) | 1.02 |
  | `TestSuite/Derived10` | 11.11 s | 13.33 s | **11.59 s** (11.79, 11.75, 11.59) | 1.04 |
  | `TestSuite/Derived11` | 3.16 s | 3.79 s | **3.23 s** (3.23, 3.29) | 1.02 |
  | `TestSuite/Derived12` | 13.17 s | 15.80 s | **13.54 s** (13.59, 13.54) | 1.03 |
  | `TestSuite/Derived13` | 6.36 s | 7.63 s | **6.45 s** (6.49, 6.45) | 1.01 |
  | `TestSuite/Derived14` | 10.89 s | 13.07 s | **11.08 s** (11.32, 11.08) | 1.02 |
  | Derived1–14, sum | 193.6 s | 232.3 s | **198.2 s** | 1.02 |
  | `Examples/Tactics/Decide` | 49.14 s | 58.97 s | **37.47 s** (37.47, 37.50) | 0.76 |
  | `Examples/ProofTree` | 9.81 s | 11.77 s | **9.74 s** (9.90, 9.74) | 0.99 |
  | `Examples/Chains/Storage` | 7.45 s | 8.94 s | **7.52 s** (7.57, 7.52) | 1.01 |
  | `Examples/ChainRewrites` (§3⁗ in `ChainRewritesOpen`, proposal 102) | 6.36 s | 7.63 s | **6.86 s** (6.86, 6.87, 6.92) | 1.08 |
  | `Examples/ChainRewritesOpen` (new at W7) | — | — | 3.43 s | — |
  | `TestSuite/Problems` (M0) | 0.81 s | 0.97 s | 0.85 s | 1.05 |
  | `TestSuite/ScopedProblems` (M0) | 1.39 s | 1.67 s | 1.45 s | 1.04 |
  | `Solkey/TestSuite` (M0) | 10.83 s | 13.00 s | 11.03 s | 1.02 |
  | `Examples/Benchmark/Syntax` (M0) | 1.41 s | 1.69 s | 1.48 s | 1.05 |
  | `Evm/Examples` (M0) | 7.75 s | 9.30 s | 7.91 s | 1.02 |
  | `Evm/Correct` (M0) | 1.68 s | 2.02 s | 1.71 s | 1.02 |

  **Gate passed**: every row within 1.2× of its W6 baseline.  The Derived
  files are 1–5% over it, as at each W7 lane (whose controls put the
  machine 2–4% slower than at W6).  `ChainRewrites` is at 1.08, the same
  figure `w7-rewrites` measured: its §3⁗ moved out, and the rest of the
  file is re-read by the open-program search, bounded at `6f24cbc4`.
  `Decide` is at 0.76 (1.04 of the lanes' 36.06 and 35.87 s).  Against
  the M0 limits: `Derived9` 7.31 (limit 8.4), `Derived10` 11.59 (11.2:
  over by 3%, as by 0.4% at W6's final gate; within its W6 gate, 13.33),
  `Derived11` 3.23 (3.4), `Problems` 0.85 (1.44), `Solkey/TestSuite`
  11.03 (12.5), `Benchmark/Syntax` 1.48 (1.44: over by 3%; M0's limit
  sat 0.03 s over the W6 baseline), `ProofTree` 9.74 (12.1),
  `Chains/Storage` 7.52 (9.0), `Evm/Examples` 7.91 (11.4), `Evm/Correct`
  1.71 (30.7).

**`NFml`, `Fml.erase` and `Semantics/Erased.lean` stay**, as decision 7's
documented IR: the decision procedure, the closer's sequent calculus, the
update rules and the chains past the program read the erased formula and
state.  Every reader at the W7 merge, by what it reads (`NFml` or its
namespace, an `NFml*` module it imports, `Fml.erase`, or the erased state
`EState`), and why it stays:
- *where they are defined*: `Update.lean` (`NFml`, `NFml.holds`,
  `NFml.Valid`), `Calculus/Fml.lean` (`Fml.erase`),
  `Semantics/Erased.lean` (`Env`, `EState`, the erased evaluators: what
  the closer's terms read, decision 40), `Semantics/State.lean`
  (`State.erase`).
- *the closer's IR* (decision 7; 83, 91): `Calculus/NFmlLogic.lean`
  (`NFml.Proves`, what a scoped leaf erases to), `Calculus/NFmlDerive.lean`
  (`NFml.Derive`: the closer's walk and its residue),
  `Calculus/Close.lean` (`sol_close`), `Calculus/NFmlUpdateRules.lean`
  (KeY's update simplification on the erasure),
  `Calculus/NFmlQuote.lean` (the quoter), `Calculus/Hyp.lean` (the
  context both sequents share), `Calculus/Closable.lean`,
  `Calculus/CloseErase.lean`, `Calculus/Close.lean`,
  `Calculus/CloseHavoc.lean`, `Calculus/HoldsErase.lean`,
  `Calculus/Proves.lean` (`Proves.close`: a scoped leaf closes by its
  erasure's validity), `Calculus/CallbackSound.lean` (the callback
  modality's leaves), `Calculus/Problem.lean` (`NFml.wt`),
  `Theory/Bridge/Denote.lean` (`eqD`'s reading).
- *the decision procedure and the closers' front ends*:
  `Calculus/Decide.lean` (`NFml.toL`, `NFml.inL`,
  `NFml.valid_iff_reduce`: the erased closers' path, `Derive.onErased` and
  the Derived replays; the scoped reduction reuses its `Sym`/`LFml` and
  reads its terms and elements on the erasure through its lemmas,
  `Tm.toLS_eq`, `Term.toL_eval`, `Surface.UpdElem.toL_sound`,
  `pair_sound`: decision 83 as superseded by W7),
  `Calculus/DecideComplete.lean` (`NFml.valid_iff_reduce`),
  `Calculus/DecideLang.lean`, `Tools/Inspect.lean` (`NFml.inL`),
  `Calculus/Closer.lean`, `Calculus/Closers.lean` (`Derive.onErased`:
  `sol_apply_upd`, `sol_fold_terms`, `sol_close_eval`, the
  `sol_decide_*`/`sol_reduce`/`sol_reads` closers), `Calculus/Derive.lean`
  (`sol_close_unwrap`), `Calculus/ProvesDerive.lean` (a leaf's first line
  erases it, `Proves.close_leaf`), `Calculus/SolSpec.lean`,
  `Frontend/Problems.lean` (`#solkey_derive?`'s search),
  `Calculus/TacticSyntax.lean`, `Calculus/TheoryRewrite.lean` (`sol_rw`
  on `NFml.Proves`).
- *update rules and rewrites on the erasure* (decisions 86–88):
  `Calculus/Rewrite.lean`, `Calculus/RewriteSyntax.lean` and
  `Calculus/WalkSyntax.lean` (the scoped macros' fallbacks to
  `NFml.Proves`), `Calculus/StateParts.lean`, `Calculus/Graft.lean`,
  `Calculus/TermRules.lean`, `Calculus/Literals.lean`.
- *chains past the program* (decisions 92–93; a merge past it is scoped
  under `sol_chain.scopedPast`, off, proposal 101):
  `Calculus/ChainBranches.lean`, `Calculus/ChainRewrites.lean`,
  `Calculus/ChainKit.lean`, `Calculus/Chains.lean`,
  `Calculus/ChainGen.lean`, `Calculus/RewriteChains.lean`,
  `Calculus/RewriteChainGen.lean`, `Calculus/LastLine.lean`,
  `Calculus/TreeData.lean`, `Calculus/ProofTree.lean`,
  `Calculus/DelabErase.lean` (printing an erased line).
- *notation and quoting of formulas with no modality*:
  `Calculus/RuleSyntax.lean` (`dl{}`, `⊨`), `Calculus/SurfaceNotation.lean`,
  `Calculus/SurfaceSpec.lean`, `Calculus/RuleKit.lean`,
  `Calculus/Sequents.lean`, `Calculus/Surface.lean`, `Calculus/Print.lean`,
  `Calculus/Quote.lean`, `Tools/Common.lean`, `Tools/Counterexample.lean`,
  `Calculus/CloseTests.lean` (the closer's tests).
- *the erased state* (`EState`, `State.erase`, `Fml.erase`'s reading;
  decision 40: the typed step erases to it, and the closer's terms read
  it): `Semantics/StateErase.lean`, `Semantics/StepErase.lean`,
  `Calculus/Logic.lean`, `Calculus/SoundKit.lean`,
  `Calculus/SoundArms.lean`, `Calculus/SoundLocal.lean`,
  `Calculus/SoundLoops.lean`, `Calculus/SoundMem.lean`,
  `Calculus/SoundStore.lean`, `Calculus/ProvesSound.lean`,
  `Calculus/UpdateRules.lean`, `Calculus/FunContract.lean`,
  `Calculus/Deploy.lean`, `Calculus/SeqRewrite.lean`,
  `Calculus/RewriteScoped.lean`, `Calculus/StatePartsScoped.lean`,
  `Calculus/UpdRuleScoped.lean`, `Calculus/DecideTyped.lean`,
  `Calculus/Taclet.lean`, `Typing/Soundness.lean`,
  `Typing/TypedRunInv.lean`, `Typing/Reachability.lean`,
  `Typing/Constructibility.lean`, `Typing/Fits.lean` (the run
  invariants, stated on the erasure as `canonInv`, `tightInv`,
  `fitsInv`), `SortCheck/Faithfulness.lean`, `Tools/Taclet.lean`,
  `Counterexamples/PreFixSortAnnotations.lean`.
- *examples and the TestSuite*: `Corpus/Imported.lean` and
  `TestSuite/Problems.lean` (the legacy statements' `NFml.wt` premise);
  `TestSuite/Derived1`, `Derived7`, `Derived12` and
  `Examples/Tactics/LoopsImport` (replays naming
  `NFml.Proves.close_dropWt`, read as `core_leaf_close_wt`, and
  `NFml.valid_iff_reduce`); `Examples/Benchmark/Mapping`,
  `Examples/Benchmark/Purchase`, `Examples/Tactics/Constructors` and
  `Solkey/Constructors` (`NFml.Proves.close`, `NFml.valid_iff_reduce`);
  `Examples/ProofTree` and `Examples/Tactics/Dangling` (the pins of
  `NFml.Derive`'s bounds); `Examples/ChainNotation` (`NFml.Via`),
  `Examples/Tactics/SelectOnSaveConsr` (`NFml.Valid`),
  `Examples/Tactics/TermTaclets` (term taclets on `NFml.Proves`); and,
  importing `Calculus/Close.lean` or `Calculus/NFmlDerive.lean` for
  `sol_close`/`sol_prove` only: `Examples/Benchmark/Coin`, `Examples/Benchmark/Counter`, `Examples/Benchmark/ERC20`, `Examples/Benchmark/EtherWallet`, `Examples/Benchmark/SimpleStorage`, `Examples/Chains/Arithmetic`, `Examples/Chains/CheckedArithmetic`, `Examples/Chains/Memory`, `Examples/Chains/MemoryArrays`, `Examples/Chains/MemoryCoverage`, `Examples/Chains/MemoryDelete`, `Examples/Chains/Payment`, `Examples/Chains/Storage`, `Examples/Chains/StorageArrays`, `Examples/Chains/StorageCoverage`, `Examples/Chains/StorageDelete`, `Examples/Notation`, `Examples/Tactics/ApplySteps`, `Examples/Tactics/Branch`, `Examples/Tactics/CallOperands`, `Examples/Tactics/Callback`, `Examples/Tactics/Calls`, `Examples/Tactics/Checked`, `Examples/Tactics/Contracts`, `Examples/Tactics/CrossDomain`, `Examples/Tactics/LedgerDelete`, `Examples/Tactics/Loops`, `Examples/Tactics/Memory`, `Examples/Tactics/Net`, `Examples/Tactics/Operators`, `Examples/Tactics/Revert`, `Examples/Tactics/Step`, `Examples/Tactics/StorageDelete`, `Examples/Tactics/StorageSuite`, `Examples/Tactics/Symex`, `Examples/Tactics/Tour`, `Examples/Tactics/TryCatch`, `Examples/Tactics/Values`, `Solkey/ScopedFlip`.

Only docstrings name `NFml` in `Calculus/DecideScoped.lean`,
`Calculus/DecideSyn.lean`, `Calculus/RewriteScoped.lean`,
`Calculus/SeqRewrite.lean`, `Calculus/Symex.lean`,
`Examples/ChainRewrites.lean`, `Examples/Tactics/Chains.lean` and
`TestSuite/Suggestions.lean`.

## W8 plan (decision 11)

Decision 11: remove `Surface.Stmt`, `Surface.Prog`, `Surface.Fml`.

### Inventory (branch `intrinsic`)

59 files name `Surface.Stmt`, `Surface.Prog` or `Surface.Fml`. Counting the bridges (`erase`, `resolve`, `eraseS`, `resolveN`, `solc_scoped`, `scopedOf`), 73 files are touched. Grouped by role:

| Role | Files |
|---|---|
| **Definitions** | `Syntax.lean` (`Surface.Stmt`/`Prog`, 16 program-term families, `toStr`, quoters, the elaborator); `Update.lean` (`Surface.Fml`, `NFml.toSurface`, `Surface.X.lower`); `RuleKit` (`Surface.Hole`/`MHole`/`VHole`/`Premise`); `Problem` (`Surface.Problem.*`); `SurfaceSpec` (`specObligation`, `primName`) |
| **Bridges** | `Syntax/Resolve` (erase/resolve); `Calculus/Fml` (`Frames.erase`, `eraseS`); `NotationResolve` (`Fml.resolveN`); `Spec` (`ofLegacy`); `Semantics/StateErase` (`*_erase`); `Evm/Examples` (`scopedOf`); `Corpus/Basic` |
| **Untyped eval of program terms** | `Semantics.lean`, `Agree`, `NoPanicOps`. Only `StateErase` reads these, and only `SortCheck/Faithfulness` reads that. |
| **Frontends** | `Splice` (`sol{}`), `Quote` (`defineCore`), `SurfaceNotation`/`Notation` (`dl!{}`), `SurfaceSpec`/`Spec` (`spec!`), `Problem`, `Deploy`, `Frontend/Import` (`solc_import`, `solc_scoped`), `Frontend/Problems` |
| **Printers** | `RuleSyntax` `pp*` (on Surface Exprs), `RuleKit.ppPremise?`, `DelabErase` (twins → Surface), `Delab`, `DelabLean`, `Print` (`Fml.show` via erase), `NFmlQuote`, `Hyp`, `Sequents`, `Chains` (`erasedQuoted`), `ProofTree` |
| **Tools** | `Tools/Run`, `Tools/DiffTest` |
| **Consumers and pins** | about 35 `Examples/*` files, `Evm/{Examples,Interpreter}`, `Semantics/Erased` pins, `Solkey/*`, `TestSuite/{Problems,ScopedProblems}` |

**The program-term families go**: `Simple`, `SPath`, `Loc`, `MPath`, `MLoc`, `Val`, `Src`, `ARhs`, `MRhs`, `NewLhs`, `MSrc`, `OpLoc`, `CallRet`, `ExtArg`, `ExtCall`, `LoopAnn`, the surface `Arg`, and the holes and `Premise`. Their only other reader is the untyped eval chain, which ends in `Faithfulness`; W8.3 restates `Faithfulness` on scoped paths.

**What stays**: `Surface.Tm`/`MAddr`/`UpdElem`/`Upd` (about 2,250 occurrences in about 40 closer files), `NFml` and `Update.lean`'s symbols. These are the closer's IR (decision 7). Renaming that namespace is a separate, optional follow-up.

### Waves

| Wave | Mode | Content |
|---|---|---|
| **W8.1** | `on_main` | The elaborator moves to `Syntax/Elab.lean` (above `Scoped`) and emits `Prog C Γ Γ'`. Wrappers that erase keep every consumer unchanged. `sol{}` picks erased or scoped by its expected type. |
| **W8.2** | 3 lanes | `printers`: new `PrintStmt.lean`, `Delab`, `Print`. `obligations`: `solc_import`, `solc_problems`, `spec!`, `Problem`. `reader-tools`: `dl!{}`, `Chains`, `Tools/Run`, `Corpus/Basic`. |
| **W8.3** | 3 lanes | Examples, `Evm` and `Faithfulness` move to scoped, split by file. |
| **W8.4** | `on_main` | Delete Surface and resolve/erase across the low modules. |
| **W8.5** | lanes | Timing gate (the only Lean agent), docs, read-only review. |

Every wave leaves the build green, for two reasons:
- **Adding comes before deleting.** The scoped API is added beside the Surface one, and the Surface one goes only in W8.4.
- **Old and new can coexist.** `sol{}` and `dl!{}` take the legacy path only when the expected type is a Surface type, so each file migrates on its own.

The lanes' files are disjoint, and there are at most three Lean agents at once.

### Keeping solc's evaluation order, captures and fresh names

W8.1 changes only the constructors the elaborator emits. These RawStmt-level passes stay untouched:
- `freshenBlocks`, `lowerLoops`, `lowerReturns`, `wrapMods`, `renameStmts`, `orderNamed`;
- `hoist`, `captureExpr`, `freshCapture` and their numbering;
- the narrow and cast captures, and the `ElabScope.inlined` ranges.

`hoist` already returns the *raw* residual. So a statement's captures are emitted first, and its values are typed afterwards, in the context those captures leave. No typed value crosses an emission.

How the typing works:
- Names resolve with `NCtx.find`, so resolve's error texts survive.
- A block is `Σ Γ', Prog C Γ Γ'`, appended with a decided `Ctx` equality and a cast.
- Branches, loops and try blocks are nested blocks.
- A call builds `Args` in the caller's context, then the frame (which the elaborator already switches to), then `CallRet.val`/`rets`/`none`/`mem` directly. Resolve used to move a memory return into the frame; now it is built there.

**Differential check.** Before W8.1, a scratch module (not committed) dumps the old elaborator's `toStr` and a quote hash for all 449 imported functions and the TestSuite programs. After W8.1, the erasing wrappers must reproduce that dump byte for byte, and every `sol{}` pin must still hold.

### Keeping the pins' text

`PrintStmt` builds exactly the syntax that today's `ppStmt`/`ppExpr`/`ppPremise?` builds from the erasure, reusing their builders.

How names are found:
- Names come from the binders: `declLocal x`, `Args`, `Binders`, `CodeBinder`, `Upd.decl`, `Fml.all`/`bind`, `Premise.bind`.
- A position indexes a name stack.
- A schema variable prints as its user name, also under `.there`/`up`, as DelabErase's twin rules do today.
- Pops, captures and hidden binders print as nothing; a block end prints `}`.
- Terms and updates still print through `Delab.tr` to the IR, which stays.

**Twin check.** While both printers exist, the option `pp.sol.twinCheck` prints both ways over the pin files and errors on any difference. No `#guard_msgs` may move.

Pins that move on purpose (each lane lists them):
- type suffixes: `: Surface.Fml X` becomes `: Fml X []`;
- constructor-tree `rfl` examples, restated in scoped constructors;
- the three hand-built `resolveCheck` guards, replaced by elaboration-error pins.

String pins such as `Surface.Prog.toStr (sol{…}) = "…"` become `Prog.toStr []` with the same strings.

### The 449 imported functions and 437 TestSuite statements

- `solc_import` declares `N.f : Prog N Γp Γ'` directly: one hash-consed literal each, checked by the kernel.
- `solc_scoped` becomes a check that every program is there, and keeps its info pin.
- `solc_problems` states `N.f.problem : Fml N []` directly. The 437 legacy statements and the erase guard go.
- The one-table declaration stays (0.4 s against 3.4 s).
- `Report.lean`'s counts are unchanged, and `Derived1–14` are not edited: they already state `⊢ N.f.problem` at the scoped type.

### Speed risk (AGENTS.md warning)

Each place below needs a timing gate: within 1.2× of the M0 baseline.

Things that could get slower:
- **The import absorbs the scoped check.** This partly undoes the module split made for timing (`solc_scoped`, `ScopedProblems`): the scoped check "costs about what the import's own does". The total stays about the same, because the Surface literal's check goes. In the spike, a scoped literal costs the kernel 0.8 ms against 0.15 ms, about +0.3 s over 449 literals in imports that never ran `solc_scoped`. If `Solkey/TestSuite` (11.18 s) goes past 1.2× its limit, `N.f` is declared from `TestSuiteScoped` again.
- **`sol{}` quotes scoped DAGs**, 1.34–1.96× larger. The risk is `Benchmark/Syntax`, which is already 3% over its limit (1.48 s against 1.44 s).
- **The printers whnf scoped Exprs**, which can cost more than walking the erasure; the `Delab.tr` pass over the program goes, which offsets some of it. Watch `Examples/ProofTree` (9.8 s) and `Examples/Tactics/Print`.

Things that get faster:
- resolve leaves the elaborator (0.045 ms per block, negligible).
- `decide +kernel` no longer evaluates resolve, in the corpus (`corpus_decide`), `Evm/Examples` and the `Tools/Run` checks.
- The legacy statements and the guard (`solc_scoped_problems`) go.

The elaboration logic is unchanged but for its output constructors, so it should be neutral. W8.5 re-times all of this against the gate table.

### Not in scope

- **The SolKey reader** (side-projects) matches on `Surface.*` after `Delab.tr`. Its port is a later task. Its require stays at the tag `w8-pre-delete` until then, and these waves do not touch it.
  *Superseded by the W8 reader port record: ported; the require was a path to this worktree, not the tag.*
- **Docstrings** that still call the Surface side "as written" are fixed in W8.5.

### W8.1 record (2026-10-11, `30611d7c`)

The elaborator is `Syntax/Elab.lean` (between `Syntax/Resolve.lean` and
`Syntax/Quote.lean`; `Syntax/Splice.lean` now imports `Quote`, whose pins
moved to `Splice`) and emits the scoped syntax.  The raw passes moved
verbatim; `synth`/`check`/`checkPath`/`checkMPath`/`elabMRhs`/`elabPush`/
`litAt` take an `NCtx` and return `TExpr C Γ.ctx`, `Val C Γ.ctx p`, … (a
local by `NCtx.find`).  What the step had to choose:

- **The elaborator's locals are newest first.** `declare` conses where it
  used `setBy` (which appended), and a call's frame is its return variables
  then its parameters, each newest first, so `ECtx.toNCtx` of the state is
  the context the next statement is read in.  Every other reader of an
  `ECtx` looks a name up; none reads its order.
- **A statement is typed where it is elaborated** (`SStmt`: its named
  context, the context it leaves, the statement) and a block is the
  statements chained (`SProg.chain`): each placed where the one before
  leaves, as it is when the names and types agree, else weakened by the
  thinning by names (`NCtx.thinInto`, `Stmt.wk`).  Two places need it: a
  flat block (`{ … }`, `unchecked`, a modifier's `_;`, a lowered loop's
  flags), whose locals the elaborator closes (`elabBranch`) but the scoped
  program keeps until its scope ends, as `resolve` kept them; and a memory
  return's variable, which the call leaves in its caller's context and the
  elaborator never names.  A mismatch is an internal error.  Within one
  statement, a value typed before a capture is weakened past it
  (`afterCapture`: the ternary's branches, `elabOpTarget`'s base,
  `elabIncTarget`'s, a send's operands).
- **A call** builds `Args` in the caller's context, the frame from its
  return variables and parameters, `CallRet.val`/`rets`/`none`/`mem` (a
  memory return in the frame, no `declMem` at the body's head), the
  separation check on `Args` (`Args.separated`).  `uint y = f(a);` reads the
  call where `y` is declared, its arguments where it is not (`resNew`,
  arguments weakened past `y`).
- **Entry points**: `elabProgS`, `elabProgAtS` (`.go`, `.goWt`, a block
  appended per statement with `Blk.append`), `ctorProgS`; `elabProg`,
  `elabProgAt`, `elabProgAt.go`, `ctorProg`, `elabStmt`, `elabStmts` erase
  them (`Prog.erase`).  No scoped path runs `Prog.resolveCheck`.
  `sol[C]{ … }` (now a `term_elab`, `solBracket`) splices the erased block
  where a list (`Surface.Prog C`) or nothing is expected, the scoped one
  (`Prog.quoteShared`) anywhere else.  `Prog.define` declares a scoped
  block; `Prog.defineCore` is `resolve` then `Prog.define`.
- **Callers**: `Calculus/SurfaceNotation.lean`'s `scopeHints` and
  `elabCompare` call `synth`/`check` at `ECtx.toNCtx` and erase; `Import`
  imports `Splice`.  No other consumer changed.

**Checks.**  The baseline dump (`Solidity/Scratch/ElabDump.lean`, not
committed: for each of the 465 programs of the seven imports — the
TestSuite, ScopedFlip, Counter, EtherWallet, CtorGap, InitGap and Loops —
`Surface.Prog.toStr`, the hash of its quoted constant and the hash of its
program resolved and quoted scoped; the six rows left out, with their
reasons; the three tables of scoped obligations) is byte for byte the same
through the wrappers.  `resolve` reads a call returning nothing whose body begins
`T memory m;` as a memory return; the scoped elaborator does not, and no
imported program has such a call (a scan of the seven imports: none).  New
pins (`Syntax/Splice.lean`): `sol{ … }` at `Prog C [] _` is
`rfl`-equal to `tour` and a block of calls resolved (`tourCore`,
`callsCore`), and prints as `Prog.show`.  No other pin moved.  The full
build (with `SolidityCorpus` and `SolkeyTestSuite`) is green, `dups.py`
(the three known), `check-orphans` (the scratch modules only),
`check-doc-paths`, `check-rule-text` pass.

**Timing** (the end-of-work method, `W6` gate rows; the base is this
worktree at `65d93a85` restored from the artifact cache, timed in the
same session; load 0.3–1.2, cgroup 7.3–7.5 GB):

| Module | base (`65d93a85`) | W8.1 | ratio | CPU, base → W8.1 | gate |
|---|---|---|---|---|---|
| `Examples/Benchmark/Syntax` | 1.44 s (1.44, 1.46, 1.48) | 1.47 s (1.48, 1.47, 1.48) | 1.02 | 1.68 → 1.68 s | 1.69 s (W6 1.2×); M0 raw 1.44 s, already crossed at the base |
| `Solkey/TestSuite` | 11.19 s (11.23, 11.19) | 11.02 s (11.02, 11.06, 11.02) | 0.98 | 11.50 → 11.31 s | 12.5 s (M0) |
| `Examples/Tactics/Calls` | 64.60 s (64.77, 64.60) | 64.49 s (64.49, 64.91) | 1.00 | 65.26 → 65.20 s | no row; 1.2× of the base |

Every row within its gate.  `Solkey/TestSuite` is 2% faster: its import
no longer runs `resolve`'s check on every statement.

### W8.2 `printers` record (2026-10-11)

`Calculus/PrintStmt.lean` (above `Calculus/DelabErase.lean`) prints the
scoped syntax from its `Expr`: `ppStmtS`, `ppProgS`, `ppBlockS`, `ppExprS`,
`ppPremiseS`, `ppFmlS`, each building the syntax `RuleSyntax.lean`'s
`ppStmt`/`ppExpr`/`ppProg?`/`ppTupleCall?`/`ppMemCall?`/`ppRetTarget?`/`ppFml`
and `RuleKit`'s `ppPremise?` build from the erasure, with their builders.  No
statement, block, premise or formula is erased; terms and updates still go
through `Delab.tr` (the closer's IR).  The name-stack walker is its API
(`idxName`, `SPiece`, `progPiecesS`, `framePiecesS`, `updShape`,
`withPrinter`), for the SolKey reader's port.  Switched to it:
`Calculus/Delab.lean` (taclets, `blockEmpty`, premises, formulas, sequents
by `hypsPartsS`), `Calculus/DelabLean.lean` (`tacletLine?`),
`Calculus/Print.lean` (`showStmts` of `Prog.quoteShared`, no
`Stmt.erase`/`Frames.erase`), `Calculus/ProofTree.lean` (`condOf?` on the
scoped `Stmt.ite`, names by `hypsNamesS`).  Each keeps its printing through
the erasure (`…Legacy`, `condOfLegacy?`), which the option
`pp.sol.twinCheck` runs beside it: a difference is an error, thrown so that
it shows in the printed text too (a message's expressions are printed
lazily, where a logged error is lost).  What the step had to choose
(proposals 106 to 110, `printers`):

- **106**: a taclet's labels are read from the scoped head through
  `labelHead` (`Stmt.ite` is `Surface.Stmt.ite` for
  `Taclet.labelledBy`, which `RuleKit` keeps until W8.4).
- **107**: `functionCallArgCapture`'s two calls still print as the terms
  of their erasure's twins (`‹Surface.Stmt.call f args hsep ret body›`,
  pinned in `Examples/Tools.lean`); its capture `T se = v` is built by
  hand.  W8.4 moves that pin when `Surface.Stmt` goes.
- **108**: a memory call is grouped with the binding after it only for
  `CallRet.mem` (the erasure also grouped a call returning nothing whose
  body begins `T memory m;`, which no elaborated program has, W8.1).
- **109**: a tuple call none of whose returns is assigned prints as the
  declarations `(uint a, uint b) = f(x);` when a later statement prints a
  return's name (the erasure searched the later statements' terms for
  it); an `↔` is two implications whose formulas are the same terms at the
  same names (the erasure compared the erased formulas).
- **110**: where the erasure printed nothing or an escape, this printer may
  print: a `Binders` variable in a premise read outside a rule (the
  erasure has no twin for it there), a closed call whose arguments are not
  separated (printed with its arguments; the erasure's `f()`; the
  elaborator writes none).  Differences of this kind are the twin check's
  only expected reports; none occurs in the pinned files.

**Checks.**  The twin check over copies of `Examples/ProofTree.lean`,
`Examples/Tactics/{Print,Symex,Step,ProofTree,Loops,Chains,Sequents,Surface}.lean`
and `Examples/Tools.lean` (its `#taclet` pins), and over every constructor
of `Taclet` and `LeanTaclet` (168, both printers compared directly): no
difference, no `#guard_msgs` moved, no pin changed.  A control (a
`Binders` variable outside a rule, proposal 110) shows a difference as a
failed print.  The default build (294 jobs), `SolidityCorpus` and
`TestSuite/Suggestions` are green; `check-orphans` (the scratch modules
only), `check-doc-paths` pass.

**Timing** (the end-of-work method; base `624c492a` restored in the same
worktree, timed in the same session, load 1.9–2.3, cgroup 9–10 GB; a first
version, which erased every update and term `viewF` looked through, ran
`Examples/ProofTree` at 11.4–13.8 s and was replaced by `updShape` and lazy
term erasure in `eqDPartsS`):

| Module | base | W8.2 `printers` | ratio | gate |
|---|---|---|---|---|
| `Examples/ProofTree` | 10.04 s (10.85, 10.04) | 9.91 s (10.10, 9.91) | 0.99 | 11.77 s (M0 1.2×) |
| `Examples/Tactics/Print` | 3.93 s (4.11, 3.93) | 3.71 s (3.74, 3.71) | 0.94 | no row; 1.2× of the base |

**Left for W8.4**: delete the `…Legacy` printers, `withErased`,
`hypsParts`, `condOfLegacy?` and `pp.sol.twinCheck` with the erasure;
`Calculus/Callback.lean`'s `CallbackTaclet` and `ProvesC` delaborators and
`Calculus/Sequents.lean` still read the erasure (`Delab.tr`, `hypsParts`;
not this lane's files), and `Chains`' `withErasedPosts`; the pin of
proposal 107; `Calculus/Print.lean`'s examples compare against
`Fml.eraseS` (`legacyShow`).

### W8.2 lane `obligations` record (2026-10-11)

The imported programs and every obligation are scoped; nothing in the
lane's files reads `Surface.Prog` or `Surface.Fml` but the closer's
`Surface.specObligation` (below).

- **`solc_import`** declares `N.f : Prog N Γp Γ'` (`Γp` the parameters,
  newest first) from `elabProgAtS.go`, one `Prog.quoteShared` literal each
  (`Prog.define`), and the constructor's the same way.  `solc_scoped N` is
  a check that every elaborated row is a scoped program of `N` (its info
  text kept).  The differential check against W8.1's baseline dump
  (`elabdump_base.keep.txt`): all 465 programs of the seven imports are
  byte for byte the resolved-and-quoted programs of the baseline (the
  hash of the value) and print the same text (`Prog.toStr`).
- **`obligation`** (`Frontend/Problems.lean`) writes `N.f.problem : Fml N
  []` on `N.f`: the `∀`s (the first parameter outermost), `Fml.wt` or
  `Problem.deployUpd`, the modality, as constructors (what
  `Problem.fml`/`ctorFml` compute, so `Symex.paramCount` reads the
  binders).  `solc_problems N` declares each, compiled;
  `solc_scoped_problems N [decl]` the one table `N.problems` (its pin
  kept).  The legacy statements, `legacyProblem`, `legacyStatement`, the
  erase guard, `scopedStatement?` and `Surface.Problem.*` are gone;
  `#solkey_problem`/`#solkey_scan` read `N.f.problem`, or the statement
  `obligation` writes where none is declared (`statement?`; the two
  TestSuite pins in `TestSuite/Problems.lean`), `#solkey_derive?` and
  `#solkey_obligations` the scoped `⊢` only.
- **`Calculus/Problem.lean`** holds the scoped `paramsN`, `Fml.wt`,
  `Problem.fml`, `deployUpd`, `ctorFml`, `ctor` (the call elaborated in
  the parameters' context, `elabStmtsP` placed by `SProg.chain`), `parts`
  and `text` (on `Fml C []`; `problem[C]{constructor}` is the scoped
  one).  `Calculus/Spec.lean` lost `Problem.resolve`/`ofLegacy`;
  `Calculus/Deploy.lean` its erasing `Problem.text`.
- **`specObligation`** (scoped) is built from `specPieces`, whose call is
  now the scoped `SProg`: the clauses by `NFml.resolveN` (local, the
  clauses of `Fml.resolveN` with no program), the snapshots by
  `Upd.resolveN`, the call placed past them by `SProg.chain` (`specModal`).
  A scratch comparison (`Fml.quote`) against the old route
  (`Fml.resolveN` of `Surface.specObligation`) over every function of the
  eleven specified example contracts: identical.  `Surface.specObligation`
  (and `spec!{f}` outside the scoped switch) stays for the examples W8.3
  moves; it erases the scoped call (`specParts`).

Proposed decisions:

- **111 (`obligations`).**  The scoped `specObligation` stays in
  `Calculus/Spec.lean`, not `Calculus/SurfaceSpec.lean` as the plan put
  it: it needs `Calculus/NotationResolve.lean` (`Upd.resolveN`,
  `Fml.closeN`), whose import would put `NFmlDerive` (which imports
  `SurfaceSpec`) behind the strategy (`Step`).  `Calculus/Problem.lean`
  imports `NotationResolve` and `Calculus/Quote.lean`: every module that
  imports it already did.
- **112 (`obligations`).**  The imported programs are not compiled: compiling
  the 449 scoped literals cost 5.9 s of the TestSuite import (LCNF mono
  3.7 s, IR 1.8 s; profiled), 17.6 s against 11.0 s, past its gate.  So an
  obligation's entry holds the program's value (the literal `N.f`
  declares), as the W3 table did, and compiled code evaluates it there
  (`sol_prove`, `#solkey_problem`); `#solc_show N.f` (new) prints a
  program by evaluating its value, which the LoopsImport pins use in
  place of `#eval … Surface.Prog.show N.f`.  `N.f` is still the kernel's
  check of each program (in `Solkey/TestSuite`, not `TestSuiteScoped`).
- **113 (`obligations`).**  `solc_scoped_problems` drops `main` (there is no
  legacy statement to sit beside): `solc_scoped_problems N [decl]`.

**Pins.**  No info or error text moved.  Command lines changed under
unchanged pins: `solc_scoped_problems … main [decl]` → `… [decl]`
(`TestSuite/ScopedProblems`, `Solkey/ScopedFlip`, `Solkey/Constructors`,
`Examples/Tactics/LoopsImport`); the `solc_problems … legacy` lines removed
(`Solkey/ScopedFlip`'s, an empty pin, `Solkey/Constructors`,
`TestSuite/Problems`, `LoopsImport`); `LoopsImport`'s three
`#eval IO.println (Surface.Prog.show N.f)` are `#solc_show N.f`, same
text.  `Examples/Tactics/Spec`: the `Surface.Problem.ctor` erasure guard
is replaced by a `Problem.text` pin of the deployment's obligation.
`Solkey/Constructors`' `counterDeployCore` is `sol[…]{…}` at
`Prog Solkey.Counter [] []` (it was `Prog.defineCore`).
`TestSuite/Report`'s counts (449 functions, 437 statements) and pins,
`TestSuite/Suggestions`' pins and `Derived1–14` (unedited) check.

**Checks.**  Every touched file and its importers through the Lean
server: the 14 `Derived` modules built one at a time (scratch modules
importing each), `TestSuite/Report`, `TestSuite/Suggestions`,
`Corpus/TestSuite`, `Corpus/Imported`, `Examples/Tactics/{Constructors,
Specs,SolSpec,Spec,LoopsImport}`, the five `Benchmark` contracts with
specifications, `Examples/{Verify,Tools}`, `Tools/{Counterexample,Verify}`.
`check-doc-paths`, `check-orphans` (scratch modules only) pass.

**Timing** (the end-of-work method, min of the runs; base is this lane's
worktree at `624c492a`, same session; load 1.5–2.7, cgroup 9–12 GB):

| Module | base | W8.2 `obligations` | ratio | gate |
|---|---|---|---|---|
| `Solkey/TestSuite` | 10.99 s | 6.74 s (7.48, 6.74, 7.25) | 0.61 | 12.5 s (M0) |
| `Solkey/TestSuiteScoped` | 3.61 s | 0.60 s (0.65, 0.60) | 0.17 | no row |
| `TestSuite/Problems` | 0.89 s | 0.87 s (0.99, 0.88, 0.87) | 0.98 | 0.97 s (1.2× 0.81) |
| `TestSuite/ScopedProblems` | 1.44 s | 1.05 s (1.10, 1.05) | 0.73 | 1.67 s (1.2× 1.39) |
| `TestSuite/Derived10` | 11.64 s | 11.63 s (11.63, 12.47, 14.59) | 1.00 | 13.33 s |

The import is faster: it no longer compiles its programs (the Surface ones
were compiled), and the scoped check moved into it is cheaper than
`TestSuiteScoped`'s resolve-and-quote.  `Derived10`'s runs above its min
had another lane's build running (load 2.7–14.6).

**Left** (other lanes or W8.3/W8.4): `Surface.specObligation`,
`specBody`, `specParts` and the unscoped `spec!{f}` (the examples outside
`open scoped Solidity.Scoped` read them); `docs/testsuite-proofs.md` still
describes `solc_problems … legacy` (not this lane's file).

### W8.2 `reader-tools` record (2026-10-11, branch `w8-w82consumersreadscopedprintersobligationsreader-reader-tools`)

The formula reader, the chains' line matching and the run tools read the
scoped syntax.

- **The reader** (`Calculus/Notation.lean`).  `elabModalProg` elaborates a
  formula's program scoped from the formula's named context: each
  statement by `elabStmtP` from the reader's scope, placed where the one
  before leaves by `SProg.chain`/`Blk.append`, as `elabProgAtS` does, with
  the `taken`/`nextFree` capture numbering and `scopeHints` unchanged; no
  `Prog.resolve`.  The reader's scope is first put in the order of the
  formula's context (`alignScope`: `setBy` appends a quantifier's local,
  which `SProg.chain`'s thinning by names would otherwise refuse), and the
  context the program leaves is named by `Prog.outNames` (`NCtx.named`).
  An atom is read as the closer's formula and resolved by
  `NFml.resolveIn` (`Calculus/NotationResolve.lean`; named apart from the
  `obligations` lane's `NFml.resolveN` in `Calculus/Spec.lean`, which has no
  `hint`: keep one at the merge).  `Fml.resolveN` on `Surface.Fml` stays
  in this lane only because `Calculus/Spec.lean`'s `specObligation` reads
  it here; the `obligations` lane removes that use, so it goes at the
  merge.
- **`dl!{ … }` with a modality is scoped** (`elabDlAuto`, a `term_elab` on
  `dl[C]{ … }` and `dl[C, m]{ … }`, now named `dlAt`/`dlAtM`): `cdl[C]{ … }`,
  its parameters bound by hidden binders (`useAll := false`), when the raw
  formula has a modality and no `Surface.Fml _` is expected
  (an expected metavariable postpones once, then reads scoped); today's
  reading otherwise (`NFml` with no modality).  The sequent forms expand
  to these.  `Calculus/Surface.lean`'s flip now matters only for a
  formula with no modality.  `Calculus/SurfaceNotation.lean`'s examples,
  which need the scoped reader and `Delab`'s printer, moved to
  `Examples/Tactics/DlNotation.lean`.
- **Chains** (`Calculus/Chains.lean`).  `Fml.erasedQuoted` is replaced by
  `Fml.lineKey` (`LineKey`, quoted by `LineKey.quote`): the erasure
  (`Fml.erase`, quoted as the closer's `NFml`) where there is no modality,
  and `LineKey.modal m strs k` where there is one, `strs` the program's and
  the frames' statements as `Prog.toStrs` prints them, a block statement
  flattened (`Prog.keyStrs`, `Frames.keyStrs`: the erasure flattens a
  call's expanded body, and the printed line does).  A written line with a
  modality is read scoped with its parameters open (`elabDlOpen`: no
  closure, so `underAlls` strips the computed line's `∀`s as before), its
  slots normalised to `slotExpr j` (`writtenSlots`); one with none is read
  as today (`elabDlN`, the closer's formula; proposal 114).
  `erasedSlot?`, `toWrittenSlots`, `underAlls` no longer name
  `Surface.Fml`.  Every pin in `Examples/Chains/*`, `ChainRewrites*`,
  `ChainNotation` passes unchanged.
- **Tools and corpus.**  `Tools/Run.lean`: scoped `Prog.runT`,
  `Prog.localAfterT`, `Contract.deployRunS` on `Prog C [] Γ'` (the
  `Surface.Prog` versions stay until W8.4); `#run`/`#deploy` elaborate
  scoped (`elabProgS`, `ctorProgS`), no `resolve`; `callProg` returns a
  `Blk C []`, and `Tools/DiffTest.lean`'s `runOnce` takes `Prog C [] Γ'`.
  `Corpus/Basic.lean`: `Diamond`, `outcome`, `runOk`, `diamond_of_runOk`
  take `{Γ'} (P : Prog C [] Γ')`; the generated `Corpus/Solc*.lean` are
  unchanged (`sol[C]{ … }` reads scoped at that expected type), and
  `corpus_decide` evaluates no `resolve`.
- **Not done: `Calculus/Hyp.lean`, `Calculus/Sequents.lean`.**  The
  sequent check (`show_sequent`) compares the goal's `Delab.tr` erasure
  (`Surface.Fml`, the printers lane's) with the line read as today's
  (`readSequent` calls the legacy `elabDlAt` by name, so it is unchanged).
  Its scoped cases (`Hyp.pre`/`Hyp.upd` take the closer's `NFml` and
  `Surface.Upd`, so a scoped `Fml.imp`/`Fml.upd` has no well-typed entry)
  belong with the goal side's printer: W8.4, after the printers lane.

**Proposals.**

- *114 (`reader-tools`):* a chain's written line with no modality is read as
  today (`elabDlN`, terms by name), not scoped.  A line past the program
  drops the `where` clause of a memory local it no longer writes
  (`{ mv1 := read(memory, carol.account) } …` in
  `Examples/Chains/MemoryCoverage.lean`), which the scoped reader would
  read as a `uint` parameter and refuse; the closer's formula, which past
  the program is what the rewrites read, is unchanged.  The no-modality
  reading (`dl!{ … }` as `NFml`) outlives W8.4 anyway.
- *115 (`reader-tools`, withdrawn at review):* `dl!{ … }` outside the flip
  no longer binds its parameters as `cdl!{ … }` does.  `elabDlAuto` reads
  through `elabCdlAt … (useAll := false)`, so `Fml.closeN false` binds every
  parameter by a hidden binder, which prints as nothing, as today's `dl!`
  left it free.  The flip's `cdl!` still binds a value parameter by
  `∀ uint x;`.  Outside the flip no proof reads a modal `dl!` (one that is
  not ascribed `Surface.Fml`), so only pins see the difference, and they
  print as before.

**Dependency on the `printers` lane.**  The scoped printer prints the
hidden binder of a `where` clause as nothing.  The two `where` pins
therefore stay on today's reading in this lane, ascribed
`(dl!{ … } : Surface.Fml StandardExample)`, so their text is unchanged.
`Delab` must print `where T memory x` for a hidden binder of a memory local
that the program assigns without declaring, as `copyDecls` does on the
erasure.  Once that printer lands, the pins switch to `Fml StandardExample []`.

**Pins that moved** (all in `Examples/Tactics/DlNotation.lean`, moved from
`Calculus/SurfaceNotation.lean`, unless said):

| Pin | Change | Reason |
|---|---|---|
| `dl!{ ⟨ uint x = 10; ⟩ x == 10 }` | `: Surface.Fml StandardExample` → `: Fml StandardExample []` | scoped reading |
| `dl!{ { carol := freshId(…) ‖ … } ⟨ carol.age = 5; ⟩ true }` | type suffix only | scoped reading |
| `dl!{ ⟨ carol = alice; carol.age = 1; ⟩ true where Person memory carol }` | none: ascribed `Surface.Fml StandardExample` | the `printers` lane's `where` printer |
| `dl!{ { sp2 := alice.account } ⟨ acc = sp2; ⟩ … where Account memory acc }` | none: ascribed `Surface.Fml StandardExample` | same |
| `dl![m]{ ⟨[ x = 1; ]⟩ x == 1 }` | type suffix only | scoped reading, hidden binder |
| `fun m φ => dl![m]{ ⟨[ x = 1; ]⟩ φ }` | `φ : NFml StandardExample` → `Post StandardExample [.val .uint]` | a scoped hole is a `Post C Γ` |
| `∀ φ, dl!{ ⟨ x = 1; ⟩ φ } = …` (`trace_state`) | `φ✝ : Post …`, `‹↑φ✝›` | same |
| `dl!{ ⟨ x = 1; ⟩ ture }` error | `(φ : Post C)` → `(φ : Post C Γ)` | the scoped reader's message |
| `fun φ => (⊨ φ) ∧ ∀ σ, NFml.holds σ φ` | `State` → `Semantics.State` | the new module sees the scoped `State` too |
| `dl!{ 5 <= selfBalance ⟹ ⟨ to.transfer(5); ⟩ true }` | type suffix only | scoped reading, hidden binder |
| `Examples/Tactics/Surface.lean`: `dl!{ a == 1 → ⟨ uint x = a; ⟩ x == 1 }` outside the flip | type suffix only (`Fml StandardExample []`); the scoped pin below it keeps `∀ uint a;` | a modality reads scoped without the flip, hidden binder |

The `rfl` examples and the error pins moved unchanged and pass.

**Checks.**  `import Solidity`, `import SolidityCorpus` and
`import SolkeyTestSuite` scratch modules: no errors; `check-orphans`
(the scratch modules only), `check-doc-paths` pass.

**Timing** (end-of-work, base the `intrinsic` worktree at `624c492a`,
interleaved in one session; other lanes building, load 2–16, so the
low-load pairs count):

| Module | base | W8.2 reader-tools | ratio | gate |
|---|---|---|---|---|
| `Calculus/SurfaceNotation` + `Examples/Tactics/DlNotation` | 8.59 s (8.50, 8.86, 8.59) | 9.84 s: 8.57 s (8.85, 7.86, 8.57) + 1.27 s (1.50, 1.27) | 1.15 | 1.2× base; the base module held the examples that `DlNotation` now holds, so the two are summed |
| `Examples/Tactics/StorageSteps` | 40.48 s | 41.08 s (40.30, 41.86) | 1.01 | 1.2× base |
| `Corpus/SolcStructs` | 1.22 s (1.24, 1.20) | 1.00 s (1.00, 0.99) | 0.82 | 1.2× base: no `resolve` in the kernel |
| `Examples/Chains/Storage` | 7.87 s (load 2.8; 10.11, 15.93 under load 7–15) | 7.57 s (load 2.5; 7.69, 9.86 under load) | 0.96 | 8.94 s (W6) |
| `Examples/ChainRewrites` | 6.91 s | 6.85 s (6.84, 6.86) | 0.99 | 7.63 s (W6) |

Every row within its gate.

### W8 W8.2 consumers read scoped (printers, obligations, reader) merge (2026-10-11)

`printers`, `obligations` and `reader-tools` merged into `intrinsic` in
that order.  The lanes' proposals are renumbered consecutively: 106–110
`printers` (as they were), 111–113 `obligations` (its 106–108), 114–115
`reader-tools` (its 106–107; 115 withdrawn at its review).

**Reconciled at the merge.**  `Fml.resolveN` (on `Surface.Fml`) is
deleted from `Calculus/NotationResolve.lean`: its last reader,
`Calculus/Spec.lean`'s `specObligation`, reads scoped since
`obligations`.  The two readers of a closer formula in a context, the
`reader-tools` lane's `NFml.resolveIn` (with a `hint`) and the
`obligations` lane's `NFml.resolveN` (local to `Spec.lean`, no `hint`),
are one: `NFml.resolveN hint` in `Calculus/NotationResolve.lean`, read by
`Calculus/Notation.lean`'s `elabFmlC` and by `Spec.lean` with
`fun _ => none` (the two definitions had the same clauses).
`Update.lean`'s note on `Surface.Fml` no longer names `Fml.resolveN`.
`docs/module-map.md` takes the `obligations` lane's lines for
`Calculus/{Spec,Deploy,Problem,SurfaceSpec}.lean` and the `reader-tools`
lane's for `Calculus/{NotationResolve,Notation,SurfaceNotation}.lean`.
No pin moved at the merge beyond the lanes' own.

**Checks.**  The full build with `SolidityCorpus` and `SolkeyTestSuite`
(328 jobs) green at the first try; `dups.py` (the three known),
`check-orphans` (the scratch module only), `check-doc-paths`,
`check-rule-text` pass.

**Timing** (the end-of-work method: each file copied under
`Solidity/Scratch/`, one fresh worker at a time through the MCP, end of
work sampled every 20 ms, the worker killed after; one run a row, the
minimum kept where there are two; load 0.7–2.4 but for Derived1's first
run, at 7.5; cgroup 7.8 GB):

| Module | W6 baseline | gate (1.2×) | W7 merge | **W8.2 merge** | ratio (W6) |
|---|---|---|---|---|---|
| `TestSuite/Derived1` | 7.32 s | 8.78 s | 7.65 s | **7.50 s** (7.56, 7.50) | 1.02 |
| `TestSuite/Derived2` | 8.63 s | 10.36 s | 8.91 s | **9.03 s** | 1.05 |
| `TestSuite/Derived3` | 13.01 s | 15.61 s | 13.36 s | **13.63 s** | 1.05 |
| `TestSuite/Derived4` | 17.57 s | 21.08 s | 17.87 s | **18.12 s** | 1.03 |
| `TestSuite/Derived5` | 6.95 s | 8.34 s | 7.20 s | **7.18 s** | 1.03 |
| `TestSuite/Derived6` | 11.42 s | 13.70 s | 11.79 s | **11.89 s** | 1.04 |
| `TestSuite/Derived7` | 50.43 s | 60.52 s | 51.41 s | **52.92 s** | 1.05 |
| `TestSuite/Derived8` | 26.38 s | 31.66 s | 26.83 s | **27.71 s** | 1.05 |
| `TestSuite/Derived9` | 7.16 s | 8.59 s | 7.31 s | **7.26 s** | 1.01 |
| `TestSuite/Derived10` | 11.11 s | 13.33 s | 11.59 s | **11.53 s** | 1.04 |
| `TestSuite/Derived11` | 3.16 s | 3.79 s | 3.23 s | **3.23 s** | 1.02 |
| `TestSuite/Derived12` | 13.17 s | 15.80 s | 13.54 s | **13.62 s** | 1.03 |
| `TestSuite/Derived13` | 6.36 s | 7.63 s | 6.45 s | **6.47 s** | 1.02 |
| `TestSuite/Derived14` | 10.89 s | 13.07 s | 11.08 s | **11.24 s** | 1.03 |
| Derived1–14, sum | 193.6 s | 232.3 s | 198.2 s | **201.3 s** | 1.04 |
| `Examples/Tactics/Decide` | 49.14 s | 58.97 s | 37.47 s | **37.48 s** | 0.76 |
| `Examples/ProofTree` | 9.81 s | 11.77 s | 9.74 s | **9.73 s** | 0.99 |
| `Examples/Chains/Storage` | 7.45 s | 8.94 s | 7.52 s | **7.70 s** | 1.03 |
| `Examples/ChainRewrites` | 6.36 s | 7.63 s | 6.86 s | **6.84 s** | 1.08 |
| `Examples/ChainRewritesOpen` | — | — | 3.43 s | **3.45 s** | — |
| `TestSuite/Problems` (M0) | 0.81 s | 0.97 s | 0.85 s | **0.84 s** | 1.04 |
| `TestSuite/ScopedProblems` (M0) | 1.39 s | 1.67 s | 1.45 s | **1.09 s** | 0.78 |
| `Solkey/TestSuite` (M0) | 10.83 s | 13.00 s | 11.03 s | **6.71 s** | 0.62 |
| `Examples/Benchmark/Syntax` (M0) | 1.41 s | 1.69 s | 1.48 s | **1.44 s** | 1.02 |
| `Evm/Examples` (M0) | 7.75 s | 9.30 s | 7.91 s | **7.91 s** | 1.02 |
| `Evm/Correct` (M0) | 1.68 s | 2.02 s | 1.71 s | **1.72 s** | 1.02 |

The lanes' own rows, against their bases (`624c492a`): `Examples/Tactics/Print`
3.73 s (base 3.93), `Calculus/SurfaceNotation` + `Examples/Tactics/DlNotation`
7.25 + 1.18 = 8.43 s (base 8.59, the examples then in one module),
`Corpus/SolcStructs` 1.01 s (1.22), `Examples/Tactics/StorageSteps`
39.10 s (40.48).

**Gate passed**: every row within 1.2× of its W6 baseline (and of the
lanes' bases); against the M0 limits, `Derived10` 11.53 (11.2, over by 3%
as at W7) and `Benchmark/Syntax` 1.44 (1.44, at its limit).
`Solkey/TestSuite` and `ScopedProblems` are faster since `obligations`
(proposal 112: the imported programs are not compiled).

**Left** (from the lanes, for W8.3–W8.5): the `…Legacy` printers,
`withErased`, `hypsParts`, `condOfLegacy?` and `pp.sol.twinCheck`, with
the erasure (W8.4); `Calculus/Callback.lean`'s delaborators,
`Calculus/Sequents.lean`, `Calculus/Hyp.lean` and `Chains`'
`withErasedPosts` still read the erasure; the pin of proposal 107
(`Examples/Tools.lean`); `Calculus/Print.lean`'s `legacyShow` examples;
`Surface.specObligation`, `specBody`, `specParts` and the unscoped
`spec!{f}` (examples outside the scoped switch), and the two `sameAs`
guards of `Examples/Tactics/Spec.lean`; `Delab` printing `where T memory
x` for a hidden binder, after which the two `where` pins of
`Examples/Tactics/DlNotation.lean` drop their `Surface.Fml` ascription;
`docs/testsuite-proofs.md`'s `solc_problems … legacy`; the read-only
review pass (W8.5).

### W8.3 lane `ex-evm-bench` record (2026-10-11, branch `w8-w83examplesandleafconsumersmigrate-ex-evm-bench`)

`Evm/{Examples,Interpreter}`, `Examples/Benchmark/{Coin,EtherWallet,Purchase,Syntax}`,
`Examples/{Tools,ExampleNames}` and `SortCheck/Faithfulness` read the
scoped syntax only; none of them names `Surface.Prog`, `resolve` or
`erase` any more.

- **`Evm/Examples.lean`**: `scopedOf` is gone; `codeOf P := compileProg 0 P`,
  and `code`, `slotAfter`, `reverts`, `compiles`, `rejects` take a
  `Prog C [] Γ'`.  `compiles`/`rejects` lose their `resolve … toBool`
  conjunct (an elaborated block is scoped already).  The named programs
  are `def setAge := (sol{ … } : Prog StandardExample [] _)`: `sol{ … }`
  with nothing expected is still the surface list until W8.4, and a
  `def` header cannot leave `Γ'` a hole.  `Evm/Interpreter.lean` reads
  `setAge` where it read `(scopedOf setAge).2`.
- **`SortCheck/Faithfulness.lean`**: `Read C Γ` is over the scoped
  `SPath C Γ T`/`MPath C Γ T` (the old `CRead`, renamed; the surface
  `Read`, `Read.Typed` and `CRead.erase*` are gone), and `Read.SortOk σ`
  reads an `EState C Γ` through the scoped `SPath.resolve`, `MPath.mval`
  and `Val.eval` (`Semantics/Erased.lean`).  `Read.sortOk` needs only
  `RunWT`: no `Agree`, no `SPath.resolve_erase`/`MPath.mval_erase`/
  `Val.eval_erase`.  `RowFaithful` quantifies over `H` and a `RunWT`
  state, not over names and an agreeing untyped state; the import of
  `Semantics/StateErase.lean` goes.  The 36 `faithful_<ctor>` theorems,
  `faithfulCtors`, `rows_covered` and `rows_accounting` are unchanged in
  text.  Its two importers follow (outside the lane's list, since they
  break otherwise): `Counterexamples/PreFixSortAnnotations.lean` drops
  `peopleStore_agree`/`flagStore_agree` and `flagStore`'s `env`, and
  applies `hall` to the scoped state; `Counterexamples/WellTypedNecessity.lean`
  states its refutation on `badCore` (`badStore` with the local `uint x`).
- **New `Syntax/PrintInlined`** (one module with `ex-calls-print`'s
  `Syntax/Inlined.lean` since the merge): `Prog.inlinedStr ns P`, a scoped
  block printed with each call as its inlined body (the strings
  `Surface.Prog.toStr (Surface.Prog.inlined (P.erase ns))` gives: the
  arguments' `T x = e;`, the return variables' `T r;` (a memory return's
  `R memory r;`), the body under `ret.names ++ args.names`, `res = r;`; a
  `{ … }` block's statements in place; a call in a branch or loop body
  printed as the call).  The `ex-calls-print` lane's pins of
  `Surface.Prog.inlined` (`Examples/Tactics/{CallOperands,Loops}.lean`)
  can use it; `Surface.Prog.inlined` in `Syntax/Splice.lean` goes in W8.4.
- **`Coin`/`EtherWallet`**: the `run_cmd … Prog.defineCore` declarations of
  `ctorCore`, `mintSendCore`, `mintCore`, `withdrawCore`, `overdrawCore`
  are plain `def`s of the scoped `sol{ … }`, the same names and types.
- **`Tools.lean`**: the three `#eval`s run `Prog.runT` (`Tools/Run.lean`'s
  scoped one).  The `functionCallArgCapture` pin (proposal 107) still
  prints `‹Surface.Stmt.call …›`: the delaborator's, W8.4.

**Pins.**  No `#guard_msgs` text moved.  Restated, same strings or
values: the 16 `Surface.Prog.toStr (sol{ … }) = "…" := rfl` examples of
`Benchmark/Syntax` and `ExampleNames` are `Prog.toStr [] (sol{ … })`
(still `rfl`); the five `#eval`s of `Surface.Prog.toStr
(Surface.Prog.inlined …)` (`Benchmark/{Syntax,Purchase}`) are
`Prog.inlinedStr [] …`; `ExampleNames`' constructor-tree pin
`sol{ uint idx = 1; … } = captured := rfl` compares the scoped blocks
(`captured` is a `Prog StandardExample [] _`).  One `#eval` of
`Evm/Examples.lean` (`total = total + age;`, its three lines) binds the
program before its `do`: a `sol{ … }` elaborated inside a `do` block fails
with "Type of b✝ is not known" (`elabSolBracket`'s scoped branch,
`fun b => (Prog.quoteShared q b.2).1`, has no binder type; W8.4 can
annotate it when it drops the surface branch).

**Checks.**  Zero errors and warnings in every touched file and in the
importers `Examples/Tactics/Operators.lean` (of `Evm/Examples`, unedited)
and the two counterexamples; `check-orphans`, `check-doc-paths` pass.

**Timing** (end-of-work method, each file copied under `Solidity/Scratch/`,
one fresh worker at a time, killed after; base = the files at `intrinsic`
`cebf1880` in the same worktree; load 1.2–1.7, cgroup 8.4–9.1 GB):

| Module | W6 baseline | gate (1.2×) | base (`cebf1880`) | **ex-evm-bench** | ratio (W6) |
|---|---|---|---|---|---|
| `Evm/Examples` (M0) | 7.75 s | 9.30 s | 7.99 s | **7.29 s** (7.29, 7.36) | 0.94 |
| `Examples/Benchmark/Syntax` (M0) | 1.41 s | 1.69 s | 1.44 s (1.49, 1.44) | **1.57 s** (1.57, 1.59) | 1.11 |

`Evm/Examples` is faster, as expected: the kernel no longer evaluates
`resolve`.  `Benchmark/Syntax` is 0.1 s slower (9% over its M0 limit of
1.44 s, within the 1.2× gate): a profile puts it in the `rfl` checks of
`Prog.toStr` on the scoped blocks (33, 30, 72 ms over 30 ms against one of
54 ms at base), the four inlined `#eval`s costing what they did
(110–124 ms each, both).

### W8.3 lane `ex-storage-memory` record (2026-10-11, branch `w8-w83examplesandleafconsumersmigrate-ex-storage-memory`)

Fourteen example files read the scoped syntax: `Examples/Tactics/{StorageSuite,
StorageDelete,Memory,LedgerDelete,Net,Values,Operators,Checked,CrossDomain,
Constructors,CallbackRuns,Tour}.lean`, `Examples/Chains/Memory.lean`,
`Examples/Notation.lean`.  None of them names `Surface.Prog` any more.

- **Strings and runs.**  `Surface.Prog.toStr (sol{ … })` is
  `Prog.toStr [] (sol{ … })`, with the same strings, still by `decide` (`rfl` in `Chains/Memory.lean`).
  `Surface.Prog.runT`/`localAfterT` are `Prog.runT`/`Prog.localAfterT`
  (`Tools/Run.lean`), and `Mini.deployRun` is `Mini.deployRunS`.  An
  ascription `: Surface.Prog C` is `: Prog C [] _`.
- **Kernel claims on the scoped program.**  In `StorageSuite`, `Net`,
  `Constructors` and `CallbackRuns`, the `run_cmd … Prog.defineCore` blocks
  are gone.  Each `…Core` is now a definition,
  `private def xCore := (sol{ … } : Prog C [] _)`, which the kernel checks
  like `Prog.define`'s.  The `decide +kernel` and `rfl` claims unfold it
  directly, with no `resolve`.  The ascription goes in the body because a
  `_` in a declared type is not filled from the body.  For the same reason,
  `StorageSuite`'s two `fail_if_success have` refusals are
  `have := (sol{ … } : Prog TestSuite [] _)`; a positive control
  (`fixedValues[2] = 1;`) was checked to elaborate in that form.
- **`Examples/Notation.lean`'s premise pin** binds the block
  `let P : Prog StandardExample [] _ := sol{ … }` in place of
  `Prog.resolve [] sol{ … }`.  The printed premise is unchanged.
- **Not moved.**
  - The bare `#check sol{ … }` error pins have no expected type, so they
    still go through the erased path.  They take the scoped one at W8.4
    with the same text, because `elabProgAt` is `elabProgAtS` followed by
    an erasure, so the errors are the same.
  - `Operators.machine_run`'s `slotAfter sol{ … }` reads at
    `Evm/Examples.lean`'s `Surface.Prog` type until the `Evm` lane moves
    `slotAfter`.  It needs no change of text here.
  - The `import Solidity.Calculus.Surface` lines stay: that module is the
    `open scoped Solidity.Scoped` switch, not the surface syntax.

**Pins.**  No `#guard_msgs` text moved.  The pins whose statement changed,
with the same expected text:

| File | Pins | Change |
|---|---|---|
| `Tactics/Checked.lean` | 1 `#eval` pin, 6 `decide` string examples | `Surface.Prog.toStr` → `Prog.toStr []` |
| `Tactics/Operators.lean` | 2 `decide` string examples | same |
| `Chains/Memory.lean` | 1 `rfl` string example | same, ascription `: Prog Calls [] _` |
| `Tactics/StorageSuite.lean` | 9 `#eval` pins (`localAfterT`/`runT`) | the scoped run tools |
| `Tactics/StorageDelete.lean` | its `#eval` pins on a run | same |
| `Tactics/Memory.lean` | its `#eval` pins on a run (some bind `let P : Prog C [] _`) | same |
| `Tactics/LedgerDelete.lean` | 3 `#eval` pins (`ledgerProgram` scoped) | same |
| `Tactics/Values.lean`, `Tactics/CrossDomain.lean` | 1 `#eval` pin each | same |
| `Tactics/Tour.lean` | 3 `#check` error pins | ascription `: Prog StandardExample [] _` |
| `Tactics/Constructors.lean` | `deployValue` (`rfl`) | `Mini.deployRunS` |
| `Notation.lean` | the `run_meta` premise pin | the block bound scoped, no `resolve` |

No constructor-tree pin is among these files.

**Checks.**  Every touched file has no errors and no warnings (checked
through the MCP).  Only `Solidity.lean` imports them.  No gate row imports
these modules, so the W6/W7 gate rows cannot move, and W8.5 re-times
them.  The lane's own files were timed with the end-of-work method
(`intrinsic` at `cebf1880` against this branch, one fresh worker each,
load 0.9–1.8):

| Module | base | lane | ratio |
|---|---|---|---|
| `Examples/Tactics/StorageSuite` | 23.78 s | 23.37 s | 0.98 |
| `Examples/Tactics/Net` | 7.80 s | 7.72 s | 0.99 |
| `Examples/Tactics/Constructors` | 6.63 s | 6.47 s | 0.98 |
| `Examples/Tactics/Checked` | 7.06 s | 7.10 s | 1.01 |
| `Examples/Tactics/Memory` | 67.36 s | 67.68 s | 1.00 |

### W8.3 lane `ex-calls-print` record (2026-10-11, branch `w8-w83examplesandleafconsumersmigrate-ex-calls-print`)

`Examples/Tactics/{CallOperands,Calls,Loops,Branch,TryCatch,Step,Print,Symex}.lean`
read and print the scoped syntax only: no `Surface.Prog`, `Surface.Fml`,
`Prog.resolve`, `Prog.resolveCheck`, `Prog.defineCore` or `elabProgAt` is
left in them.  `Examples/Tactics/Surface.lean` needed nothing: its pin
already reads `: Fml StandardExample []` (W8.2 `reader-tools`).

- **Programs.**  `Surface.Prog.toStr (sol{…} : Surface.Prog C)` is
  `Prog.toStr [] (sol{…} : Prog C [] _)`, `Surface.Prog.show` is
  `Prog.show []`, `Surface.Prog.runT` is `Prog.runT`, `elabProgAt` is
  `elabProgAtS`.  A block that was declared `Surface.Prog C` and then
  `Prog.defineCore`d is declared scoped by `sol{…}` at its type
  (`countTo3Core`, `countUpCore`, `pushLvalueCore`, `pingNoCodeCore`, same
  names).  `Calls.lean`'s `calleeStr` reads the last statement's call
  scoped and prints its body in the frame's names
  (`CallRet.names ++ Args.names`).
- **Inlined calls.**  `Surface.Prog.inlined` has no scoped twin (a call's
  body lives in its own frame), so the new `Syntax/Inlined.lean` prints a
  block with its calls inlined (`Prog.inlinedStr`, `Prog.inlinedShow`):
  the arguments' declarations, the return variables', the body (inlined in
  turn), the result, as `Surface.Stmt.expandBody` built them.  The four
  pins (`Loops`' `find`, `pair`, `ModifierRuns.f`; `CallOperands`'
  `choosePersonMem`) print as before.
- **Formulas.**  `Step`'s `agree`, `Symex`'s `coreSymex`, `Print`'s
  `stepsShowOf` and `headPremise` take `Fml C []` from `dl!{ … }` (each file
  imports `Calculus/Notation.lean`, where the scoped reader is); no
  `Prog.resolve`, no rebuilt `.modal m P .nil .tt` (the reader writes that
  term).  `Print`'s formulas with free locals were read under an `NCtx`
  and closed by `∀`s (`closeAll`); they are written with the `∀`s now
  (`dl!{ ∀ uint a; ∀ uint b; [ (a, b) = pair(3); ] true }`), the formula
  and text the pins had, and `headPremise` reads the program under them.
- **Refused programs.**  `Loops`' four elaboration-error pins state the
  scoped type with its output context (`Prog StandardExample [] [.val
  .uint]`): with `_` the error is preceded by "don't know how to synthesize
  placeholder".  `Branch`'s `Prog.resolveCheck` guard (alike in both
  branches, at another type in a later one) is an `example` at
  `Prog StandardExample [] [.val .bool]`: the scoped elaborator accepting it
  is the check.

Proposed decisions:

- **116 (`ex-calls-print`).**  `Syntax/Inlined.lean` (above
  `Syntax/Scoped.lean` only) replaces `Surface.Prog.inlined` for display:
  a string printer, not a scoped program (a call's body is closed over its
  frame, so inlining it as a `Prog` would need the weakening `Stmt.wk` and
  the frame's pops; the pins only print it).  A memory return prints as the
  `T memory r;` the erasure's body began with.  `Syntax/Splice.lean`'s
  `inlined` pin can take it in W8.4.
- **117 (`ex-calls-print`).**  A scoped `sol{ … }` inside `#eval do … ←`
  fails to elaborate ("Invalid projection: Type of b✝ is not known"),
  even ascribed; `TryCatch`'s two runs declare their programs first
  (`pingP`, `pingPanicP`).  Left as found for W8.4 (the splice's shared
  `let`s under `do`, presumably); a `sol{}` outside `do` is unaffected.

**Pins.**  No printed text moved (every `#guard_msgs` and every `rfl`
string is as before).  Command lines changed under unchanged pins:
`Print`'s `stepsShowOf … Γ`/`headPremise … Γ` drop the context argument
(`abΓ`, `okToΓ`, `closeAll` gone); `TryCatch`'s two `#eval`s run the
declared `pingP`/`pingPanicP`; the inlined pins call
`Prog.inlinedShow`/`Prog.inlinedStr`.

**Checks.**  Every touched file through the Lean server: no errors, no
warnings (`Syntax/Inlined.lean` included); their only importer outside
`Solidity.lean` is `Print` (of `Symex`), checked.  `check-orphans` (the
scratch modules only) and `check-doc-paths` pass.

**Timing** (the end-of-work method, each file copied under
`Solidity/Scratch/`, base the same file at `cebf1880` in this worktree,
same session; load 0.8–1.4, cgroup 8.1 GB).  No W6/W7 gate row imports
these files; the lane's rows against the base:

| Module | base (`cebf1880`) | `ex-calls-print` | ratio |
|---|---|---|---|
| `Examples/Tactics/Print` | 3.71 s (3.72, 3.71) | 3.43 s (3.43, 3.49) | 0.92 |
| `Examples/Tactics/Calls` | 64.91 s | 64.69 s | 1.00 |
| `Examples/Tactics/Loops` | 26.63 s | 26.31 s | 0.99 |
| `Examples/Tactics/Step` | 29.08 s | 29.15 s | 1.00 |
| `Examples/Tactics/CallOperands` | 20.49 s | 20.49 s | 1.00 |
| `Examples/Tactics/TryCatch` | 5.33 s | 5.26 s | 0.99 |
| `Examples/Tactics/Branch` | 7.84 s | 7.83 s | 1.00 |
| `Examples/Tactics/Symex` | 1.22 s | 1.17 s | 0.96 |

Every row within 1.2× of its base (`Print`'s W8.2 merge row: 3.73 s).

### W8 W8.3 examples and leaf consumers migrate merge (2026-10-11)

`ex-evm-bench`, `ex-storage-memory` and `ex-calls-print` merged into
`intrinsic` in that order.  Only `ex-calls-print` proposed decisions;
its 116–117 follow 115 and keep their numbers.

**Reconciled at the merge.**  The two inlining printers are one module,
`Syntax/Inlined.lean` (`ex-calls-print`'s, the one proposal 116 names):
it takes `ex-evm-bench`'s `Syntax/PrintInlined`'s `.block` clause, so a
`{ … }` block's statements are written in place with their calls inlined,
as `Surface.Prog.inlined` on the erasure (which flattens a block) wrote
them, and keeps `Prog.inlinedShow`.  `Syntax/PrintInlined` is deleted;
`Examples/Benchmark/{Syntax,Purchase}.lean` import `Syntax/Inlined.lean`.
`Solidity.lean` and `docs/module-map.md` carry the one module.
`Operators.machine_run`'s `slotAfter sol{ … }` (left by
`ex-storage-memory`) reads scoped since `ex-evm-bench` moved `slotAfter`,
with no change of text.  No pin moved at the merge beyond the lanes' own.

**Checks.**  The full build with `SolidityCorpus` and `SolkeyTestSuite`
(329 jobs) green at the first try; `dups.py` (the three known),
`check-orphans` (a scratch module only), `check-doc-paths`,
`check-rule-text` pass.

**Timing** (the end-of-work method as at the W8.2 merge, one run a row,
load 0.9–2.4, cgroup 8.2–13.3 GB):

| Module | W6 baseline | gate (1.2×) | W8.2 merge | **W8.3 merge** | ratio (W6) |
|---|---|---|---|---|---|
| `TestSuite/Derived1` | 7.32 s | 8.78 s | 7.50 s | **7.56 s** | 1.03 |
| `TestSuite/Derived2` | 8.63 s | 10.36 s | 9.03 s | **8.97 s** | 1.04 |
| `TestSuite/Derived3` | 13.01 s | 15.61 s | 13.63 s | **13.34 s** | 1.03 |
| `TestSuite/Derived4` | 17.57 s | 21.08 s | 18.12 s | **17.85 s** | 1.02 |
| `TestSuite/Derived5` | 6.95 s | 8.34 s | 7.18 s | **7.07 s** | 1.02 |
| `TestSuite/Derived6` | 11.42 s | 13.70 s | 11.89 s | **11.64 s** | 1.02 |
| `TestSuite/Derived7` | 50.43 s | 60.52 s | 52.92 s | **51.26 s** | 1.02 |
| `TestSuite/Derived8` | 26.38 s | 31.66 s | 27.71 s | **27.11 s** | 1.03 |
| `TestSuite/Derived9` | 7.16 s | 8.59 s | 7.26 s | **7.24 s** | 1.01 |
| `TestSuite/Derived10` | 11.11 s | 13.33 s | 11.53 s | **11.47 s** | 1.03 |
| `TestSuite/Derived11` | 3.16 s | 3.79 s | 3.23 s | **3.29 s** | 1.04 |
| `TestSuite/Derived12` | 13.17 s | 15.80 s | 13.62 s | **13.51 s** | 1.03 |
| `TestSuite/Derived13` | 6.36 s | 7.63 s | 6.47 s | **6.48 s** | 1.02 |
| `TestSuite/Derived14` | 10.89 s | 13.07 s | 11.24 s | **11.00 s** | 1.01 |
| Derived1–14, sum | 193.6 s | 232.3 s | 201.3 s | **197.8 s** | 1.02 |
| `Examples/Tactics/Decide` | 49.14 s | 58.97 s | 37.48 s | **37.62 s** | 0.77 |
| `Examples/ProofTree` | 9.81 s | 11.77 s | 9.73 s | **9.83 s** | 1.00 |
| `Examples/Chains/Storage` | 7.45 s | 8.94 s | 7.70 s | **7.55 s** | 1.01 |
| `Examples/ChainRewrites` | 6.36 s | 7.63 s | 6.84 s | **6.81 s** | 1.07 |
| `Examples/ChainRewritesOpen` | — | — | 3.45 s | **3.48 s** | — |
| `TestSuite/Problems` (M0) | 0.81 s | 0.97 s | 0.84 s | **0.83 s** | 1.02 |
| `TestSuite/ScopedProblems` (M0) | 1.39 s | 1.67 s | 1.09 s | **1.04 s** | 0.75 |
| `Solkey/TestSuite` (M0) | 10.83 s | 13.00 s | 6.71 s | **6.78 s** | 0.63 |
| `Examples/Benchmark/Syntax` (M0) | 1.41 s | 1.69 s | 1.44 s | **1.60 s** (1.60, 1.60) | 1.13 |
| `Evm/Examples` (M0) | 7.75 s | 9.30 s | 7.91 s | **7.25 s** | 0.94 |
| `Evm/Correct` (M0) | 1.68 s | 2.02 s | 1.72 s | **1.72 s** | 1.02 |

**Gate passed**: every row within 1.2× of its W6 baseline.  Against the
M0 limits, `Derived10` 11.47 (11.2, over by 2%, as since W7) and
`Benchmark/Syntax` 1.60 (1.44, over by 11%): the `ex-evm-bench` lane's
`rfl` checks of `Prog.toStr` on the scoped blocks (its record), which
W8.4 may win back when `sol{}` with nothing expected reads scoped.
`Evm/Examples` is faster: the kernel no longer evaluates `resolve`.

**Left** (from the lanes, for W8.4–W8.5): `Examples/Tools.lean`'s
`functionCallArgCapture` pin (proposal 107) prints `‹Surface.Stmt.call …›`
(the delaborator, W8.4); `Surface.Prog.inlined` and its pin in
`Syntax/Splice.lean` (can take `Prog.inlinedStr` from
`Syntax/Inlined.lean`); a scoped `sol{}` inside a `do` block fails with
"Type of b✝ is not known" (proposal 117: `elabSolBracket`'s scoped
branch, `fun b => (Prog.quoteShared q b.2).1`, has no binder type), worked
around in `Evm/Examples.lean` and `Examples/Tactics/TryCatch.lean` by
binding the program first; the `(sol{…} : Prog C [] _)` ascriptions that
can go when `sol{}` with nothing expected reads scoped, and the bare
`#check sol{ … }` error pins that then take the scoped path; the
`import Solidity.Calculus.Surface` lines stay (it is the `open scoped
Solidity.Scoped` switch); if `Contract.deployRunS` is renamed back to
`deployRun`, `Examples/Tactics/Constructors.lean` and its module-map line
follow; the lead's calls on proposals 116–117; the read-only review pass
(W8.5).

### W8.4 record (2026-10-11, step `delete`, on `intrinsic`)

Tagged `w8-pre-delete` (`f16586b1`) before the step, for the SolKey
reader, whose port to the scoped constructors is a later task on
side-projects (its require stays at the tag).  The untyped statement and
everything that existed only for it are deleted, about 4,200 lines.

**Syntax.**  `Syntax.lean` keeps the grammar, the raw syntax, the contract,
`ArrTy`/`IndexTy`, `RefTy.newArrOk`, `IncDec.show`, `braced` and the
quoters' helpers; `Surface.Stmt`/`Prog`, the sixteen program-term families,
the surface `Arg`, `codeBinders`, `expandBody`, the printers and quoters
are gone, and the module docstring is rewritten.  `Syntax/Resolve.lean` is
deleted: `NCtx`, `NCtx.find`, `LTy.toStr`, `Binders.nctx`/`snocAll`/
`ofList`, `CodeBinder.ofOption`/`nctx`/`toOption` and `Prog.castIn` moved
to `Syntax/Elab.lean` (its only reader; *amended by the final-review fixes:
`Binders.nctx`, `CodeBinder.nctx`, `CodeBinder.toOption`, their lemmas,
`NCtx.ctx_append`/`names_append` and `Binders.toList_snocAll`/
`toList_ofList` had no reader left there and are removed*); `Prog.sepArgs`, `Stmt.Fresh`,
`Prog.Fresh` and the cast lemmas had no reader left and are not moved.
`Syntax/Elab.lean` loses `elabStmt`/`elabStmts`/`elabStmtsS`,
`Syntax/Splice.lean` the erasing entry points and the expected-type
dispatch (`sol{}` is always the scoped block; the lambda's binder now has
its type, proposal 117), `Syntax/Quote.lean` `Prog.defineCore`.
`Surface.primName` is `PrimTy.toStr`.

**Semantics and `Update.lean`.**  The surface evaluators
(`Semantics.lean`), their frame lemmas (`Semantics/Agree.lean`), no-panic
lemmas (`Semantics/NoPanicOps.lean`) and the program-term `*_erase`
lemmas (`Semantics/StateErase.lean`; `aliasPath_erase` and the state
lemmas stay) are gone; `Semantics/Erased.lean`'s example programs are
plain definitions of scoped `sol[C]{}` blocks.  `Update.lean` loses
`Surface.Fml`, `NFml.toSurface`, `Surface.Fml.toFml` and the surface
lowerings (`Term.keyAt` stays); `Calculus/Lower.lean` its `lower_erase`.

**Calculus.**  `Calculus/Fml.lean` loses `Frames.erase` and `Fml.eraseS`;
`Calculus/Closable.lean` `Frames.Fresh`.  `RuleSyntax.lean`: the readers
write the scoped constants directly (`coreFamily?` keeps the term
families: `Tms`, `Fml`, `Tm`, `Upd`, `UpdElem`), the unscoped taclet
reading (`schemaTaclet`, `schemaPremise`, `schemaInv`), `stmt{ s; }` and
the `dl{ premise }` macro are gone (taclet lines read under `open scoped
Solidity.Schema`), and so are the surface printers (`ppExpr`, `ppStmt`,
`ppProg?`, …, `delabStmt`, `copyDecls`/`withDecls`); the builders the
scoped printer uses stay.  `RuleKit.lean` keeps the branch labels
(`labelledBy` on the scoped heads) and `delabTacletBinders`.
`DelabErase.lean` translates terms, updates and the closer's formulas only
(`untwinnedFamilies`, `withErased`, `asSurface` gone).  `PrintStmt.lean`,
`Delab.lean`, `DelabLean.lean`, `Callback.lean`, `ProofTree.lean` lose the
`…Legacy` printers, `hypsParts`, `condOfLegacy?` and `pp.sol.twinCheck`.
`SurfaceNotation.lean` reads the closer's `NFml` (a modality is
`Notation.lean`'s), `NFmlQuote.lean` loses `Surface.Fml.quote`,
`Hyp.lean` and `Sequents.lean` their surface cases, `SurfaceSpec.lean`
`specBody`/`specParts`/`Surface.specObligation` and the unscoped `spec`
reading, `Print.lean` `legacyShow`, `Tools/Run.lean` the surface wrappers
(`Contract.deployRunS` is `deployRun` again).  `rg
'Surface\.(Stmt|Prog|Fml|Val|SPath|Loc|MPath|MLoc|Simple|OpLoc|CallRet|Src|MSrc|ARhs|MRhs|NewLhs|LoopAnn|ExtCall|ExtArg|Premise|Hole|VHole|MHole|Problem)' Solidity`
is empty.

**Pins that moved.**  `Syntax/Splice.lean`'s string pins read `Prog.toStr
[]` (same strings), its constructor trees are scoped, the inlined pin is
`Prog.inlinedStr` (same string), and the three `resolveCheck` guards are
elaboration-error pins of `sol{}` text (proposal 126);
`Examples/Tools.lean`'s `functionCallArgCapture` (proposal 118);
`Examples/Tactics/DlNotation.lean`'s two `where` pins now print the
scoped formula with its clause (proposal 120: type suffix `Fml
StandardExample []`, text unchanged); `Calculus/Print.lean`'s pin of the
erasure's printing, and `Examples/Tactics/Spec.lean`'s two `sameAs`
guards, are gone with what they compared against.  No other pin moved.

What the step had to choose (proposals, lane `delete`):

- **118**: `functionCallArgCapture`'s two calls print as the scoped terms
  `‹Stmt.call f args ret body›`, `‹Stmt.call f as' ret body›` (the twins'
  `hsep` is gone); `#check_rule_text` lets the escape
  `‹Solidity.Stmt.call …›` pass, as it let `‹Solidity.Surface.…›` pass,
  and counts the program families among `scopedOnlyRoots` otherwise.
- **119**: `show_sequent` compares the line the goal prints as (its context
  folded in front, `Hyps.wrap`, a block's end not shown) with the line read
  scoped (`cdl[C]{ … }`), printed alike; it unified the two erasures.
  The fold alone made the check weaker (a context entry prints as an
  implication or update of the formula, so `⟹ ∀ uint x; a → φ` passed
  for the goal `∀ uint x, a ⟹ φ`); the review restored the old entry
  count, the goal's printed entries (`Delab.hypsPartsS`, a hidden binder
  none) against the line's, pinned by a `fail_if_success` in
  `Examples/Tactics/Sequents.lean`.
- **120**: `Delab.ppFmlE` prints `φ where T memory x` for a memory local a
  copy out of storage binds (`MRhs.copy`) under a hidden binder, the
  scoped form of `copyDecls`; only a formula standing alone (`dl{ … }`)
  gets the clause, as before.
- **121**: `Fml.Plain` of a modality is `False` (it asked the box and
  `Prog.Fresh`/`Frames.Fresh`, which went with the erasure); its only
  reader, `holds_erase_fo`, asks `Fml.FO`, false of a modality.
- **122**: `spec[C]{f}` and `spec!{f}` read as `cspec[C]{f}` everywhere
  (`Calculus/Spec.lean`), not only under `open scoped Solidity.Scoped`.
- **123**: a program schema variable lowered to a term prints, through
  `Delab.tr`, as the local of its name (`loweredVar?`: `Term.pv`,
  `PTerm.pv`, `ITerm.pv`); `RuleSyntax.lean`'s `loweredExpr?` is gone.
- **124**: `Contract.deployRunS` is `Contract.deployRun` again.
- **125**: `Prog.sepArgs`, `Stmt.Fresh`/`Prog.Fresh` and the cast lemmas
  are deleted, not moved: nothing reads them.
- **126**: the `resolveCheck` guards' messages are not reachable from
  `sol{}` text (the elaborator checks a local's type before `NCtx.find`
  would): the pins are the elaborator's own (`unknown name x`, `a number
  where a bool is expected`, `a bool where a uint is expected`, `unknown
  name y` after a branch).
- **127**: taclet lines read only under `open scoped Solidity.Schema` (the
  unscoped reading went with `Surface.Premise`); `dl{ p }` keeps its syntax,
  which the premise printer writes, and loses its macro.
- **128**: `Syntax/Splice.lean` declares `callsCore` (`Semantics/Run.lean`'s)
  from `elabProgS` and `Prog.define`; `tourCore` is gone.

**Checks.**  The full build with `SolidityCorpus` and `SolkeyTestSuite`
(328 jobs) green (once more after an OOM kill, exit 137); `dups.py` (the
three known), `check-orphans` (a scratch module only), `check-doc-paths`,
`check-rule-text` pass.  No `sorry`, `axiom` or `maxHeartbeats` added.

**Timing** (the end-of-work method, `scratchpad/w84m.sh`, one run a row,
load 0.9–9.7 falling as the build ended, cgroup 7.7 GB):

| Module | W6 baseline | gate (1.2×) | W8.3 merge | **W8.4** | ratio (W6) |
|---|---|---|---|---|---|
| `TestSuite/Derived1` | 7.32 s | 8.78 s | 7.56 s | **7.50 s** | 1.02 |
| `TestSuite/Derived2` | 8.63 s | 10.36 s | 8.97 s | **8.72 s** | 1.01 |
| `TestSuite/Derived3` | 13.01 s | 15.61 s | 13.34 s | **13.30 s** | 1.02 |
| `TestSuite/Derived4` | 17.57 s | 21.08 s | 17.85 s | **17.81 s** | 1.01 |
| `TestSuite/Derived5` | 6.95 s | 8.34 s | 7.07 s | **7.14 s** | 1.03 |
| `TestSuite/Derived6` | 11.42 s | 13.70 s | 11.64 s | **11.70 s** | 1.02 |
| `TestSuite/Derived7` | 50.43 s | 60.52 s | 51.26 s | **51.48 s** (54.47 at load 2.6) | 1.02 |
| `TestSuite/Derived8` | 26.38 s | 31.66 s | 27.11 s | **26.92 s** | 1.02 |
| `TestSuite/Derived9` | 7.16 s | 8.59 s | 7.24 s | **7.25 s** | 1.01 |
| `TestSuite/Derived10` | 11.11 s | 13.33 s | 11.47 s | **11.56 s** | 1.04 |
| `TestSuite/Derived11` | 3.16 s | 3.79 s | 3.29 s | **3.36 s** | 1.06 |
| `TestSuite/Derived12` | 13.17 s | 15.80 s | 13.51 s | **13.66 s** | 1.04 |
| `TestSuite/Derived13` | 6.36 s | 7.63 s | 6.48 s | **6.54 s** | 1.03 |
| `TestSuite/Derived14` | 10.89 s | 13.07 s | 11.00 s | **11.20 s** | 1.03 |
| Derived1–14, sum | 193.6 s | 232.3 s | 197.8 s | **198.1 s** | 1.02 |
| `Examples/Tactics/Decide` | 49.14 s | 58.97 s | 37.62 s | **37.50 s** | 0.76 |
| `Examples/ProofTree` | 9.81 s | 11.77 s | 9.83 s | **9.75 s** | 0.99 |
| `Examples/Chains/Storage` | 7.45 s | 8.94 s | 7.55 s | **7.58 s** | 1.02 |
| `Examples/ChainRewrites` | 6.36 s | 7.63 s | 6.81 s | **6.85 s** | 1.08 |
| `Examples/ChainRewritesOpen` | — | — | 3.48 s | **3.54 s** | — |
| `TestSuite/Problems` (M0) | 0.81 s | 0.97 s | 0.83 s | **0.86 s** | 1.06 |
| `TestSuite/ScopedProblems` (M0) | 1.39 s | 1.67 s | 1.04 s | **1.11 s** | 0.80 |
| `Solkey/TestSuite` (M0) | 10.83 s | 13.00 s | 6.78 s | **6.77 s** | 0.63 |
| `Examples/Benchmark/Syntax` (M0) | 1.41 s | 1.69 s | 1.60 s | **1.61 s** | 1.14 |
| `Evm/Examples` (M0) | 7.75 s | 9.30 s | 7.25 s | **7.34 s** | 0.95 |
| `Evm/Correct` (M0) | 1.68 s | 2.02 s | 1.72 s | **1.77 s** | 1.05 |

**Gate passed**: every row within 1.2× of its W6 baseline.  Against the
M0 limits, `Derived10` 11.56 (11.2, over by 3%) and `Benchmark/Syntax`
1.61 (1.44, over by 12%) as at W8.3: `sol{}` was already scoped where that
module reads it, so the step wins nothing back there.

**Left** (for W8.5 and after): the `(sol{…} : Prog C [] _)` ascriptions
in the examples, which `sol{}` no longer needs, and the workarounds of
proposal 117 in `Evm/Examples.lean` and `Examples/Tactics/TryCatch.lean`
(binding the program before a `do` block), both left as they are; the
SolKey reader's port to the scoped constructors (side-projects, from tag
`w8-pre-delete`); docstrings that still call the erased side "as written";
the read-only finder/skeptic review (W8.5); the lead's calls on proposals
118–128.

### W8.5 lane `gate` record (2026-10-11, branch `w8-w85gatedocsreview-gate`, at `9d9fdf67`)

The gate re-timed after W8.4, with this lane as the only Lean agent; no
`.lean` file edited, no pin moved.  Method as in "Gates" (each file copied
under `Solidity/Scratch/`, opened in a fresh worker through the MCP, every
import built beforehand, `/proc` sampled every 20 ms, the worker killed
after each run; end of work, the minimum of three runs; CPU the minimum of
the runs).  Three interleaved passes over the thirteen modules; load (1 min)
at the starts 5.0 falling to 2.0 in pass 1 (a full build had just ended;
btrfs writeback threads), 1.8–1.3 in pass 2, 1.2–0.9 in pass 3; cgroup
9.9 GB.  The driver is `scratchpad/w85.sh` (a copy of `w84m.sh` on this
worktree), results under `w85_*` in `scratchpad/results.txt`.

| Module | baseline | gate (1.2×) | W8.4 | **W8.5** (three runs) | ratio | CPU |
|---|---|---|---|---|---|---|
| `TestSuite/Derived6` | 11.42 s (W6) | 13.70 s | 11.70 s | **11.72 s** (11.73, 11.72, 11.73) | 1.03 | 13.33 s |
| `TestSuite/Derived10` | 11.11 s (W6) | 13.33 s | 11.56 s | **11.45 s** (11.48, 11.50, 11.45) | 1.03 | 12.84 s |
| `TestSuite/Derived14` | 10.89 s (W6) | 13.07 s | 11.20 s | **11.15 s** (11.15, 11.31, 11.17) | 1.02 | 11.73 s |
| `Examples/ProofTree` | 9.81 s (W6) | 11.77 s | 9.75 s | **9.80 s** (9.80, 9.81, 9.84) | 1.00 | 10.05 s |
| `TestSuite/Problems` (M0) | 0.81 s (W6) | 0.97 s | 0.86 s | **0.88 s** (0.88, 0.89, 0.89) | 1.09 | 0.88 s |
| `TestSuite/ScopedProblems` (M0) | 1.39 s (W6) | 1.67 s | 1.11 s | **1.06 s** (1.06, 1.08, 1.09) | 0.76 | 1.10 s |
| `Solkey/TestSuite` (M0) | 10.83 s (W6) | 13.00 s | 6.77 s | **6.67 s** (6.87, 6.81, 6.67) | 0.62 | 7.06 s |
| `Examples/Benchmark/Syntax` (M0) | 1.41 s (W6) | 1.69 s | 1.61 s | **1.60 s** (1.63, 1.63, 1.60) | 1.13 | 1.92 s |
| `Evm/Examples` (M0) | 7.75 s (W6) | 9.30 s | 7.34 s | **7.33 s** (7.36, 7.33, 7.34) | 0.95 | 7.79 s |
| `Solkey/TestSuiteScoped` | 3.61 s (W8.2 base) | 4.33 s | — | **0.61 s** (0.65, 0.61, 0.64) | 0.17 | 0.57 s |
| `Examples/Tactics/Print` | 3.93 s (W8.2 base) | 4.72 s | — | **3.55 s** (3.55, 3.62, 3.57) | 0.90 | 3.71 s |
| `Calculus/SurfaceNotation` | 7.25 s (W8.2 merge) | 8.70 s | — | **7.19 s** (7.23, 7.19, 7.26) | 0.99 | 9.18 s |
| `Corpus/SolcStructs` | 1.22 s (W8.2 base) | 1.46 s | — | **1.02 s** (1.11, 1.02, 1.08) | 0.84 | 1.44 s |

**Gate passed**: every row within 1.2× of its baseline, and every run of
every row within it too.  Against the M0 limits (M0 + 20%):
`Benchmark/Syntax` 1.60 s against 1.44 s (over by 11%, 0.93 of 1.2× the
limit; scoped `sol{}` DAGs since W8.3, unchanged by W8.4), `Derived10`
11.45 s against 11.2 s (over by 2%, as since W7); `Solkey/TestSuite` 6.67 s
against 12.5 s, `Problems` 0.88 against 1.44, `ProofTree` 9.80 against
12.1, `Evm/Examples` 7.33 against 11.4.  The speed risks the plan named
("Speed risk") did not materialise: the import absorbing the scoped check
is 0.62 of its W6 time, the printers (`ProofTree`, `Tactics/Print`) 1.00
and 0.90.

**Checks** (this worktree): `node scripts/check-orphans.mjs` 314
reachable, 0 orphaned; `./scripts/check-doc-paths.sh` OK (eleven
ambiguous basenames, all resolving, as before); `./scripts/check-testsuite.sh`
stops at its input check against `../solkey` (its `TestSuite.sol` is
`4150e0a8…`, the fixture was imported from `2fe50a03…`), and passes with
`--solkey` at a checkout of solkey `1b4341a303` (`TestSuite.sol`
`2fe50a03…`) (trust: 22 modules clean; axioms:
`propext`, `Classical.choice`, `Quot.sound`; parity: 438 functions = 435
derived + 1 pending + 1 divergent + 1 excluded, 2 skipped).
`lean_build` of the default targets green (295 jobs); every timed copy
elaborated with no error.

### W8 result (W8.5 lane `docs`, 2026-10-11)

**Decision 11 is done.**  The user's call ("you can remove it",
2026-10-11) is carried out: `Surface.Stmt`, `Surface.Prog` and
`Surface.Fml` (the formula as written), the sixteen program-term families,
the surface `Arg`, `Surface.Premise` and the holes, `Surface.Problem.*`,
and `resolve`/`erase` between the surface and the scoped syntax are gone.
The elaborator emits `Stmt C Γ Γ'`/`Prog C Γ Γ'` and `Fml C Γ` directly,
and the printers print the scoped syntax.  `rg
'Surface\.(Stmt|Prog|Fml|Premise|Hole|Problem)' Solidity` is empty.
`Surface.Tm`, `Surface.MAddr`, `Surface.Upd` and `Surface.UpdElem` remain:
they are the closer's IR (decision 7), not the surface syntax.  Over the
wave, 90 files under `Solidity/` changed: 5,954 lines added and 8,374
deleted (`65d93a85..9d9fdf67`).

**Modules.**

| | Module | Step |
|---|---|---|
| removed | `Syntax/Resolve.lean` (`resolve`, `Prog.erase`, `Prog.resolveCheck`; `NCtx` and the binders' contexts moved to `Syntax/Elab.lean`) | W8.4 |
| added | `Syntax/Elab.lean`: the elaborator, from `Syntax.lean`, emitting the scoped syntax | W8.1 |
| added | `Calculus/PrintStmt.lean`: the printer of the scoped syntax and its name API (`idxName`, `SPiece`, `progPiecesS`, `framePiecesS`, `updShape`, `withPrinter`) | W8.2 `printers` |
| added | `Syntax/Inlined.lean`: a block printed with its calls inlined (`Prog.inlinedStr`, `Prog.inlinedShow`), in place of `Surface.Prog.inlined` | W8.3 (`Syntax/PrintInlined`, added by `ex-evm-bench`, was merged into it) |
| added | `Examples/Tactics/DlNotation.lean`: `Calculus/SurfaceNotation.lean`'s examples, which need the scoped reader | W8.2 `reader-tools` |

`Syntax.lean` keeps the grammar, the raw syntax, the contract and the
quoters' helpers.  `Semantics.lean`, `Semantics/Agree.lean`,
`Semantics/NoPanicOps.lean` and `Semantics/StateErase.lean` lost their
surface evaluators and lemmas but remain, with the state's operations.

**Pins that moved**, each lane's list collected.  The printed text of
every `#guard_msgs` pin is as before, except for the rows below that
change printed text (type suffixes, a hole's `Post C Γ` type,
`Semantics.State`, `‹Stmt.call …›`), the elaboration errors, and the
removed pins.

| Step | Pins | Change | Why |
|---|---|---|---|
| W8.1 | `Syntax/Quote.lean`'s pins | moved to `Syntax/Splice.lean`, same text | `Splice` now imports `Quote` |
| W8.1 | `Syntax/Splice.lean`: `tourCore`, `callsCore`, `Prog.show` | new constructor-tree `rfl` and print pins | the scoped elaborator equals `resolve` of the old one |
| W8.2 `obligations` | `solc_scoped_problems … main [decl]` (4 files) | command line `… [decl]`, pin unchanged | proposal 113 |
| W8.2 `obligations` | `solc_problems … legacy` lines (5 files) | removed | no legacy statement |
| W8.2 `obligations` | `LoopsImport`'s three `Surface.Prog.show N.f` | `#solc_show N.f`, same text | proposal 112 |
| W8.2 `obligations` | `Examples/Tactics/Spec`'s `Surface.Problem.ctor` erasure guard | a `Problem.text` pin of the deployment's obligation | `Surface.Problem` removed |
| W8.2 `reader-tools` | `Examples/Tactics/DlNotation.lean` (from `SurfaceNotation`): four pins, `Examples/Tactics/Surface.lean`: one | type suffix `: Surface.Fml X` → `: Fml X []` | a modality reads scoped |
| W8.2 `reader-tools` | `fun m φ => dl![m]{ … }`, the `trace_state` pin, the `ture` error | `NFml` → `Post StandardExample [.val .uint]`, `(φ : Post C)` → `(φ : Post C Γ)` | a scoped hole is a `Post C Γ` |
| W8.2 `reader-tools` | `fun φ => (⊨ φ) ∧ ∀ σ, NFml.holds σ φ` | `State` → `Semantics.State` | the module sees the scoped `State` |
| W8.3 (all lanes) | string pins `Surface.Prog.toStr (sol{…}) = "…"` (16 in `Benchmark/Syntax`, `ExampleNames`; more in `Checked`, `Operators`, `Chains/Memory`, `Calls`, …) | `Prog.toStr [] (sol{…})`, same strings | `Surface.Prog` removed |
| W8.3 | `Surface.Prog.inlined` pins (`Benchmark/{Syntax,Purchase}`, `Loops`, `CallOperands`) | `Prog.inlinedStr`/`inlinedShow`, same strings | proposal 116 |
| W8.3 | the run pins (`StorageSuite`, `StorageDelete`, `Memory`, `LedgerDelete`, `Values`, `CrossDomain`, `Tools`) | `Prog.runT`/`Prog.localAfterT`, same values | the scoped run tools |
| W8.3 `ex-evm-bench` | `ExampleNames`' constructor tree `sol{ uint idx = 1; … } = captured` | the scoped blocks compared | constructor-tree `rfl` pin |
| W8.3 `ex-calls-print` | `Loops`' four elaboration-error pins | the type is `Prog StandardExample [] [.val .uint]` | with `_`, a placeholder error comes first |
| W8.3 `ex-calls-print` | `Branch`'s `Prog.resolveCheck` guard | an `example` at `Prog StandardExample [] [.val .bool]` | the scoped elaborator accepting it is the check |
| W8.3 `ex-calls-print` | `Print`'s `stepsShowOf`/`headPremise` | no context argument | formulas written with their `∀`s |
| W8.4 | `Syntax/Splice.lean`'s string pins, constructor trees, inlined pin | `Prog.toStr []`, scoped trees, `Prog.inlinedStr`; same strings | `Surface.Prog` removed |
| W8.4 | `Syntax/Splice.lean`'s three hand-built `resolveCheck` guards | the elaborator's own errors on `sol{}` text: `unknown name x`, `a number where a bool is expected`, `a bool where a uint is expected`, `unknown name y` | proposal 126: `resolve`'s messages cannot be reached from text |
| W8.4 | `Examples/Tools.lean`'s `functionCallArgCapture` | `‹Surface.Stmt.call f args hsep ret body›` → `‹Stmt.call f args ret body›` | proposals 107, 118 |
| W8.4 | `DlNotation`'s two `where` pins | type suffix `Fml StandardExample []`, same text | proposal 120 |
| W8.4 | `Calculus/Print.lean`'s `legacyShow` pin, `Examples/Tactics/Spec.lean`'s two `sameAs` guards | removed | what they compared against is gone |

**Follow-ups.**

- *The SolKey reader* (side-projects `lean/solkey`) still matches the
  surface constructors after `Delab.tr`.  Its port to the scoped families
  goes through `Calculus/PrintStmt.lean`'s name API (`idxName`, `SPiece`,
  `progPiecesS`, `framePiecesS`, `updShape`, `withPrinter`).  Until then
  its require stays at the tag `w8-pre-delete` (`f16586b1`), and at the
  merge into `master` it can point back to `../../../solidity-lean` only
  once the port builds.
  *Superseded by the W8 reader port record: ported; the require was a
  path to this worktree, not the tag.*
- *Optional*: rename the IR namespace `Surface.Tm`/`Surface.MAddr`/
  `Surface.Upd`/`Surface.UpdElem` (2,235 occurrences in 45 files under
  `Solidity/`) to `NFml`, so that `Surface` no longer names anything.
  This is a mechanical rename with pins (`Delab.tr`'s escapes
  `‹Solidity.Surface.…›`, `#check_rule_text`'s roots) and a full rebuild.
  It needs the speed warning of `AGENTS.md`, but changes no
  representation.
- The `(sol{…} : Prog C [] _)` ascriptions in about 18 example files and
  the proposal 117 workarounds in `Evm/Examples.lean` and
  `Examples/Tactics/TryCatch.lean` (W8.4 "Left") are harmless and stay
  as they are.

**Docstrings.**  A scan of `Solidity/`, `AGENTS.md`, `.claude/` and
`docs/` (this record aside) for the surface names (`Surface.Stmt`,
`Surface.Prog`, `Surface.Fml`, `Surface.Premise`, `Surface.Problem`,
`Syntax/Resolve`, `Prog.resolve`, a bare `resolve`, `resolveCheck`, `defineCore`), for "as
written (`Surface.…`)", and for the identifiers W8.4 deleted
(`expandBody`, `copyDecls`, `withErased`, `legacyShow`, `specParts`,
`scopedOf`, `deployRunS`, …) finds nothing left: W8.4 and its review
(`9d9fdf67`) already rewrote them.  No Lean file is edited here.  The
remaining "as written" in Lean docstrings describe raw text (a term or
formula read by name, `Calculus/SurfaceNotation.lean`) or a printed block,
not the removed syntax.  The "today's" docstrings name the closer's IR,
which stays ("What is left").  `AGENTS.md`'s layering line now says that
`Syntax.lean` holds the grammar and raw syntax, that `Syntax/Elab.lean`
elaborates it, and that the SolKey reader's require is pinned at
`w8-pre-delete`.  `docs/README.md`'s row for this record mentions W8.

**Checks** (lane `docs`, no Lean): `./scripts/check-doc-paths.sh` passes.

### W8.5 lane `review` record (2026-10-11, branch `w8-w85gatedocsreview-review`)

The read-only review of W8 (AGENTS.md's milestone pass), on `intrinsic` at
`9d9fdf67`, with no Lean server: a finder and a skeptic per area, against
the code before W8 (`30611d7c`, `575cfba7^`) where a check compares.  No
Lean file was edited and no pin moved.

**Checked, no defect.**
- *Elaborator.*  Since W8.1's dump, `Syntax/Elab.lean` has changed only in
  error texts (`Surface.primName p` is `p.toStr`, the same string),
  docstrings, the moved `NCtx`/`NCtx.find` (texts as `resolve`'s) and the
  deleted erasing entry points; no capture, `freshCapture` or raw pass
  changed.  W8.2's `obligations` lane compared the direct scoped import
  with the baseline's resolved hashes (465 programs, byte for byte), so
  capture order and fresh numbering stand as the W8.1 dump left them.
- *`CallRet.mem`.*  `elabCallRet` builds it in the frame (`[.mem R] ++ ps`,
  names `r :: as.names`, matching `Γf = Γr ++ Γp`, newest first), with
  `defaultOkS` checked; the caller binds it at `.here` of
  `(r, .mem R) :: Γs` (`elabMemCall`), where `CallRet.outNames` leaves it.
- *Printers.*  `PrintStmt`'s argument positions (`Prog.cons`, `Frames.*`,
  `Upd.*`, `Fml.bind`/`modal`/`all`, `Stmt.call`, `CallRet.*`) match the
  constructors; `.there` and `up` move down the stack, a schema index under
  `.there` prints as itself, `Frames.pop`/`drop` and `Upd.pop`/`drop` keep
  the names they keep, a hidden binder pushes its name.
- *Deletions.*  No `Surface` program family is left in `Solidity/`
  (`Surface.Tm`/`UpdElem`/`Upd` are the closer's IR, decision 7).

**Confirmed defects** (not fixed: the lane is read-only).
1. **A chain line after `whileUnwind` cannot be written.**
   `Calculus/Chains.lean:144` (`Prog.keyStrs`) flattens a `Stmt.block` only
   at the top of a block; nested in a branch it prints braced
   (`Syntax/Scoped.lean:540`).  `whileUnwind` leaves one there
   (`Calculus/Blocks.lean:280`: `if (c) { {body} while … }`), while the
   elaborator never emits `Stmt.block` (`.block b => elabBranch b`) and the
   printer flattens it (`PrintStmt`'s `stmtPiecesS`).  So the line `#chain`
   writes keys flat and the computed one braced, and `sol_chain` does not
   reach it.  `erasedQuoted` matched it (`Stmt.erase` flattened a block at
   every depth).  No pin covers a chain through a loop.  Fix: flatten
   blocks in branches in the key too.
2. `docs/intrinsic.md:24` and `:29` ("What changed") still say the
   elaborator emits `Surface.Stmt`, `resolve` scopes it, and `Surface.Fml`
   is `dl!{}`'s text.
3. `docs/kernel-port.md:178`: "`resolve` reads it back as the closed frame"
   (the elaborator builds the frame).
4. `Examples/Tactics/Sequents.lean:7`: "its erasure against the line read
   as today's"; `show sequent!` compares the printed lines (proposal 119).
5. `Calculus/Chains.lean:114` (`LineQ.erased`) and `:229`: what is called
   the line's erasure is its key (`Fml.lineKey`), the erasure only where
   the line has no modality.

**Fixed** (same branch, after the review): 1. `Stmt.keyStr`
(`Calculus/Chains.lean`) prints a branch's, a loop body's and a `try`
clause's statements by `Prog.keyStrs`, so the key flattens a block at every
depth; `loopChain` (`Examples/Tactics/Chains.lean`) pins a chain through
`whileUnwind`.  2–5: the texts reworded.  No other pin moved.

### W8 W8.5 gate, docs, review merge (2026-10-11)

`w8-w85gatedocsreview-gate`, `-docs` and `-review` merged into
`intrinsic` in that order.  Conflicts were textual only, in this record and
`docs/kernel-port.md`: "What changed"'s Syntax and Formulas rows and the
callee row of `kernel-port.md` take both lanes' wording; the milestones'
W8 and `left` rows are the docs lane's (proposals 95–105 are approved);
the three lane records are kept in full.  None of the lanes proposed a
decision, so none is renumbered.  The review's defect 1 (the chain key
after `whileUnwind`) is fixed on its branch and pinned (`loopChain`).

**Checks** (merged tree): `lean_build` green with `SolidityCorpus` and
`SolkeyTestSuite` added to the default targets for the run (328 jobs, no
error; `lakefile.toml` reverted); `dups.py` lists only its known false
positives (`as`, `delabFml`, `delabProves`); `node
scripts/check-orphans.mjs` 314 reachable, the one orphan the git-excluded
`Solidity/Scratch/ElabDump.lean`; `./scripts/check-doc-paths.sh` OK;
`./scripts/check-rule-text.sh` passes.  No `.lean` file changed in the
merge, so the gate lane's table stands.  The three worktrees are removed;
their branches stay.

### W8 close-out (2026-10-11, on `intrinsic` at `f36fd067`)

**Decision 11 resolved.**  No Lean file names `Surface.Stmt`,
`Surface.Prog` or `Surface.Fml` (`rg 'Surface\.(Stmt|Prog|Fml)' Solidity`
is empty; only this record and its history do).  What still lives under
`Surface` is the closer's IR, kept by decision 7, not a dead family:
`Surface.Tm`, `Surface.MAddr`, `Surface.Upd`, `Surface.UpdElem`
(`Update.lean`, read by `NFml` and the rewrites; the optional rename to
`NFml` is in "What is left") and two meta helpers, `Surface.elemTy`
(`Calculus/SurfaceNotation.lean`) and `Surface.cmpParts?`
(`Calculus/RuleSyntax.lean`, `Calculus/PrintStmt.lean`).  The modules
`Calculus/Surface.lean` (the `open scoped Solidity.Scoped` switch),
`Calculus/SurfaceNotation.lean` and `Calculus/SurfaceSpec.lean` keep their
names.

**Checks.**  `lean_build` with `SolidityCorpus` and `SolkeyTestSuite` added
to the default targets for the run: green, 328 jobs, no module
OOM-killed (`lakefile.toml` reverted).  `dups.py`: only `as`, `delabFml`,
`delabProves`.  `node scripts/check-orphans.mjs`: 314 reachable, the one
orphan the git-excluded `Solidity/Scratch/ElabDump.lean`.
`./scripts/check-doc-paths.sh` OK (eleven ambiguous basenames, all
resolving); `./scripts/check-rule-text.sh` passes.  No `.lean` file
changed in the close-out; `AGENTS.md` and `docs/module-map.md` lose their
last mention of the surface statement.

**Gate**, re-timed as in "Gates" (each module copied under
`Solidity/Scratch/`, opened in a fresh worker through the MCP, every import
built, `/proc` sampled every 20 ms, the worker killed after each run; end of
work, the minimum of three interleaved passes; CPU the minimum of the
runs).  This lane the only Lean agent; load (1 min) 1.6 falling to 0.7,
cgroup 8.6 GB.  Driver `scratchpad/w8c.sh` (`w85.sh` on this worktree),
results under `w8c_*` in `scratchpad/results.txt`.

| Module | baseline | gate (1.2×) | W8.5 | **W8 close-out** (three runs) | ratio | CPU |
|---|---|---|---|---|---|---|
| `TestSuite/Derived6` | 11.42 s (W6) | 13.70 s | 11.72 s | **11.75 s** (12.00, 11.75, 11.77) | 1.03 | 13.26 s |
| `TestSuite/Derived10` | 11.11 s (W6) | 13.33 s | 11.45 s | **11.51 s** (11.87, 11.55, 11.51) | 1.04 | 13.12 s |
| `TestSuite/Derived14` | 10.89 s (W6) | 13.07 s | 11.15 s | **11.23 s** (11.54, 11.29, 11.23) | 1.03 | 11.94 s |
| `Examples/ProofTree` | 9.81 s (W6) | 11.77 s | 9.80 s | **9.80 s** (10.07, 9.80, 9.84) | 1.00 | 10.01 s |
| `TestSuite/Problems` (M0) | 0.81 s (W6) | 0.97 s | 0.88 s | **0.86 s** (0.89, 0.86, 0.92) | 1.06 | 0.89 s |
| `TestSuite/ScopedProblems` (M0) | 1.39 s (W6) | 1.67 s | 1.06 s | **1.06 s** (1.10, 1.09, 1.06) | 0.76 | 1.08 s |
| `Solkey/TestSuite` (M0) | 10.83 s (W6) | 13.00 s | 6.67 s | **6.73 s** (6.83, 6.73, 6.75) | 0.62 | 7.12 s |
| `Examples/Benchmark/Syntax` (M0) | 1.41 s (W6) | 1.69 s | 1.60 s | **1.62 s** (1.64, 1.67, 1.62) | 1.15 | 1.96 s |
| `Evm/Examples` (M0) | 7.75 s (W6) | 9.30 s | 7.33 s | **7.27 s** (7.43, 7.33, 7.27) | 0.94 | 7.67 s |
| `Solkey/TestSuiteScoped` | 3.61 s (W8.2 base) | 4.33 s | 0.61 s | **0.61 s** (0.61, 0.61, 0.61) | 0.17 | 0.55 s |
| `Examples/Tactics/Print` | 3.93 s (W8.2 base) | 4.72 s | 3.55 s | **3.57 s** (3.62, 3.57, 3.66) | 0.91 | 3.73 s |
| `Calculus/SurfaceNotation` | 7.25 s (W8.2 merge) | 8.70 s | 7.19 s | **7.28 s** (7.33, 7.33, 7.28) | 1.00 | 9.27 s |
| `Corpus/SolcStructs` | 1.22 s (W8.2 base) | 1.46 s | 1.02 s | **1.04 s** (1.06, 1.04, 1.09) | 0.85 | 1.41 s |

**Gate passed**: every row, and every run of every row, within 1.2× of its
baseline; every row within 1% of W8.5 but `Problems`/`Evm/Examples`
(faster) and `Derived10` (+0.5%).  Against the M0 limits (M0 + 20%), as at
W8.5: `Benchmark/Syntax` 1.62 s against 1.44 s (over by 12%; scoped
`sol{}` DAGs since W8.3), `Derived10` 11.51 s against 11.2 s (over by 3%,
as since W7); the rest under theirs.

### W8 reader port record (2026-10-11, side-projects `intrinsic` at `99c6477`)

The SolKey reader (side-projects `lean/solkey`, branch `intrinsic`,
worktree `../side-projects-intrinsic`) is ported to the scoped syntax.
Its require already pointed at this worktree (`../../../solidity-lean-intrinsic`,
a path, not the tag), so it did not build after W8.4; it now builds
against `intrinsic` at `9a2c3914`.

- **The walk** (`SolKey/Corresp/LeanShape.lean`) reads the scoped
  constructors themselves (`Stmt.*`, `Simple`/`Val`/`SPath`/`Loc`/`MPath`/
  `MLoc`/`OpLoc`/`Src`/`MSrc`/`ARhs`/`MRhs`/`NewLhs`, `SHole.fill`/
  `MHole.fill`/`VHole.fill`/`NewLhs.fill`, `Premise.*`): names from the
  binders, a position from the stack of the `Var`s the premise declared
  (`Delab.stmtOutNames`), `.there`, `up` and `Prog.wk up` (`Delab.wkUp?`)
  transparent, `Ext`/`Thin` invisible, a nested `{ … }` its statements,
  as `Calculus/PrintStmt.lean` prints them.  Its tables (roles, heads,
  coercions, side-condition predicates) are keyed by the scoped names;
  `Delab.legacyName?` is no longer used.  Only terms, updates and
  formulas go through `Delab.tr`/`updParts`/`updList`.
- **Lowerings.**  `Delab.tr` erases `se.lower` to `Term.pv (Var.user "se")`
  (`Delab.loweredVar?`, since W8.4); the walk reads a `Var.user` naming a
  schema variable of the constructor back as `lowerV`/`lowerP` of it, the
  shape the old `Surface.Simple.lower` gave.
- **Imports unchanged**: `Calculus/Rules`, `Calculus/DelabErase`,
  `Calculus/KeyTaclets`.  It uses `DelabErase`'s helpers (`stmtOutNames`,
  `wkUp?`, `isUp`, `isCtx`, `tr`, `updParts`, `updList`, `withTwins`) and
  not `PrintStmt`'s name API, which would add a module to its dependency
  surface for nothing it needs.
- **Result**: `Corresp/Proved.lean` regenerated (GenProved's `main` run
  from a scratch module) is **byte-identical** to the committed one: no row
  moved, every docstring's printed shape is the same (206 theorems, 170
  `Agrees`, 36 `FindAgrees`; `tryCallNoCallbackBox` still `differs`).  MCP
  `lean_build` of the reader's default target passes (`Proved` 14 s); the
  axiom probe of `scripts/check-axioms.sh`, run from a scratch module:
  "checked 206 correspondence theorems", none on `sorryAx`/`ofReduceBool`/
  `trustCompiler`.  Not run: the `keycheck` executable (not a default
  target) and the VS Code extension's tests.
- **Docs**: the reader's `AGENTS.md` (intro, import paragraph, a W8
  paragraph); this repository's `AGENTS.md` no longer says the reader is
  pinned at `w8-pre-delete`.

### W8 final-review fixes (2026-10-11, on `intrinsic`)

The confirmed findings of the final review, applied.

- **Dead code removed**: in `Syntax/Elab.lean` `NCtx.ctx_append`/
  `names_append`, `Binders.nctx` (with `nctx_ctx`/`nctx_names`),
  `Binders.toList_snocAll`/`toList_ofList`, `CodeBinder.nctx` (with its
  lemmas) and `CodeBinder.toOption` (no reader either: the review's second
  finding listed it as used, but only `Option.toOption` of `Except` is);
  `Prog.ext_nil`/`ext_cons` (`Syntax/Scoped.lean`), `Delab.twin?`
  (`Calculus/DelabErase.lean`), `NFml.isSlot`
  (`Calculus/SurfaceNotation.lean`), `elabDlC` (`Calculus/Notation.lean`),
  `Tools.elabFormula` (`Tools/Common.lean`), `Fml.not_valid_of_eval3`
  (`Tools/Counterexample.lean`), the `hsep` branch of
  `delabTacletBinders` (`Calculus/RuleKit.lean`), the `cov` disjunct of
  `branchLabel` (`Calculus/TreeData.lean`), and `resolveRule`'s duplicate
  candidate (`Tools/Taclet.lean`).
- **Left, with the reason**: `Prog.localAfterT` and
  `Contract.deployRun` (`Tools/Run.lean`) are not dead, contrary to the
  finding: `Examples/Tactics/StorageSuite.lean`'s `#eval`s read
  `localAfterT`, and `Examples/Tactics/Constructors.lean`'s `deployValue`
  is `Mini.deployRun … = .error .revert := rfl`.  `deployReport` keeps its
  own run, since it prints the typed end state (balance and storage), which
  `deployRun`'s untyped result does not carry; only the `#deploy`
  docstring changes ("in the typed run").
- **`solc_scoped` removed** (`elabSolcScoped`, its paragraph in
  `Frontend/Import.lean`, its pins in `Solkey/Constructors.lean` ×4 and
  `Examples/Tactics/LoopsImport.lean`, and `Solkey/TestSuiteScoped.lean`
  with its import in `SolkeyTestSuite.lean`): every elaborated row is
  declared through `Prog.define`, so the check could not fail, and the
  count it pinned is the import report's.  The gate row
  `Solkey/TestSuiteScoped` goes with the module.
- **`solc_problems` removed** (its syntax, `elabSolcProblems`, and
  `declareObligations`' `table` parameter with the constants-of-their-own
  branch): no file ran it since W8.2.  `Frontend/Problems.lean`'s docstring
  is rewritten around `solc_scoped_problems`; its two messages now name
  `solc_scoped_problems` (no pin reads them).  The current-behaviour
  mentions follow (`Frontend/Import.lean`, `Calculus/Problem.lean`,
  `Solkey/Constructors.lean`, `scripts/solkey-port.mjs`,
  `docs/testsuite-proofs.md`'s parameters paragraph, the module map); the
  dated records keep the name of their date.
- **`sol_symex`/`sol_step` on a goal that is not `⊨ φ`** now fail with
  "expected a goal `⊨ φ`" and the goal, not "Unexpected syntax".  The
  `negativeKey` pin (`Examples/Tactics/Decide.lean`) pins only the
  elaboration refusal (`#check dl!{ … }`).
- **The memory conditional** (`T memory m = c ? a : b;`): the documentation
  fix, not the behaviour change.  `mv1` stays bound to the index-free branch
  before the branches; that read cannot revert on a set local, but an unset
  one (only a hidden binder holds one, decision 17') reverts where solc reads
  only the branch taken.  Recorded in `docs/solc-alignment.md`'s row, the
  `hoist` and `MPath.indexFree` docstrings and the `Syntax/Splice.lean` pin's
  comment.  The alternative (a fresh default object whenever `defaultOkS`)
  would add an object solc does not allocate on every such conditional and
  move the `Syntax/Splice.lean` and `Examples/Tactics/Branch.lean` pins, so
  it is left as an option.
- **`#proof_node`'s tactics** stay as the node elaborated them
  (`apply Proves.update (Taclet.toStep .localValueAssign); apply
  Proves.updIntro`), where master printed the walk text `apply update
  .localValueAssign`: a node's tactics are the terms it ran.  The module
  docstring of `Calculus/ProofTree.lean` now says so, and
  `Examples/ProofTree.lean`'s header records the change from master.
- **Docs**: `Syntax.lean` (a memory return declared by the call's frame,
  `CallRet.mem`), `Calculus/RuleSyntax.lean`'s schema-variable table (the
  scoped sorts, `Stmt.call f args ret body`), `Calculus/SurfaceNotation.lean`
  (`NFml.Post C`, `Calculus/RewriteChains.lean`), `Syntax/Scoped.lean`'s
  example section, `Solkey/Constructors.lean`; `docs/kernel-port.md`
  (`ppTupleCallS`), `docs/lean-key-rule-map.md` (`functionBodyExpand`'s
  names), `docs/loops.md` (`Val.eval_lower`), `docs/solkey-feedback.md`
  (`Args.separated`), `docs/testsuite-proofs.md`'s introduction; here,
  decisions 46–48 superseded, the W8.4 record amended, the reader's
  "Not in scope" and follow-up items superseded, the `left` row.

**Checks.**  `lean_build` with `SolidityCorpus` and `SolkeyTestSuite` added
to the default targets for the run: green, 327 jobs (one module fewer), no
module OOM-killed (`lakefile.toml` reverted).  `dups.py`: only `as`,
`delabFml`, `delabProves`.  `node scripts/check-orphans.mjs`: 313
reachable, the one orphan the git-excluded `Solidity/Scratch/ElabDump.lean`.
`./scripts/check-doc-paths.sh` OK; `./scripts/check-rule-text.sh` passes.

**Gate**, re-timed as in the W8 close-out (driver `scratchpad/w8f.sh`,
results under `w8f_*` in `scratchpad/results.txt`); this lane the only Lean
agent, load (1 min) 4.4 falling to 0.9 after the build, cgroup 8.5 GB.

| Module | baseline | gate (1.2×) | W8 close-out | **final-review fixes** (three runs) | ratio | CPU |
|---|---|---|---|---|---|---|
| `TestSuite/Derived6` | 11.42 s (W6) | 13.70 s | 11.75 s | **11.64 s** (11.70, 11.64, 11.69) | 1.02 | 13.08 s |
| `TestSuite/Derived10` | 11.11 s (W6) | 13.33 s | 11.51 s | **11.46 s** (11.51, 11.46, 11.49) | 1.03 | 12.90 s |
| `TestSuite/Derived14` | 10.89 s (W6) | 13.07 s | 11.23 s | **11.15 s** (11.15, 11.18, 11.21) | 1.02 | 11.68 s |
| `Examples/ProofTree` | 9.81 s (W6) | 11.77 s | 9.80 s | **9.79 s** (9.80, 9.86, 9.79) | 1.00 | 10.02 s |
| `TestSuite/Problems` (M0) | 0.81 s (W6) | 0.97 s | 0.86 s | **0.87 s** (0.90, 0.88, 0.87) | 1.07 | 0.90 s |
| `TestSuite/ScopedProblems` (M0) | 1.39 s (W6) | 1.67 s | 1.06 s | **1.04 s** (1.04, 1.09, 1.09) | 0.75 | 1.07 s |
| `Solkey/TestSuite` (M0) | 10.83 s (W6) | 13.00 s | 6.73 s | **6.73 s** (6.79, 6.75, 6.73) | 0.62 | 7.11 s |
| `Examples/Benchmark/Syntax` (M0) | 1.41 s (W6) | 1.69 s | 1.62 s | **1.58 s** (1.61, 1.63, 1.58) | 1.12 | 1.90 s |
| `Evm/Examples` (M0) | 7.75 s (W6) | 9.30 s | 7.27 s | **7.31 s** (7.34, 7.38, 7.31) | 0.94 | 7.76 s |
| `Solkey/TestSuiteScoped` | 3.61 s (W8.2 base) | 4.33 s | 0.61 s | removed | — | — |
| `Examples/Tactics/Print` | 3.93 s (W8.2 base) | 4.72 s | 3.57 s | **3.55 s** (3.61, 3.56, 3.55) | 0.90 | 3.68 s |
| `Calculus/SurfaceNotation` | 7.25 s (W8.2 merge) | 8.70 s | 7.28 s | **7.23 s** (7.25, 7.23, 7.29) | 1.00 | 9.15 s |
| `Corpus/SolcStructs` | 1.22 s (W8.2 base) | 1.46 s | 1.04 s | **1.02 s** (1.05, 1.02, 1.08) | 0.84 | 1.44 s |

## W9 plan (the IR's removal)

Asked by the user on 2026-10-11 ("full port, in waves"): remove the
closer's untyped IR.  **Two IRs.**  The *syntax* IR is `NFml`, its terms
`Surface.Tm`/`MAddr`/`Upd`/`UpdElem` and `Fml.erase`/`Tm.erase` (about 3,600
occurrences in 80 files).  W9.1–W9.5 remove it.  The *state* IR is
`Env`/`EState`/`State.erase`: the scoped `holds` reads it
(`Calculus/Logic.lean`), and so do the run invariants (`RunInv.Holds`).
W9.6 is a proposal of its own.  `Semantics.State`, the symbols
`Op0`–`Op3` with their `eval`/`denote` (decision 83), and the value-level
erasure (`PrimTy.erase`, `Storage.erase`, `Heap.erase`) stay.

**Do positions slow kernel evaluation?**  No.  Both routes key a local by a
`Var` in an association list.  A position's key is `slotVar k = .fresh "#" k`;
the extra cost is `Idx.toNatR`'s walk, which the recursor form keeps cheap
(G0: 0.8× on symex).  At W7 `w7-closer`, moving the atoms to positions left
`Tactics/Decide` at 1.04× with the machine 2–4% slower.  Positions also
remove `Fml.closeErase`'s `Nodup`/`Avoids` checks and the string-keyed
`decide +kernel` of `NFml.inL`.

**Gates**: 1.2× the W7 merge table.

| Row | Gate |
|---|---|
| `Derived1`–`14` (sum) | 237.8 s |
| `Derived7` | 61.7 s |
| `Tactics/Decide` | 45.0 s |
| `ProofTree` | 11.7 s |
| `Chains/Storage` | 9.0 s |
| `ChainRewrites` | 8.2 s |
| `ChainRewritesOpen` | 4.1 s |
| `Solkey/TestSuite` | 13.2 s |

**Waves**: at most two Lean-heavy lanes at once, each in its own worktree.

| Wave | Lanes | Work | Rows at risk |
|---|---|---|---|
| W9.0 | spikes (scratch) | the scoped leaf closer on `Derived7`'s leaves against `Fml.closeErase` + `NFml.Derive.residue`; `ChainRewrites` with scoped lines past the program | — |
| W9.1 | `terms` ‖ `print` | `TermTacletS` on `Tm C Γ .val` (solkey's names, `tm{}`), `Tm.Theq`, sort-generic `Tm.reads`/`litVarsS`/`beqR` (recursor + `match` twin), `holds_eqD_iff` on `holds`; `DelabErase`/`RuleSyntax` print scoped `Tm`/`Upd`/`Fml` from a name stack, twin-checked, no pin moves | none |
| W9.2 | `decide` ‖ `rw` | `Tm.toLS` sound over `RelU` directly; `sameAt`/`allocPairS?` by `Tm.beqR`; `LFml.closeS` with a layout from a scoped `wt(storage)` premise (proposal 100); scoped `sol_reduce`/`sol_reads`/`sol_decide_*`; `SeqRewrite`, `Walk.rwTheory`, `Proves.updRw`, `FmlRw.lawEq`/`lawUpd`, `UpdateRules.rewrite` read `TermTacletS` | `Tactics/Decide` |
| W9.3 | `walk` ‖ `close` | `Calculus/LeafDerive.lean`: a leaf closes by `Fml.reduceS` + `LFml.closeS`, sound by `Proves.closeHolds`/`Fml.toLSM_sound`; a scoped `seqUpd`, ground split, `pick`/`Fml.stripN`; the replays re-derived (`Derived1`, `7`, `12`, `LoopsImport`, `Benchmark/Mapping`, `Purchase`, `Tactics/Constructors`, `Solkey/Constructors`, `TestSuite/Suggestions`, `Frontend/Problems`); `Calculus/CloseScoped.lean` (`sol_close` over `holds`/`Tm.eval`/`Upd.apply`, symbol lemmas split out to `Calculus/CloseLemmas.lean`) | Derived rows, `ProofTree`, `Solkey/TestSuite` |
| W9.4 | `chains` ‖ `fronts` | lines past the program scoped (decision 101's list: `simplifyUpdate` dropping unread locals with their binders, a merge across a hidden binder, the laws, `~~>`/`calc`, a positional `lineKey`; `Fml.ViaE`, `NFml.Via`, `scopedPast` go); `Tools/Inspect`, `Counterexample`, `Problem`/`Corpus/Imported`/`TestSuite/Problems` (`NFml.wt` scoped), `SurfaceSpec`/`NotationResolve`, `dl!{}` with no modality reads `Fml C []`, `RuleSyntax`'s sequents scoped | `Chains/*`, `ChainRewrites*` |
| W9.5 | on master | delete `NFml`, `Surface.*` terms, the erasure, `HoldsErase`, `CloseErase`, `Close`, `NFmlLogic`, `NFmlDerive`, `NFmlUpdateRules`, `NFmlQuote`, `StateParts`, `Rewrite`, `Proves.close`, `Atom.name`; `TermTacletS` → `TermTaclet`; the SolKey reader ported (asked first: it reads the erased syntax) | all |
| W9.6 | proposal | the state IR: `Tm.eval` over `State C Γ`, the Sound* files against `TRun.*`, the run invariants over `State` (12–20k lines of proof) | — |

**Fallbacks.**  If a Derived row fails W9.3's gate, that leaf class keeps
`Fml.closeErase` + `NFml.Derive` and W9.5 deletes the rest.  If
`ChainRewrites` fails W9.4's, the links past the program stay on the IR, and
`NFml` survives only as `RewriteChains`' line type.  W9.6 is judged
infeasible within this plan.  Its fallback keeps `EState` as the terms'
state (decisions 40, 83) and deletes only `Erased.lean`'s program
evaluators and `StepErase`.

**Pins expected to move**: `ProofTree`'s residues (`rounds2`/`4`/`6`,
`pushes22`, `writes4`/`6`, `deletes10`) and `Dangling`'s four (W9.3); the
open `⟨ alice.age = 1; ⟩ true` leaf, which closes only if a Lean-only
clause "a typed storage has every root" is added; `CloseTests`; every
`#last_line`, `ChainRewrites`, `ChainNotation`, `Tactics/Chains` (W9.4);
and `DlNotation`'s types, now `Fml C []`.

### W9.1 `terms` record

Branch `w9-terms`, additive: nothing on the IR moved, no pin changed.

- **`Calculus/TermLib.lean`** (imports `Logic`, `Rules`, `TermTaclets`; no
  module imports it yet but `Solidity.lean`).  `TermTacletS` restates every
  `TermTaclet` constructor under its solkey name on `Tm C Γ .val`, in
  `tm{ … }`; `TermTacletS.findOnDelAtSave` as before; `TermTacletS.sound`
  over the scoped `Tm.denote` into `Tm.Theq` (with `refl`/`symm`/`trans`/
  `of_eq`), axioms `propext`, `Classical.choice`, `Quot.sound`.  The side
  conditions on scoped paths: `Tm.hasSeg`, `Tm.litInt?`, `Tm.shape?`,
  `Tm.diverges`, `Tm.divergesLen`, `Tm.eraseChecks`, `Tm.sameSegs` (by
  `Tm.beqR`), `Tm.extendsAny`/`Tm.extends`, `Tm.root?`, `Tm.shift?`,
  `Tm.svLit?`, `Tm.findLitBy`/`Tm.findLit?`, `Tm.KindFreeAt`, `SCtxS` with
  `fill`, each with its `_denote` lemma; every recursive one generic in the
  sort, so `by rfl` closes them on closed paths (pinned).
- **Sort-generic helpers** by the recursor, a `match` twin and a link
  theorem: `Tm.reads`/`readsM` (`Tm.reads_eq_readsM`; positions as `AnyIdx Γ`),
  `Tm.litVarsS`/`litVarsSM`, `Tm.beqR`/`beqM` (`Tm.beqR_eq_beqM`,
  `Tm.eq_of_beqR`, `Tm.beqR_self`, `Tm.beqR_iff`; sorts and symbols compared
  by `hbeqAt`: `Idx.hbeq`, `Op0.hbeq`–`Op3.hbeq`).  Each reduces by `rfl`
  in the kernel (pinned).  `Tm.isLitLikeS` already exists, non-recursive, in
  `Calculus/DecideScoped.lean`; a second one would clash with it once
  `DecideScoped` imports `TermLib`, so it was not restated (W9.2 may make it
  sort-generic in place).
- **`holds_eqD_iffS`** is in `Calculus/SoundLoops.lean`, beside the term
  bridge `Tm.denote_eval` it needs (`TermLib` sits below `SeqRewrite` and
  `DecideScoped`, which `SoundLoops` imports).
- **Notation.** `TermLib` adds a `tm{ … }` rule that reads the expected
  type (`tm_at%`): at `Tm C Γ s` the text's symbols become their `Tms`
  twins (`coreNames`), elsewhere it is the closer's term as before (and
  while the type is unknown, after postponing).  `delabTmS` prints a scoped
  term over schema variables back as `tm{ … }` through the closer's printers
  (`tmSurface`, the variables twinned at their closer types): the scoped
  rules print as `TermTaclet`'s do, escapes included (pinned at the end of
  the module).  Both are active only where `TermLib` is imported, so a
  module that imports it later (W9.2) may see a raw scoped `Tms` term in a
  message print as `tm{ … }`.
- **Rule map.** `docs/lean-key-rule-map.md`'s term-taclet table has a
  `TermTacletS` column.
- **Checks.** Per-file diagnostics clean (`TermLib`, `SoundLoops`);
  `lean_build` of the default targets; `check-orphans`, `check-doc-paths`.

### W9.0 spike record (2026-10-11, not committed)

**The leaf closer on the scoped leaf** (`Proves.closeHolds` + `Valid.of_reduceS`
+ `LFml.closeS`, walked by `Seq.run`), timed against the erased route
(`Fml.closeErase` + `NFml.Derive`):

| Row | Erased | Scoped | Ratio |
|---|---|---|---|
| `Derived7`, whole file | 49.79 s | 42.05 s | 0.84 |
| `Derived12`, whole file | 13.14 s | 11.24 s | 0.855 |

The compiled walk costs the same on both routes.  **Go for W9.3**, once
these leaf classes are closed scoped:
1. *The layout* (26 leaves in `Derived7`, 27 in `Derived12`).  `LFml.closeS`
   reads `[]` (`Calculus/DecideComplete.lean`).  Proposal 100: the layout
   comes from the scoped `wt(storage)` premise, and `Valid.of_reduceS` needs
   a `LayoutOk` premise for it.
2. *A parallel update of two elements that is not an allocation pair*
   (23 and 9 leaves; `{x := x+1 ‖ se := x}`).  The fragment refuses it
   (`Calculus/DecideScoped.lean`).  Read with both elements in the
   pre-state, it closes at 0.9×; the proof, a twin of `RelU.two`, is
   missing.
3. *A push alias* (`{storage := extend(a) ‖ sp := next(a)}`, 4 leaves):
   `pushAlias?` (`Calculus/NFmlDerive.lean`) has no scoped twin.
4. *`wt(storage)` under the parameters' `∀`*: the scoped `dropWt`.
5. Two more: the split refutation's ground test (`Seq.ground`,
   `Calculus/ProvesDerive.lean`; without it, up to 3× on split-heavy
   theorems), and the replays of the leaves the closer leaves open.

Decision 78's class (a value-typed hidden local read before its update)
does not occur in `Derived7` or `Derived12`.

**Chains past the program** (`Examples/ChainRewrites`): 6.74 s as is,
7.19 s with `sol_chain.scopedPast` on (1.07×, gate 8.2 s).  Go on speed,
but not on coverage.  Forced scoped, a link past the program fails at:
1. a merge across a hidden binder;
2. a merge that keeps a shadowed storage write (`Upd.mergeStL` drops it);
3. `simplifyUpdate` dropping an unread local with its binder;
4. `applyStorageBox` on `==` (the `defined(…)` conjuncts);
5. a law in an update's right-hand side (`lawUpd` is box-only);
6. the memory read laws;
7. `findMemberCons`'s side condition, which reads a position as a root
   name.

`~~>` past the program reads the erasure by design (`Fml.LeadsE`).  W9.4
ports these seven classes first, then re-times.
### W9.1 `print` record

Branch `w9-print`: the printers no longer read the erasure; no pin moved.

- **`Calculus/PrintTerm.lean`** (new, over `DelabErase`'s non-erasing
  helpers): a scoped term is read by its view (`viewTmS`): a schema
  variable, a local's name (`idxName`, moved here from `PrintStmt`; a
  lowered program schema variable is the local of its name), `net(x, a)`,
  `t⊕⊕`, or a symbol by its constructor (`Op2.find`) on its subterms, `up`s
  read through, computed (`whnf`) unless `pp.sol.reduce` is off.
  `ppTermS` … `ppMValS` restate `RuleSyntax.lean`'s `ppTerm` … `ppMVal`
  case for case on the view (the builders `lenTerms`, `elemTerm`,
  `dotTerm`, `allocTy?`, `termOpSym?` shared).  Updates by their pieces
  (`updPiecesS`: an element with the names its sides are read at, a
  declaration, a variable, a stuck part; pops and drops nothing), printed
  as `ppUpd` prints the erased list (`ppUpdPiecesS`, `updElemS`,
  `rhsElemS`).  `eqTmS` compares two terms read at two name stacks by their
  views (the erasure compared their erasures); `cmpPartsS` is
  `Surface.cmpParts?` on views.  The view's tags are the symbols `Op0`–`Op3`,
  which stay at W9.5 (not `Update.lean`'s `Term.find`, which goes).
- **Switched to it**: `PrintStmt` (`ppFmlS`'s equations, `defined`, `=`,
  comparisons and `{U}`, `Premise.update`/`cases`/`inv`); `Delab`'s
  sequent context (`hypsPartsS`: an update by `updHypS`, as `ppHyp?`
  prints one, a rule's update at a fixed modality when it has a schema
  variable, `updHasSchemaVar`); `Print` (`Tm.show`, `Upd.show` on
  `Tm.quote`/`Upd.quote`; `Upd.hasElem` for an update that prints as
  nothing; `Fml.eqDParts?` by `eqTmS`, now in `MetaM`; `↔` by the quoted
  formulas, as `PrintStmt`'s `iffPartsS` already did, decision 109).
  `withPrinter` builds the twins only under the twin check.
- **Kept, unchanged**: `Delab.tr`, `Env`, `loweredVar?`, `wkUp?`, `isUp`,
  `isCtx`, `unknownVar`, `stmtOutNames`, `withTwins`, `updParts`,
  `updList` (the SolKey reader's surface, and the twin check's).  Not
  switched: TermLib's `delabTmS` (`tm{ … }` of a scoped term over schema
  variables, printed as written through `tmSurface`'s twins of the
  closer's terms); its pins stay with it until W9.5 deletes the closer's
  printers.
- **Twin check.**  `pp.sol.twinCheck` (re-registered in `PrintStmt`, as at
  W8.2) prints every term and update, the `same term` and comparison
  choices of `eqDPartsS` and `Print`'s `Tm.show`/`Upd.show`/`sameAt`/`↔`
  both ways and throws on a difference.  A control (an `Fml.eq` on
  `Tm.app2 o x y`, `o` a variable symbol: `‹Tm.app2 o x y›` against the
  erasure's `‹Surface.Tm.app2 …›`) fails to print with it on.  Run with it
  on, every pin passing (copies under `Solidity/Scratch/`, deleted):
  `Examples/{ProofTree,ChainRewrites,ChainRewritesOpen,ChainNotation,Tools,Notation,Verify}`,
  `Examples/Tactics/{Print,DlNotation,UpdateRules,ProofTree,Symex,Step,Loops,Chains,Sequents,Surface,Notation,Branch,Checked,Dangling,Derive,Revert,StorageDelete,StorageSuite,TryCatch,Payment,Values,LedgerDelete,Tour,Spec,Constructors,CallOperands,UpdRulesScoped,Calls,Memory,Decide}`,
  `Solkey/Constructors`, `Theorems`, and `Calculus/Print`'s own pins.
  `Examples/Tactics/{Rules,TermTaclets}` and `Calculus/KeyNotation` do not
  import the printers.
- **Timing** (the end-of-work method: each file copied under
  `Solidity/Scratch/`, a fresh worker through the MCP, `/proc` sampled every
  20 ms; base `f6adf036` in a second worktree filled from the artifact
  cache, runs interleaved; load 0.7–1.3, cgroup 13–16 GB, another Lean lane
  running):

  | Module | base | W9.1 `print` | ratio | gate |
  |---|---|---|---|---|
  | `Examples/ProofTree` | 9.73 s (9.73, 9.80, 9.90, 9.80) | 9.77 s (10.04, 10.03, 9.87, 9.77) | 1.00 | 11.7 s |
  | `Examples/Tactics/Print` | 3.55 s (3.57, 3.55) | 3.55 s (3.58, 3.55) | 1.00 | 1.2× the base |

  Printing is a small part of either file: a `#proof_tree` command's
  elaboration is under 30 ms in the profiler.
- **Checks.**  Per-file diagnostics clean (`PrintTerm`, `PrintStmt`,
  `Delab`, `Print`, the pin files above); `lean_build` of the default
  targets; `check-orphans`, `check-doc-paths`.

### W9.2 `rw` record

Branch `w9-rw`: the scoped rewrites read the scoped term taclets
(`TermTacletS`) and no longer erase a goal's terms; no pin moved.

- **The rewrite's pair is scoped.**  `q : Tm C [] .val × Tm C [] .val`, two
  closed terms at the empty scope, everywhere the scoped calculus rewrites:
  `Tm.sideC`, `Fml.rwEqC`, `Hyps.rwEqC`, `Tm.pickC`/`Tm.rwC`/`Rhs.rwC`/
  `UpdElem.rwC`/`Upd.rwC`, `Proves.rewrite` (`hq : Tm.Theq q.1 q.2`),
  `Proves.updRw` (`hq : Tm.EvalRefines q.1 q.2`), `Proves.rewrite'`/`updRw'`,
  `SolkeyProves`, `ProvesSound`.  A term of the sequent fires where it has no
  local and reads `q.1` at the empty scope (`Tm.closedAs`: `Tm.toNil?`, then
  `Tm.beqR`); it becomes `q.2` read at its scope (`Tm.ofNil`).  Soundness
  through `Tm.eval_toNilS`/`Tm.denote_toNilS` and
  `Tm.eval_ofNil`/`Tm.denote_ofNil` over the state's global part at the empty
  scope (`EState.nil`, `EState.nil_eq_of_glob`); `Tm.EvalRefines.of_theq`
  (a Theory equation onto a literal, `Tm.isLit`) by the term bridge
  `Tm.denote_eval`, moved from `Calculus/SoundLoops.lean` into
  `Calculus/SeqRewrite.lean`.  `Tm.denote_toNil`/`Tm.eval_toNil` (a closed
  term as its erasure) are gone.
- **Modules.**  The update rewrite (`Tm.toNil?` … `holds_upd_rwC`) moved from
  `Calculus/Graft.lean` to `Calculus/SeqRewrite.lean`, which now imports
  `Calculus/TermLib.lean` (Graft does not).  `Tm.ofClosed?` stays there, only
  for the literal laws (below).
- **`rw`/`sol_rw` on a scoped goal** (`Calculus/RewriteSyntax.lean`): a name
  resolves to its `TermTacletS` twin (`qualifyTacletS`), a `Tm.Theq` becomes
  `TermTacletS.theory` (`asTacletS`), and its left side is unified with each
  candidate read at the empty scope (`Walk.rwCandidates`: the closed sides of
  the equations, then every closed value subterm of the last box update,
  `Tm.toNilQ?`, `Tm.closedNilVals`, `Walk.valSubterms`).  `Walk.rwTheory`
  reads the Theory's laws on the scoped term (`theoryRewriteS`: the scoped
  `Tm.denote_*S` unfold lemmas, `rfl`, and `reifyTermS` … back to `Tms`
  terms; `Tm.Theq.of_eq`).  The erased `theoryRewrite` stays for
  `NFml.Proves`' `sol_rw` (`Calculus/Rewrite.lean`) and the chains past the
  program.
- **Chains while the program is open** (`Calculus/RewriteScoped.lean`,
  `Calculus/Chains.lean`): `FmlRw.lawEq`/`FmlRw.lawUpd` take a
  `TermTacletS t t'` at the empty scope (`lawUpd` with `t'.isLit`).  The
  elaborator maps a law to its twin (`scopedLaw?`) and finds its instances
  among the line's closed terms read at the empty scope
  (`Tm.closedNilVals`, `NFml.Chain.lawInstances`, whose `lawSides?` reads a
  `TermTacletS` and whose head pattern is the scoped side's constructor).
  `FmlRw.lit`/`litEq` keep `LitLaw` on the closer's terms: the law's two
  sides are read at the empty scope at the boundary
  (`Term.closedPairS?`, `LitLaw.closedPairS`), so the line is not erased, but
  their instances are still found on the erased line.
- **Callbacks** (`Calculus/CallbackSound.lean`): `Tm.reclose?` is
  `Tm.toNil?` then `Tm.ofNil`; `Proves.assumeInv` asks the goal to read as
  the invariant at the empty scope (`he : φ.reclose? = some I`, by `rfl`,
  through `holds_reclose`), in place of `Fml.closedB` and an equal erasure;
  `holds_closedB` (an `NFml.holds` reader) is gone.
- **Deferred.**  `lawUpd` beyond the box is not direct: under the diamond a
  law onto a literal changes where the update halts, and
  `Examples/ChainRewritesOpen`'s pinned refusal of `findOnSave` under the
  diamond would move; it needs the erased `LineRw.lawUpdAny`'s condition
  (`Upd.covers`) restated scoped (W9.4, the spike's class 5).  The `…In`
  laws (a storage context `SCtxS`) match on the scoped line by unification
  only, with no spine search (`matchLaw` searches `SCtx` positions on the
  erasure).  A closer `Term.Theq` hypothesis no longer rewrites a scoped
  goal (a `Tm.Theq` does); no pin used one.  The literal laws' instances
  (above), `Calculus/Rewrite.lean`, `TheoryRewrite`'s `NFml.Proves` side,
  `RewriteChains` and `ChainRewrites` past the program stay erased (W9.4).
- **Timing** (each file copied under `Solidity/Scratch/`, a fresh worker
  through the MCP, `/proc` sampled every 20 ms, wall to the last CPU tick;
  base `57598cd3` in a second worktree, runs interleaved; load 2.5–4, the
  `decide` lane running):

  | Module | base | W9.2 `rw` | gate |
  |---|---|---|---|
  | `Examples/ChainRewritesOpen` | 3.47 s, 5.02 s (CPU 3.61, 3.75 s) | 2.96 s, 3.47 s (CPU 3.64, 3.59 s) | 4.1 s |
  | `Examples/ChainRewrites` | 7.54 s, 6.83 s (CPU 8.53, 7.79 s) | 7.31 s, 6.84 s (CPU 8.37, 7.82 s) | 8.2 s |

  Before any edit, on this worktree: 3.46 s and 6.76 s.
- **Checks.**  Per-file diagnostics clean (`SeqRewrite`, `Proves`,
  `ProvesSound`, `SolkeyProves`, `UpdateRules`, `CallbackSound`,
  `RewriteScoped`, `RewriteChains`, `Chains`, `RewriteSyntax`, and the pins
  `ChainRewritesOpen`, `Tactics/{SelectOnSaveConsr,StorageDelete,UpdateRules,Sequents,Callback}`);
  `lean_build` of the default targets; `check-orphans`, `check-doc-paths`.

### W9.2 `decide` record (2026-10-11, branch `w9-decide`)

The scoped decision procedure no longer reads the erasure; the erased
lowering in `Calculus/Decide.lean` (`Surface.Tm.toL`, `NFml.toL`, its
soundness) stays for its users until W9.5.  `Op*.toL` and the elimination
are unchanged.

- **`Calculus/DecideRel.lean`** (new, imported by `DecideTyped`).  The
  relation by position: `RelB σ ρ B τ` (the positions are `ρ`'s keys,
  distinct, fresh from `ρ.next`; `ρ`'s storage stack reads `τ`'s storage;
  each bound position holds what its symbol reads, `BindRel`, its memory
  names in the births `B`; the values of the transaction are `σ`'s) and
  `RelU σ ρ τ` (`RelB` in the births of `ρ`'s memory, whose run leaves
  `τ`'s heap, `MemAt`).  No untyped state `τu`, no `AgreeB`.  Over it the
  erased reduction's soundness restated on `Tm C Γ s` and `Tm.eval`:
  `TermOKS` … `MValOKS` with their steps and `RelU.all_ok` (by
  `Tm.lsize`), `RelU.val`/`path`/`ident`/`memT`, `RelU.stor_eval`,
  `RelU.slotPath_eval`, `RelU.stale_write`/`stale_push`, `RelU.storT`;
  one right-hand side, element and declaration written into another state
  than the one read (`RelU.rhs`, `RelU.elem`, `RelU.decl`, with what the
  element reads of the memory or storage the first left: `needsMem`,
  `needsStor`); updates (`RelU.zero`, `RelU.one`), the allocation's pair
  (`RelU.pairCopy_key`, `RelU.pairKey`, `RelU.half`, `RelU.two`) and two
  parallel elements (`RelU.par`).  The structural steps: `RelB.pop`,
  `thin`, `push`, `setLocal`, `withGlob`, `write`, `grow`, `setMem`,
  `RelU.pushQ`, `pushFree`.  Gone from `DecideTyped`: `Surface.Tm.ReadsIn`,
  `AgreeB`, `AgreeU`, `Tm.eval_eraseB`, `Rhs`/`UpdElem.write_eraseB`, the
  readers of `Term.toL_eval`, `pair_sound`, `Surface.UpdElem.toL_sound`;
  gone from `DecideScoped`: the links to the erasure (`Tm.toLS_eq`,
  `Tm.inLS_imp`, `ElemS.guard_eq`, `UpdElem.nact_eq`, `pairLS_eq`, …,
  `ElemS.erase`).  The locals are still listed by key through
  `Env.erase` (the state IR, W9.6), and `RelB.thin` reads
  `Env.mem_erase_thin`, which lives in `HoldsErase` (to move at W9.5).
- **`sameAt`, `allocPairS?` by `Tm.beqR`** (`DecideScoped` imports
  `TermLib`).  `sameAt` asks one context (`decEq`), the same keys
  (`SymS.names`) and one term; its soundness is semantic
  (`sameAt_toLS`, `Tm.toLSM_congr`: the two readings lower to one
  `LTerm`).  `allocPairS?` drops its `SymS` argument.
- **Proposal 100.**  `Fml.layoutS` (the roots of a premise `wt(storage)`
  under the leaf's parameters' quantifiers) and `Fml.dropWtS` (the premise
  set aside), both by the recursor with `match` twins (`layoutSM`,
  `dropWtSM`) and links.  `Valid.of_reduceSL` (`DecideComplete`, beside
  `Valid.of_reduceS`): `∀ σ, LayoutOk (layoutS φ) σ → (dropWtS φ).reduceS`
  holds gives `Valid φ`, through `holds_of_dropWtSM` and
  `layoutOk_of_wtS`.  `LFml.closeS L φ` takes the layout (`closeS_valid`,
  `closeS_valid_nil`); `sol_decide_close` accepts both goal shapes, and
  `sol_reduce` the one with the layout.  `sol_decide` on a scoped leaf
  takes this path when `layoutS` is not empty (`reduceScoped`), the
  closer first, the other steps without the layout
  (`LFml.forall_layout`).  Pinned: `deleteWithoutWriteScoped`.
- **Two parallel elements** (`{x := x + 1 ‖ se1 := x}`): `Fml.toLS`/`inLS`
  take an update of two elements that is no allocation's pair when
  `ElemS.parOk` (both in the fragment; no memory set before a memory
  read, no storage set before an alias), guarded by `seqL` of both
  guards, both acts read in the pre-state (`UpdElem.actS ρ`); sound by
  `RelU.par`.  Pinned: `postIncrementParallel`.
- **Decision 80's parts on a scoped goal** (`Calculus/Closers.lean`,
  `Decide.onReduced`): `sol_reduce`, `sol_reads`, `sol_decide_cons`,
  `sol_decide_heuristic`, `sol_decide_unconstrained` on `Valid ψ` reduce by
  position (`reduceScoped`) and then take their step on the reduction:
  `sol_decide_cons` is the constraints with the parameters typed
  (`sol_decide_typed`; `typedCons` factored out), `sol_reads` its first
  part, the heuristic ones `sol_decide_body; sol_decide_heuristic`.  The
  erased elaborators stay for today's goals; `Derive.onErased` is no longer
  used for these five.
- **Checks.**  Per-file diagnostics clean, no warning (`DecideScoped`,
  `DecideRel`, `DecideTyped`, `DecideComplete`, `Closers`,
  `Examples/Tactics/Decide`); `lean_build` of the default targets;
  `check-orphans`, `check-doc-paths`; `sorry` count unchanged (20, all in
  prose or strings); axioms of `Valid.of_reduceS`, `Valid.of_reduceSL`:
  `propext`, `Classical.choice`, `Quot.sound`.  No pin moved; no leaf that
  failed before closes in an existing pin (the two new capabilities are
  pinned by the two new theorems).
- **Timing, `Examples/Tactics/Decide`** (fresh worker, read from `ps`):
  before 41 s wall, 39 s CPU; after (with the two new theorems) 42 s wall,
  40 s CPU; gate 45.0 s (W7: 35.87 s; the machine shared with another lane).
- **Deferred.**  The push alias (`pushAlias?`) and the ground split, the
  re-timing on `Derived7`/`Derived12` (W9.3); a pair-shaped update whose
  `pairLS` fails still leaves the fragment (no fallback to `parOk`); the
  layout is read only from the first premise under the leading `∀`s (not
  under a hidden binder or an update); `Env.mem_erase_thin` to move out of
  `HoldsErase` before W9.5.

### W9.3 `walk` record (2026-10-11, branch `w9-walk`)

`sol_prove`'s walk (the `⊢` route) closes a leaf on its scoped form; the
erased closer is the fallback for a leaf the scoped one does not read.

- **Step 0.**  `lean_build` of the default targets passed on the merge of
  `decide` and `rw` (`13b0b810`): no integration commit.
- **`Calculus/LeafDerive.lean`** (new, imported by `ProvesDerive`).
  `Seq.leafCheckS H φ` reads the wrapped leaf (`Hyps.wrap`): `none` where a
  modality is left or the fragment does not read it, else whether it closes
  (`Seq.checkCore`: `Fml.dropWtS` in the fragment, `Fml.toLS` within
  `closeSize`, `LFml.closeS` of `Fml.reduceS` with `Fml.layoutS`);
  `Seq.leafCheckS_sound` is `Proves.closeHolds` of `Valid.of_reduceSL` and
  `LFml.closeS_valid`.  A leaf not read as it is is read prepared
  (`Fml.prepS`, `holds_of_prepS`).  The kernel-evaluated functions
  (`checkCore`, `Fml.prepS`, `Tm.stablePathS`, `Hyps.groundInS`,
  `Upd.resolveS`, `Fml.litPos`, `Thin.posWk`) are recursors with `match`
  twins and link theorems.
- **The walk** (`Calculus/ProvesDerive.lean`).  `Seq.leafS`: `some true`
  closes, `some false` leaves the leaf (no erased try: the erased closer
  has the same bounds and knows no more of a leaf the fragment reads),
  `none` falls back to `Seq.leafRes` (`Fml.closeErase`, `Derive.residue`).
  `Seq.refutes` reads the ground test by position (`Hyps.groundS`) and the
  same leaf; the erased `Seq.ground` and `Derive.groundCond` … `litVars`
  are gone.  `Seq.leafQuoteS` marks as before; `Seq.scanLeaves` counts
  writes on the scoped context (`Hyps.storageWrites`).
- **The spike's classes.**
  1. *Layout* and 2. *two parallel elements*: W9.2 (`Valid.of_reduceSL`,
     `ElemS.parOk`).
  3. *Push alias*: `Upd.pushSplit` (the scoped `pushAlias?`: `{storage :=
     extend(storage, a) ‖ x := next(a)}` as the push, then `x :=
     a[a.length - 1]` read after it), sound by `holds_push_alias`
     (`stable_evalS`, `lastSlotS_eval`, `next_eval_of_extend`; the typed
     state between the two updates is the one the parallel update ends in
     with the alias reset).  10 TestSuite leaves.
  4. *`wt(storage)` under the parameters' `∀`*: W9.2's `Fml.dropWtS`; on a
     leaf a tactic closes, `sol_leaf_wt` (`Valid.of_dropWtS`).
  5. *The ground test*: `Hyps.groundS`, which agrees with the erased test
     on all 437 TestSuite statements (the walk's leaf counts equal).
  6. *`pick`/`Fml.stripN`* (decision 27): not ported.  The scoped leaf keeps
     its parameters bound (`LFml.all`), read at their types
     (`Facts.bind`), which closes every leaf the free reading closed (0 of
     910 TestSuite leaves differ); `pick` stays on the fallback.
  7. *A scoped `seqUpd`*: not needed.  No leaf in the default targets or the
     TestSuite has an update of three elements (`UView.many`) or a pair
     outside `parOk`/`pairLS` that the erased closer closes; such a leaf
     falls back.
  8. *`Seq.residue` without the erasure*: a leaf the scoped closer reads
     never evaluates the erasure, in the kernel or in compiled code.
  9. *(new, Lean only)* a hidden binder of a value read as the `∀` it is
     (`Fml.bindAsAll`, in `Fml.prepS`): `spec!{f}` obligations bind their
     parameters so (`Examples/Benchmark/SimpleStorage.lean` `spec_set`,
     `Examples/Benchmark/Mapping.lean` `spec_nested_set`); rule-map row
     `sequentialToParallel1-3`.
- **Coverage.**  TestSuite (437 statements, compiled walk): 910 leaves
  closed scoped, all 910 the erased closer closed; 8 left: 7 read and not
  closed, 1 not read.  With the fallback disabled (an experiment, not
  committed), the default targets built but for the two
  `#solkey_obligations` pins the experiment's `sorry` moved: the fallback
  closes no leaf there or in the TestSuite.
- **Fallback classes** (leaves the scoped closer does not read; in each
  example the erased closer does not close them either, and the replay is
  `sol_leaf` and an erasing closer):
  - an alias whose index reads the storage, used after a storage write: a
    nested push's returned alias (`testStorageNestedPushReturnAlias`,
    `TestSuite/Derived7.lean`; `sol_leaf; sol_close`);
  - a deployment's update, three elements over `mtSt`
    (`Examples/Tactics/Constructors.lean` `deployMini`, `miniDeploy`;
    `Solkey/Constructors.lean`; `sol_leaf; sol_close_mt`);
  - a loop's frame (`anon`, `havoc`): `Examples/Tactics/LoopsImport.lean`
    (`sol_leaf; sol_close`);
  - a modality left in the leaf: neither closer reads it, the walk fails.
- **`sol_leaf`** (`Seq.leafValid`): a leaf `H ⊢ φ` as `⊨ ψ`, `ψ` the wrapped
  sequent quoted (`Proves.closeValid`, `Symex.normValid`), `Fml.modalFree`
  checked by the kernel; `sol_leaf_wt` sets `wt(storage)` aside.
  `Derive.leafTacs` tries on a scoped leaf `sol_leaf` then `sol_decide`
  (within `Seq.leafFitsS`: `Seq.leafFitsOn`, the scoped `closeSize` and
  `elimSize`), `sol_close`, `sol_spec_close`, and today's lines after.
  `Derive.searchLeaf` runs each try `withoutRecover`: a scoped tactic that
  logs its error and admits the goal (`Symex.reporting`) no longer counts
  as closing it.  `Derived*` import no `Closers`, so the scoped leaf's
  `sol_decide` (`Calculus/DecideComplete.lean`), not
  `sol_decide_cons`, is the replay.
- **Replays re-derived** (`sol_prove?`, `#solkey_derive?`):
  `TestSuite/Derived1.lean` (2), `Derived12.lean`, `Examples/Benchmark/Mapping.lean`
  `remove_spec`, `Examples/Benchmark/Purchase.lean` `ctor_spec`,
  `abort_onlySeller`: `sol_leaf; sol_decide`; `Derived7.lean`
  `testStorageNestedPushReturnAlias`, `Examples/Tactics/LoopsImport.lean`
  (3): `sol_leaf; sol_close`; `Examples/Tactics/Constructors.lean` (2),
  `Solkey/Constructors.lean`: `sol_leaf; sol_close_mt`.  None searches.
  `Purchase.ctor_spec` had passed `maxHeartbeats` once the walk ran both
  closers on its leaf (the erased `sol_close` replay alone takes 181M raw
  heartbeats); with the erased closer only on leaves the scoped one does
  not read, and the replay `sol_decide`, it fits.
- **Pins moved.**
  - `Examples/ProofTree.lean`: `balances[k] = 5; balances[j] = 5;`'s
    suggestion is `sol_leaf; sol_decide` (was today's five lines through
    `NFml.valid_iff_reduce`): the leaf is closed scoped.  `pushes22`,
    `writes6`, `deletes10` read the scoped leaf (`Fml.toLS` within
    `closeSize`, `Seq.leafFitsOn`) instead of its erasure (`Seq.leafErase`,
    `Derive.leafFits`): the same values, and the scoped sizes equal the
    erased ones (pushes22 1723/13498 nodes, deletes10 330/79587, writes6
    3122 past `closeSize`).  `writes4` (`isEmpty`) did not move.
  - `Examples/Tactics/Dangling.lean`: `rounds4`, `rounds6` read the scoped
    leaf likewise (935/15931, 1799/44719: the sizes the prose gives);
    `rounds2` (`isEmpty`) and the four `sol_prove?` pins (`sol_prove`) did
    not move.
  - `TestSuite/Suggestions.lean`: `testStorageNestedPushReturnAlias` is
    `sol_leaf; sol_close`.
  - The open `⟨ alice.age = 1; ⟩ true` leaf stays open: no Lean-only
    clause "a typed storage has every root" was added.
- **Timing** (each file copied under `Solidity/Scratch/`, a fresh worker
  through the MCP, one at a time after a warm-up, `/proc` sampled every
  20 ms, wall to the last CPU tick; base `13b0b810` in this worktree,
  filled from the artifact cache; load 1–2.5, cgroup 15–18 GB, the `close`
  lane running):

  | Row | base | W9.3 `walk` | gate |
  |---|---|---|---|
  | `Derived1`–`14` (sum) | 223.0 s | 191.4 s | 237.8 s |
  | `Derived7` | 54.2 s | 48.1 s | 61.7 s |
  | `ProofTree` | 10.7 s | 9.9 s | 11.7 s |
  | `Solkey/TestSuite` | 7.5 s (CPU 6.9) | 8.8 s (CPU 6.9) | 13.2 s |

  Per file, base / walk: `Derived1` 9.2/9.0, `2` 10.8/9.0, `3` 14.1/13.1,
  `4` 23.3/16.2, `5` 7.9/7.0, `6` 12.8/11.0, `7` 54.2/48.1, `8` 27.1/25.3,
  `9` 8.5/6.7, `10` 16.0/10.6, `11` 4.0/3.3, `12` 14.3/12.9, `13` 8.8/10.0
  (CPU 6.6/6.4), `14` 12.2/9.4.
- **Checks.**  Per-file diagnostics clean (`LeafDerive`, `ProvesDerive`,
  `NFmlDerive`, the replays and pins above, `Derived1`–`14`,
  `TestSuite/Suggestions`); `lean_build` of the default targets and
  `SolkeyTestSuite` (the `Derived` modules first in three batches of a
  temporary library in `lakefile.toml`, not committed, so that Lake runs at
  most five at once: cgroup peak 23.4 GB; then the three targets
  together); `check-orphans`, `check-doc-paths`; `sorry` count
  unchanged (20 lines, prose and strings); axioms of `Proves.of_residue`,
  `Seq.leafCheckS_sound`, `holds_push_alias`, `Proves.closeValid`,
  `Valid.of_dropWtS`: `propext`, `Classical.choice`, `Quot.sound`.
- **Left.**  The erased fallback (`Seq.leafRes`, `Proves.close`,
  `close_leaf`, the erased lines of `Derive.leafTacs`) until W9.5; the
  fallback classes above need an erasing closer (`sol_close`,
  `sol_close_mt`: the `close` lane's).
### W9.3 `close` record

Branch `w9-close`: `sol_close`, `sol_close_mt` and `sol_spec_close` close a
scoped leaf without the erasure; no pin moved.

- **The leaf read on the erased state** (`Calculus/CloseScoped.lean`).  Read
  as `holds` reads it, every update leaves `∀ σ', σ'.erase = τ → H <+: σ'.H →
  …`, which `simp` can only use contextually: the spike's leaf (`[
  balances[a] = 1; balances[b] = 2; uint x = 0; if (a == b) …`) took 5.4 s of
  `simp` against the erased path's 1.8 s, and 4.5 s with the quantifier
  pushed past the first-order rest.  So `sol_close_unwrap` takes the leaf
  first to `CloseS.holdsE σ.erase ψ` (`valid_of_holdsE`, sound one way by
  `holds_of_holdsE`): an update's rest read where it ends, a hidden binder
  over its type's erased values (`LTy.forallE`: a primitive type's typed
  values), a parameter over `p.Denote` (decision 82: `forall_uint`,
  `forall_int`, then `0 ≤ n`, `n < uintBound` for `omega`), a negation and a
  precondition only of a first-order formula (`fo`, `∀` included: the two
  readings agree there, `holds_iff_holdsE`).  It is the erased leaf's
  strength (`Fml.posB`'s class), plus the value binders' ranges; the heap
  typing (`H`) drops out.  On the spike's leaf: 1.78 s of `simp`, as the
  erased path.
- **The set `close_rw_s`** (registered in `Calculus/ReadWrite.lean`, with
  `close_rw_s_last`): `holdsE`'s equations; a term one constructor at a time
  (`CloseS.eval_find` …, `close_rw`'s `Close.Term.eval_*` restated on
  `Tm C Γ s`, a local by `EState.get`); `Upd.apply`, `UpdElem.write`,
  `Rhs.eval`; the erased state through its operations only (`push`,
  `setLocal`, `withGlob`, `glob`, `drop`, `thin`, `anon`: a stack of pushes
  over `withGlob`, never `EState`'s fields).  The interpreter lemmas are
  shared.  Names are qualified where the typed and untyped namespaces
  overlap: `State.envVal` inside `namespace Solidity` is the typed state's,
  and a draft that listed it bare left `msg.sender` unread.
- **`Calculus/CloseLemmas.lean`** (new; `NFmlClose` imports and re-exports
  it, so `DecideLang`/`Decide` see the same names): `Modality.wp` and its
  lemmas, values, operators, the ledger, `Close.State.havoc_eq_mk` (from
  `CloseHavoc`), and the symbols one constructor at a time
  (`Close.Op0.eval_lit` … `Close.Op3.eval_write`), from which the scoped
  term equations follow.  `close_rw`'s own lemmas (`Surface.Tm`, `NFml`,
  `Binding`) stay in `NFmlClose`.
- **Dispatch.**  `sol_close_eval`, `_facts`, `_reads`, `_reads_all` and the
  new `sol_close_mt_eval` are elaborators in `NFmlClose` that step aside on a
  scoped goal (`Close.scopedGoal`: the goal or its context names
  `Solidity.State`, `EState`, `Valid` or `CloseS.holdsE`) for
  `CloseScoped`'s; `sol_close`, `sol_close_mt`, `sol_spec_prep` and
  `Benchmark/Coin`'s hand-written steps are unchanged text.
  `Derive.evalSolCloseUnwrapCore` (the erasure) and `SolSpec`'s erasing
  `sol_spec_prep` are gone; `Derive.eraseLeaf` loses `typed`.
- **Erased callers that remain**: `refine close ?_` (`Proves.close`, an
  `NFml.Valid` goal) and the leaf searches on it (`NFml.Derive.searchLeaf`,
  `Walk.closeLeaf`, `sol_prove?`); `Calculus/Closers.lean`'s second
  elaborators (`sol_close_eval` on a bare `Valid ψ`, `sol_decide_*`,
  `sol_reduce`, `sol_reads`, `sol_apply_upd`, `sol_fold_terms`: the
  `decide` lane's file, not edited here); `Decide`'s own `close_rw` passes.
- **Pins.**  None moved: every `fail_if_success sol_close` still fails
  (`Tactics/Decide`'s three, `CallOperands`' push row), and
  `Constructors`' `sol_close_mt` limits stay open.  `CloseTests` gains one
  example pinning the scoped reading (`show CloseS.holdsE σ.erase _`).
  Checked: `CloseTests`, `Tactics/{Constructors,Specs,SolSpec,ProofTree,
  ApplySteps,LoopsImport,SelectOnSaveConsr,UpdRulesScoped,Decide,StorageSteps,
  Values,StorageSuite,Calls,Contracts,Derive,StorageDelete,Net,Loops,Revert,
  Checked,Branch,UpdateRules,Payment,Operators,CallOperands,TryCatch,Tour,
  Callback,LedgerDelete,Memory,CrossDomain}`, `Benchmark/{Coin,EtherWallet,
  Mapping,Purchase}`, `ChainNotation`, `Notation`, `ProofTree`, `Verify`,
  `Solkey/Constructors`, `Corpus/Basic`, `TestSuite/{Derived7,Suggestions}`.
- **Timing** (each file copied under `Solidity/Scratch/`, a fresh worker
  through the MCP, `/proc` sampled every 20 ms, wall to the last CPU tick,
  idle gaps over 1 s, the worker waiting on `lake setup-file`, subtracted;
  base `111e5119` on this worktree before any edit; load 0.6–2.6, the
  `decide` lane running):

  | Module | base | W9.3 `close` | gate |
  |---|---|---|---|
  | `Examples/Tactics/Decide` | 37.76 s (CPU 38.54 s) | 38.48 s, 38.71 s (CPU 39.23, 39.35 s) | 45.0 s |
  | `Solkey/TestSuite` | 8.54 s (CPU 6.94 s) | 7.17 s, 6.88 s (CPU 7.35, 7.05 s) | 13.2 s |
  | `Examples/Chains/Storage` | 7.61 s (CPU 7.98 s) | 7.86 s, 7.63 s (CPU 8.35, 7.98 s) | 9.0 s |

  One more `Chains/Storage` run read 9.53 s (CPU 8.53 s) at load 2.1.
  `Examples/Tactics/Values` (37 `sol_close`s on scoped leaves): 9.96 s (CPU
  10.06 s), no base taken.
- **Checks.**  Per-file diagnostics clean (`CloseLemmas`, `NFmlClose`,
  `CloseScoped`, `Derive`, and the pins above); `#print axioms
  CloseS.valid_of_holdsE`: `propext`, `Classical.choice`, `Quot.sound`;
  `lean_build` of the default targets; `check-orphans`, `check-doc-paths`.

### W9.4 `fronts` record (2026-10-11, branch `w9-fronts`)

The front ends and the notation stop producing `NFml`; the walk and the
tree close a leaf by `sol_leaf` and the scoped closers.

- **Step 0.**  `lean_build` of the default targets passed on master
  `6aca012a` (`close` over `decide` and `walk`): no integration commit.
  `TestSuite/Derived7` and `Examples/Tactics/LoopsImport` are clean.  The
  walk's fallback classes are already closed scoped there: after
  `sol_leaf` the goal is the scoped `⊨ ψ`, so `sol_close` and
  `sol_close_mt` are the `close` lane's (`sol_close_unwrap` to
  `CloseS.holdsE`; `Calculus/Closers.lean`'s erasing elaborator steps
  aside once the state is introduced): the alias index after a storage
  write (`testStorageNestedPushReturnAlias`), the deployment's `mtSt`
  (`Tactics/Constructors`, `Solkey/Constructors`) and the loop frames
  (`LoopsImport`, three) close without the erasure.
- **`NRead`** (`Calculus/NotationResolve.lean`): a formula over names, read
  where it stands, `(Γ : NCtx) → Except String (Fml C Γ.ctx)`, with the
  connectives `NFml` had (`tt`, `eqD`, `all`, `upd`, `conj`, `bool`,
  `cmp`, …).  `NFml.resolveN` is gone: `dl!{}`'s atoms
  (`Calculus/Notation.lean`'s `elabAtomN`) and the specification compiler
  (`Calculus/SurfaceSpec.lean`'s clauses, layout, frame, `specPieces`)
  build `NRead`s, `Calculus/Spec.lean` reads them in the parameters'
  context, and `Tools/Counterexample.lean`'s `SpecProblem.posts` are
  `NRead`s, a frame conjunct printed resolved at `old`/`oldNet` and closed
  by hidden binders (`Examples/Verify.lean`'s pin unchanged).
- **`wt(storage)` scoped** (`Calculus/Problem.lean`): `NFml.wt` is gone;
  `holds_wt` is over a typed state (`holds σ (Fml.wt C) ↔ storageWtB …
  σ.erase.glob.storage`), `initStorage_wt : holds (State.init C) (Fml.wt
  C)`, and `Corpus/Imported.lean`'s `runs_of_proved` takes it as it is (no
  `holds_erase_fo` detour); `TestSuite/Problems.lean`'s `initState_wt`
  likewise.  `Problem.parts` reads the obligation by position
  (`Problem.isWt`, `Problem.isDeploy`), not its erasure.
- **`#wp`** (`Tools/Inspect.lean`): the fragment test and the reduction are
  the scoped ones (`Fml.inLS`, `Fml.reduceS`); a key `#k` prints by its
  binder's name (`Fml.keyNames`, `keyedNames`, replaying `SymS.next`), so
  the three `Examples/Tools.lean` pins and `Tactics/{Surface,Notation}`'s
  did not move.
- **`dl!{}` with no modality is `Fml C []`** (`elabDlAuto` reads every
  formula; `SurfaceNotation`'s `elabDlAt` is gone): outside `open scoped
  Solidity.Scoped` its parameters are hidden binders, inside `∀`.
  `SurfaceNotation`'s `elabDl`/`elabFml` (the closer's reading) stay only
  for `Calculus/Chains.lean`'s `elabDlN` (the `chains` lane's).
- **`⊨`/`⊧`** (`Calculus/RuleSyntax.lean`, `elabValidHolds`): `Valid` and
  `holds` of a scoped formula, the closer's of any other (the `chains`
  lane's `NFml.Via` lines, which `Calculus/RewriteChains.lean` writes
  without importing `Logic`); `Theorems.lean`'s scoped copies are gone;
  `holds` prints `σ ⊧ φ` (`Calculus/Surface.lean`).  `Decide`'s two
  `NFml` theorems and `DecideComplete`'s say `NFml.Valid`.
- **Sequents** `dl{ ..H ⟹[R] φ }` are the scoped `Proves` wherever
  `Calculus/SequentNotation.lean` is imported (its macros no longer
  scoped; `Calculus/Surface.lean` imports it); the closer's are `open
  scoped Solidity.NFmlSeq`'s (`Calculus/NFmlLogic.lean` opens it).  The
  scoped taclets' formulas are written as `Fml`'s constructors (`fmlC`):
  `coreNames` turns terms only (`coreFamily?` lost `NFml`), as TermLib's
  `tm{}` rule needs.
- **The leaf step** (`Calculus/ProofTree.lean`, which now declares
  `sol_leaf`; `Calculus/Derive.lean`, `Calculus/NFmlDerive.lean`,
  `Calculus/ProvesDerive.lean`): the tree's `closeTacs` and
  `Walk.closeLeaf` are `sol_leaf; sol_close`; `Derive.leafTacs` gives a
  scoped leaf the scoped lines only; `Seq.leafS` leaves a leaf the scoped
  closer does not read (no erased fallback: `leafRes`, `pick`, `pickH`,
  `full` and `Seq.residue`'s `np` are gone, `Seq.residue R H φ`), and
  `Proves.close_leaf`, `Seq.leafErase`, `core_leaf_close` and the
  `refine NFml.Proves.close ?_` macro on a scoped leaf are gone too.
  `Tools/ProofTree.lean` imports `ProvesDerive` (the tree's leaves need
  `sol_leaf`'s elaborator).  `Proves.close` stays for `Calculus/ChainKit.lean`'s
  last line past the program and `Calculus/CloseTests.lean`'s erased
  section; `refine close ?_` (`Calculus/WalkSyntax.lean`) is documented
  as that fallback.  `sol_close_eval` on a bare scoped `Valid ψ` is
  `sol_close_unwrap; intro σ; sol_close_eval` (`Calculus/Closers.lean`);
  `sol_apply_upd` and `sol_fold_terms` still erase (no scoped reading).
  `NFml.Derive.closeSize`/`elimSize` are `Decide.closeSize`/`elimSize`'s
  abbreviations, `Derive.replayFits` left `NFml.Derive`.
- **Examples.**  190 lines `refine close ?_` (and `refine Proves.close []
  rfl List.nodup_nil ?_`), with the `sol_symex` after them, in 26 files
  (scripts and pins) are `sol_leaf`, the closer after unchanged, but: `Tactics/LedgerDelete` `ledgerWriteThenDelete`
  (the scoped `sol_close` ran out of 200000 heartbeats; `sol_decide`
  closes it), `Benchmark/Coin` `spec_mint` (the hand-written steps fail on
  the scoped leaf; `sol_spec_close` closes it under the same 400000
  override, 300000 does not), `Tactics/{Callback,TryCatch}`'s havoc
  leaves (`Hyp.valid_after_havoc` dropped: `CloseS.holdsE` reads `havoc`),
  `Tactics/Revert`'s `true` leaves (`sol_close`).
  `Tactics/SelectOnSaveConsr` `ageWriteRead` reads the scoped leaf by
  hand on `CloseS.holdsE`, the `consr` path `[] ++ [.field "age"]` where it
  was.  `Tactics/TermTaclets` is on scoped sequents over `StandardExample`
  (`⊢ dl!{ … }`, `rw`/`sol_rw`, `Proves.eqRefl`).  `Tactics/Dangling` and
  `Examples/ProofTree` name `Seq.residue .all .nil` and `Decide.closeSize`.
  `Tools/Common.lean` imports `Syntax`, not `Update`.
- **Pins moved.**
  - `Examples/Tactics/DlNotation.lean`: the seven type pins `NFml
    StandardExample` → `Fml StandardExample []` (the parallel update, `∨`/`↔`,
    `∃`, `defined`/`≐`, `!=`/`<`, `Token[3]`, `newArr`); `dl{ a = 1 }` now
    of a closed scoped tree (a hidden binder over `.pvV .here`); the
    `⊨`/`⊧` pin `fun φ => (⊨ φ) ∧ ∀ (σ : State StandardExample []), σ ⊧ φ :
    Fml StandardExample [] → Prop`.  Examples (not pins) rewritten: the two
    equation trees and the push tree as scoped trees, the Lean-formula
    holes at `Fml` types, and `{ p := unset } true` needs `where Person
    storage p` (the scoped reader asks the alias's type).
  - `Examples/ProofTree.lean`: eight `sol_derive?` pins, `refine close ?_ /
    sol_symex` → `sol_leaf` at each leaf (the scoped `sol_close` closes
    every one).  `Examples/Tactics/Derive.lean`: the explicit walk's
    `refine Proves.close [] rfl List.nodup_nil ?_ / sol_symex` → `sol_leaf`;
    the `⊢ₖ` refusal's message lost its `Proves.close` clause (a leaf
    need not be closable now).  `Examples/Tactics/ProofTree.lean`:
    `#proof_node 3`'s tactics are `sol_leaf; sol_close`.
  - `Examples/Tactics/TermTaclets.lean`: the `rw [h]` pin lost `C :
    Contract`; the `findOnSaveFrame` side-condition pin is `#guard_msgs
    (drop error)` (the scoped `rw` steps aside and Lean's fails; the
    closer's `sol_rw` message is not reached).
  - The open `⟨ alice.age = 1; ⟩ true` leaf stays open.
- **Timing** (each file copied under `Solidity/Scratch/`, a fresh worker,
  `/proc` sampled every 20 ms, CPU of the worker; base master `6aca012a`
  in this worktree):

  | Module | base | W9.4 `fronts` | gate |
  |---|---|---|---|
  | `Examples/ProofTree` | 9.00 s | 8.10 s | 11.7 s |
  | `Solkey/TestSuite` | 6.93 s | 6.95 s | 13.2 s |
  | `Examples/Tactics/DlNotation` | 1.21 s | 1.20 s | — |

- **Checks.**  Per-file diagnostics of every file touched; `lean_build` of
  the default targets (after the last edit); `SolkeyTestSuite`,
  `Corpus/TestSuite` and `Solkey/Constructors` through a temporary library
  in `lakefile.toml` (not committed), the `Derived` modules five at a time;
  `check-doc-paths`, `check-orphans`; `sorry` lines unchanged (20); axioms
  of `Proves.of_residue`, `Seq.leafS_sound`, `holds_wt`,
  `initStorage_wt`, `Corpus.runs_of_proved`: `propext`,
  `Classical.choice`, `Quot.sound`.
- **What still reads `NFml` here, and why.**  `SurfaceNotation`'s
  `elabDl`/`elabFml`/`fillSlots`/`NFml.slot`/`boolFml`/`cmpFml` and
  `Surface.Tm.quote` (`st!{}`, `pt!{}`): `Calculus/Chains.lean`'s lines past
  the program (`elabDlN`, the `chains` lane).  `RuleSyntax`'s `schemaFml`
  (`dl_schema{}`, `dl{ φ }`, the `NFmlSeq` sequents) and the `NFml`
  delaborators: `Calculus/{Hyp,NFmlLogic,NFmlUpdateRules}.lean`, W9.5's.
  `⊨`/`⊧`'s and `valid%`'s `NFml` branch: the `chains` lane's `NFml.Via`.
  `Calculus/NFmlQuote.lean`: `Calculus/Quote.lean` imports it (the
  `ToExpr` of `PrimVal`), `NFmlDerive`, `TheoryRewrite`.  `Proves.close`:
  `ChainKit`'s bridge and `CloseTests`.  `Derive.eraseLeaf`:
  `sol_apply_upd`, `sol_fold_terms`.  `NFmlDerive`'s erased `leafTacs`
  branch: the closer's own sequents.

### W9.4 `chains` record (2026-10-12, branch `w9-chains`)

- **Landed.**  Past the program a chain's lines are scoped (`Fml C Γ`):
  every link is an `FmlRw` checked by the kernel on the written line.
  - The classes as scoped rewrites with their soundness
    (`Calculus/RewritePast.lean`): `mergePast` (KeY's
    `sequentialToParallel`, across a hidden binder too: `Upd.absorb`
    moves a write to a local into the base of the elements it is read in,
    `Upd.apply_absorb` up to `Res.OkEq`), `simplifyPast`
    (`simplifyUpdate`: drops unread locals with their binders, `Thin.mask`,
    identity thins normalised), `applyStorageBoxP`.
  - The laws in an update's right side (`Calculus/RewriteLaws.lean`,
    `FmlRw.lawUpdE`): solkey's term taclets on the erasure, lifted to the
    scoped term by `ErasedCov` (`covered`, `ref`, `eqv`, `eval`): a law
    instance is sound when the erasure of both sides agrees
    (`Tm.eval_erase`, `Upd.apply_erase`).
  - `~~>` past the program: `Fml.LeadsK φ L` (`Calculus/ChainKit.lean`),
    a scoped `Fml.Leads φ B` whose last line's erasure is the written
    line; `Fml.Via.leadsK`, `Fml.Leads.leadsK`, `Fml.LeadsK.valid`.
  - `#chain`, `#chain_rest`, `#last_line`, `sol_rws`/`sol_rws?`
    search the scoped line (`ChainGen.pastSearch`, batched evaluation of
    the candidates: `scopedRwCandsMany`, `lawUpdECands`).
  - Gone: `Fml.ViaE`, `Fml.LeadsE`, `NFml.Via`, `sol_chain.scopedPast`,
    the erased elaboration of `sol_chain` (a goal that is not a chain is
    refused), the erased `#chain`/`#last_line` paths
    (`RewriteChains`/`RewriteChainGen` keep syntax and the IR's law
    instances only).
- **Gates** (fresh worker, end of work, base `2c07be6b`):

  | Row | base | after | gate |
  |---|---|---|---|
  | `ChainRewrites` | 6.82 s (CPU 7.73) | 7.52 s (CPU 8.35) | 8.2 s |
  | `ChainRewritesOpen` | 3.48 s | 3.43 s | 4.1 s |
  | `Chains/Storage` | 7.68 s (CPU 8.05) | 8.72 s (CPU 10.07) | 9.0 s |
  | `ProofTree` | 9.13 s | 9.01 s | 11.7 s |

  `Chains/Storage` is 7.53 s without its 24 `#last_line` pins: the cost is
  the scoped search, which evaluates its candidates in one compiled batch
  per line (17 s before batching).  No fallback was needed.
- **Pins moved.**
  - `#last_line` prints the line as written, `dl{ φ }` for a post (was
    `↑φ`, the erasure's coercion); `#chain` lines keep their `∀`.
  - `ChainNotation`: `sol_chain?` suggests `Fml.Via.leadsK`;
    `composed` ends in `.leadsK`; `headline_valid` by `sol_decide`.
  - `ChainRewrites`: `readBackValue`, `headlineValue` by
    `Fml.Via.valid` (no `ViaE`).
  - `Chains/Memory` (`t` before `carolAcc`), `MemoryArrays` (`tk` before
    `mv`), `MemoryDelete` (`mv4` before `mv5`), `MemoryToStorage`
    (`aliceTok` before `sp`): a merge across a hidden binder declares the
    late local first (`Fml.absorbAllMergeP`), so the parallel update
    prints in that order — a deviation from KeY's order, marked in the
    rule map.  `mergePast` tries the order-keeping merge first, so the
    storage chains keep their pins.
  - `ChainRewritesOpen`: its `set_option` is gone.
- **On the IR, and why.**  Law instances are found on the line's
  erasure (`NFml.Chain.lawInstances`) and lifted by `ErasedCov`: the
  taclets are solkey's term taclets, stated once, on the IR.  `LeadsK`
  keys its last line by erasure (`pastKey`), so a written line need not
  match binder names; `legacyWritten`/`ppLegacyLine` print it.  The erased
  `LineRw` library (`Calculus/ChainRewrites.lean`) and `NFml.Post` stay
  for W9.5.
- **Checks.**  Per-file diagnostics clean (`ChainRewrites`,
  `ChainRewritesOpen`, `ChainNotation`, `Tactics/Chains`, `ProofTree`,
  `CallOperands`, `ExampleNames`, `FreshNames`, `Chains/*`);
  `lean_build` of the default targets; `check-orphans`,
  `check-doc-paths`; `sorry` count unchanged (20 lines); axioms of
  `FmlRw.lawUpdE`, `FmlRw.mergePast`, `FmlRw.simplifyPast`,
  `FmlRw.applyStorageBoxP`, `Upd.apply_absorb`: `propext`,
  `Classical.choice`, `Quot.sound`.

### W9.5a `delete` record (2026-10-12, branch `w9-del`)

The syntax IR is deleted.  No prover code builds, reads or proves anything
about an untyped formula: every closer, chain, walk and printer reads
`Fml C Γ`.  160 files, +6.5k/−21.4k lines.

**Deleted modules**: `Calculus/{NFmlLogic, NFmlDerive, NFmlUpdateRules,
NFmlQuote, HoldsErase, CloseErase, Closable, CloseHavoc, Rewrite,
TheoryRewrite, ChainRewrites, ChainBranches, Literals, StateParts,
TermRules, TermTaclets}`, and the old `Calculus/Close` (`Valid.of_erase`).
**Deleted names**: `NFml` but its stub (`holds`, `Valid`, `Post`,
`NFml.Proves`, `NFml.Chain.*`, `NFml.toL`/`inL`/`valid_iff_reduce`, the
erased lowering in `Decide`), `Fml.erase`, `Proves.close` (with its
`SolkeyProves` case), `Hyp` and its rules, `Atom.name` (proposal 99: an
atom is a position, `key{}` spells a local `pos(k)` and reads no
identifier as a local; `Var.isSlot`, `LFml.slotKeys` check the quantified
keys where `LFml.syn_valid_alls` reads them), `dl_schema{}` and
`NFmlSeq`'s sequents, the erased delaborators, `holds_eqD_iff`, the erased
`TermTaclet`/`EvalLaw`/`Term.Theq`.

**Renamed / new**: `TermTacletS` → `TermTaclet`, `EvalLawS` → `EvalLaw`
(the rule map's column follows); `Calculus/NFmlClose.lean` →
`Calculus/Close.lean` (the simp sets and syntax of `sol_close`; the
elaborators are `CloseScoped`'s); `Calculus/Closable.lean` →
`Calculus/FirstOrder.lean` (`Fml.FO`, `Idx.nameR`, `Thin.namesR`);
`Calculus/TermLaws.lean` (the laws past the program, scoped: `LitLaw`,
`TermTaclet.RefLaw`, `EvalLaw`, `Upd.covers`/`coversRef`/`coversEval`,
`LawCov`, the evidence `FmlRw.lawUpdS` asks, sound by `TermTaclet.sound`
and `EvalLaw.sound`, no erasure lemma); `Calculus/StateFacts.lean` (the
state and symbol lemmas the deleted modules held, moved verbatim).
`FmlRw.lawUpdE`/`ErasedCov` became `FmlRw.lawUpdS`/`LawCov`.

**Chains past the program.**  A line's key (`Fml.lineKey`) is text: its
terms and updates printed by name (`Tm.keyStr`, `Upd.keyStrs`), a
program as its statements, a postcondition by its slot.  A written line
with no modality is read by name into the same key (`elabKeyQ`), so it
need not declare a memory local it no longer writes.  `Fml.LeadsK φ L` is
`∃ B, Fml.Leads φ B ∧ B.eraseNames = L.eraseNames` (`L` read where it
stands, the binders' names aside: `Fml.eraseNames`, `holds_eraseNames`),
and `Fml.LeadsK.valid h hL : Valid φ` from `Valid L` (the coordinator's
point: `ChainNotation`'s `composed` now proves `Valid` by it).  A law's
instances are found on the scoped line (`lawInstances`, `spinePositions`
for the `…In` laws), its side conditions closed by `rfl`/`decide` or a
`Tm.KindFreeAt` hypothesis (`Tm.KindFreeAt.ofNil`).  The line's closed
terms are read once a candidate search, not once a law (`tsMemo`:
`Chains/Storage` 9.05 → 8.25 s).

**Folded**: one traversal for every rewrite of an update's right-hand
sides (`Tm.rwBy`, `Upd.rwBy`, `Upd.hasBy`, sound by `Upd.rwBy_apply`,
`_rev`, `_eq` over `PickLe`/`PickGe`/`PickEq`), of which `Upd.rwC`
(`Tm.pickClosed`) and `Upd.rwG` (`LawPair.pick`) are instances;
`Tm.down?`/`Rhs.down?` as `thinS? (.drop .refl)`; `Tm.isLit` as
`(Tm.litVal? t).isSome`.  Dead code the deletion left (a probe over the
environment, kept only where the name had a user at `887f4d1a`): the
erasure's `*_nat`/`*_wl`/`Agree.*` lemmas, `Decide.Rel`/`EnvRel`, the
`Surface.*` frame lemmas, `Tm.reads`, `Surface.Tm.lsize`, and others.

**What remains of the untyped syntax, and why.**  `Surface.Tm`/`MAddr`/
`Upd`/`UpdElem`, `Tm.erase`/`Upd.erase`, `DelabErase`'s `Delab.tr` and
its helpers (`Delab.Env`, `loweredVar?`, `wkUp?`, `isUp`, `isCtx`,
`unknownVar`, `stmtOutNames`, `withTwins`, `updParts`, `updList`) and
`inductive NFml (C) | eq (a b : Term C)` (`Update.lean`, the one
constructor `Delab.tr` emits) remain only as the SolKey reader's shim
(the user's decision: the reader is not ported, side-projects untouched);
no prover code reads them.  The untyped terms are also the notation's
front end: `tm{}`, `st!{}`/`pt!{}` and a chain's by-name key are parsed
into `Surface.Tm` and resolved to `Tm C Γ` (`Tm.resolveN`) or printed
(`Surface.Tm.keyStr`).  The state IR (`Env`, `EState`, `State.erase`,
`CloseS.holdsE`) stays for W9.6.

**Pins moved**: `ChainRewrites` (the `add_literals` side condition now
prints `Int.ofNat …`, `findOnSaveFrame`'s the scoped `Tm.app1 … diverges`;
`Laws.readBack`/`Laws'.readBack` stated as scoped `TermTaclet`s, `hk` a
`Tm.KindFreeAt`); `Chains/StorageDelete` (`hk` a `Tm.KindFreeAt`);
`Tactics/Chains` (the memory `~~>`/`sol_rws` example is the explicit
`Via` chain `#chain` writes: its last line read where it stands cannot
match the computed line's binders); `ChainNotation` (a new
`(composed m φ).valid h`); `KeyNotation` (named locals spelled `pos(k)`,
the `se1` example gone); `Tactics/Decide`'s memory clauses (`at(pos(0))`
for `at(i)`; the `#eval` results unchanged); `TermLib`'s `Tm.reads`
example gone; `CloseTests` (`sol_leaf` for `refine close ?_; sol_symex`).

**Checks.**  `lake build` of `Solidity`, `solkeycheck`, `SolidityCorpus`
and `SolkeyTestSuite` (a temporary default-target list, restored):
green.  `.lake/build/bin/solkeycheck`: OK (326 taclets at the local
`../solkey`).  `check-orphans`: only `Solidity/Scratch`.
`check-doc-paths`: no missing path.  `sorry` lines 19, as at
`887f4d1a`.  `#print axioms` of `FmlRw.lawUpdS`, `Fml.LeadsK.valid`,
`holds_eraseNames`, `LawCov.covered`, `Upd.rwBy_apply(_rev, _eq)`,
`holds_upd_rwG`, `Proves.sound`, `Valid.of_reduceS`,
`LFml.syn_valid_alls`: `propext`, `Classical.choice`, `Quot.sound`.
`check-testsuite.sh` refuses the local `../solkey` (`4150e0a8`, stale, as
before).  `rg "\bNFml\b"` outside the records: the stub and the reader
shim's docs.

**Gates** (fresh worker, wall s; base measured at `887f4d1a` the same day):

| Row | Gate | Base | W9.5a |
|---|---|---|---|
| `Derived1`–`14` (sum) | 237.8 | 179.1 | 180.9 |
| `Derived7` | 61.7 | 47.9 | 48.5 |
| `Tactics/Decide` | 45.0 | 38.9 | 39.1 |
| `ProofTree` | 11.7 | 8.3 | 8.3 |
| `Chains/Storage` | 9.0 | 8.7 | 8.3 |
| `ChainRewrites` | 8.2 | 7.6 | 7.1 |
| `ChainRewritesOpen` | 4.1 | 5.0 (cpu 3.7) | 3.5 |
| `Solkey/TestSuite` | 13.2 | 6.8 | 6.9 |

### W9.5 review fixes (2026-10-12, branch `w9-tidy`)

The confirmed findings of the W9.5a review, fixed:
- **Dead code** deleted: `Tm.rwC_eval` (`Calculus/SeqRewrite.lean`),
  `Skel.isConn` (`Calculus/RewriteScoped.lean`), an unused
  `variable {U : Surface.Upd C} …` (`Calculus/StateFacts.lean`).
- **Kept as the reader's shim**, with no prover user: the lemmas over
  `Surface.*` listed under W9.5b below.  Their section docstrings now say
  so; they are not deleted because the user keeps the reader untouched.
- **`docs/module-map.md`**: the Closers, CloseTests and DecideLang rows no
  longer describe an erased leaf (`sol_fold_terms`, `Derive.eraseLeaf`,
  `Valid.of_erase`, the erased fallback, an erased atom's name); dangling
  names fixed or dropped (`Idx.nameR_eq`, `lawResolveQ`, `pairL`/`pairMem`
  → `pairLS`/`pairMemS`/`allocPairS?`, `Config.erased`, `Stmt.complete`,
  `Proves.close_leaf`, `State.glob` → `EState.glob`); `Update.lean` holds
  the terms, updates and the shim, not the closer's formulas (here and in
  `AGENTS.md`); the DelabErase and NoPanic rows say what reads them.
- **`docs/lean-key-rule-map.md`**: the old `pair_sound` is `RelU.two`
  (with `RelU.pairKey`).
- **Docstrings** that described the deleted erased side as live, or cited
  a deleted name, rewritten (prose only): `Fml.erase`, the twin check,
  `close_rw`'s "untyped formulas", `STerm.eval_mtSt`, "today's macro",
  `NFmlClose`, `ChainBranches`/`LineRw.*`, `Surface.Upd.mergeMem`,
  `holds_eqD_iff`, `Surface.Tm.spineAny` and kin, the `PTerm.*`/`STerm.*`/
  `Term.*`/`SValT.*` twins in `Calculus/TermLib.lean`,
  `Calculus/TermLaws.lean`, `Calculus/Decide.lean`,
  `Calculus/DecideScoped.lean` (each "`X`, by position" now says what it
  does), `Calculus/DecideRel.lean`, `Calculus/LeafDerive.lean`
  (`Derive.*`), `Calculus/Proves.lean` (`Hyp.*`), `Derive.fitsClose` →
  `Seq.leafFitsOn`, `Derive.elimSize` → `Decide.elimSize`, and the
  examples' `Upd.mergeSt`/`mergeStL`/`mergeMem`/`withStM`/`Tm.rwEv`/
  `LineRw.lawUpdAny`/`Upd.rwEv`; the misplaced "Pins" heading of
  `Calculus/TermLaws.lean` moved to its section.
- **`docs/testsuite-proofs.md`**: `Calculus/ChainRewrites` (deleted) for
  the bare `ChainRewrites`.  `Typing/Reachability.lean` and
  `Typing/Constructibility.lean` bound a pattern variable named
  `Surface.Tm` (a W5 rename's leftover): renamed `Tseg`.
- The lead's note of 2026-10-11 (2) (proposals 106–128 approved; "`NFml`
  and its term vocabulary stay as the closer's IR") left "What is left":
  superseded by W9, which removed that IR.

## W9.6 plan (the state IR, the notation's front end)

Asked by the user on 2026-10-12 ("put the types on it"; chosen: W9.6 and
the typed notation, the reader's shim frozen, side-projects untouched).
Speed warning given first: the closer's `simp` reads typed locals
(`LTy.TDenote C σ.H`), so `sol_close` may slow; no kernel path evaluates
`Tm.eval` (`sol_decide` decides `inLS`/`closeS` over the syntax, the
refutation `TRes.isPanic` over the typed run).  Gates: the W9 table.

**Three parts of the state IR.** (1) The program evaluators
(`Semantics/Erased.lean`'s `Val.eval`, `Loc.resolve`, `OpLoc.*`, …), read
only by `StepErase`, `SoundArms`' equations and `Typing/`'s `EKeeps`/
`SRuns`.  (2) The term reader: `Tm.eval`/`Tm.denote` read `σ.glob` and
`Env.get`; over `State C Γ` they read `State.globE σ` (the global part
from the value-level erasure) and `TDenote.erase (TEnv.get i σ.env)`, equal
by `rfl` per constructor.  The symbols `Op0`–`Op3` stay untyped over
`Semantics.State` (decision 83: `save` of an untyped `sv` may build an
ill-typed storage).  (3) An update's result: an untyped `MObj` does not fix
the heap typing, an allocation pair writes the local before the heap that
types it, and `net`/`pay` read the intermediate global part, so an update
cannot be applied element by element to a typed state.  Two carriers:
- **U1, the pair**: `Upd.apply σ₀ : Res (Semantics.State × Env C Δ)`,
  `Env` kept as `TEnv.erase`'s target; `EState` goes, `holdsE` becomes a
  reading at the pair.
- **U2, landing**: `Upd.Lands σ₀ U g σ'` relates the typed result directly;
  `holdsE` and `Env` go, every update law is restated, the closer reads
  `holds` (measured at about 3× `holdsE`'s work at W9.3).

| Wave | Lanes | Work | Rows at risk |
|---|---|---|---|
| W9.6.0 | spike (scratch) ‖ `notation` | **spike**: the typed `Tm.eval` (`rfl` against today's); U2's `Lands` for every `UpdElem` with `decl`/`pop`/`drop`, `Lands ↔ σ'.erase = τ`, `holds_upd_graft` and `Premise.sound_update` for the allocation pair; `sol_close` on `Derived7`'s leaves and `SelectOnSaveConsr` read through U1 and U2 against `holdsE`.  Chooses U1 or U2.  **notation (W9.6N)**: `tm{}`, `st!{}`/`pt!{}`, a chain's by-name key and the spec front end parse to `Tm C Γ`/`Upd` directly; `delabTmS` prints a scoped term without `tmSurface`; the twin check goes; `Surface.*`, `Tm.erase`, `Delab.tr`, `NFml` stay as the reader's frozen shim, read by nothing in the prover | notation pins |
| W9.6.1 | `logic` ‖ `inv` | `Logic.lean`'s readers on the typed state with the chosen carrier (old ones kept as `rfl` twins), `holdsC`, `Deploy`; `RunInv.HoldsT` over `State` in `Typing/TypedRunInv.lean`, `TKeeps` per statement against `TRun` (replaces `EKeeps`, `canonInv.ekeeps`, `SRuns.of_agrees`, `Faithfulness`' `RunWT`) | all rebuild, no pin |
| W9.6.2 | `sound` ‖ `laws` | `Premise.sound_update` and `SoundArms`' equations against `TRun.*`, then `SoundCalls`/`Local`/`Loops`, `CallbackSound`, `ProvesSound`; the update laws (`Graft`, `UpdRuleScoped`, `RewritePast`, `TermLaws`, `UpdateRules`, `RewriteScoped`, `SeqRewrite`, `StatePartsScoped`, `LeafDerive`, …) | `Chains/*`, `ChainRewrites*`, Derived |
| W9.6.3 | `decide` ‖ `close` | `RelB`/`RelU`, `peelS`, `redState`, `Valid.of_reduceSL` on the typed state; `CloseScoped` without `EState` (U2) or on the pair (U1); `Close`, `CloseTests`, `Closers`, `State.lift?` | `Tactics/Decide`, Derived, `Solkey/TestSuite`, `ProofTree` |
| W9.6.4 | master | delete Erased's evaluators and `EState` (and `Env` under U2), the twins, `StepErase` (its `State`/`TEnv` erase lemmas move to `State.lean`), the old `RunInv.Holds`/`EKeeps`; docs | all |

**Fallback**: if U2 fails the gate, U1 (the evaluators, `EState`,
`StepErase` and the erased invariant still go).

### W9.6.0 record (the spike)

**U1 chosen.**  U2 is sound and complete: `Upd.lands_iff : U.Lands σ₀
σ'.globE σ' ↔ U.apply σ₀.erase = .ok σ'.erase`, `holds_upd_iff` (U2's
clause equals `holds`'), and the allocation pair lands on
`(σ.allocDefault R hm).1.push (some id)` with no `EState`.  But a leaf read
through `Lands` costs 1.8× `holdsE`'s (`ageWriteRead`: 116–131 ms against
70–78 ms; `sol_close` 103–105 ms), and every law would be restated over
hypotheses instead of a computed state.  `EState` is the pair `U1` names,
so it stays as an update's result and nothing else: what a typed state
erases to and what the laws compute on.  The typed reader
`Tm.evalT σ t = Tm.eval σ.erase t` is not `rfl` at an abstract position
(`Env.get i (TEnv.erase x)` recurses on `i`): one `TEnv.get_erase` per
local case.  What W9.6 removes, then: the program evaluators, `StepErase`,
the erased run invariant (`EKeeps`, `SRuns.of_agrees`), so the soundness
and the invariants read the typed run only.

### W9.6N record (2026-10-12, branch `w96-notation`)

The notation's front end reads straight to the scoped terms: nothing in
the prover or the notation builds, reads or prints a `Surface.*` term, and
`Tm.erase`, `Delab.tr` and `NFml` are read by nothing in the package.  They
stay, frozen and unrenamed, in the modules the reader imports (`Update.lean`,
`Calculus/Fml.lean`, `Calculus/RuleSyntax.lean`, `Calculus/DelabErase.lean`).
No speed change expected: the readers build closures instead of untyped
trees, resolved once where they stand, as `NRead` already was.

- **Terms by name** (`Calculus/NamedTerm.lean`, new): `NTm C s` is a
  term's text (`key`, what `Tm.keyStr` writes of the term it names) and
  the scoped term it is at each named context (`resolve : (Γ : NCtx) →
  Except String (Tm C Γ.ctx s)`), a local the newest of its name and of its
  sort's kind, with `Tm.resolveN`'s error texts.  `NTerm` … `NMValT` carry
  `Update.lean`'s symbol names (`.find .storage p` reads as before),
  `NTm.ofTm ns t` reads a scoped term by its names, `NUpdElem` is an
  update's element (`keyStr`, `setsLocal?`, `fits`, `ownTy?`).
  `NCtx.findAny` and `kindError` moved here (no `FreshNames`).
- **The readers** (`Calculus/SurfaceNotation.lean`: `readers`, `tVal` …,
  `elabUpd`) return `NTm`s and `NUpdElem`s; `elabCompare` reads the
  lowered scoped operands by name (`NTm.ofTm`), where it erased them.
  `Surface.elemTy` is `arrayElemTy`.
- **Resolution** (`Calculus/NotationResolve.lean`): `Tm.resolveN` and the
  `Surface.UpdElem.*` helpers deleted; `Rhs.resolveN`/`Upd.resolveN` read
  `NUpdElem`s, `NRead.eq`/`eqD`/`defined`/`bool`/`cmp` `NTerm`s.
- **`st!{}`/`pt!{}`** resolve the read term at `[]` (`(·.resolve [])`).
- **A chain's by-name key** (`elabKeyFml`) is the terms' `key`s and the
  elements' `NUpdElem.keyStr`: `Surface.Tm.keyStr` and
  `Surface.UpdElem.keyStr` deleted.  Not left on the shim.
- **The spec front end** (`Calculus/SurfaceSpec.lean`) writes its clauses,
  layout and frame over `NTerm`/`NPTerm`/`NSTerm`, its snapshot update as a
  `List (NUpdElem C)`, which `Upd.resolveN` declares (`Calculus/Spec.lean`).
- **`tm{ … }`** (`Calculus/TermLib.lean`) is always the scoped term where
  `TermLib` is imported (its untyped fallback where the expected type was
  not a `Tm` is gone; it postpones until the type is known).  The untyped
  `tm{ … }` of `Calculus/RuleSyntax.lean` (`schemaTerm` building
  `Surface.Tm`) and its printer `delabTm` remain, for the reader and the
  rule table, in modules that do not import `TermLib`.  It still reads its text by
  `RuleSyntax.schemaTerm` and turns the names into the scoped symbols by
  `coreNames`, the rule table's own path: syntax only, no untyped value.
- **`delabTmS`** prints by `Calculus/PrintTerm.lean`'s `ppTermS` …
  `ppMValS` at `[]`, under `pp.sol.reduce false`, after unfolding the
  scoped symbols (`Tms.*`, `Tm.lit`/`storage`/`memory`) down the term
  positions (`unfoldTmsSyms`); `tmSurface`, `tmsTwin?`, `sortType?`,
  `withTmTwins` deleted.  Inside a `‹…›` of its own a scoped symbol prints
  with the field notation the twin printed (`s.save p v`,
  `delabTmsField`, under the new `pp.sol.tmField`, which only `delabTmS`
  sets), so `TermLib`'s pins are unchanged; elsewhere (`pp.sol.dl false`,
  `Examples/Notation.lean`) a `Tms.*` application prints as Lean prints it.
- **The twin check is deleted** (`Calculus/PrintStmt.lean`):
  `pp.sol.twinCheck`, `twinCompare`, `PEnv.tr`, `runTr`, `termS`, and the
  checks in `termPP`, `eqDPartsS`, `updS`, `ppFmlS`'s comparison and
  `withPrinter`.
- **Moved**, no reader use and prover-only modules: the `Surface.*` lemmas
  of `Calculus/NoPanic.lean` and `Theory/Bridge/Denote.lean`
  (`Surface.Tm.eval_noPanic`, `Surface.UpdElem.write_noPanic`,
  `Surface.Upd.apply_ne_panic`, `Surface.Tm.denote_eval`,
  `SValT.denote_eval`) to a module of their own, unchanged; it had no
  consumer and was deleted at the W9.6 review.  Two unused
  `variable {q : Term C × Term C}` of `Calculus/StateFacts.lean` deleted.

**Checked**: per-file diagnostics of every touched module; `lean_build` of
the default targets (every example pin: `Examples/ProofTree.lean`,
`Examples/Tactics/Print.lean`, `Examples/Tactics/DlNotation.lean`,
`Examples/Notation.lean`, `Examples/ChainNotation.lean`,
`Examples/ChainRewrites.lean`, `Examples/ChainRewritesOpen.lean`, the
`Examples/Chains/` modules, `Examples/Tactics/Spec.lean`,
`Examples/Tactics/Specs.lean`, `Examples/Tactics/SolSpec.lean`, `Calculus/TermLib.lean`'s and
`Calculus/TermLaws.lean`'s), clean; `check-orphans`, `check-doc-paths`; no
new `sorry`.  Not run: `SolkeyTestSuite` (it reads no notation front end).

### W9.6.1 inv record (2026-10-12, branch `w96-inv`)

The run invariants and the typing results read the typed run only: nothing
in `Typing/` or `SortCheck/` imports or names `Semantics/StepErase.lean`,
`TRes.Agrees`, `StepAgrees` or `Semantics/Erased.lean`'s program evaluators
(`Val.eval`, `Loc.resolve`, `OpLoc.*`, `MRhs.eval`, `CallRet.enter`, …),
but `Typing/Soundness.lean`, left as it was so that `Calculus/Logic.lean`
and everything above it do not rebuild.
- **`RunInv.HoldsT`** (`Typing/TypedRunInv.lean`) beside the old
  `RunInv.Holds`: the invariant of a typed state, its global part read as
  `σ.erase.glob` and its locals as `TEnv.erase Γ σ.env` (definitionally
  `Holds H σ.erase`).  `TKeeps` reads it; `EKeeps`, `TKeeps.of_agrees`,
  `StepAgrees.ok` and `CallRet.enterT_ok` are gone.  A call's and a `try`'s
  locals are values or a fresh memory object, and every invariant here
  reads the global state through its storage alone (`RunInv.ValMemOk`), so
  `tkeeps_call`/`tkeeps_tryCall` lost their argument, entry and decoding
  hypotheses.  The `TEnv` facts it needs are restated over `Env.All`
  (`Env.All.tappend`, `ttake`, `tset`, `tdrop`, `twk`), and
  `SRef.field_erase`/`SRef.index_erase` are `StepErase`'s
  `SRef.erase_field`/`erase_index` under new names (both modules are
  imported together above `Typing/`).
- **The leaves on `TRun.*`**: `Typing/Reachability.lean` (`keepsC_*`,
  through `Storage.find_canon`, `save_canon`, `write_canon`,
  `delete_canon`, `push_canon`, `pushPlace_canon`, `pop_canon`: each typed
  storage operation through its erasure lemma, over `Storage.glob st`, the
  untyped state of the storage alone, under the empty store typing),
  `Typing/Constructibility.lean`'s `tight_*` (`Tight` is now of a typed
  state; keys by `SPath.resolveT_keys`, live indices by
  `Loc.resolveT_live` through `Storage.checkIndex_erase`) and the builder
  (`Resolves σ q r segs`: the typed path resolves to a reference erasing to
  `r.segs`; `run_push`, `run_pop`, `run_delete`, `run_assignLit`,
  `run_decl` compute the typed step and read it back through
  `pushAt_erase`, `popAt_erase`, `delete_erase`, `writeStorage_erase`;
  `SRuns.of_agrees`, `push_none_ends` and `TRes.Agrees.ok_of_ends` are
  gone), `Typing/Fits.lean` (its leaves were typed already; its scopes and
  `RunFits` moved to `HoldsT`).  `State.glob_wt` (`Typing/TypedWT.lean`)
  states the global part's well-typedness without `RunWT`.
- **`SortCheck/Faithfulness.lean`**: `Read.SortOk σ rs` reads the typed
  evaluators (`resolveT`, `Storage.find`, `mvalT`, `Val.evalT`) of a typed
  state, erased; `Read.sortOk` needs no invariant (the values are of their
  types, `SVal.erase_hasTy`, `MVal.erase_hasTyH`), and `RowFaithful`
  quantifies over typed states.  `Counterexamples/PreFixSortAnnotations.lean`
  refutes the pre-fix rows on `State.init` (`person_not_int`,
  `bool_not_int`).  `Read.sortOk_typed` is deleted: `Read.sortOk` is its
  statement, with no `nodupKeysB` hypothesis.
  `Counterexamples/WellTypedNecessity.lean`'s ill-typed store is no typed
  state, so its last conjunct could no longer be `¬ Read.SortOk`; it was
  replaced by two facts stated apart (`badStore.findStorage "total" [] =
  .ok (.bool true)` and `SortOkS … (.bool true) = false`), which no longer
  linked the read to the store: restored at the W9.6 review (record below).

**Statements changed** (by reading `State` for `EState`; for
`RowFaithful` and `Read.SortOk` that is a narrower claim, below):
`Prog.run_canon` and `Prog.run_tight` take and give `σ.storage.erase`
(`CanonStorage C σ.storage.erase`, `Tight C σ` of the typed state);
`Tight.init : Tight C (State.init C)`; `no_hidden_invariant`'s step reads
`σ.storage.erase`; `RunCanon`/`RunTight`/`RunFits` are over `State`;
`RowFaithful`/`Read.SortOk` as above: they quantified over every erased
state meeting `RunWT` and now over the typed states, a subset (every
typed state erases to a `RunWT` one), so the positive `faithful_*` results
claim less; kept, since every reachable state is typed;
`readSelect_needs_storage`'s last conjunct (above).  `reachable_canon`,
`reachable_tight`, `reachable_iff`, `reachable_iff_fits`, `canon_reachable`
and the witnesses are unchanged (axioms: `propext`, `Classical.choice`,
`Quot.sound`).  The `keepsC_*` leaves lost their unused side conditions.

**`EState` as a carrier, where it stays**: `HoldsT` reads `σ.erase.glob`
(an update's result is the pair, decision U1); the builder tracks
`σ.erase.storage` and `σ.erase.env` through `Wrote`, `Bound` (the alias on
the erased locals) and `Wrote.saveCore`; `Reachable.init_erase` is kept
for `Calculus/Problem.lean`.

**Deleted at W9.6.4**, with no `Typing/` reader now: `RunInv.Holds`,
`RunWT`, `wtInv`, `Holds.withEnv`/`drop`, `RunWT.*` and the evaluators'
typing (`Loc.resolve_wt`, `SPath.resolve_wt`, `MPath.mval_wt`,
`MLoc.read_wt`, `Val.eval_wt`, `Simple.eval_wt`) in `Typing/Soundness.lean`,
`State.erase_wt` (`Typing/TypedWT.lean`), and `CallRet.leave_all`.

### W9.6.2 sound record (2026-10-12, branch `w96-sound`)

The rules' soundness reads the typed run against the rules' terms directly:
`Calculus/` neither imports nor names `Semantics/StepErase.lean`, nor any
program evaluator of `Semantics/Erased.lean` (`Val.eval`, `Loc.resolve`,
`MLoc.addr`, `OpLoc.store`/`bump`, `MRhs.eval`, `Src.value`, …).  Carrier U1:
an update is still applied to `σ.erase` (`EState`), and `holds`/`Tm.eval`
read it there (`aliasPath`/`memRef` stay, as the term readers).

- **The evaluators against the terms** (`Calculus/LowerRun.lean`, new):
  `Val.lower_evalT : TRes.Agrees PrimTy.erase (v.evalT σ) (v.lower.eval σ.erase)`
  and its mutual kin (`SPath`/`Loc.lower_resolveT`, `MPath.lower_mvalT` at
  a reference type, `MLoc.lower_addrT`), `Simple.lower_evalT`,
  `Simple.denote_lowerT`, `Src.lower_valueT`, `MSrc.lower_mvalT`,
  `readAddr_erase`; by induction on the syntax over the typed evaluator,
  from `TEnv.get_erase` and the storage/heap erasure.  The mutual block
  recurses on `MPath` at `.ref R` (well-founded, found by Lean).
- **The seam** (`Semantics/TypedErase.lean`, new): imports `StepErase` for
  its value-level lemmas (`TRes.Agrees`, `opStoreT_erase`,
  `bumpStoreT_erase`, `writeAddr_erase`, `MAddr.erase`, `TRun.clearT_erase`,
  …) and adds `TRes.Agrees.eq_ok`/`eq_error`/`of_eq_right`/`bind_fst`.  At
  W9.6.4, when those lemmas move below it, it imports their new home.
- **The kit** (`Calculus/SoundKit.lean`): `Premise.sound_update_typed`,
  `sound_updateSim_typed`, `sound_cases_typed` take the statement's typed
  step agreeing with the update on the erasure; `sound_update_erased`,
  `sound_updateSim_erased`, `sound_cases_erased`, the erased `*.eval_lower`
  lemmas, `Tm.keyAt_eval` and `Val`/`SPath`/`Loc.*_noPanic` are deleted.
- **The arms** (`Calculus/SoundArms.lean`): each `*_run` equation against
  `StepAgrees.erased` is now `*_agrees` (typed step against `U.apply σ.erase`).
  A compound target is read once as a term (`save_compound`,
  `write_compound`, `save_bump`, `write_bump`, `save_bump_assign`,
  `write_bump_assign`, `bumped_find`, `bumped_read`), the typed side by the
  global ops' erasure; `send_sim`, `clearMem_sim` are up to the halt.
- **Statements changed**: `sound_allocCopy`'s hypothesis is the right-hand
  side's typed agreement (`TRes.Agrees … (r.evalT σ) …`, given by
  `allocCopy_copy`/`allocCopy_newArr`) where it was an equation of
  `MRhs.eval`; `Val.eval_erase_ok`/`_error` (`SoundLoops`) are
  `Val.lower_eval_ok`/`_error`; `Simple.eval_lower`/`denote_lower`
  (`Logic.lean`) are deleted for `Simple.lower_evalT`/`denote_lowerT`.  No
  `*_sound`, `Stmt.sound`, `Proves.valid` statement changed; their axioms
  are `propext`, `Classical.choice`, `Quot.sound`.
- **Deleted, unused**: `MPath.mval_noPanic` (`SoundStore`),
  `MSrc.mval_noPanic` (`SoundMem`), `Res.map_bind'`,
  `Res.Sim.err_of_not_ok`.
- **Still on `StepErase`/the erased evaluators**: `Typing/` (`EKeeps`,
  `SRuns.of_agrees`, `Constructibility`, `Reachability`, `Fits`,
  `TypedRunInv`: the `inv` lane), and the value-level lemmas the seam
  re-exports.  `Theory/StateWrites.lean` names `MPath.mval` in a docstring.

**Checked**: per-file diagnostics of `LowerRun`, `TypedErase`, `SoundKit`,
`SoundArms`, `SoundStore`, `SoundMem`, `SoundControl`, `SoundLoops`,
`Sound`, `CallbackSound`, `Theorems` (and the Sound chain they import),
clean; `#print axioms` above; no new `sorry`; `check-orphans`,
`check-doc-paths`; no removed name is read elsewhere (`rg`).  Not run: the
default build (the modules above `Logic.lean` lost only its two unused
`Simple` lemmas and a docstring) and `SolkeyTestSuite`; no speed
measurement (no row is time-sensitive).

### W9.6.4 record (2026-10-12, branch `w96-del`)

**Merged master built first**: the three lanes (`w96-notation`, `w96-inv`,
`w96-sound`) build together, default targets and `SolkeyTestSuite`, with
no fix needed.

**Deleted** (`git diff --stat master`: 2,165 Lean lines removed, 515
added, all of them moved; 19 Lean files):
- `Semantics/Erased.lean`'s program evaluators: `Simple.eval`,
  `SPath`/`Loc.resolve`, `MPath.mval`, `MLoc.read`/`write`/`addr`/`write_eq`,
  `Val.eval`, `Src.value`/`pushVal`, `MSrc.mval`, `MRhs.eval`, `ARhs.eval`,
  `opLocal`, `OpLoc.store`, `bumpLocal`, `OpLoc.bump`, `sendAt`,
  `ExtCall.key`, `Args.eval`, `Binders.defaults`/`decode`,
  `CodeBinder.decode`, `CallRet.enter`/`leave`, `guardOk`, `assertOk`
  (453 → 181 lines).  `Env`, `EState` and `aliasPath`/`memRef` stay.
- `Semantics/StepErase.lean` (1,361 lines), merged into
  `Semantics/TypedErase.lean` (58 → 509 lines; it sits above `Run`, which
  the `TRun.*` lemmas need, so not `State.lean`): every lemma stating an
  agreement with an erased evaluator went (`Val.evalT_erase` and its mutual
  kin, `Src.valueT_erase`, `MSrc.mvalT_erase`, `ARhs`/`MRhs.evalT_erase`,
  `MLoc.addrT_erase`, `OpLoc.storeT_erase`/`bumpT_erase`,
  `Args.evalT_erase`, `ExtCall.keyT_erase`, `Binders`/`CodeBinder.decodeT_erase`,
  `CallRet.enterT_erase`/`leaveT_erase`, `StepAgrees`, `StepAgrees.erased`,
  and the 21 step lemmas `TRun.*_erase`, `assign_erase` to `assert_erase`;
  `TRun.clearT_erase`, `State.allocDefault_glob`, `State.erase_env_adopt`
  stay), and the value-level lemmas
  moved unchanged (`TRes.Agrees` and its kit, `TRes.NoPanic`, the
  evaluators' `*_noPanic`, `SRef.erase_field`/`erase_index`, `MAddr.erase`,
  `writeAddr_erase`, `opStoreT_erase`, `bumpStoreT_erase`, `opMemT_erase`,
  `bumpMemT_erase`, `compound_erase`, `bump_erase`, …).  Then the ones left
  with no reader: `State.withStorage_into`, `PrimTy.ofValue?_fits`,
  `TEnv.append_erase`/`take_erase`, `Binders.defaultsT_erase`,
  `State.pay_erase`, `TRes.Agrees.emap`/`mapLeft`,
  `TRun.State.withGlob_copyStToMG`.  `Semantics/NoPanic.lean` imports
  `TypedErase`.
- `Typing/Soundness.lean` (706 → 280 lines): `RunInv.Holds`,
  `Holds.withEnv`/`drop`, `wtInv`, `RunWT` and `RunWT.*` (`init` too),
  `CallRet.leave_all`, the evaluators' typing (`Simple.eval_wt`,
  `aliasPath_wt`, `SPath`/`Loc.resolve_wt`, `MPath.mval_wt`,
  `MLoc.read_wt`, `Val.eval_wt`, `Binders.defaults_wt`), and the lemmas
  only they read (`evalBinop_wt`, `evalUnop_wt`, `mHasTyHFields_lookup`,
  `mHasTyHElems_mem`, `MObj.hasTyH_arrElem`, `RefTy.arrElem?`,
  `ArrTy.arrElem`, `MVal.asValue_hasTy`, `Value.toMVal_hasTyH`,
  `SVal.asValue_hasTy`, `MVal.asRef_ok`, `int_toSVal_hasTy`,
  `applyBinOp_nonarith_bool`, `StateWT.ofCopyOut`, `compound_isArith`,
  `newArrVal_hasTy`, `map_ok_inv`, `LTy.WT.mem_some`,
  `Contract.layout_tyAt_root`).  `RunInv`, `RunInv.env_mono`, `Env.All`,
  `LTy.WT` stay (`Typing/TypedRunInv.lean`, `WellTypedNecessity`).
- `Typing/TypedWT.lean`: `State.erase_wt`, its example, and
  `LTy.TDenote.erase_wt`/`TEnv.erase_wt` (read only by it);
  `State.glob_wt` stays.  `Tools/Taclet.lean`'s scoped-family list lost
  `RunWT`.
- Prose naming them: the module docstrings of `Erased`, `TypedErase`,
  `Typing/Soundness`, `TypedWT`, `Typing/State`; docstring citations in
  `Semantics.lean`, `Run`, `Heap`, `HeapErase`, `StateWrites`,
  `Constructibility`, `StoragePreservation`; `.claude/rules/typing.md` and
  `soundness.md` (an update arm is now `*_agrees` closed by
  `Premise.sound_update_typed`); `docs/module-map.md`,
  `solc-alignment.md`, `solc-validation.md`, `solkey-feedback.md`,
  `loops.md`, `testsuite-proofs.md`, `lean-key-rule-map.md`.

**Checked**: `lean_build` of the default targets and `SolkeyTestSuite`
(`SolkeyTestSuite` added to `defaultTargets` for the build, not
committed), clean; `check-orphans` (310 reachable), `check-doc-paths`;
`sorry` count unchanged (19 occurrences, prose and strings); `#print axioms
Proves.valid`: `propext`, `Classical.choice`, `Quot.sound`.
`check-testsuite.sh` refuses the local `../solkey` (`4150e0a8`, stale, as
before).

**Gates** (each file copied under `Solidity/Scratch/`, a fresh worker
through the MCP, one at a time after a warm-up, `/proc` sampled every
20 ms, wall to the last CPU tick, wall s; load 1–5, no other Lean agent;
no base measured, the W9.5a column is the last record's):

| Row | Gate | W9.5a | W9.6.4 |
|---|---|---|---|
| `Derived1`–`14` (sum) | 237.8 | 180.9 | 177.8 |
| `Derived7` | 61.7 | 48.5 | 48.0 |
| `Tactics/Decide` | 45.0 | 39.1 | 39.4 |
| `ProofTree` | 11.7 | 8.3 | 8.3 |
| `Chains/Storage` | 9.0 | 8.3 | 8.3 |
| `ChainRewrites` | 8.2 | 7.1 | 7.2 |
| `ChainRewritesOpen` | 4.1 | 3.5 | 3.5 |
| `Solkey/TestSuite` | 13.2 | 6.9 | 7.0 |

Per file: `Derived1` 7.0, `2` 7.9, `3` 11.7, `4` 15.4, `5` 8.0, `6` 10.3,
`7` 48.0, `8` 25.2, `9` 5.8, `10` 8.7, `11` 2.7, `12` 12.2, `13` 6.3,
`14` 8.6.

### W9.6 review record (2026-10-12, branch `w96-review`)

A read-only review of W9.6 (finder and skeptic per area); each finding
checked against the code before it was acted on.

**Typing.**
- T1, confirmed and fixed: `readSelect_needs_storage`'s read and store were
  stated apart (the `Env.All` conjunct over a free `(.int 0, ())`).  It
  now reads the statement's path on `badCore` (`badStore` with the local
  `x`): the term `Val.lower` writes for the read, `find(storage,
  totalPath.lower)`, evaluates (`Tm.eval`) to `.bool true`, where the
  row's `SortOkS` is false; `Env.All` is of `badCore.env`.
  `Calculus/LowerRun.lean` is what makes that term the typed run's read.
- T2, confirmed and kept: `RowFaithful` over typed states is a narrower
  claim than over `RunWT` erased states; kept (reachable states are
  typed), and the W9.6.1 record now says so, with the
  `WellTypedNecessity` change and `Read.sortOk_typed`'s deletion;
  decision 57 has a dated note.
- T5, confirmed and fixed with T1: the docstring named `StateWT`.

**Soundness.**
- S2, confirmed and fixed: `RefTy.arrElem?`, `ArrTy.arrElem`,
  `MVal.asValue_hasTy`, `SVal.asValue_hasTy` deleted (no reader).
- S3, confirmed and fixed: the empty sections of `Typing/Soundness.lean`
  removed.
- S4, confirmed and fixed: unused `open` names trimmed in
  `Semantics/Erased.lean`, `Semantics/TypedErase.lean`,
  `Calculus/LowerRun.lean`.
- S5–S7, confirmed and fixed: the summary row names `TypedErase`;
  `solc-alignment.md` names `OpLoc.storeT`/`bumpT`, `MPath.mvalT`/`memRef`,
  `Loc.resolveT`; `kernel-port.md` `CallRet.enterT`/`leaveT`.
- S8, confirmed and fixed: `git diff --shortstat 09cd8878 f3d43a08` is 19
  files, 2,165 lines removed.

**Notation.**
- N1, N2, confirmed and fixed: `module-map.md`'s `Update.lean` row and its
  docstring say the untyped terms are the reader's shim only (and
  `RuleSyntax.lean`'s `tm{ … }` where `TermLib` is not imported).
- N3, confirmed and fixed: `Calculus/ShimFacts.lean` was outside the
  import closure of `Rules`, `DelabErase`, `KeyTaclets` (33 modules) and
  had no importer but `Solidity.lean`; deleted with its row and the
  records' mentions.  `testsuite-proofs.md` cited `Upd.apply_ne_panic`,
  now `Upd.apply_noPanic`.
- N4, confirmed and kept: `RuleSyntax.lean`'s untyped `tm{ … }` and
  `delabTm` are in the reader's closure.  The W9.6N record and
  `RuleSyntax.lean`'s notation table now say so.
- N5, confirmed and fixed: `termPP`/`updS` inlined (11 call sites).
- N6, confirmed and fixed: `PrintTerm.lean`'s docstring states the equal
  text as a design intent, unchecked since the twin check went.
- N7, confirmed and fixed: `unfoldTmsSyms` did not descend into
  `Tms.Term.bumped`'s operand, so `tm{ find(s, q)⊕⊕ }` printed as
  `tm{ ‹Term.find s q›⊕⊕ }`.  It now unfolds the operand (index 4) and
  keeps the `bumped` head for the printer's `t⊕⊕`; pinned
  (`bumped_pin`, `Calculus/TermLib.lean`).

**Checked**: per-file diagnostics of every touched module; `lean_build` of
the default targets (with the printer pins `Examples/ProofTree.lean`,
`Examples/Tactics/Print.lean`, `Examples/Notation.lean`), clean;
`check-orphans` (309 reachable), `check-doc-paths`; `sorry` count 19.

## W9.7 plan (the last untyped parts)

Asked by the user on 2026-10-12 ("put the types here as well, and let lean
solkey outdated"): the reader's shim goes, and so does `EState` as an
update's result.  The side-projects SolKey reader is left to break; it is
not edited.  Warned before: U2 costs about 1.8× `holdsE`'s work on a leaf
(W9.6.0); the gates stay the W9 table, and a row that fails is reported
with its leaf class, not hidden.

| Wave | Lanes | Work |
|---|---|---|
| W9.7.1 | `shim` ‖ `lands` | **shim**: delete `Surface.Tm`/`MAddr`/`Upd`/`UpdElem` and their lemmas, `Tm.erase`/`Upd.erase`, `Delab.tr` and helpers, the `NFml` stub, `RuleSyntax`'s untyped `tm{}`/`ppTerm`/`delabTm` (the rule table prints scoped terms); AGENTS.md's reader paragraph says the reader is outdated.  **lands**: `Tm.eval`/`Rhs.eval` over `State C Γ` (`State.globE`, `TEnv.get` erased), `Upd.globT`/`Held.OKT`/`Upd.Lands`/`Upd.afterT` (W9.6.0's sketch), `holds`' `.upd` clause by `afterT`, `holds_upd_iff` against the old clause while it exists |
| W9.7.2 | `laws` ‖ `close` | the update laws (`Graft`, `UpdRuleScoped`, `RewritePast`, `TermLaws`, `UpdateRules`, `RewriteScoped`, `SeqRewrite`, `StatePartsScoped`, `LeafDerive`, …) over `Lands`: a typed substitution lemma and `Lands` composition; `CloseScoped` reads `holds` by `Lands` (no `holdsE`), `RelB`/`RelU`/`peelS`/`redState` on the typed state, `Counterexample`'s `State.lift?` |
| W9.7.3 | master | delete `EState`, `Env` (if `TEnv.erase` has no other reader), `Upd.apply`/`UpdElem.write`, `holdsE`, `Erased.lean`; gates; review |

### W9.7.1 shim record (2026-10-12, branch `w97-shim`)

The SolKey reader's shim is deleted; the reader in side-projects is left
outdated, not edited (the user, 2026-10-12).  No speed change expected:
only dead code and one name lookup went.

- **`Update.lean`**: `Surface.Tm` and its sorts' abbreviations (`Term`,
  `PTerm`, `STerm`, `SValT`, `ITerm`, `Surface.MAddr`, `MTerm`, `MValT`)
  with their constructor patterns (`Term.find`, …, `Term.bumped`),
  `Surface.Tm.eval`, `Surface.Tm.denote`, `Surface.UpdElem`/`Surface.Upd`
  with `write`/`apply`, `NFml`, the "Frames" section (`Surface.Tm.vars`,
  `Surface.UpdElem.vars`, `Surface.Upd.vars`, `Op0`…`Op3.eval_agree`,
  `Op0`…`Op2.denote_agree`, `Surface.Tm.eval_frame` and the per-sort
  `eval_frame`s, `Surface.Tm.denote_frame`, `Surface.UpdElem.write_frame`,
  `readAddr_congr`, `arrayLen_congr`, `ResultsAgree.bindEq`, `Srt.Agree`,
  `Modality.after_frame`), `Term.keyAt`/`Term.keyAt_eval`.  Kept: the
  signature and the symbols' meaning (`Srt`, `Op0`…`Op3`, `OpN.eval`,
  `OpN.denote`, `Op1.vars`, which `Calculus/StateFacts.lean` reads),
  `IntOp`, `State.havoc`/`State.anon`, `PrimTy.admits`.
- **`Calculus/Fml.lean`**: `Tm.erase`, `Rhs.erase`, `UpdElem.erase`,
  `Upd.erase` (`Upd.names`, `Thin.names` kept: the printers read them).
- **`Calculus/DelabErase.lean`**: `Delab.tr` and its helpers (`generic`,
  `trArg`, `trIdx`, `updParts`, `elem`, `rhs`, `updList`, `Piece`,
  `loweredVar?`, `withProofHoles`, `legacyNames`/`legacyName?`/
  `legacyType?`, `isCtx`, `Env`/`TrM`, `twinsFrom`, `withTwins`).  What
  stays is the printers' name stack (`stmtOutNames`, `thinNames`,
  `extDepth`, `isUp`, `stripUps`, `wkUp?`, …); the module keeps its name.
  `isScopedFamily` named the scoped families by their erased twins; it now
  lists them (`Tm`, `Upd`, `UpdElem`, `Fml`, `Idx`), the same set, and
  takes no environment (`Tools/Taclet.lean`).
- **`Calculus/RuleSyntax.lean`**: the untyped `tm{ … }` (`macro_rules` to
  `schemaTerm`), its printer `delabTm` and the untyped printers
  (`ppTerm` … `ppMVal`, `keyAddr?`, `ppUpdElem?`, `updParts?`, `ppUpd`,
  `Surface.cmpParts?`, `foldTmHead`, `whnfTm`, `whnfPP`, `whnfF`).
  `elemTerm`/`lenTerms` stay (the scoped printers build with them).
  `schemaTerm` still writes the symbols by their KeY names (`Term.find`,
  `MAddr.field`, `UpdElem.storage`), now resolved by nothing below the rule
  table; `coreNames` maps such a name by its family (`coreFamily?`) to the
  scoped symbol (`Tms.Term.find`, `UpdElem.storage`) as it mapped the
  quotation's resolution before, and still fails on a missing one.  The
  `Surface` branch of `coreName?` is gone.
- **Docstrings**: `Arms.lean`, `Lower.lean`, `PrintTerm.lean`,
  `Rules.lean`, `KeyTaclets.lean` (the reader's corpus check no longer
  runs), `Tools/Taclet.lean`; `AGENTS.md`'s reader paragraph,
  `module-map.md`'s rows, `solc-alignment.md` (`Tm.keyAt`).

Printed output: unchanged (every pin builds).  **Checked**: per-file
diagnostics of `Update`, `Calculus/Fml`, `Calculus/RuleSyntax`,
`Calculus/Rules`, `Calculus/DelabErase`; `lean_build` of the default
targets, clean (the printer pins `Examples/ProofTree.lean`,
`Examples/Tactics/Print.lean`, `Examples/Notation.lean`,
`Examples/Tactics/DlNotation.lean`, the `#taclet` pins and
`#check_rule_text`); `check-orphans` (309 reachable), `check-doc-paths`;
`sorry` count unchanged.  Diff: 10 Lean files, about 1,480 lines removed.

### W9.7.1 `lands` record (2026-10-12, branch `w97-lands`)

**U2 in `holds`.**  `holds`' update clause is `Upd.afterT m σ (holds · φ)`
(`Calculus/Logic.lean`), and so is `holdsC`'s (`Calculus/CallbackHolds.lean`):
`p` of every typed state the update lands on, `m.onHalt` where its global
part halts.  The new module `Calculus/Lands.lean`, just below `Logic`,
holds what that reads:
- the `EState` readers moved out of `Logic` unchanged (`Tm.eval`,
  `Tm.denote`, `Rhs.eval`, `UpdElem.write`, `Upd.apply`, `Modality.afterC`),
  with `Graft`'s `Held`, `Subst`, `Subst.set`/`cons`, `Upd.held`,
  `Held.OK`, `Upd.held_ok` and its `Env` lemmas, and `UpdateRules`'
  `Env.ext_get`;
- the typed readers, W9.6.0's sketch: `State.globE`, `State.getE`,
  `State.aliasPathT`/`memRefT`, `Tm.evalT`, `Tm.denoteT`, `Rhs.evalT`,
  each equal to its twin on the erasure (`Tm.evalT_eq`, `Tm.denoteT_eq`,
  `Rhs.evalT_eq`, by `TEnv.get_erase` per local case);
- landing: `UpdElem.globT`, `Upd.globT`, `Held.OKT`, `Upd.Lands`,
  `Upd.afterT`; `Upd.apply_glob` (the global part `Upd.apply` computes is
  `globT`'s), `Upd.lands_iff` (`U.Lands σ₀ g σ' ↔ U.apply σ₀.erase = .ok
  σ'.erase ∧ σ'.globE = g`), `Upd.afterT_iff` (the old clause); the typed
  kit `Upd.afterT_imp`, `afterT_and`, `afterT.of_apply`.

`holds_upd_erased` (`Logic`) and `holdsC_upd_erased` state the old clause.
Naming: the typed readers are the `T` twins (`ARhs.evalT`'s convention),
not `Tm.eval` renamed: renaming would touch every `EState` reader above
while the `shim` lane edits `Update.lean`; W9.7.3 renames when the twins
go.  The equation and definedness clauses still read `Tm.denote`/`Tm.eval`
on `σ.erase`: switching them breaks about 40 leaf proofs (`CloseScoped`,
`DecideTyped`, `SoundLoops`, `UpdRuleScoped`, …) that the `close` lane
rewrites anyway.

**Ported** (typed kit, no erased reading): `holds_upd_mono`
(`UpdRuleScoped`), `holds_upd_imp` (`LeafDerive`), `Hyps.wrap_and` and the
`inv` case (`ProvesSound`), `holdsC`'s `Hyps.wrap` (`CallbackSound`),
`Fml.stepR_sound` (`Symex`), `Fml.mergeAt_leads` (`Merge`),
`Fml.belowS_sound` (`RewriteScoped`), `Fml.mergeAtP_sound`,
`Fml.simpPastAt_sound` (`RewritePast`), `ChainKit`'s `stepFocusR`,
`Deploy`'s two theorems (`Upd.afterT.of_apply`).

**Through `holds_upd_erased`** (the W9.7.2 worklist; uses per file, the
`show`/`change`/`have … := h` sites that unfolded the old clause):
`RewritePast` 15, `CallbackSound` 14 (`holdsC_upd_erased` mostly),
`RewriteScoped` 9, `UpdRuleScoped` 8, `SoundLoops` 7, `Graft` 6,
`ProvesSound` 4, `UpdateRules` 3, `LeafDerive` 3, `DecideTyped` 3,
`SeqRewrite` 2, `RewriteLaws` 2, `CloseScoped` 1, `ChainKit` 1,
`FunContract` 1, `SoundKit` 1, `Tools/Counterexample` 1,
`Examples/Tactics/Chains` 1.

**Checked**: `lean_build` of the default targets, clean; `check-orphans`
(310 reachable), `check-doc-paths`; `sorry` count unchanged.

**Timings** (each file copied under `Solidity/Scratch/`, a fresh worker
after a warm-up, `/proc` sampled every 20 ms; the `shim` lane ran in
parallel, load 1–5, so CPU seconds are the steadier column):

| Row | before wall | before CPU | after wall | after CPU |
|---|---|---|---|---|
| `Derived7` | 51.1 | 53.2 | 48.6 | 50.6 |
| `Tactics/Decide` | 39.3 | 40.0 | 39.4 | 40.5 |
| `ProofTree` | 8.3 | 8.4 | 18–20 | 8.4 |

No row moves (`ProofTree`'s wall waited on the other lane; its CPU is
unchanged).  Expected: the closer still reads a leaf through `holdsE` and
`Upd.apply` (`holds_of_holdsE` rewrites by `holds_upd_erased`), so the
1.8× of W9.6.0 lands with W9.7.2's `close` lane, when a leaf is read by
`Lands`.

### W9.7.2 close record (2026-10-12, branch `w97-close`)

**The closer and the decision procedure read the typed state.**  No
`holdsE`, no `EState`, no `Upd.apply` in `CloseScoped`, `DecideRel`,
`DecideTyped`, `DecideComplete`, `LeafDerive`, `Close*`, `Closers`,
`ProofTree` or `Tools/Counterexample`.

- **`holds`' equation and definedness clauses** read `Tm.denoteT`/`Tm.evalT`
  on the typed state (`Calculus/Logic.lean`).  The erased readings stay as
  lemmas for the update laws until W9.7.3: `holds_upd_erased`,
  `holds_eq_erased`, `holds_defined_erased`.
- **An update computed on the typed state** (`Calculus/Lands.lean`, this
  lane's section): `Upd.applyV σ₀ U`, the global part and the locals'
  values (`Locs C Δ`, a function by position; `Locs.push`/`set`/`drop`/
  `thin`), each right-hand side read once in `σ₀`.  `Upd.applyV_ok` (what
  it computes is `globT`'s global part and `Upd.held`'s locals),
  `Upd.lands_iff_applyV`, `Upd.afterT_applyV` (`holds`' update clause read
  by it).  Also there: `State.loc`, the typed state's reads by position
  (`getE_push_*`, `getE_setLocal_*`, `getE_drop`, `loc_push`/`drop`/`thin`,
  `aliasPathT_getE`, `memRefT_getE`, `TEnv.get_thin_wk`) and the typed term
  bridge `Tm.denoteT_evalT` (the module now imports
  `Theory/Bridge/Denote.lean`).
- **`sol_close`** (`Calculus/CloseScoped.lean`) reads `holds` itself.
  `CloseS.holds_upd : holds σ (.upd m U φ) ↔ m.wp (U.applyV σ)
  (LandedRest σ.H φ)`; `LandedRest` unfolds, once the result is a literal
  pair, to `LandedAll H g ℓ fun x => holds x.val φ`, over the structure
  `Landed H g ℓ` (a typed state with that global part and those locals,
  its heap typing extending `H`).  A landed state's reads are rewrites
  (`Landed.globE_eq`, `Landed.loc_eq`); the locals are a stack of
  `Locs.push` over the root's (`loc_push`, `set_push_here`/`_there`).  The
  first design, `∀ σ'` with `Lands` destructured into one `getE` equation a
  local and read by the contextual pass, cost 2–10× the erased leaf; what
  brought it to par, each measured on `Tactics/Operators`, `CrossDomain`
  and `Memory` leaves: (1) the rest a constant until the update's result is
  known (`LandedRest`: as a lambda, `simp` simplified the rest first with
  the result abstract, then again, 2× a level); (2) the landed state in the
  binder's type, not in hypotheses (no contextual pass needed); (3) the
  binder a constant (`LandedAll`), so `forall_const` and its kin, each
  synthesising `Nonempty` of the binder's type, are not tried at it; it is
  opened by `landedAll_def` after the reads pass; (4) `Landed` names the
  heap typing before, not the state (`H_push`), so a hidden binder pushed
  before an update is unread after it and `forall_const` drops it, as the
  erased reading did; (5) natural literals cast to `Int` as literals
  (`CloseS.natCast_ofNat`: `uintBound` and the bitwise results compare by
  `Int.reduceLT`); (6) the write-naming lemmas without the locals' fact
  (`CloseS.wp_box_saveStorage` …, the erased state's `getEnv`, never read).
  A landed state the rest no longer reads leaves a premise `Nonempty
  (Landed …)` (`landedAll_const`); `sol_close`'s last step therefore
  introduces every premise and splits every conjunct before `omega |
  grind` (`Calculus/Close.lean`, and `sol_spec_prep` in
  `Calculus/SurfaceSpec.lean`).  Hidden binders read at their types
  (`holds_bind_val` … `_oldNet`).  `Examples/Tactics/SelectOnSaveConsr.lean`'s
  hand reading is restated on these lemmas.
- **`sol_decide`** (`Calculus/DecideRel.lean`): `RelB`/`RelU σ ρ g ℓ` relate
  the reduction's state to a global part and `Locs` (the env field over
  `Locs.erase`, `Locs.mem_erase_*` ported from `Env`'s); `RelT σ ρ τ` at a
  typed state; the terms' soundness (`TermOKS` … `MValOKS`) over
  `Tm.evalT`; the update lemmas (`RelU.elem`, `decl`, `zero`, `one`, `par`,
  `half`, `two`) over `Upd.applyV`'s pairs, so no typed state is needed
  between an allocation pair's two writes.  `DecideTyped`: `zero_typed`,
  `peel_*`, `Fml.toLSM_sound` read updates by `Upd.afterT_applyV`
  (`RelT.of_lands`, `RelT.push`); `State.redState := withLocals τ.globE []`;
  `RelU.empty`.  `DecideComplete`'s layout lemmas read `τ.globE.storage`.
- **`LeafDerive`**: the push split (`holds_push_alias`) over two typed
  states (`stable_evalS`, `lastSlotS_eval`, `keyFreeS_evalT` read `x` with
  `σ`'s locals and the storage written); `Env.set_get_self` gone.
- **`Tools/Counterexample`**: `State.lift? σ q` lifts `Upd.applyV`'s pair
  (`TEnv.lift?` over `Locs`), `State.lift?_spec` gives the landing facts;
  `Fml.eval3`/`eval3C` evaluate updates by `Upd.applyV`.

**Outside this lane's files, the smallest fixes** (each a `show` of the
old equation clause replaced by `holds_eq_erased`/`holds_defined_erased`,
or `Tm.evalT_eq` at a definedness witness): `SeqRewrite` (`rwEqC_holds`),
`SoundLoops` (`holds_isBoolD`, `holds_eqD_iffS`), `SoundControl`
(`holds_isBool`), `UpdateRules`, `FunContract` (`holds_wkFO`),
`CallbackSound` (`holds_FO_erase`, `holds_reclose`), `UpdRuleScoped`
(`holds_congr_erase`), `RewriteScoped` (`lawAtom_holds`,
`litPVAlong_holds`), `RewritePast` (`withStS_holds`, `thinFO`), `Problem`
(`holds_wt`).  The `laws` lane rewrites these on `Lands`.

**Left** (`rg 'holdsE|EState|Upd\.apply|holds_upd_erased'` over this lane's
files): `Lands.lean`'s `EState` twins and `Upd.apply`, and `Logic.lean`'s
`holds_upd_erased` and `EState.anon`: what the update laws (laws lane) still
read; they go at W9.7.3.

**Checked**: `lean_build` of the default targets and `SolkeyTestSuite`
(added to `defaultTargets` for the build, not committed), clean; every pin
built unchanged (`Examples/ProofTree.lean`, `CloseTests`, `Verify`'s
`#verify` outputs); `check-orphans` (310 reachable), `check-doc-paths`;
`sorry` count unchanged; `#print axioms Valid.of_reduceS`: `propext`,
`Classical.choice`, `Quot.sound`.

**Gates** (each file copied under `Solidity/Scratch/`, a fresh worker, `/proc`
sampled every 20 ms, wall to the last CPU tick; before: this branch's base,
master at `f009cc96`, measured at the start; the `laws` lane ran in
parallel, load 1–8):

| Row | Gate | before wall | before CPU | after wall | after CPU |
|---|---|---|---|---|---|
| `Derived1`–`14` (sum) | 237.8 | 219.3 | 225.5 | 216.7 | 220.8 |
| `Derived7` | 61.7 | 55.2 | 57.2 | 47.9 | 49.7 |
| `Tactics/Decide` | 45.0 | 39.2 | 39.9 | 38.3 | 39.1 |
| `ProofTree` | 11.7 | 8.2 | 8.1 | 8.6 | 8.5 |
| `Solkey/TestSuite` | 13.2 | 6.9 | 7.0 | 6.8 | 6.9 |

Per file after: `Derived1` 7.0, `2` 7.8, `3` 12.2, `4` 16.7, `5` 7.2, `6` 12.5,
`7` 47.9, `8` 53.7, `9` 9.0, `10` 9.4, `11` 5.8, `12` 12.0, `13` 6.3, `14` 9.2.
`Derived8` varies on either tree (this branch 48.9–53.7; master's file
re-measured back to back 31.4 and 55.5): its `sol_prove` leaves split in
four files measured alike on both.  Single leaves of `sol_close` against
master (s of `simp`, the three passes): `compoundStorage` 1.7 against 3.4,
`storageToMemoryAssign` 3.6 against 4.1, `storageToMemoryUnfold` 3.3 against
3.7, `precedence` 0.5 against 1.0, `memoryFieldDeleteRef`'s leaf 3.8 against
3.0 (memory leaves remain the costliest class: an allocation pair and its
hidden binders).

## What is left

**W9.5b: the reader's shim**: deleted at W9.7.1 (record above); the
side-projects reader is outdated.

**W9.6 (the state IR)**: done (records above, W9.6.0 to W9.6.4).  No
program is evaluated on the erasure: the soundness and the invariants read
the typed run only.  What stays untyped: `EState` (`Env`, `State.erase`, `aliasPath`/`memRef`) as an
update's result and what the terms are read on (decision U1, W9.6.0
record): an untyped `MObj` does not fix the heap typing, an allocation pair
writes the local before the heap that types it, and `net`/`pay` read the
intermediate global part, so an update cannot be applied element by
element to a typed state; landing on a typed state (U2) costs a leaf 1.8×
and restates every law over hypotheses.

**Open items:**
- The reduction's symbols over the typed state (decision 83): a scoped
  term's symbols still read the global part untyped (`State.globE`, since
  W9.7.2).
- `Close`'s `simp` set over typed symbols (decision 82: done for the
  scoped leaf at W9.3, `Calculus/CloseScoped.lean`).
- A write under the diamond leaves its leaf open (`⟨ alice.age = 1; ⟩
  true`, pinned in `Examples/ProofTree.lean`): the closer reads the
  storage untyped, with no layout without a `wt(storage)` premise
  (proposal 100).
- `simplifyUpdate` while the program is open does not drop unread locals
  with their hidden binders (past the program it does, `FmlRw.simplifyPast`);
  what an update pops under the diamond (decision 87's rest).
- A `~~>` line read where it stands is matched up to its binders' names
  (`Fml.LeadsK`); a line whose context order differs from the computed one
  (`Tactics/Chains`' memory example) is written as an explicit chain.
- Printing a reduction's atoms by their binders' names (proposal 99) would
  take the leaf's context to `KeyNotation`'s printer.
- Not run since W4: `check-corpus.sh` (its probes need `lake`), the
  reader's `keycheck` executable and the VS Code extension's tests.
- `check-testsuite.sh` passes at the W8.5 gate with `--solkey` at a
  checkout of solkey `1b4341a303` (`TestSuite.sol` `2fe50a03`);
  `../solkey` itself is stale (`4150e0a8`).
- Lean docstrings may still call the erased side "today's" in places.
