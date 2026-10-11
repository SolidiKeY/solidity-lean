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
| M6c | **done with IR** (W6–W7, merged 2026-10-11; gates passed) | the closer on `Fml C Γ`: 6a (`DecideSyn`, `DecideComplete`, `NFmlClose`), 6b (`Decide.lean` as a scoped front end), 6c (update rules, merges, `⊢`/`⊨` leaves, the chains' rewrites while the program is open); W7: atoms by position and the closer on the scoped reduction, the `⊨` route on the walk, the scoped update rules given their consumers.  `NFml`, `Fml.erase` and `Semantics/Erased.lean` stay as decision 7's IR, every reader listed ("M6c", W7 merge) |
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
| left | — | the lead's calls on proposals 95–105; optional ports on the IR ("What is left") |

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
- *docs*: `sol_close` cited at `Calculus/NFmlClose.lean`; master's arms
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
  `Calculus/NFmlClose.lean` (`sol_close`), `Calculus/NFmlUpdateRules.lean`
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
  importing `Calculus/NFmlClose.lean` or `Calculus/NFmlDerive.lean` for
  `sol_close`/`sol_prove` only: `Examples/Benchmark/Coin`, `Examples/Benchmark/Counter`, `Examples/Benchmark/ERC20`, `Examples/Benchmark/EtherWallet`, `Examples/Benchmark/SimpleStorage`, `Examples/Chains/Arithmetic`, `Examples/Chains/CheckedArithmetic`, `Examples/Chains/Memory`, `Examples/Chains/MemoryArrays`, `Examples/Chains/MemoryCoverage`, `Examples/Chains/MemoryDelete`, `Examples/Chains/Payment`, `Examples/Chains/Storage`, `Examples/Chains/StorageArrays`, `Examples/Chains/StorageCoverage`, `Examples/Chains/StorageDelete`, `Examples/Notation`, `Examples/Tactics/ApplySteps`, `Examples/Tactics/Branch`, `Examples/Tactics/CallOperands`, `Examples/Tactics/Callback`, `Examples/Tactics/Calls`, `Examples/Tactics/Checked`, `Examples/Tactics/Contracts`, `Examples/Tactics/CrossDomain`, `Examples/Tactics/LedgerDelete`, `Examples/Tactics/Loops`, `Examples/Tactics/Memory`, `Examples/Tactics/Net`, `Examples/Tactics/Operators`, `Examples/Tactics/Revert`, `Examples/Tactics/Step`, `Examples/Tactics/StorageDelete`, `Examples/Tactics/StorageSuite`, `Examples/Tactics/Symex`, `Examples/Tactics/Tour`, `Examples/Tactics/TryCatch`, `Examples/Tactics/Values`, `Solkey/ScopedFlip`.

Only docstrings name `NFml` in `Calculus/DecideScoped.lean`,
`Calculus/DecideSyn.lean`, `Calculus/RewriteScoped.lean`,
`Calculus/SeqRewrite.lean`, `Calculus/Symex.lean`,
`Examples/ChainRewrites.lean`, `Examples/Tactics/Chains.lean` and
`TestSuite/Suggestions.lean`.

## What is left

**On the IR, optional.**  M6c is done with `NFml` as decision 7's IR.
Each item below is gated against the final W7 table, and a module that
fails stays on the IR:
- `NFmlClose`'s `simp` set over typed symbols (decision 82); the
  reduction's symbols over the typed state (a term still reads them on
  the erasure, `Tm.toLS_eq`, decision 83); `Atom.name` with `NFml.toL`
  (proposal 99); the scoped closer's layout from a `wt(storage)`
  premise, if wanted (proposal 100).
- `simplifyUpdate` (scoped) dropping unread locals with their hidden
  binders (the formula strengthened out of the local's scope), and what an
  update pops under the diamond (decision 87's rest; W7 `w7-rewrites` did
  the shadowed writes, under either modality).
- While the program is open, not yet scoped: the laws of memory reads
  (`EvalLaw`), a law in an update's right-hand side where the update holds
  the write it reads back (`Upd.covers`) or member-wise (`Term.base?`), a
  term taclet in a diamond update or under a modality variable (`lawUpd`).
- Past the program (proposal 101): a merge across a hidden binder, then
  `sol_chain.scopedPast` on by default and the laws, `~~>` and `calc`
  steps on the scoped line; `sol_apply_upd`, `sol_fold_terms` on the
  scoped leaf.
- A write under the diamond leaves its leaf open (`⟨ alice.age = 1; ⟩
  true`, pinned in `Examples/ProofTree.lean`): the closer reads the IR
  over untyped states with no contract roots.
- Each of these shortens the reader list ("M6c"); `NFml`, `Fml.erase` and
  `Semantics/Erased.lean` go only when it is empty.

**Besides M6c:**
- The lead's calls on proposals 95–105; the user's on decision 11 (whether
  `Surface.Stmt`, an IR with no semantics, counts as "deleting the untyped
  `Stmt`").
- At the merge into `master`: the SolKey reader's require back to
  `../../../solidity-lean` (side-projects `lean/solkey`, branch
  `intrinsic`) and that branch merged.
- Not run since W4: `check-corpus.sh` (its probes need `lake`),
  `check-testsuite.sh` past its input check (the `../solkey` checkout is
  stale, "W7 merge"), the `solkeycheck` executable (built), the reader's
  `keycheck` executable as a target and the VS Code extension's tests.  No
  read-only finder/skeptic pass of W6's or W7's merge.
- Lean docstrings still call the erased side "today's" in places and cite
  this record's sections (at `ad728b16` and `b8565d23`).
- `Delab.withTwins` (`Calculus/DelabErase.lean`) does not pass `schema` on
  its `frames = true` path; nothing calls it with both set.
