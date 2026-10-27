# The intrinsic model

The model is intrinsic. A statement is `Stmt C Γ Γ'`
(`Syntax/Scoped.lean`); its locals are positions `Idx Γ t` in a context
(`Scope.lean`), so a local read out of scope or at another type cannot be
written. `Stmt.run` (`Semantics/Run.lean`) reads `State C Γ`
(`Semantics/State.lean`), with typed storage, heap and locals. It halts only
by revert, panic, divergence or exhaustion; it is never stuck.

The elaborator emits scoped syntax directly (`Syntax/Elab.lean`), the
printers print it (`Calculus/PrintStmt.lean`), and formulas are `Fml C Γ`
(`Calculus/Fml.lean`). Every layer reads the typed state: the closers, the
Theory's observations (`Theory/Typed/Obs.lean`), run invariants (`Typing/`),
EVM simulation (`Evm/`) and tools. KeY's unbounded `int` has its own sort
(`Srt.kint`). External inputs and responses retain their Solidity types
(`CallValue`, `ExtResult`, decoded by `PrimTy.ofWord?`). There is no untyped
statement, formula, term, state or value.

[module-map.md](module-map.md) locates the layers. This document records
the conditions on kernel-evaluated code (Gate G0), decisions in force,
what stays extrinsic on purpose and remaining work.

The refactor ran from 2026-10-07 (M0) to 2026-10-14 (W11), with W12 item 1
on 2026-10-25.  Its full record (lane notes, timings, gate tables, review
logs) is in git:

| Version | Holds |
|---|---|
| `git show ad728b16:docs/intrinsic.md` | the original design, M0–M6 and W0–W5 lane notes ("M4 lane", "M6a lane", "how `dl{ … }` will write a scoped taclet", "Decision 17', implemented", "Captures by provenance", "W1 lane `runlemmas`", "W3b lane `testsuite`", "W4 lane `calc-del`", "W5 reader", …) |
| `git show b8565d23:docs/intrinsic.md` | W6: the M7 review in full, the W3/W4b gate tables, M6c's lane notes |
| `git show aa1b76c5:docs/intrinsic.md` | everything to W12 before this cut: the W8–W12 plans and records, every decision and proposal in full |

Docstrings that cite a section of this file by name cite those versions;
the labels themselves are summarised in "Milestones and waves" below.

## Milestones and waves

One line each; where the work lives now is in `docs/module-map.md`.

| Label | What it did |
|---|---|
| M0 | baselines and the spike behind Gate G0 |
| M1 | stuck causes needing no index removed: a negative `**` exponent or payment reverts, literals in range, `memOk` in the syntax, captures declared, the reference conditional, an unset alias (`Rhs.unset`); (f): the locals check run by the elaborator (gone with M3) |
| M2 | `Ctx`/`Idx`/`Thin`, the scoped syntax (`Syntax/Scoped.lean`); M2–M3 review: a block's local renamed apart (`x_1`) when its name is declared again later in the scope |
| M3 | a scoped run over positions; the locals checker deleted (M3's run went at decision 40); M3b review: both modalities carry the reachability premise |
| M4 | typed values (M4a, `Semantics/Value.lean`, `Semantics/Ops.lean`), storage (M4b, `Semantics/Storage.lean`), heap (M4c, `Semantics/Heap.lean`); `stuck` deleted.  "M4 lane": the typed run (`Semantics/Run.lean`) and its recursor forms (`Semantics/Storage/Ops.lean`, Gate G0) |
| M5 | the compiler on the scoped syntax (`Evm/Compile.lean`), `Sim` by position, `compile_correct` over the typed run |
| M6a | the scoped calculus: `Fml C Γ`, `Frames`, `Premise`, `Stmt.step`, symex, chains, the tree (`Calculus/Fml.lean`, `Calculus/Proves.lean`, `Calculus/Step.lean`, `Calculus/Arms.lean`); its speed gate passed (decision 9; "M6a lane" has the kernel times) |
| M6b | formula front ends: `cdl!{}`, specs, obligations, callbacks, read in the parameters' context (`Calculus/Notation.lean`, `Calculus/Spec.lean`, `Calculus/Problem.lean`); M6b review fixes |
| M6c | the closer on `Fml C Γ` (decisions 78–94); its untyped IR deleted at W9.5a |
| M7 | docs and the review pass (proposals 75–77) |
| W0 | the M6 lanes merged; `Proves.fmlValid` unconditional |
| W1 | off M3's run: lanes `runlemmas` (the typed run's weakening and frame lemmas, `Semantics/RunWk.lean`, `Semantics/RunFrame.lean`, `Semantics/Callback.lean`), `typing`, `evm` (`Evm/Expr.lean`, `Evm/Stmt.lean`, `Evm/Correct.lean`, `Evm/Interpreter.lean`), `rules` (the rule table read scoped, `Calculus/Rules.lean`) |
| W2 | soundness over the typed run (`sound`), the strategy (`symex`: termination retired, the scoped strategy is fuelled), chains (`chains`, `Calculus/Chains.lean`, `Calculus/ChainKit.lean`), the tree (`tree`: `Calculus/CallbackHolds.lean`, the scoped switch `Calculus/Surface.lean`); W2.5: typed soundness of the arms and blocks, decisions 12–17' implemented |
| W3 | the flip of the tactics, the TestSuite, the tree and the chains onto the scoped calculus (W3 `chains`: `evalExpr` without the kernel check of its throwaway definition, a third of a short chain's time); W3b (`testsuite`: `TestSuite/ScopedProblems.lean` a module of its own for its timing gate; the merge's exemption from Gate G0 condition 1, `Calculus/Merge.lean`); W3c (`tactics`: the sequent's update rules exempt too, `Calculus/Graft.lean`, `Calculus/UpdateRules.lean`, `Calculus/CallbackSound.lean`; `testsuite`; `tree`; an import's `N.f.proved : ⊢ N.f.problem`); captures by provenance (decision 30) |
| W4 | the untyped run (`sem-del`) and calculus (`calc-del`: progress `Fml.active_iff_step` and the old rule table retired) deleted; `theorems` (`Theorems.lean` restated, decision 36); `contracts`; `modal`; item 11 (modules split out: `Calculus/RuleKit.lean`, `Calculus/TreeData.lean`, `Calculus/TacticSyntax.lean`); W4b `run40` (decisions 40, 50), `rules36` (36, 53), `printers` |
| W5 | the rename (`Solidity.Core.X` → `Solidity.X`, decisions 62–72); the reader port (now unmaintained; see [contributing.md](contributing.md#toolchain-and-proofs)) |
| W6 | canonicity on the typed state (75), `Stmt.step` total (76), `Reachable → Fits` found false (77), M6c 6a–6c |
| W7 | the `⊨ᶠ` route on the `⊢` walk (95), "only an `assert` panics" (`Prog.run_noPanic`), decision 77's conditional form (97), the closer on the scoped reduction, the scoped update rules and links given their consumers |
| W8 | decision 11: the untyped statement, program and formula removed; the elaborator emits `Prog C Γ Γ'` (`Syntax/Elab.lean`); W8.2: the printers on the scoped syntax (`Calculus/PrintStmt.lean`) |
| W9 | the closer's untyped IR removed: W9.1 (`terms`, `print`: `Calculus/TermLib.lean`, `Calculus/PrintTerm.lean`), W9.3 (`walk`, `close`: "W9.3 `walk` record" below), W9.4 (every formula reads scoped, `elabDlAuto`; chains past the program scoped), W9.5a (`NFml` and the erasure deleted) |
| W9.6–W9.7 | the erased state removed: `holds` reads an update by where it lands (`Upd.Lands`, `Upd.afterT`, `Calculus/Lands.lean`); W9.6.4 the program evaluators, W9.7.1 the untyped terms (`Surface.Tm`) and the reader's shim, W9.7.3 `EState` |
| W9.8 | typed sorts (`Signature.lean`): W9.8.1 `Tm.eval` (`Calculus/TermEval.lean`), W9.8.2 the lowering (`Calculus/Lower.lean`; a typed symbol is not shifted, `Tm.shift?`), W9.8.3 `Tm` is the typed term, W9.8.4 the closer's frame facts (`Calculus/CloseFrame.lean`), W9.8.5 a push at a full array exhausts the update reading too (`Upd.exh`, decision 15); W9.8 review: KeY's unbounded `int` is its own sort (`Srt.kint`) |
| W10 | W10.1–2 `Update.lean`'s remnant and the counterexample candidates typed, W10.3 the typed Theory (`Theory/Typed/Obs.lean`), W10.4 `sol_decide`'s language typed (`Calculus/DecideLang.lean`) and the untyped Theory deleted |
| W10.5 | the typed state, fully: W10.5.1 dead untyped layers deleted, W10.5.2 the Typing chain over the typed state, W10.5.3 the EVM simulation (`Evm/Sim.lean`), W10.5.4 the memory laws on the typed heap (`Theory/Typed/Mem.lean`), W10.5.5 the tools, W10.5.6 `Semantics.State` and the erasure deleted, W10.5.7 the EVM's operator tails on the typed operators |
| Typed boundary follow-up | call inputs (`CallValue`, `ExtKey`), path segments (`Seg`, `Segs`, `RefSegments`), the ledger (`Ledger`), the EVM's store (`Evm.WordStore`) typed |
| W11 | nothing untyped: ABI responses (`ExtResult`, `PrimTy.ofWord?`), mapping keys at their type, `uint` indices, operators taking their `accepts` proof, selector labels (W11.9), EVM words and addresses (`Evm.Word`) |
| W12 | checks that should be types: item 1 done ("Open") |

## Gate G0: kernel-evaluated code

The positional design passed M0's spike (43 statements, symex checked by
the kernel) under conditions; every later wave kept them.  The spike's
symex in the recursor form ran at 0.8× the named design's kernel time and
the run at 0.25×; a `match` form cost 11–13×.

1. **No `match` on an indexed family in kernel-evaluated code.**  The
   equation compiler casts every index, even for `_` patterns, and the
   kernel pays a context comparison per cast (11–13× on symex, 4× on a
   fold).  Hot functions use `T.casesOn`/`T.rec` with the motive
   generalising the indices.  `match` is fine on parameter-only families
   (`Val C Γ`, a path), on types, and in elaboration-time code.
2. **The fastest form is `T.rec` plus an `@[implemented_by]` twin** written
   with `casesOn` and structural recursion (the code generator rejects
   `T.rec`), linked by a theorem (`…_eq_…M`, by induction).  `casesOn` with
   structural recursion alone costs 1.7×.  Every twin needs its link
   theorem (W10 review found 28 missing).
3. **Labels stay out of the index**: `Ctx := List LTy`, the name on the
   binder.  With `(Var × LTy)` the literal is three times larger and
   symex 15% slower.  Printers keep names beside the context.
4. **The locals are computed from the context** (`TEnv`), not an inductive
   family: reads and writes are recursions on `Idx` over projections.
5. **Scope ends are suffixes** (`Ext Γ Δ`); the general `Thin` is for
   weakening only.
6. **No administrative steps**: `Premise.fml` takes the rest and the frames
   apart, so an update continues into the box directly (the extra step
   cost 1.23×).
7. **The quoter hash-conses contexts**: a shared DAG is 1.34–1.96× the
   named one; unshared trees are 26–37× larger.

Pitfalls: a `casesOn`-style definition has no per-constructor equations
(`simp [f]` loops on `f.eq_1`), so its equations are stated and proved by
`rfl` (`Eqns.lean`); Lean promotes a uniform first index to a parameter,
which breaks structural recursion unless it is bound before the colon; an
inner `match` loses the refinement of an index, so compute it first.  A
`rfl` lemma such as `Option.bind_some` lets `simp` rewrite through
`PrimTy.ofInt?`, and the kernel then unfolds its `2^256` range test
("deep recursion detected"): state such a lemma by `rw` (`some_bind'`,
`Evm/SimLemmas.lean`).

**Exemptions from condition 1**, each because it runs once a link or a
rule, not once a step, and each timed: the merge (`Calculus/Merge.lean`,
W3b), the sequent's update rules (`Calculus/Graft.lean`,
`Calculus/UpdateRules.lean`, `Calculus/CallbackSound.lean`, W3c
`tactics`), the chains' rewrite links (`Calculus/RewriteScoped.lean`,
decision 92) and the walks W7 added there and past the program
(`Calculus/RewritePast.lean`, `Calculus/RewriteLaws.lean`,
`Calculus/ExpandLaws.lean`; proposal 104).  What `sol_upd` and `sol_merge`
run on a whole leaf is by the recursor (`Calculus/UpdRuleScoped.lean`).

## How `dl{ … }` writes a scoped taclet

Under `open scoped Solidity.Schema` every name a rule declares is a
position, `Idx.there^j .here` at its distance `j` from the newest, and a
schema variable of the `\find` is read under all of them
(`Calculus/RuleSyntax/Grammar.lean`, `coreScope`).  What scoping adds to a
rule (`Calculus/Arms.lean`): a fresh local is pushed by its declaration and
the parts of the `\find` read after it are shifted under it
(`Calculus/Shift.lean`), the premise popping it after the statement; a
declaration with an initializer binds its local in front of the rest
(`Premise.bind`); a call's body, closed over its frame, is weakened under
the caller's locals once per call and its frame dropped under the returns
it leaves (`Premise.inline`).

## Decisions in force

Numbered as they were taken; the code cites the numbers.  Decisions not
listed (1, 5, 6, 8, 18, 20–26, 29, 31–34, 37–38, 41–49, 51–52, 54–58,
62–67, 69–74, 79–82, 84–85, 88, 91, 94–96, 98, 100, 102–103, 106–128)
were superseded, implemented without a lasting constraint, or concerned
deleted code; their text is at `aa1b76c5`.

- **2.** Locals are block-scoped, as in solc: popped at the end of a
  branch, loop body, `try` block or block (`docs/solc-alignment.md`,
  "Block-scoped locals").
- **3.** A `uint` or `int` value is an `Int` in its type's range
  (`PrimTy.Denote`), not a bitvector: arithmetic stays on `Int` with range
  proofs, so the kernel never unfolds word arithmetic.  Kept at W11.
- **4.** Storage is typed: `SVal T` has the shape `T` gives it over
  `structDef` (`Semantics/Storage.lean`).
- **7.** Every milestone runs; a failed gate takes its stated fallback.
  The fallback it allowed, an untyped formula IR for the closer, was
  deleted at W9.5a.
- **9.** The M6a gate counts as passed: the scoped symex is about 2.9×
  faster in aggregate, a few small programs 3–23 ms over.  The calculus
  stays positional.
- **10, 14.** A `bool` mapping key follows solc: it hashes as the word
  `0`/`1` (`PrimTy.key`).  Since W11.3 the key itself is a `bool`
  (`SMap K V` holds keys of the key type); `PrimTy.key` is the EVM slot's
  and the selector label's observation.
- **11.** No untyped statement, program or formula (user, 2026-10-11, done
  at W8): the elaborator emits the scoped syntax and the printers print it.
  Since W9.4 a formula with no modality reads scoped too (`elabDlAuto`).
- **12.** The hidden binder at a memory type: superseded by 17' (the
  diamond no longer asks it for an inhabitant).
- **13.** A dynamic array's length is below `2^256` by its type
  (`SVal.array`, `MObj`), so a typed length read is in range.  Amended by
  15: the push at the bound is exhausted, not a revert.
- **15.** A push at the bound is resource exhaustion, read as KeY reads gas
  (not at all): the run halts `exhausted` (`Storage.full`, `TRun.push`),
  both modalities accept it (`Modality.onTHalt`), and so does the update
  reading (`Upd.exh`, W9.8.5), so the TestSuite's pushing diamond
  obligations stay provable.  solc panics far earlier; an exhausted run
  proves any modality (`docs/solc-alignment.md`, "Array lengths").  A
  recursive call's bottom frame is exhausted for the same reason.
- **16.** A struct that repeats a member name is refused
  (`refusedStructs`, "Identifier already declared"), so no hypothesis about
  duplicate members is needed.
- **17, 17'.** 17 (the binder ranging over a grown heap) was infeasible.
  17': a memory local may be unset, as a storage alias may:
  `LTy.TDenote (.mem R)` is an `Option`, a read or write through an unset
  one reverts (`MPath.mvalT`), the run's declarations always bind an
  object.  So the hidden binder has an inhabitant at every type and
  `Stmt.sound` needs no hypothesis (`docs/solc-alignment.md`, "Memory local
  without an object").
- **19.** `CallRet.isRets` follows solkey: a memory return steps by
  `internalCallExpand`, not `functionBodyExpand`.
- **27, 28.** A leaf keeps its leading `∀`s, read at their types; `cdl!`
  marks the parameters (`Fml.markExplicit`), so an explicit `∀` keeps its
  range and gets its `allRight` line in the walk.
- **30.** Captures by provenance, a recorded deviation: `captureExpr` skips
  a fresh name only outside the inlined ranges (`ElabScope.inlined`); a
  program's own fresh-shaped local (`FreshNames.parse`) is read as a
  written-out capture (`docs/solc-alignment.md`).
- **35.** The scoped rule lines were once diffed against the unscoped
  table; that table is gone, and the lines are pinned where each rule is
  shown (`#taclet`, `scripts/check-rule-text.sh`).
- **36.** The step rules of `Proves` read the rule set: a last,
  default-proved argument `hR : R.admits m s = true` (`rule_admits`), read
  off the statement (`Stmt.keyStep`).  Under `.solkey` a statement whose
  rule may be a `LeanTaclet` is not admitted, so `⊢ₖ` is `⊢` on solkey's
  fragment (`Calculus/SolkeyProves.lean`, `Calculus/SolkeyFragment.lean`)
  and `sol_prove` on `⊢ₖ` walks solkey's rules only.
- **39, 40, 50.** One run: the typed run is the only run of a statement and
  it halts only by `revert`, `panic`, `diverge` or `exhausted` (`THalt`);
  M3's run, the untyped run and their `stuck`/`undef` halts are gone.
- **53.** `Calculus/DelabErase.lean` (the printers' name stack) sits below
  the delaborators, the sequent and the strategy.
- **68.** `scripts/check-doc-paths.sh` skips this file: it named files by
  the paths they had at each step.  Since this cut every path here is
  current.
- **75.** The canonicity, tightness and fit invariants are run invariants
  of the typed state (`RunInv.HoldsT`; `canonInv`, `tightInv`, `fitsInv`),
  each leaf against the typed step.
- **76.** `Stmt.step` is total (a `Premise`, not an `Option`): every
  statement has exactly one rule (`Stmt.rule_exists`).
- **77, 97.** `Reachable → Fits` is false (`huge_reachable_not_fits`: a
  `uint[2^256 + 1]` root).  Its conditional form holds: under `FixedFits C`
  (every fixed size at most `2^256`, solc's "type too large for storage")
  every reachable storage fits (`reachable_fits`, `Typing/Fits.lean`), so
  `reachable_iff_fits` needs no premise on the storage and `reachable_iff`
  keeps `Fits` for other contracts.  W12 item 5 would make `Fits` a type.
- **78, 83.** The decision procedure keys atoms by position.  Its
  kernel-evaluated functions keep G0's conditions 1 and 2; `match` stays on
  helpers that take one `Tm` or `Rhs` apart at fixed constructors
  (`Tm.totalB`, …), since their context is the family's parameter.
- **86.** The scoped update rules are one way (`UpdRuleS.sound`:
  `holds σ ψ → holds σ φ`), since a merged update can reach a typed state
  the two in turn do not; so they apply at positive positions only
  (`Fml.rwAtS`).
- **87.** The update rules transcribe solkey's as far as positions allow:
  `sequentialToParallel` is `Upd.seqPar`, `simplifyUpdate` drops shadowed
  writes and what the update pops later (`Upd.simp`), but while the
  program is open it keeps an unread local in scope ("Open").
  `elimSelfUpdate`, commented out in solkey, is not ported.
- **89.** `sol_prove` leaves the walk's own sequents (`Seq.SLeaf`,
  `Seq.leafS`), goals of the scoped calculus; on `⊨ᶠ φ` it is
  `Proves.fmlValid` then the same walk (decision 95).
- **90.** `Proves.rewrite` is a rule of the scoped sequent: a Theory
  equation in every equation of the sequent, through updates, binders and
  an open modality's postcondition (`Calculus/SeqRewrite.lean`).
- **92.** A chain's rewrite links on `Fml C Γ` are sound on the typed
  reading itself (`Calculus/RewriteScoped.lean`), under the G0 exemption
  above.
- **93.** A scoped rewrite was first tried only while the program is open;
  revisited at W9.4, the lines past the program are scoped too
  (`Calculus/RewritePast.lean`, `Calculus/RewriteLaws.lean`).
- **99.** A reduction prints its atoms by position (`pos(k)`): its terms
  carry no names ("Open").
- **101.** Past the program a merge crosses a hidden binder:
  `bind x ({x := e ‖ U} φ)`, `e` and `U` not reading `x`, is
  `{x :=decl e ‖ U} φ` (`Upd.absorb`, `Calculus/RewritePast.lean`).
- **105.** While the program is open `~[applyOnRigidBox]~>` applies under
  the box any update, under the diamond one that cannot halt, as KeY's
  `applyOnRigidFormula` does; `~[applyStorageBox]~>` is the box's only.

## What stays extrinsic, on purpose

- **The EVM fragment** (`inFrag`, `Evm/Compile.lean`): a fact about the
  target, not the source.
- **Function and modifier bodies** in `Contract`, as read: a contract
  holding `Stmt` bodies indexed by itself is inductive-inductive; each call
  carries its typed body (`docs/kernel-port.md`, "Where a callee's body
  lives").
- **Taclet soundness and the closer's completeness**: theorems by nature.
- **Storage canonicity beyond shape** (`SVal.Canon`, `SVal.Tight`,
  `SVal.Fits`): run invariants, so `decide +kernel` keeps association-list
  stores.  `Fits` and `FixedFits` stay explicit hypotheses (W12 item 5).
- **Narrow integer widths** (`uint8` …): the elaborator's checks
  (`narrowCheck`); `PrimTy` is `bool`, `uint`, `int`.
- **The fresh-name numbering** (`Taclet C k`): labels only, so pins keep
  `se1`, `sp1`.
- **Memory identities in the term signature** are `Nat`, indexed by their
  sort: a formula's memory terms grow heaps apart from the state's (KeY's
  `Identity` sort).  Typing them by the global heap (W11.12, local branch
  `w11-ident`, not merged) made the closer more than ten times slower on
  the call examples (`Examples/Tactics/Calls.lean`'s `withdrawShort` past
  15 minutes), for an invariant that only excludes an identity naming
  another type's object.
- **The EVM's slot offsets** are `Nat` (`Slot.root`, `Slot.add`): the
  simulation's symbolic address space, not a value the run computes.
  Balances on the machine are `Nat` amounts.
- **The Theory's lengths** (`TVal`) are `Nat`; the slot past the end is
  `uintOfNat` of the length, exact below `2^256`.
- **Validation at the boundary**: external responses are ABI words decoded
  at the locals' types (`PrimTy.ofWord?`, `Binders.decodeT`); data that
  does not decode reverts.

## W9.3 `walk` record

`sol_prove`'s walk closes a leaf on its scoped form (`Calculus/LeafDerive.lean`,
`Proves.closeHolds`); since W9.4 there is no erased fallback.  Leaves the
scoped `sol_decide` does not read, each replayed by `sol_leaf` and a
closer: an alias whose index reads the storage, used after a storage write
(`testStorageNestedPushReturnAlias`, `sol_close`); a deployment's update of
three elements over `mtSt` (`Examples/Tactics/Constructors.lean`,
`sol_close_mt`); a loop's frame (`anon`, `havoc`,
`Examples/Tactics/LoopsImport.lean`, `sol_close`).  A modality left in a
leaf is read by neither, and the walk fails.

## Open

- **W12 items 2–5** (plan 2026-10-24): roots and fields as positions
  (`Loc.root` with `C.rootType r = some T` becomes `Idx C.vars T`, about 80
  hypotheses, `nodupKeysB` goes; needs item 1); structs carrying their
  members (an inductive type, so unknown, empty and recursive structs
  cannot be written; W9-sized, **may slow checking**: larger types for the
  kernel to compare); operators indexed by their type (`BinOp p q`, about
  90 hypotheses, low priority); `SVal.Fits` by type (removes `Fits` from
  `wt_iff_reachable`).  Item 1 left `structOk` admitting any encoded name
  (`isEnc`): full validation of struct names belongs to item 3.
- **A write under the diamond at a path with an index** leaves its leaf
  open: the index check may revert.
- **`simplifyUpdate` while the program is open** does not drop unread
  locals with their hidden binders (past the program it does,
  `FmlRw.simplifyPast`), nor what an update pops under the diamond
  (decision 87).
- **A `~~>` line read where it stands** is matched up to its binders' names
  (`Fml.LeadsK`); a line whose context order differs from the computed one
  is written as an explicit chain.
- **Printing a reduction's atoms by name** (decision 99) would take the
  leaf's context to the printer (`LTm.ppWith`).
- `Derived13` pays about 5 s for `testDanglingInnerArrayReappearsAfterPush`,
  restored at W9.8.5.
- Lean docstrings may still call the deleted unscoped side "today's".
