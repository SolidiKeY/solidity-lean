# KeY taclet → Lean `RuleName` mapping

Tracking checklist for the port. One row per taclet in
`solidityProgramRules.key` (plus `ifThenElseRules.key`), in file order.

**Pinned to solkey `8c5c69ca25` on 2026-09-20** (310 program taclets, three
`\heuristics` classes; `Calculus/KeyTaclets.lean` is regenerated from that
file and `RuleShapes.taclets_partitioned` claims 306 of the 310, the four
excused being `emptyModality`, `blockEmpty`, `ifSplit`, `ifElseSplit`).  The
same pass made the rule table read as the paper's tables do —
`Calculus/PaperRules.lean` is the paper-side twin of this file — so the Lean
column below carries the paper's names where the paper has one: the Step 2
partition is the paper's (`unfold_leftFst` / `unfold_leftSnd` /
`unfold_source`, each with a `Ref` instance), the three delete targets, the
five memory delete rules and the two transfer modalities are one rule each,
the arithmetic families are `*OpAssign` / `*Increment`, and the scratch names
a residual binds are the paper's `se`/`ie`/`sp`/`mv`.

**The storage copy fold is not followed, by decision.** solkey's storage copy
changed twice on 2026-09-16: `c80a54494c` added `copyAt`/`merge` to
`structRules.key` and respelled all eight copy rules' updates
`copyAt(storage, p, find<[StValue]>(storage, src))`, and `8c5c69ca25` folded
that back into `save`: the eight copy rules write `save(…)` again,
`copyAt`/`merge` and their taclets are gone, and `save(st, nil, v)` is a leaf
every write leaves, never collapsed, read through by member sort by the five
`selectOnSaveEmpty*`/`saveOnEmptyPrim` taclets so that a struct written over
a location keeps the location's mapping members.  The same fold moved
`storageIndexDelete` to `delAt` and gave `structMemoryRules.key` two
`selectOnCopyMem*` reads.  The program rows are unchanged, since
`Rules.StVal.find` is the whole term in one value slot.
`Theory/Storage.lean` keeps the **pre-fold** algebra — `saveOnEmpty`,
`saveOnStoreCons` with its `isEmpty(flds)` split, `selectOnSaveEmpty` over
solkey's two sorts — because that is the paper's signature (`saveEmptyPath`:
`save(st, ∅, v) = (Struct) v`, `sections/signature.tex`) and this repository
is the source both the paper and solkey are ported from: the non-collapsing
leaf differs from the plain write only on a storage-to-storage copy of a
mapping-carrying type, which solc ≥ 0.7 and solkey's own parser
(`ParserUtils.parseAssignmentMaybe`) reject and `TypedStmt.Assign.mk` cannot
build.  `docs/solkey-feedback.md` carries the request that solkey drop the
fold.  The storage half of the denotation went with the leaf.

The commits between `e67a0d7c48` and `8c5c69ca25` were reviewed for this
pin: `efc047a470`, `4635f8a530` and `4599dd6d91` add the `*CaptureAll`,
`*StorageRef*`/`*MemRef*` and `memoryToStorage*` unfold families and the
memory arithmetic (all claimed below); `63c38cfaf6` deleted the two
`index*InnerNonSimpleIndexCapture` taclets and `4635f8a530` renamed the three
`*RootRhs*` ones to their `*StorageRef*` forms (their Lean rules were already
the merged, sort-free form); `c095c5c602` only tightens a schema variable
and `293b81c31d` only re-spells the modalities.  The example corpus (`scripts/solkey-port.mjs`
against `c80a54494c`) and `SortCheck/Annotations.lean` are now pinned to the
same tree.

Re-pinned to solkey `e67a0d7c48` on 2026-09-02: that commit touches only
`structRules.key` (the delete-default rules `delValueDefault` /
`selectStDelNodeDefault` are now bounded `alphaPrim \extends Prim`, and a
`Struct`-sorted `selectStDelNodeIndexStruct` reads `mtSt` — the Prim/Struct
split is by sort), so every row below is unchanged.
Re-synced against solkey `0f9b99ad55` on 2026-09-01 (238 program taclets;
the sort-hierarchy changes of that sync — `RefField` for `IdField`/`PrimField`,
the `Field[primitive]`/`Field[reference]` schema sorts replaced by
`\hasFieldSort`/`\hasMemoryFieldSort` bounds, `transfer*` split by modality —
are in the rows below and in the `SolKey` reader's `Decode/Sorts.lean`). The
2026-08-29 sync (237 program taclets) found solkey had
moved since the original sync: several decl-init taclets were renamed or
collapsed (`*InitSplit` → `*InitDrop`), five `*_unfold_rightSnd*` rules that
were Lean-only now exist as taclets, and new taclet families had landed
with no Lean counterpart (`ternary*`, `local{Add,Sub,Mul,Div,Mod}Assign`,
bare `local{Pre,Post}{in,de}crement`,
`{add,sub,mul,div,mod}AssignValueRhsCapture`) — all of which were ported
the same day (rows marked `done` below). Ideas flowing the other way are
collected in `docs/solkey-feedback.md`.

Status legend:

- `existing` — already modeled in `Calculus/Rules.lean` (possibly merged with siblings).
- `done` — ported with a `from` clause naming the taclet; the note column
  carries what the `from` cannot say.
- `gone upstream` / `renamed upstream` / `deleted upstream` — the taclet is
  not in the pinned solkey; the row stays for the history and names the
  commit.
- `planned(N)` — to be added in plan phase N.
- `arch` — no direct Lean counterpart by design (architectural difference of
  the block-rewriting model); note explains.
- `verify` — likely covered but the correspondence must be checked against
  the KeY taclet before being trusted.
- `lemma` — ported as a theorem about `SolidityJudgment`/`State`, not a
  `RuleName` (proof-level or state-level content that a single-successor
  rewrite step cannot express).

## The taclet column is now machine-checked

This file is prose, and prose drifts. The **name** column is therefore no
longer only here: every rule of `Calculus/Rules.lean` carries a typed
`KeyOrigin` — `taclet t`, `merged [t₁, …]` or `leanOnly` — over the
`KeyTaclet` enumeration of `Calculus/KeyTaclets.lean`, which is the vendored
`solidityProgramRules.key` transcribed one constructor per taclet. Three
consequences:

- a misspelled taclet name is a type error, not a stale table row;
- `RuleShapes.taclets_partitioned` checks the *coverage* direction — of the 310
  taclets, 306 are claimed by some Lean rule and exactly four are excused with a
  reason (`emptyModality`, `blockEmpty`, `ifSplit`, `ifElseSplit`). A taclet
  may be claimed by two rules: each `*CaptureAll` by the `UnfoldLeftFst` and
  the `UnfoldLeftSndIndex` of its family, `memoryFieldWrite` /
  `memoryIndexWriteArray` by the value write and the reference copy;
- `RuleShapes.leanOnlyRules` is the other direction, computed from the table
  rather than transcribed.

What stays prose here is everything the `origin` cannot say: *why* a merge is a
merge, which upstream commit moved a rule, and the evaluation-order and
sort-annotation notes below. Rows whose only content is "this taclet ↔ this
rule" are now redundant with the code and are kept for their notes.

## Sort annotations (machine-checked column)

This table maps taclet *names*; the taclets' **read-sort annotations**
(`find<[int]>` vs `find<[Struct]>` vs sort-free `find<[StValue]>`/`valAt`
vs varcond-resolved `find<[alphaPrim]>`) are tracked separately and
machine-checked from both sides:

- `Solidity/SortCheck/Annotations.lean` — one `TacletReadAnn` row per
  read-bearing taclet, kept in sync with the live `.key` file by
  `lake exe solkeycheck` (`scripts/check-solkey.sh`); any upstream sort
  drift fails the check.
- `Solidity/SortCheck/Faithfulness.lean` — proves each row's sort claims
  against the interpreter (`sortFaithful_all`), so updating the table to
  match a mis-sorted taclet breaks the build. A fixed sort is a
  `KeySort` (`Solidity/KeySort.lean`, the transcribed lattice shared with
  the `SolKey` reader's decoder), and the claim is `(v.keySort).le s` — the
  sort-free `find<[StValue]>` is literally `fixed .stValue`.

This layer exists because a sort bug slipped through the name-level
mapping: solkey `12e72a1b4b` fixed hard-coded `find<[int]>` reads on the
copy rules (mis-sorting `bool` copies), which no Lean theorem could see —
the hand-translated Lean rules were already sort-free. The pre-fix
annotations are refuted in
`Solidity/Counterexamples/PreFixSortAnnotations.lean`. The last two
`find<[Struct]>` reads on possibly-primitive sources
(`storageFieldWriteCopySource`, `storagePushValueCopySource`) went sort-free
upstream in `29c44e225b`, so `SortFaithfulness.openFindings` is empty.

## Naming drift against solkey

**`lake exe solkeycheck` is at zero** against `8c5c69ca25`. The 78-row
drift the 2026-09-16 corpus pin left open — solkey `29c44e225b` split the
storage-index arithmetic taclets into `Mapping`/`Array` forms, merged the
`_root`/`_decompose` pairs and changed three read sorts
(`storageFieldWriteCopySource` and `storagePushValueCopySource` read
`StValue`; `storageIndexReadArray{BindLocalRoot,StoreRoot}` read `length`
twice), `444f029579` added the memory arithmetic — was re-synced with the
rule-table rewrite, moving `SortCheck/Annotations.lean`,
`SortCheck/Faithfulness.lean` and `Counterexamples/PreFixSortAnnotations.lean`
together. The merged and split taclets are one row each below.

One naming drift is left, and it is not a semantic difference:

- `unfoldArgument` is a name from solkey's `docs/net.md` backlog. The
  calculus declares no rule of that name, which is why
  `functionCallArgCapture` is a Lean-only rule.

The two drifts that used to sit beside it are closed: Lean now spells the
declaration rules `storageLocalDeclInitDrop` / `memoryLocalDeclInitDrop` /
`localValueDeclInitDrop` and the conditional rules `ifElseUnfold` /
`ifElseTrue` / `ifElseFalse` / `ifElseNegated`, as solkey does.
`ifElseUnfold` still merges solkey's `ifUnfold`/`ifElseUnfold` pair, because
`Stmt.ite` always carries both branches.

The box/diamond twins are a *Lean* naming decision with no upstream
counterpart: where the calculus stacks a bounds or nonempty check as two
sequents, Lean splits the rule by modality and names the halves with the
rule name plus a `Box`/`Diamond` suffix — the convention already used in
`revertBox` and `transferNoCallbackBox`.

## Evaluation-order note (KeY `testStorageEvaluationOrder`)

KeY evaluates an assignment's RHS *before* the target's index
(`a[++i] = ++i` with `i = 0` ends with `a[2] == 1`), and so does the Lean
**interpreter** (`execAssignNested`, RHS first as in solc; locked in by
`RuleValidation.storageEvaluationOrder_interpreter_rhsFirst`). The Lean
**rewrite layer** agrees when the RHS is complex: `assignCandidate` tests
`rhs.simple` first, so a nonsimple value source is hoisted into `se` before
any path/index capture — by `*UnfoldSource` on a simple receiver, by the
`T se ?= e` freeze the `*UnfoldLeft*` rules carry otherwise
(`storageEvaluationOrder_rewrite_rhsFirst`).

When the **path** is complex, the `*UnfoldLeft*` rules
(`storageFieldWriteUnfoldLeftFst`, `storageIndexWriteUnfoldLeftSndIndex`, …,
mirroring KeY's `*_unfold_leftFst` / `*NonSimpleIndexCapture` /
`*CaptureAll`) used to capture the path or index *first*, a genuine order
swap against the interpreter: on `people[i++].age = i` the interpreter writes
the old `i`, the residual the incremented one. **Fixed.** `Rules.freezeRhs`
prepends `T se = e;` to every target-capture residual whose source is a
primitive value — the `T se ?= e` of the rule text; a source that already
*is* `se` is left alone, since with fixed alias names `se = se` would be
wrong — so every `*UnfoldLeft*` rule with a value source (storage, memory,
memory-to-storage, and the `*OpAssignUnfoldLeftFst` /
`*IncrementUnfoldLeftFst` families) is sound on a primitive right-hand side
with no semantic side condition — no `hstable`, no `hev`, no `pureExpr index`, only
the syntactic `hprim` (which is about the interpreter, not the rule; see the
upstream-state bullets below) — and `Counterexamples/EvaluationOrder.lean`
proves agreement on the two programs it used to refute, keeping the
refutation of the pre-fix residual beside it.

The freeze is **not** conditional on the path being impure, and cannot be:
`Counterexamples/ErrorOrder.lean` refutes the unfrozen residual on
`people[1 / 0].age = ghost`, where both operands are pure but the two sides
fail with different `Halt`s (stuck vs revert). Error ordering, not just
interference, is what forces the freeze.

**Upstream state (re-checked 2026-09-12).** solkey landed the fix in
`8ba30fd742` ("i++ evaluation order", storage half) and `63c38cfaf6`
("replace the rules to get m[i++] = i", memory half plus recursion), after
the 2026-09-09 attempt was reverted the same day (`beeb97d2b1`). KeY binds
the value with a second `\newTypeOf(rv, se)` and splits each affected write
on `SimpleExpression[primitive]` versus a new `…Ref…` taclet, because
binding a reference is aliasing rather than a read — the same split the
table makes: `freezeRhs` on `rhs.ty.isPrimitive` for the value rules, and a
`Ref` instance (`isReference`, no freeze) of each `unfold_leftFst` /
`unfold_leftSnd`, as the paper states them.

Two things to know about the upstream state:

* `63c38cfaf6` **deleted** `indexWriteInnerNonSimpleIndexCapture` and
  `indexReadInnerNonSimpleIndexCapture` (rows below) in favour of four new
  `{storage,memory}{Field,Index}WriteIndexedReceiver_unfold_leftFst`
  taclets. Those four **never fired** — two red tests, `storageMatrixNseIndex`
  and `testNestedIndexWriteImpureIndexPrimitiveRhs` — bisected upstream to
  `\varcond(\newTypeOf(sp, nsp))`. The residual they emitted is
  character-for-character Lean's `indexWriteResolveBlock`, and Lean's version
  works, so the bug was in taclet instantiation, not in the rule. **Fixed**:
  a schema variable off the plain `ProgramSVSort.VARIABLE` sort gets no name
  proposal, so `VariableNamer`'s `previousProposals` list carried a `null`
  and `equals` threw; these four were the only taclets minting two fresh
  program variables at *different* data locations, which is what put a `null`
  there. 242 -> 0 failures. `4635f8a530` then replaced the four (and their
  `*Ref*IndexedReceiver*` twins from `efc047a470`) by the `*CaptureAll`
  taclets — receiver and index captured in one step, which is what the Lean
  `UnfoldLeftFst` rules had done all along (rows below).
* **Reference sources are the one place the KeY rule is right and the Lean
  interpreter is wrong.** solc is right-hand-side-first for a primitive
  source, but copies a *struct* source member by member after resolving the
  target, so an impure index has already run. Confirmed on a real EVM
  (`TestSuite.storageIndexWriteRefSourceImpureIndex` stores `1`);
  `Semantics.execAssignNested` stores `0`. The `hprim` hypothesis on the Lean
  `*UnfoldLeft*` soundness theorems fences this off rather than claiming the
  rule is at fault — see `Counterexamples/RefSourceOrder.lean` and
  `docs/solc-alignment.md`.
* the `SolKey` reader's vendored corpus is still pinned at the revert (`beeb97d2b1`), so its
  `AgreesModulo` theorems compare against the pre-fix taclets and must be
  re-pinned together with this change.

## Modality / sequent rules

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `emptyModality` | — | arch | A derivation ending in the empty `Block` is the Lean analogue; DL-syntax layer (goal task) makes it explicit. |
| `blockEmpty` | — | arch | no nested-block `Stmt` constructor: `Block = List Stmt` and branch bodies are inlined lists, so the `{} ; rest` find-shape is unrepresentable. |
| `functionBodyExpand` | `functionBodyExpand` | done | inlining via `SoliditySyntax.expandCall` (KeY `ExpandFunctionBody`: param decls from actuals, one named return, body, result assignment); the interpreter is stuck on `Stmt.callStmt` — meaning comes from `SolidityJudgment.checkInlined` (fuel-bounded `inlineBlock`; `inlineStmt_callStmt` is the definitional soundness anchor, acyclicity locked in by the `blockCallFree` `native_decide` in `Examples/Taclets/FunctionCallOps.lean`) |
| — | `functionCallArgCapture` | done | Lean-only (`unfoldArgument` on solkey's backlog — `docs/net.md` §5.1; the name is solkey's, and the calculus declares no such rule): hoists the leftmost complex call argument into `se` |
| `revertDiamond` | `revertDiamond` | done | explicit rule; the modality truth value lives in `Semantics.lean` |
| `revertBox` | `revertBox` | done | explicit rule; the modality truth value lives in `Semantics.lean` |

## Storage root/field write & read

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `storageRootWriteStore` | `storageRootWriteStore` | existing | |
| `storageRootWriteCopySource` | `storageRootWriteCopySource` | existing | |
| ~~`storageRootWriteCopySource_struct`~~ | `storageRootWriteCopySource` | gone upstream | deleted by solkey `12e72a1b4b`: the int/struct rule pair collapsed into one sort-free copy (`find<[StValue]>`), which is what the merged Lean rule modeled all along — see the sort-annotations section and `Counterexamples/PreFixSortAnnotations.lean` |
| `storageRootReadSelect` | `storageRootReadSelect` | existing | |
| `storageFieldWriteSave` | `storageFieldWriteSave` | existing | |
| `storageFieldWriteCopySource` | `storageFieldWriteCopySource` | existing | |
| `storageFieldWriteCaptureSrc` | `storageFieldReadUnfoldRightSndResult` | existing | merged: the SndResult chain captures a complex storage source (`RuleValidation.storageFieldReadUnfoldRightSndResult_valid` exercises the KeY find-shape) |
| `storageRootWriteValueRhsCapture` | `storageRootWriteUnfoldSource` | done | the paper's `unfold_source` at a global root: `gsp = nse ⇝ T se = nse; gsp = se` with `isValueSource nse` (primitive, and not a path read, memory, push place, call or ternary — a ternary is lowered by `ternaryToIf*` first); solkey's taclet is location-neutral, the table states one instance per receiver shape |
| `fieldWriteValueRhsCapture` | `storageFieldWriteUnfoldSource` (storage), `memoryFieldWriteUnfoldSource` (memory) | done | KeY's generic `e1.a = nse`, one Lean instance per kind, on a **simple receiver only** (`sp.fld`/`mv.fld`); a complex receiver with a complex value source is `*FieldWriteUnfoldLeftFst`, which takes any `isValueSource` and freezes it into `se` itself |
| `indexWriteValueRhsCapture` | `storageIndexWriteUnfoldSource` (storage), `memoryIndexWriteUnfoldSource` (memory) | done | same, receiver and index simple (`sp[ie] = nse`); soundness `RuleSoundness.valueRhsCaptureAssign_sound` is conditional on the target surviving the source's effects (`hstable`) — see the evaluation-order note above |
| `storageFieldRead_unfold_rightFst` | `storageFieldReadUnfoldRightFst` | existing | |
| `storageFieldReadFind` | `storageFieldReadFind` | existing | |
| `storageFieldWrite_unfold_leftFst` | `storageFieldWriteUnfoldLeftFst` | done | `nsp.fld = e ⇝ T se ?= e; T storage sp = nsp; sp.fld = se` with `isValueSource e` — `e` may be a complex value (binop, unop, incDec, literal, stack var, primitive storage root), never a path read; the freeze is `Rules.freezeRhs` (evaluation-order note) |
| ~~`storageFieldWriteRootRhs_unfold_leftFst`~~ | `storageFieldWriteRefUnfoldLeftFst` | renamed upstream (`4635f8a530`) | now `storageFieldWriteStorageRef_unfold_leftFst` (next row): the "root RHS" slice that KeY's `SimpleExpression` excluded was a reference source, which the paper's `Ref` instance names outright |
| `storageFieldWriteStorageRef_unfold_leftFst` | `storageFieldWriteRefUnfoldLeftFst` | done | the `Ref` instance of `unfold_leftFst`: `nsp.fld = sp2 ⇝ T storage sp = nsp; sp.fld = sp2` with `isReference sp2` — a reference source is aliased, not read, so there is no freeze (and, per the reference-source bullet above, none to make) |
| `storageFieldReadBindLocalRoot` | `storageFieldReadBindLocalRoot` | existing | |
| `storageFieldReadStoreRoot` | `storageFieldReadStoreRoot` | existing | |
| `storageFieldRead_unfold_rightSndResult` | `storageFieldReadUnfoldRightSndResult` | existing | was Lean-only; solkey adopted the taclet (result capture no longer folded into the read taclets) |

## Storage index (mapping)

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `storageIndexWriteMappingSave` | `storageIndexWriteMappingSave` | done | solkey `29c44e225b` merged the `_root`/`_decompose` pair into one taclet — the merge Lean had made |
| `storageIndexReadMappingFind` | `storageIndexReadMappingFind` | done | merged `_root`/`_decompose` upstream (`29c44e225b`) |
| `storageIndexReadMappingBindLocalRoot` | `storageIndexReadMappingBindLocalRoot` | existing | |
| `storageIndexWriteMappingCopySource` | `storageIndexWriteMappingCopySource` | existing | |
| `storageIndexWriteStorageRefRhsCapture` | `storageIndexReadUnfoldRightSndResult` | done | the paper's `storageIndexWriteRef_unfold_source`: at a reference type the source alias the paper calls `sp2` is the kind-neutral `se`; dispatch hoists the source before the index, which *is* the RHS-before-index order — `RuleValidation.storageIndexWriteStorageRefRhsCapture_corresp` (the taclet was renamed from `storageIndexWriteMapRefRhsCapture`) |
| `storageIndexReadMappingStoreRoot` | `storageIndexReadMappingStoreRoot` | existing | was Lean-only; solkey adopted the taclet |

## Storage index (array)

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `storageIndexWriteArraySave` | `storageIndexWriteArraySaveBox` / `storageIndexWriteArraySaveDiamond` | done | solkey `29c44e225b` merged `_root`/`_decompose`; Lean splits by modality (bounds/revert) instead |
| `storageIndexReadArrayFind` | `storageIndexReadArrayFindBox` / `storageIndexReadArrayFindDiamond` | done | merged upstream (`29c44e225b`); Lean splits by modality |
| `storageIndexReadArrayBindLocalRoot` | `storageIndexReadArrayBindLocalRootBox` / `…Diamond` | existing | |
| `storageIndexReadArrayStoreRoot` | `storageIndexReadArrayStoreRootBox` / `…Diamond` | existing | |
| `storageIndexWriteArrayCopySource` | `storageIndexWriteArrayCopySourceBox` / `…Diamond` | existing | |
| ~~`storageIndexWriteNonSimpleRhsCapture`~~ | `storageIndexWriteUnfoldSource` | gone upstream | replaced by the location-neutral `indexWriteValueRhsCapture` (storage root/field table). `binopUnfoldResult`, the Lean rule that used to take this taclet's arith-simple cell, is gone with it — subsumed by `*UnfoldSource`, and solkey never had an `_unfold_result` taclet |
| `storageIndexWriteNonSimpleIndexCapture` | `storageIndexWriteUnfoldLeftSndIndex` | done | `sp1[nse] = e ⇝ T se ?= e; T storage sp = sp1; T ie = nse; sp[ie] = se` with `isValueSource e`; the simple receiver is re-aliased too, which the paper does not write — pinning the base is what lets soundness drop a purity hypothesis on the index. Order vs source capture locked in by `RuleValidation.storageEvaluationOrder_rewrite_rhsFirst` (`a[++i] = ++i`) |
| ~~`storageIndexWriteRootRhsNonSimpleIndexCapture`~~ | `storageIndexWriteRefUnfoldLeftSndIndex` | renamed upstream (`4635f8a530`) | now `storageIndexWriteStorageRefNonSimpleIndexCapture` (next row); the Lean rule never distinguished a stack from a storage simple RHS, only value from reference |
| `storageIndexWriteStorageRefNonSimpleIndexCapture` | `storageIndexWriteRefUnfoldLeftSndIndex` | done | the `Ref` instance of `unfold_leftSnd`: `sp1[nse] = sp2 ⇝ T storage sp = sp1; T ie = nse; sp[ie] = sp2` with `isReference sp2`, no freeze — `RuleValidation.storageIndexWriteRefUnfoldLeftSndIndex_valid` |
| ~~`indexWriteInnerNonSimpleIndexCapture`~~ | `storageIndexWriteUnfoldLeftFst` / `memoryIndexWriteUnfoldLeftFst` | **deleted upstream** (`63c38cfaf6`) | Lean captures the whole inner path, which is **strictly more general**, not "coarser but equivalent": the KeY `\find` was hard-coded to `e1[nse][e2]`, so `m[i++][j][k] = v` matched nothing. It also had no RHS freeze, so it wrote the incremented `i` on `matrix[i++][0] = i`. Never modelled separately in Lean; recorded as a rejected design |
| ~~`indexReadInnerNonSimpleIndexCapture`~~ | `storageIndexReadUnfoldRightFst` / `memoryIndexReadUnfoldRightFst` | **deleted upstream** (`63c38cfaf6`) | same: depth-2 shape-keyed, replaced by the (currently non-firing) receiver capture |
| `storageIndexWrite_unfold_leftFst` | `storageIndexWriteUnfoldLeftFst` | done | `nsp[e1] = e2 ⇝ T se ?= e2; T storage sp = nsp; T ie ?= e1; sp[ie] = se` with `isValueSource e2` (a memory source, which the old `isSimple` admitted, now goes to `memoryToStorageIndexUnfoldLeftFst`) |
| ~~`storageIndexWriteRootRhs_unfold_leftFst`~~ | `storageIndexWriteRefUnfoldLeftFst` | renamed upstream (`4635f8a530`) | now `storageIndexWriteStorageRef_unfold_leftFst` (next row) |
| `storageIndexWriteStorageRef_unfold_leftFst` | `storageIndexWriteRefUnfoldLeftFst` | done | `nsp[e] = sp2 ⇝ T storage sp = nsp; T ie ?= e; sp[ie] = sp2` with `isReference sp2` |
| `storageIndexWriteCaptureAll` | `storageIndexWriteUnfoldLeftFst` **and** `storageIndexWriteUnfoldLeftSndIndex` | done | receiver and index both nonsimple (`nsp[nse] = e`), added in `efc047a470` and generalised in `4635f8a530` in place of the `*IndexedReceiver*` taclets. KeY captures both in one step; so does Lean's `UnfoldLeftFst` (its `T ie ?= e1` is the index capture), and the index half is `UnfoldLeftSndIndex` — both rules claim the taclet |
| `storageIndexWriteStorageRefCaptureAll` | `storageIndexWriteRefUnfoldLeftFst` **and** `storageIndexWriteRefUnfoldLeftSndIndex` | done | the `Ref` twin of the row above |
| `storageIndexRead_unfold_rightSndIndex` | `storageIndexReadUnfoldRightSndIndex` | existing | was Lean-only; solkey adopted the taclet |
| `storageIndexRead_unfold_rightSndResult` | `storageIndexReadUnfoldRightSndResult` | existing | was Lean-only; solkey adopted the taclet |
| `storageIndexRead_unfold_rightFst` | `storageIndexReadUnfoldRightFst` | done | was Lean-only (KeY covered the shape via `storageFieldRead_unfold_rightFst` + the deleted `indexReadInnerNonSimpleIndexCapture`); solkey adopted the taclet |

## Storage push / pop

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `storagePushValue_unfold_leftFstReceiver` | `storagePushValueUnfoldLeftFstReceiver` | existing | |
| `storagePush_unfold_leftFstReceiver` | `storagePushUnfoldLeftFstReceiver` | existing | |
| `storagePop_unfold_leftFstReceiver` | `storagePopUnfoldLeftFstReceiver` | existing | |
| `storageLocalRootPush_unfold_leftFstReceiver` | `storageLocalRootPushUnfoldLeftFstReceiver` | existing | |
| `storagePushValue_unfold_rightSndArgument` | `storagePushValueUnfoldRightSndArgument` | existing | |
| `storagePushValueCopySource_unfold_leftFstReceiver` | `storagePushValueUnfoldLeftFstReceiver` | existing | merged value/copy-source receiver unfolds — `RuleValidation.storagePushValueCopySource_unfold_leftFstReceiver_corresp` |
| `storagePushValueSave` | `storagePushValueSave` | existing | |
| `storagePushValueCopySource` | `storagePushValueCopySource` | existing | |
| `storagePushLengthSave` | `storagePushLengthSave` | existing | |
| `storageLocalRootPushBind` | `storageLocalRootPushBind` | existing | |
| `storagePopSave` | `storagePopSaveBox` / `storagePopSaveDiamond` | existing | Lean splits by modality |
| — | `storagePushLhsToPushValue` | existing | Lean-only normalization (push-lvalue forms) |

## Storage local declarations

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `storageLocalDeclInitDrop` | `storageLocalDeclInitDrop` | existing | same name both sides (Lean was `storageLocalDeclInitSplit` until the renaming that aligned both sides) |
| `storageLocalRootRebind` | `storageLocalRootRebind` | existing | |
| `storageLocalDeclSkip` | `storageLocalDeclSkip` | existing | |

## Storage delete

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `storageRootDelete` | `storageRootDelete` | done | `delete(gsp) ⇝ {storage := delAt(storage, gsp)}`; the three simple targets were one Lean rule (`storageDeleteSimpleTarget`) until the paper's split gave each its own |
| `storageFieldDelete` | `storageFieldDelete` | done | |
| `storageIndexDelete` | `storageIndexDelete` | done | `isArray sp ∨ isMapping sp`; writes `delAt` upstream since the `copyAt`→`save` fold (delete-semantics note below) |
| `storageFieldDelete_unfold_leftFst` | `storageFieldDeleteUnfoldLeftFst` | done | was one third of `storageDeleteComplexTarget` |
| `storageIndexDelete_unfold_leftFst` | `storageIndexDeleteUnfoldLeftFst` | done | `delete(nsp[e])`; a nonsimple index is the next row's |
| `storageIndexDeleteNonSimpleIndexCapture` | `storageIndexDeleteNonSimpleIndexCapture` | done | `delete(sp[nse]) ⇝ T ie = nse; delete(sp[ie])` — `RuleValidation.storageIndexDeleteNonSimpleIndexCapture_valid` |
| — | `storagePushPlaceDelete`, `storagePushPlaceDeleteUnfoldLeftFst` | done | Lean-only: `delete(arr.push())` is this syntax's push-place target, with no rule upstream (`isSimplePushPlaceDeleteTarget` / `isComplexPushPlaceDeleteTarget`) |

**Delete semantics:** solkey's delete writes the lazy `delAt`/`delNode`
marker whose read rules preserve mapping members of a deleted struct
(`selectStDelNodeMap` reads through to the original — real Solidity
semantics). Lean's `SVal.defaultOf` (`Semantics.lean`) matches: it
resets primitives, empties arrays, recurses into struct fields, and
leaves mappings untouched (exercised by the `wallet` examples in
`Examples/Taclets/StorageOps.lean`). solkey's `storageIndexDelete` used
to reset a collection element outright (`defVal`, mappings included);
since the `copyAt`→`save` fold it writes `delAt` like the root and field
deletes, so the two sides agree at every path shape — the
Solidity-faithful choice Lean had made.

## Memory allocation, aliasing, declarations

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `memoryReferenceDeclFreshAlloc` | `memoryDeclFreshAlloc` | existing | merged struct/array |
| `memoryArrayFreshAlloc` | `memoryDeclFreshAlloc` | existing | merged (solkey renamed `memoryArrayDeclFreshAlloc` → `memoryArrayFreshAlloc`) |
| `memoryRootDeleteFreshRebind` | `memoryRootDeleteFreshRebind` | done | `delete(mv) ⇝ {mv := freshId(alloc(mv)) ‖ memory := alloc(mv)}`, the pair KeY writes; write-after-delete exercised in `Examples/Taclets/MemoryOps.lean` |
| `memoryRootRebind` | `memoryRootAlias` | existing | `memoryRootAlias` is now restricted to memory RHSs, making it exactly KeY `memoryRootRebind`; the storage-RHS case it silently absorbed is `memoryStorageCopy` |
| `memoryStorageCopy` | `memoryStorageCopy` | done | `m = sp;` deep copy (fresh identity + `copySt` in the interpreter); previously absorbed by `memoryRootAlias` |
| `memoryStorageCopyUnfold` | `memoryStorageCopyUnfold` | done | complex storage path captured into the storage alias first; deep paths (`m = alice.account.token`) already step via `storageFieldReadUnfoldRightFst` / `storageIndexReadUnfoldRightFst` |
| `memoryLocalDeclInitDrop` | `memoryLocalDeclInitDrop` | existing | solkey deleted the whole per-RHS decl-init family (`memoryLocalDeclInitRootAlias`, `…StorageCopy`, `…StorageCopyUnfold`, `…FieldReadValue/Memory/_unfold_rightFst`, `…IndexReadValue/Memory`) and adopted the Lean approach: one generic decl-with-init split, then the assignment rules apply |
| — | `storageToMemoryDeclCopyRoot`, `storageToMemoryDeclCopyField`, `storageToMemoryDeclUnfoldRightFst` | existing | now Lean-only decl-specific granularity; their former KeY counterparts (`memoryLocalDeclInitStorageCopy`, `…Unfold`) were removed with the family above |

## Memory field/index write & read

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `memoryFieldWrite` | `memoryFieldWriteStore` (value), `memoryFieldWriteCopy` (reference source, `image(mv2)`) | done | Lean's sorts are not generic, so KeY's one write is two rules here; both claim the taclet |
| `memoryFieldRead` | `memoryFieldReadHeap` / `memoryFieldReadAliasRoot` | existing | solkey `0f9b99ad55` merged the former `memoryFieldReadValue` (`Field[primitive]`) and `memoryFieldReadMemory` (`Field[reference]`, `read<[Identity]>`) into one rule over a bare `Field`, its result sort resolved by `\hasMemoryFieldSort(a, \sort(alpha))` — the merge Lean had made already |
| `memoryFieldRead_unfold_rightFst` | `memoryFieldReadUnfoldRightFst` | existing | |
| `memoryFieldWriteCaptureSrc` | `memoryFieldReadUnfoldRightSndResult` | done | the paper's `memoryFieldWriteRef_unfold_source`, its source alias `mv2` spelled `se` as in storage |
| `memoryFieldWrite_unfold_leftFst` | `memoryFieldWriteUnfoldLeftFst` | done | `nmp.fld = e ⇝ T se ?= e; T memory mv = nmp; mv.fld = se` with `isValueSource e` — the storage rule with the heap alias. A *storage* source on a memory target is admitted by no memory rule; that residue is `Coverage.ResidueShape.assignMemFieldFromStorage` |
| `memoryFieldWriteMemRef_unfold_leftFst` | `memoryFieldWriteRefUnfoldLeftFst` | done | `Ref` instance: `nmp.fld = mv2 ⇝ T memory mv = nmp; mv.fld = mv2`, no freeze (`4635f8a530`) |
| `memoryIndexWriteArray` | `memoryIndexWriteStoreBox` / `…Diamond` (value), `memoryIndexWriteCopyBox` / `…Diamond` (reference source) | done | Lean splits by modality (bounds) and by source sort; all four claim the taclet |
| `memoryIndexReadArrayValue` | `memoryIndexReadHeapBox` / `…Diamond` | existing | |
| `memoryIndexReadArrayMemory` | `memoryIndexReadHeapBox` / `memoryIndexReadAliasRootBox` / `…Diamond` | existing | |
| `memoryIndexRead_unfold_rightFst` | `memoryIndexReadUnfoldRightFst` | existing | |
| `memoryIndexWrite_unfold_leftFst` | `memoryIndexWriteUnfoldLeftFst` | done | `nmp[e1] = e2 ⇝ T se ?= e2; T memory mv = nmp; T ie ?= e1; mv[ie] = se` with `isValueSource e2` |
| `memoryIndexWriteMemRef_unfold_leftFst` | `memoryIndexWriteRefUnfoldLeftFst` | done | `nmp[e] = mv2 ⇝ T memory mv = nmp; T ie ?= e; mv[ie] = mv2` |
| `memoryIndexWriteCaptureAll` | `memoryIndexWriteUnfoldLeftFst` **and** `memoryIndexWriteUnfoldLeftSndIndex` | done | as `storageIndexWriteCaptureAll`: both rules claim it |
| `memoryIndexWriteMemRefCaptureAll` | `memoryIndexWriteRefUnfoldLeftFst` **and** `memoryIndexWriteRefUnfoldLeftSndIndex` | done | the `Ref` twin |
| `memoryIndexWriteMemRefRhsCapture` | `memoryIndexReadUnfoldRightSndResult` | done | the paper's `memoryIndexWriteRef_unfold_source`; a reference source at an index is hoisted into `se` before the write |
| `memoryIndexWriteNonSimpleIndexCapture` | `memoryIndexWriteUnfoldLeftSndIndex` | done | `mv1[nse] = e ⇝ T se ?= e; T memory mv = mv1; T ie = nse; mv[ie] = se` with `isValueSource e` (`RuleValidation.memoryIndexWriteUnfoldLeftSndIndex_valid`); order vs source capture as in the storage case |
| `memoryIndexWriteMemRefNonSimpleIndexCapture` | `memoryIndexWriteRefUnfoldLeftSndIndex` | done | `mv1[nse] = mv2 ⇝ T memory mv = mv1; T ie = nse; mv[ie] = mv2` |
| `memoryFieldRead_unfold_rightSndResult` | `memoryFieldReadUnfoldRightSndResult` | existing | was Lean-only; solkey adopted the taclet |
| `memoryIndexRead_unfold_rightSndIndex` | `memoryIndexReadUnfoldRightSndIndex` | existing | was Lean-only; solkey adopted the taclet |
| `memoryIndexRead_unfold_rightSndResult` | `memoryIndexReadUnfoldRightSndResult` | existing | was Lean-only; solkey adopted the taclet |
| — | ~~`memoryWriteUnfoldRightSndResult`~~ | removed | the Lean-only `nmp = nse ⇝ _ se = nse; nmp = se` is gone with the paper's partition: a complex value source on a memory target is `memory{Field,Index}WriteUnfoldSource` on a simple receiver, the `T se ?= e` freeze of `memory{Field,Index}WriteUnfoldLeftFst` on a complex one, and a ternary source is lowered by `ternaryToIfMemory` first |

## Memory delete

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `memoryFieldDeletePrimitive` | `memoryFieldDeletePrimitive` | done | `delete(mv.fp)`, `isPrimitiveMember`. The five memory deletes were one Lean rule (`memoryDeleteSimpleTarget`) until the paper's split; each now states the term its target's sort selects — `write(memory, mv.fp, defVal(mv.fp))` here, `write(alloc(mv.fr), mv.fr, fresh)` for a reference member |
| `memoryFieldDeleteReference` | `memoryFieldDeleteReference` | done | `delete(mv.fr)`, `isReferenceMember` |
| `memoryIndexDeletePrimitive` | `memoryIndexDeletePrimitiveBox` / `…Diamond` | done | `delete(ap[ie])`, `isPrimArray ap`; now a guarded split (`inBounds`/`revert()`), Lean splitting by modality as for every array index |
| `memoryIndexDeleteReference` | `memoryIndexDeleteReferenceBox` / `…Diamond` | done | `delete(ar[ie])`, `isRefArray ar` |
| `memoryFieldDelete_unfold_leftFst` | `memoryFieldDeleteUnfoldLeftFst` | done | was one third of `memoryDeleteComplexTarget` |
| `memoryIndexDelete_unfold_leftFst` | `memoryIndexDeleteUnfoldLeftFst` | done | |
| `memoryIndexDeleteNonSimpleIndexCapture` | `memoryIndexDeleteNonSimpleIndexCapture` | done | `delete(mv[nse]) ⇝ T ie = nse; delete(mv[ie])` — `RuleValidation.memoryIndexDeleteNonSimpleIndexCapture_valid` |

## Memory → storage copies

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `memoryToStorageStoreRoot` | `memoryToStorageStoreRoot` | existing | |
| `memoryToStorageFieldCopyRoot` | `memoryToStorageFieldCopyRoot` | existing | deep-copy of a memory root into a storage slot exercised in `Examples/Taclets/MemoryOps.lean` |
| `memoryToStorageFieldCopyField` | `memoryToStorageFieldCopyField` | done | `sp.fld = mv.fr ⇝ {storage := copyMem(sp.fld, rhs)}` with `isMemberSource rhs` — the one member-source shape read directly (was folded into `…CopyRoot` plus unfolds). `memoryToStorageUnfoldRightFstSource` excludes it (`isFieldCopySource`) and hoists every other complex memory source into `se` |
| `memoryToStorageIndexMappingCopyRoot` | `memoryToStorageIndexMappingCopyRoot` | existing | indexed deep-copy, mapping receiver |
| `memoryToStorageIndexArrayCopyRoot` | `memoryToStorageIndexArrayCopyRootBox` / `…Diamond` | existing | indexed deep-copy, array receiver; Lean splits by modality (bounds/revert) |
| `memoryToStorageField_unfold_leftFst` | `memoryToStorageFieldUnfoldLeftFst` | done | `nsp.fld = mv ⇝ T se ?= mv; T storage sp = nsp; sp.fld = se`; the `?=` is inert on a reference, so the residual is `T storage sp = nsp; sp.fld = mv`. Was Lean-only `memoryToStorageUnfoldLeftFstTarget` until `4635f8a530` |
| `memoryToStorageIndex_unfold_leftFst` | `memoryToStorageIndexUnfoldLeftFst` | done | `nsp[e] = mv ⇝ T se ?= mv; T storage sp = nsp; T ie ?= e; sp[ie] = se`; new on both sides — a memory source into a complex indexed receiver used to slip through `storageIndexWriteUnfoldLeftFst`'s `isSimple` |
| `memoryToStorageIndexNonSimpleIndexCapture` | `memoryToStorageIndexUnfoldLeftSndIndex` | done | `sp1[nse] = mv ⇝ T se ?= mv; T storage sp = sp1; T ie = nse; sp[ie] = se`; was Lean-only `memoryToStorageUnfoldLeftSndTargetIndex` |
| `memoryToStorageIndexCaptureAll` | `memoryToStorageIndexUnfoldLeftFst` **and** `memoryToStorageIndexUnfoldLeftSndIndex` | done | as `storageIndexWriteCaptureAll` |
| — | `memoryToStorageUnfoldRightFstSource` | done | Lean-only source unfold, `path = nmp ⇝ _ se = nmp; path = se` |

## Value declarations (phase 2)

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `localValueDeclInitDrop` | `localValueDeclInitDrop` | done | same name both sides (Lean was `valueDeclInitSplit` until the renaming that aligned both sides) |
| `valueDeclSkip` | `valueDeclSkip` | done | |
| `localValueAssign` | `localValueAssign` | done | terminal `vp = se;` for simple RHS |

## Binary arithmetic operators (phase 2)

Family pattern per op `X ∈ {addition, subtraction, multiplication, power,
division, modulo}`: `X_unfold_left`, `X_unfold_right`, `XAssignment`. Lean
has one rule per shape over `BinOp` — `binopUnfoldLeft op`,
`binopUnfoldRight op`, `binopAssignment op` — with the taclet as the
instance's origin. There is no `_unfold_result` on either side:
`binopUnfoldResult`, which hoisted an arith-simple binop out of a write, is
gone, subsumed by the `*UnfoldSource` rules.

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `addition_unfold_left/right`, `additionAssignment` | `binopUnfoldLeft/Right .add`, `binopAssignment .add` | done | |
| `subtraction_*`, `subtractionAssignment` | `… .sub` | done | |
| `multiplication_*`, `multiplicationAssignment` | `… .mul` | done | |
| `power_*`, `powerAssignment` | `… .pow` | done | `localOpAssign .pow` and the other `**=` instances are `leanOnly`: solkey has no `PowAssign` taclets |
| `division_*`, `divisionAssignment` | `… .div` | done | zero-divisor guard per plan D2 |
| `modulo_*`, `moduloAssignment` | `… .mod` | done | zero-divisor guard per plan D2 |

## Comparisons, boolean operators, unary (phase 2)

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `boolEqualityCaptureLhs`, `boolEqualityAssignment` | `binopUnfoldLeft .eqB`, `binopAssignment .eqB` | done | |
| `boolEqualityCaptureRhs` | `binopUnfoldRight .eqB` | done | added by solkey `0f9b99ad55`; claimed by the generic right-operand unfold, which binds the fixed `se` where KeY mints a fresh `pv` — the scratch-name defect `docs/calculus-parity.md` §2 records for two nonsimple operands |
| `boolInequalityCaptureLhs/CaptureRhs`, `boolInequalityAssignment` | `binopUnfoldLeft/Right .neB`, `binopAssignment .neB` | done | |
| `lessThanCaptureLhs/CaptureRhs`, `lessThanAssignment` | `… .lt` | done | |
| `greaterThanCaptureLhs/CaptureRhs`, `greaterThanAssignment` | `… .gt` | done | |
| `lessEqualCaptureLhs/CaptureRhs`, `lessEqualAssignment` | `… .le` | done | |
| `greaterEqualCaptureLhs/CaptureRhs`, `greaterEqualAssignment` | `… .ge` | done | |
| `logicalAndCaptureLhs`, `logicalAndAssignment` | `binopUnfoldLeft .and`, `binopAssignment .and` | done | no `binopUnfoldRight` instance for `.and`/`.or` (`op.shortCircuits = false`): the right operand is the short-circuit row |
| `logicalOrCaptureLhs`, `logicalOrAssignment` | `… .or` | done | |
| `logicalAndShortCircuitRhs` | `logicalAndShortCircuitRhs` | done | `v = se && nse;` → `if (se) { v = nse } else { v = false }` — the statement-level image of KeY's ternary residual; the interpreter itself short-circuits, so the rewrite is exact (`RuleValidation.logicalAndShortCircuitRhs_shortCircuits_valid` shows the reverting RHS is skipped) |
| `logicalOrShortCircuitRhs` | `logicalOrShortCircuitRhs` | done | dual (`v = se ? true : nse`) |
| `logicalNotCapture`, `logicalNotAssignment` | `unopCapture .not`, `unopAssignment .not` | done | |
| `unaryMinusCapture`, `unaryMinusAssignment` | `unopCapture .neg`, `unopAssignment .neg` | done | |

## Storage compound assignments (phase 3)

Pattern per op `Op ∈ {Add, Sub, Mul, Div, Mod}`:

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `storageRootOpAssign` | `storageRootOpAssign op` | done | Div/Mod: zero-divisor guard |
| `storageFieldOpAssign` | `storageFieldOpAssign op` | done | |
| `storageIndexMappingOpAssign` | `storageIndexMappingOpAssign op` | done | `map[ie] ⊕= se`, no bounds goal |
| `storageIndexArrayOpAssign` | `storageIndexArrayOpAssign op` | done | `arr[ie] ⊕= se` with the bounds split (`compoundIndexGoals`); solkey `29c44e225b` split the receiver kinds and the one Lean rule (`storageIndexCompoundAssign`) followed |
| `storageFieldOpAssign_unfold_leftFst` | `storageFieldOpAssignUnfoldLeftFst op` | done | residual `T se ?= se1; T storage sp = nsp; sp.fld ⊕= se` — the freeze is `freezeRhs` (was an unconditional `T rv = se` into a second scratch name, now gone) |
| `storageIndexOpAssign_unfold_leftFst` | `storageIndexOpAssignUnfoldLeftFst op` | done | same `?=` freeze |
| `memoryField{Add,Sub,Mul,Div,Mod}Assign`, `memoryIndexArray{Add,Sub,Mul,Div,Mod}Assign` | `memoryFieldOpAssign op` / `memoryIndexArrayOpAssign op` | done | the paper's `memoryFieldOpAssign` / `memoryFieldDivAssign` / `memoryIndexArrayOpAssign`. Landed upstream in solkey `444f029579` (feedback item 10); the Lean rules carried no origin until the rule-table rewrite. No root form (a memory root binds an identity, not a value cell) and no mapping form (memory has no mappings) |
| `memoryField{Add,…}Assign_unfold_leftFst`, `memoryIndex{Add,…}Assign_unfold_leftFst` | `memoryFieldOpAssignUnfoldLeftFst op` / `memoryIndexOpAssignUnfoldLeftFst op` | done | complex memory path, same `?=` freeze as the storage twins (the index unfold drops `Array` from its name upstream as the storage one does); `RuleValidation.memory{Field,Index}OpAssignUnfoldLeftFst_*_valid` |
| `localOpAssign` (`localAddAssign`, …) | `localOpAssign op` | done | terminal `lv ⊕= se;`; the Div/Mod zero-divisor revert lives in the interpreter's `applyBinOp`; update theorem `localOpAssign_update` (Wp/Terminal/UpdateCompound.lean) |
| `{add,sub,mul,div,mod}AssignValueRhsCapture` | `compoundAssignValueRhsCapture op` | done | location-neutral capture of a nonsimple compound-assign RHS into `se`; soundness `compoundAssignValueRhsCapture_sound` is conditional on the target's old value surviving the RHS's effects (`hstableOld`) — the compound image of the evaluation-order note |

## Increment / decrement (phase 3)

Pattern per `V ∈ {Preincrement, Postincrement, Predecrement, Postdecrement}`:

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `storageRootV` / `storageRootVAssignment` | `storageRootIncrement v` / `storageRootIncrementAssignment v` | done | the calculus calls the family `storageRootIncrement` |
| `storageFieldV` / `storageFieldVAssignment` | `storageFieldIncrement v` / `storageFieldIncrementAssignment v` | done | |
| `storageIndex{Mapping,Array}V` / `storageIndex{Mapping,Array}VAssignment` | `storageIndexIncrement v` / `storageIndexIncrementAssignment v` | done | solkey `29c44e225b` split the receiver kinds; Lean keeps one rule per form over both (`KeyOrigin.merged`) |
| `storageFieldV_unfold_leftFst` | `storageFieldIncrementUnfoldLeftFst v` | done | |
| `storageIndexV_unfold_leftFst` | `storageIndexIncrementUnfoldLeftFst v` | done | |
| `memoryField{Pre,Post}{in,de}crement[Assignment]`, `memoryField*_unfold_leftFst`, `memoryIndexArray{Pre,Post}{in,de}crement[Assignment]`, `memoryIndex{Pre,Post}{in,de}crement_unfold_leftFst` | `memoryFieldIncrement v` / `…Assignment v` / `…UnfoldLeftFst v`, `memoryIndexArrayIncrement v` / `…Assignment v`, `memoryIndexIncrementUnfoldLeftFst v` | done | the paper's `memoryFieldIncrement`; same upstream commit as the compound-assign family above, origins added with the rule-table rewrite |
| `localDeclV` (`localDeclPreincrement`, ...) | `localAssignIncrement v` | done | `T vp = ++lv;` — merged with the next row (`KeyOrigin.merged`): Lean reaches it by `localValueDeclInitDrop` then the assignment form |
| `localAssignV` (`localAssignPreincrement`, ...) | `localAssignIncrement v` | done | `vp = ++lv;` |
| `localV` (`localPreincrement`, ...) | `localIncrement v` | done | bare statement `++lv;` on a stack local; update theorem `localIncrement_update` (Wp/Terminal/UpdateCompound.lean) (`--` cannot be a `sol!` token — decrement instances are exercised via `incDecExpr`) |

## Assert, if-then-else (phase 4)

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `assertConditionCapture` | `assertConditionCapture` | done | |
| `assertSimple` | `assertSimple` | done | terminal in the rewrite layer; the Holds/Violated split is the revert semantics in `Semantics.lean` |
| `requireConditionCapture` | `requireConditionCapture` | done | clone of the assert capture over `Stmt.requireStmt` |
| `requireSimple` | `requireSimple` | done | terminal; the interpreter reverts on false — box `c → φ`, diamond `c ∧ φ` fall out of `check` (solkey `docs/require-assert.md`); the KeY assert/require difference (⊥ vs revert) lives entirely in that layer |
| `ifUnfold` / `ifElseUnfold` | `ifElseUnfold` | done | solkey's statement-level nonsimple-condition capture (`solidityProgramRules.key`); Lean merges the if/if-else pair since `Stmt.ite` always carries both branches (else = `[]`) |
| `ifSplit` / `ifElseSplit` | `SolidityJudgment.ite_split` | lemma | solkey's sequent-level two-goal split on a simple condition (`\add(se = TRUE/FALSE ==>)`); a `BlockStep` cannot produce two goals, so the rewrite layer is intentionally stuck there and the split is the lemma (`Calculus/JudgmentSplit.lean`; `ite_split_pure` is the exact KeY shape for pure conditions) |
| `ternaryCaptureCond` | `ternaryCaptureCond` | done | `WrappedExpr.mkTernary` + `c ? t : e` in `sol!`; the interpreter short-circuits like `&&`/`||`; fires on any target kind now that `ternaryToIfMemory` lowers the memory case (the old memory-complex-lhs exclusion went with `memoryWriteUnfoldRightSndResult`) |
| `ternaryToIf` | `ternaryToIf` | done | `v = se ? e1 : e2;` ⇝ `if (se) v = e1; else v = e2;` — both sides evaluate the same branch in the same state (`ternaryToIf_sound` is an equality up to defeq) |
| `ternaryToIfStorage` | `ternaryToIfStorage` | done | twin for a storage-path target; soundness pinned to the primitive-write dispatch (branch types agree) |
| — | `ternaryToIfMemory` | done | Lean-only twin for a memory-path target (`mpath = s ? e1 : e2`); KeY has none. With the three, a conditional is never a write's *source* (`isValueSource` excludes it): it is lowered first |
| `ifTrue`, `ifElseTrue` | `ifElseTrue` | done | program-level literal-condition simplifiers, added upstream 2026-09-10 on this repository's suggestion (`docs/solkey-feedback.md`) in `concrete_solidity` so they outrank the split; Lean merges the if/if-else pair as for `ifElseUnfold`. The term-level `ifthenelse_true` of `ifThenElseRules.key` is the same rule one layer down (plan D3b) and is not in `KeyTaclets` |
| `ifFalse`, `ifElseFalse` | `ifElseFalse` | done | same, literal `false` |
| `ifElseNegated` | `ifElseNegated` | done | swaps branches on `!se`; program-level upstream since 2026-09-10 (term-level `ifthenelse_negated` before) |
| `ifthenelse_same_branches` | `SolidityJudgment.ite_same_branches` | lemma | corollary of `ite_split`; a `RuleName` port would overlap `ifElseTrue`/`ifElseFalse` on literal conditions and need `DecidableEq Block` in a guard. |
| `ifthenelse_concrete`–`_concrete4` | — | arch | term-level `\if(φ)\then(true)\else(false)` simplification; `WrappedExpr` has no conditional-expression constructor, and on the meta level Lean's own `if`/`Bool.cond` simp set covers it. |
| `ifExthenelse1_*` (all) | — | arch | commented-out dead code in the KeY source (`\ifEx` deprecated since 2014). |
| `ifthenelse_*_for` (all `_for` variants) | — | arch | formula-sort duplicates of the term-level rules (same `\displayname`, schema vars of sort `\formula`), an artifact of KeY's term/formula distinction; Lean's `Prop`/`Bool` need no such split. (The earlier "loops are outside the fragment" note was wrong — these are not loop rules.) |

## Payments (phase 5)

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `transfer_unfold_leftFstReceiver` | `transferUnfoldLeftFstReceiver` | done | |
| `transfer_unfold_rightSndArgument` | `transferUnfoldRightSndArgument` | done | |
| `transferNoCallbackBox`, `transferNoCallbackDiamond` | `transferNoCallbackBox` / `transferNoCallbackDiamond` | done | solkey `333cc7b353` split the rule by modality and Lean now does too (`twins`, one rule each as the paper has them). The box rule books `{transfer(sadr, se)}` unguarded — a *strengthening* of the interpreter, which reverts an unfunded transfer, so its `Update/TacletTable` bridge is open by construction; the diamond rule owes the "sufficient funds" goal `0 ≤ se ≤ selfBalance` (`084de89677`; the interpreter's revert condition, `docs/solc-alignment.md`) beside the same booked update. No `revert()` goal on either side. `ruleNamesWithCallback` erases both twins |
| `transferWithCallbackBox`, `transferWithCallbackDiamond` | `transferWithCallback` | done | same split and balance debit; the callback havoc also quantifies over `selfBalance`. KeY's `transferSemantics` *choice*: lives in the alternative rule list `ruleNamesWithCallback` (never coexists with `transferNoCallback` — `candidateWithCallback` / `applicable_eq_candidateWithCallback`; coverage unchanged by `ruleApplies_withCallback_iff`). The rule is terminal; its meaning is the relational layer `CallbackSemantics.ExecC`/`HoldsC`: `holdsC_transfer_split` is the KeY branch split (invariant-on-exit ∧ resume-under-havoc, both storage and net havocked per solkey net.md), `holds_of_holdsC` shows it soundly over-approximates the executable semantics. Examples incl. the negative (trivial-invariant) case: `Examples/Taclets/CallbackOps.lean`. |

## Terminal rules as updates

Every terminal rule (empty residual) has a state update in
`Wp/Terminal/Table.lean` (`terminalUpdate?`, written in state vocabulary,
not through the interpreter) and a theorem `<rule>_update` in
`Wp/Terminal/Update*.lean` proving `execStmt s stmt = terminalUpdate r
stmt s` under the rule's guard; `Wp/Terminal/Soundness.lean` dispatches them
(`terminalUpdate_sound`, `terminal_step_sound`). The KeY `\replacewith`
update of a terminal taclet is therefore matched by a Lean function, and
"taclet ⇒ update" is a theorem per rule.

## Update algebra (`updateRules.key`)

The Lean model has no update syntax — state change is function
application — so KeY's update calculus splits into (a) point-of-
application laws with real semantic content, ported as `State` lemmas in
`Semantics/Properties.lean`, and (b) the update-monoid normal-form
machinery, which is definitional function composition in Lean.

| KeY rule | Lean analogue | Status | Notes |
| --- | --- | --- | --- |
| `applyOnPV` / `applyOnPVLastInParallel` | `State.getEnv_setEnv_self`, `State.getNet_setNet_self`; storage: `State.findStorage_saveStorage_same` (existing) | lemma | read after write at the point of application |
| `applyOnDifferentPV` / `applyOnDifferentPVLastInParallel` | `State.getEnv_setEnv_ne`, `State.getNet_setNet_ne`; storage: `State.saveStorage_frame` (existing) | lemma | frame under a distinct location |
| `simplifyUpdate1`–`3` | `State.setEnv_setEnv_absorb`, `State.setNet_setNet_absorb` (core: `setBy_setBy_self`) | lemma | the syntactic `\dropEffectlessElementaries` procedure is meaningless without update terms; its semantic law is overwrite absorption |
| `sequentialToParallel1-3`, `applyOnParallel`, `applyOnElementary`, `applyOnSkip`, `applySkip1-3`, `parallelWithSkip1-2` | — | arch | the update monoid normal form. The monoid laws are `Upd.seq_assoc`/`Upd.id_seq`/`Upd.seq_id` (`Update.lean`), definitional; the sequential-to-parallel step proper is `Upd.Par.seq_single`, `{u}{x := t} = {u ‖ x := {u}t}`, and a derivation writes it as a `⇝≡` line whose obligation is `Frontier.Equiv` (`Update/Step.lean`, discharged by `upd_merge` over `Update/Merge.lean`'s reader lemmas) |
| `simplifyIfThenElseUpdate1-4`, `commuteSimpleUpdates`, `elimSelfUpdate*` | — | arch | commented-out dead code in the KeY source; `commuteSimpleUpdates` is additionally false as *State equality* on the assoc-list representation (only true pointwise) |


## The data-structure theories

The rows above are `solidityProgramRules.key`, the *program* calculus. Its
updates are written over symbols — `find`, `save`, `selectSt`, `read`,
`write`, `addM` — that solkey declares in `structHeader.key`/`memoryHeader.key`
and defines nowhere: their whole meaning is the taclet sets of
`structRules.key`, `memoryRules.key` and `structMemoryRules.key`.
`Solidity/Theory/` is that meaning, as a term algebra with one theorem per
taclet; `Solidity/Update/Theory.lean` proves a rule's stated *memory* update
denotes the interpreter's (`heapRhs_eq_theory`). The storage algebra has no
denotation: it is a theory over free terms, and the one place its terms would
differ from the interpreter — a copy of a mapping-carrying type — is not a
statement (`TypedStmt.Assign.mk`).

Paths are `Semantics.Seg` on both sides: a member constant is `Seg.field n`,
`at(i)` is `Seg.at i`, `size` is `Seg.field "length"`, `consr(p, a)` is
`p ++ [a]`. `listRules.key` therefore needs no module — it is `List`.

### `structRules.key` → `Theory/Storage.lean` (`Struct`, `StValue`)

| KeY taclet | Lean theorem | Status |
| --- | --- | --- |
| `defaultValueStruct` | `defaultValueStruct`, with `defaultValueInt`/`defaultValueBool` | done: `defaultValue<[α]>` is `st mtSt`, the `Struct` default, read through the caller's cast |
| `selectOnStore` | `selectOnStore` | done |
| `selectOnEmptyStorage` | `selectOnEmptyStorage` | done |
| `saveOnEmptyStorage` | `saveOnEmptyStorage` | done, in the pre-fold shape (an `isEmpty(flds)` split) |
| `saveOnStoreCons` | `saveOnStoreCons` | done, in the pre-fold shape: the `isEmpty(flds)` split is back, since the leaf collapses; `(Struct) v0` is `asStruct v0` |
| `findDefinitionEmpty` | `findDefinitionEmpty` | done |
| `findDefinitionCons` | `findDefinitionCons` | done |
| ~~`saveOnEmpty`~~ (pre-fold) | `saveOnEmpty` | done — gone upstream with the `copyAt`→`save` fold and kept here: `save(st, nil, v) ⇝ v`, the collapsing leaf (see the opening note) |
| ~~`selectOnSaveEmpty`~~ (pre-fold); `selectOnSaveEmptyRef`, `selectOnSaveEmptyIndexStruct`, `selectOnSaveEmptyDefault` | `selectOnSaveEmpty` | done as the pre-fold rule — a member of `save(st, nil, v)` is a member of `(Struct) v`; the three post-fold instances are it at one sort each |
| `saveOnEmptyPrim` | `saveOnEmptyPrimInt`, `saveOnEmptyPrimBool` | done, as the two cast readings at the end of a walk: `storeSt`'s third argument is the supersort, so the primitive leaf is stored verbatim |
| `selectOnSaveEmptyMap` | — | **arch**: upstream a mapping member of a written location stays the location's own; here the leaf collapses and a mapping member is a subtree like any other. Unreachable — solc ≥ 0.7 and solkey's parser reject the copy, `TypedStmt.Assign.mk` cannot build it, `Semantics.rhsToSVal` is stuck on it |
| `selectOnSaveCons` | `selectOnSaveCons` | done, and **unconditional** — the fundamentals repository's analogue (`selectSave`) needs `isStruct`; total definitions do not. Proved for the one-segment walk (`selectSt_storeAt`) and lifted; KeY's `cast<[α]>(save(…, flds, v))` is the `isEmpty(flds)` split |
| `delValueStruct` | `delValueStruct` | done |
| `delValueDefault` | `delValueDefault` (`primDefault`, keyed on the value's own sort) | done |
| `selectStDelNodeMap` | — | **arch**: a `Seg` carries no `MapField`, so a mapping member of a deleted node is reset here; the mapping-preserving `delete` is the interpreter's `SVal.defaultOf` |
| `selectStDelNodeRef` | `selectStDelNodeRef` | done, unconditional: one theorem covers `Ref`, `Default` and an absent member |
| `selectStDelNodeIndexStruct` | `selectStDelNodeIndexStruct` | done |
| `selectStDelNodeDefault` | `selectStDelNodeRef`, `selectStDelNodeDefault` | done |
| `delAtEmpty` | `delAtEmpty` | done |
| `selectOnDelAtCons` | `selectOnDelAtCons` | done, through `selectOnSaveCons`: `delAt` is eager, `save st p (delValue (find st p))` |
| ~~`copyAtEmpty`~~, ~~`selectOnCopyAtCons`~~, ~~`mergePrim`~~, ~~`selectStMerge{Map,Ref,IndexStruct,Default}`~~, ~~`mergeStValueCast`~~ | — | gone upstream with the fold; not modelled here for the reason `selectOnSaveEmptyMap` is not |
| `findStValueCast`, `delValueStValueCast`, `selectStValueCast` | `asStruct_st`, `asStruct_prim`, `find_append` | done as the cast being the inverse of the injection `st` |
| `sizeNotNegative` | — | **arch**: an `\add` of a reachability fact, not a rewrite; its Lean form is `WellFormedConsumers` row C1 (`length_read_nonneg`) |

**Beyond the taclets.** solkey has no `find(save(…), …)` rule at all: a read of
a write is reached by `findDefinitionCons` then `selectOnSaveCons`, one
selector at a time. `Theory/Storage.lean` packages the four cases over
`save` — `find_save_same`, `find_save_extends` (below the write, through the
cast `find<[Struct]>` makes), `find_save_prefix` (above it) and
`find_save_frame` (off it, over `diverges`) — and `find_append` composes reads
along `++`. `Semantics` had only the first, and only in the form that
presupposes the write succeeded (`SemanticsProperties.SVal.find_save_same`).

**`storeAt` and the two sorts.** `save` is a recursion on the path over
`storeAt`, the one-segment walk (not an upstream symbol, but the shape
`saveOnStoreCons` produces). It returns `Struct`, as KeY's does, and stores
the written value verbatim at the last segment: `storeSt`'s third argument is
the supersort `StValue`, so a primitive leaf is kept as itself and `find`
reads it back at the caller's sort — which is what `saveOnEmptyPrim` does in
KeY, and why `find`'s one-segment arm (`isEmpty(flds)`) is not decoration.
`delAt`/`delNode` are eager over the same walk. The pre-state leaf
`Struct.cur` (KeY's `storage` program variable, below a path) is a view with no
upstream taclet, and there is no denotation of storage *writes*
(`Update/Lower.lean` relates storage *reads* only): the `*CopySource` / `…StoreRoot` program rows
below are untouched because the copy they state is mapping-free by
construction (`TypedStmt.Assign.mk`, `stmtTypingOk`), and
`Rules.StTerm.pushAt` still merges KeY's three push taclets.

### `memoryRules.key` → `Theory/Memory.lean`

Identities are KeY's path identities `idC(idp, flds)`, so the chain-walking
rows have counterparts and `addM` carries the root it allocates. Resolving a
path identity against the interpreter's heap happens in the *denotation*
(`Update/Theory.lean`, `Memory.resolve`), not in the algebra.

| KeY taclet | Lean theorem | Status |
| --- | --- | --- |
| `readOnWrite` | `readOnWrite` | done |
| `readFromEmptyMemory` | `readFromEmptyMemory` | done |
| `readOnAddM` | `readOnAddM` (`readAddEqual`/`readAddDifferent` are the paper's split form) | done |
| `newFromEmptyMemory` | `newFromEmptyMemory` | done |
| `newFromWrite` | `newFromWrite` | done |
| `newFromAdd` | `newFromAdd` (`newAddSame`/`newAddDifferent` split) | done |
| `defaultValueInt`, `defaultValueBool`, `defaultDef`, `defValResolve` | `MemValue.asPrim` / `StValue.asInt` / `StValue.asBool` and `defaultDefInt` | done as casts |
| `defaultDefIdentity` | `defaultDefIdentity` (`MemValue.asIdentity`) | done |
| `idCCDef` | `idCCDef` | done |
| `readREmpty`, `readRCons` | `readREmpty`, `readRCons` (`Memory.readR`, `readRId`) | done |

The freshness predicate is not only transcribed but *discharged*:
`Update/Theory.lean`'s `denoteMem_new` proves that a denoted memory term is
`new` at every identity its counter has not reached, so KeY's `\add(new(memory,
freshIdp) ==>)` is a consequence of the denotation here rather than an
assumption about it.

### `structMemoryRules.key` → Theory/CrossDomain.lean

| taclet | Lean | state |
|---|---|---|
| `findOnCopy` | `StValue.findCopyMem` | done |
| `readFromCopyToStorage` | `Memory.readCopySt` | done |
| `readFromCopyToStorageIdentity` | `Memory.readCopyStIdentity` | done |
| — | `Memory.readCopyStOther` | the paper's split form of the frame |

The views are constructors of the two sorts, as KeY declares them
(`Struct copyMem(Struct, Memory, Identity)`,
`Memory copySt(Memory, IdentityPrim, Struct)`), which makes `Struct`,
`StValue` and `Memory` one mutual inductive — `Theory/Terms.lean`.

Three functions gain an arm upstream has no taclet for, each chosen so the rule
that *does* exist subsumes it: `selectSt` on a view pushes the view down and
reads nothing; `storeAt` puts a `storeSt` shadow node over it (replacing it
would make `find_save_frame` false); `delNode` answers `mtSt`, since it is
eager here and cannot walk a view whose members it does not know.

What this does not model is a view nested in a view. `readIn` reads its copied
struct with `findSt`, the reader that stops at a view, which is what keeps every
definition structural and so kernel-reducible; `StValue.find_eq_findSt` states
where the two readers agree. No worked example nests one and no taclet rewrites
under one. The interpreter's `copyStToM`/`copyMem`
(`Semantics.lean`) remain the *update*-level bridge
(`Update/TacletTable.openBridges`); this is the term-level one.

### Where the copy nests

KeY writes a storage-to-memory declaration as
`copySt(addM(memory, freshIdp), freshIdp, find<[Struct]>(storage, sp))` — the
allocation *inside* the copy's first argument. `Rules.allocTerm` writes
`copySt(memory, T, sp)` instead, because `Semantics.copyStToM` allocates the
object it copies into: nesting an `addM` beside it would mint one object too
many and leave `nextId` too high. The term is one symbol shorter than KeY's and
means the same thing.

### The paper's names for these rules

`Theory/Rewrite.lean` is the enumeration of the theory's rules under the names
the paper's `sections/signature.tex` gives them, with `lemmaNames` mapping each
to the theorem(s) above. The theorems keep their upstream names — that is what
makes this file a map — and the join is checked rather than prose.

### `memoryRules.key` → the update vocabulary

`Rules.MemTerm` is the signature, not an enumeration of update shapes:
`{memory := write(memory, mv.fld, se)}`, `{memory := addM(memory)}` and their
nestings are terms, as KeY's `\replacewith` updates are. That is what lets
`memoryFieldDeleteReference`'s `write(addM(memory, freshIdp), mv, fld,
idC(freshIdp, nil))` be written at all — its value is the root the enclosing
allocation minted, which no `Sym` can name and which `Rules.MemVal.fresh` does.

An allocation is the **two parallel elements** KeY writes,
`{mv := freshId(alloc(T)) || memory := alloc(T)}`, not one fused constructor.
The two agree on which root was minted because they name the same subterm:
KeY shares the schema variable `freshIdp`, this shares the term, and
`Update.memEval` returns the root beside the state so both are projections of
one evaluation. Note the root is *not* the pre-state counter —
`Semantics.copyStToM` allocates a struct's members before the struct.

| KeY | here |
|---|---|
| `write(Memory, Identity, Field, MemValue)` | `MemTerm.write (m) (target) (v : MemVal)`; the place `target` is the `(Identity, Field)` pair, named by its kind |
| `addM(Memory, IdentityPrim)` | `MemTerm.addM (m) (ty)` — eager, so the type rides along |
| `copySt(Memory, IdentityPrim, Struct)` | `MemTerm.copySt (m) (ty) (src)`, with the allocation inside (row above) |
| `idC(freshIdp, nil)` as a value | `MemVal.fresh` |
| `idC(freshIdp, nil)` as a binding | `BindRhs.freshId (m)` |
| `defVal` | `MemVal.defVal (ty)` |
| `read<[alpha]>(memory, mv, fld)` | `Sym.read` of a `WrappedExpr.field Kind.memory`, and `BindRhs.mref` where the sort is `Identity` — Lean's sorts are not generic, so KeY's one `memoryFieldRead` is two rules here |

`delete` is the one memory update still given by an evaluator rather than a
term: KeY has five delete taclets whose `MemTerm`s differ by the target's shape
and sort, and Lean now has the five rules too (`memoryRootDeleteFreshRebind`,
`memoryFieldDelete{Primitive,Reference}`, the `memoryIndexDelete{Primitive,
Reference}` twins), and each writes the `MemTerm` its sort selects.  The
reference case's `write(addM(memory, r), mv, fr, idC(r, nil))` names in its
value the root the same update mints; `alloc(·)` and `fresh` are how a literal
element says that — the allocation is a shared subterm, as KeY's `freshIdp` is
a shared schema variable.

### Deviations, collected

Two places where a term carries something KeY's does not, both because KeY is
lazy and the interpreter is eager:

* `Theory.Memory.addM` carries the allocated `RefTy` beside its root. KeY's
  `readOnAddM` resolves a never-written slot of a fresh object to
  `default<[α]>` at the reader's sort; `Semantics.allocDefault` materializes
  the object at allocation, so the term has to know its type to denote. The
  root is KeY's own and is what makes `readOnAddM`/`newFromAdd` the taclets.
* `Theory/Storage.lean` renders `defaultValue<[α]>` as `st mtSt`, the `Struct`
  default, resolved by the caller's cast (`asInt (st mtSt) = 0`) rather than
  by the sort the read asks for.

And one where the *update* is spelled differently: KeY writes `arr.push(se)`
as two saves in one parallel update, the new slot `at(n)` and the new length
`size`, both reading the pre-state. The slot index is the array's old length,
which `SVal.save` reverts on — so the two writes are `Rules.StTerm.pushAt`
and `Rules.StTerm.setSize`, which go through `SVal.saveExt`, where a write one
past the end appends and `size` is a location.  They are written as KeY writes
them, `save(save(storage, arr[arr.length], se), arr.length, arr.length + 1)`,
and only the data tells them from a plain `save`: a *program* can perform
neither, so the soundness bridges keep comparing rules with `SVal.save`.
Same for `pop`.

What that whole-array write now *carries* is upstream's `delAt`: both
`storagePopSave` and `storagePushLengthSave` clear the slot at `n` rather
than dropping it, so a mapping nested in a popped element survives into the
next `push`. `SVal.array` holds those recycled slots in a second field and
`Semantics.pushSlot` is the eager `delAt`; `testDeepPopDoesNotResetMappingMember`
is the obligation that turns on it.
