# KeY taclet → Lean `RuleName` mapping

Tracking checklist for the port. One row per taclet in
`solidityProgramRules.key` (plus `ifThenElseRules.key`), in file order.

solkey's storage copy changed twice on 2026-09-16 — **without moving the
pin**: `c80a54494c` added `copyAt`/`merge` to `structRules.key` and respelled
all eight copy rules' updates `copyAt(storage, p, find<[StValue]>(storage, src))`,
and `8c5c69ca25` folded that back into `save`: the eight copy rules write
`save(…)` again, `copyAt`/`merge` and their taclets are gone, and
`save(st, nil, v)` is a leaf every write leaves, never collapsed, read through
by member sort by the five `selectOnSaveEmpty*`/`saveOnEmptyPrim` taclets so
that a struct written over a location keeps the location's mapping members.
The same fold moved `storageIndexDelete` to `delAt` and gave
`structMemoryRules.key` two `selectOnCopyMem*` reads. The program rows are
unchanged, since `Rules.StorageUpd.copy` is the whole term in one constructor.
`Theory/Storage.lean` does **not** follow the fold: the non-collapsing leaf
differs from the plain write only on a storage-to-storage copy of a
mapping-carrying type, which solc ≥ 0.7 and solkey's own parser
(`ParserUtils.parseAssignmentMaybe`) reject and `TypedStmt.Assign.mk` cannot
build, so the algebra keeps the pre-fold rules (`saveOnEmpty`,
`saveOnStoreCons` with its `isEmpty(flds)` split, `selectOnSaveEmpty`) over
solkey's two sorts, and the storage half of the denotation went with the leaf.
The nine upstream commits between `e67a0d7c48` and
`c80a54494c` are **unreviewed** — `efc047a470`, `4635f8a530`, `c095c5c602`
and `4599dd6d91` add, delete and re-shape taclets in
`solidityProgramRules.key`, and `293b81c31d` re-spells every modality — so the
pin below still reads `e67a0d7c48` and the taclet counts are still that
commit's.

**The example corpus and the rule table are now pinned to different
commits, deliberately.** `scripts/solkey-port.mjs` was re-run against
`c80a54494c` on 2026-09-16, so `Solidity/Examples/Solkey/`,
`Solidity/Examples/Derivations/Solkey/` and `tests/solkey/` are that commit's
278 `TestSuite.sol` functions; this file and `TacletAnnotations.lean` are
still `e67a0d7c48`'s 238 taclets. That is why `lake exe solkeycheck` still
reports its 78 rows and why the 92 taclets added upstream since the pin have
no rows below: re-syncing the table is its own change (`AGENTS.md`), and a
corpus that lags the examples it is meant to check is worth less than one
that leads the table.

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

- `existing` — already modeled in `Rules.lean` (possibly merged with siblings).
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
longer only here: every rule of `Rules.lean` carries a typed
`KeyOrigin` — `taclet t`, `merged [t₁, …]` or `leanOnly` — over the
`KeyTaclet` enumeration of `KeyTaclets.lean`, which is the vendored
`solidityProgramRules.key` transcribed one constructor per taclet. Three
consequences:

- a misspelled taclet name is a type error, not a stale table row;
- `RuleShapes.taclets_partitioned` checks the *coverage* direction — of the 252
  taclets, 246 are claimed by some Lean rule and exactly six are excused with a
  reason (`emptyModality`, `blockEmpty`, the two deleted
  `index*InnerNonSimpleIndexCapture`, `ifSplit`, `ifElseSplit`);
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

- `Solidity/TacletAnnotations.lean` — one `TacletReadAnn` row per
  read-bearing taclet, kept in sync with the live `.key` file by
  `lake exe solkeycheck` (`scripts/check-solkey.sh`); any upstream sort
  drift fails the check.
- `Solidity/SortFaithfulness.lean` — proves each row's sort claims
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
`Solidity/Counterexamples/PreFixSortAnnotations.lean`, and the two
surviving `find<[Struct]>` reads on possibly-primitive sources
(`storageFieldWriteCopySource`, `storagePushValueCopySource`) are
recorded as `SortFaithfulness.openFindings` with counterexamples.

## Naming drift against solkey

**`lake exe solkeycheck` is currently red.** The sort-annotation table has
drifted from upstream by 78 rows against a solkey checkout beside this
repository (`~/projects/solkey`, 315 program taclets): solkey split the
storage-index taclets into array/mapping forms and merged the
`_root`/`_decompose` pairs, changed three read sorts
(`storageFieldWriteCopySource` and `storagePushValueCopySource` now read
`StValue` where the table says `Struct`;
`storageIndexReadArray{BindLocalRoot,StoreRoot}` read `length` twice), and
added the memory-arithmetic family. That re-sync is its own change: it moves
`SortFaithfulness.lean` and `Counterexamples/PreFixSortAnnotations.lean`
together, and it is not implied by porting the rules.

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
`rhs.simple` first, so the `*ValueRhsCapture` rules hoist the RHS before
any path/index capture (`storageEvaluationOrder_rewrite_rhsFirst`).

When the RHS is *simple* and the **path** is complex, the
`*WriteUnfoldLeft*` rules (`storageFieldWriteUnfoldLeftFst`,
`storageIndexWriteUnfoldLeftSndIndex`, …, mirroring KeY's
`*_unfold_leftFst` / `*NonSimpleIndexCapture`) used to capture the path or
index *first*, a genuine order swap against the interpreter: on
`people[i++].age = i` the interpreter writes the old `i`, the residual the
incremented one. **Fixed.** `Rules.freezeRhs` prepends `T rv = e;` to every
target-capture residual on a primitive value operand, so all ten rules
(storage and memory) are now sound on a primitive right-hand side with no
semantic side condition — no `hstable`, no `hev`, no `pureExpr index`, only
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
binding a reference is aliasing rather than a read — the same split
`freezeRhs` makes on `rhs.ty.isPrimitive`.

Two things to know about the upstream state:

* `63c38cfaf6` **deleted** `indexWriteInnerNonSimpleIndexCapture` and
  `indexReadInnerNonSimpleIndexCapture` (rows below) in favour of four new
  `{storage,memory}{Field,Index}WriteIndexedReceiver_unfold_leftFst`
  taclets. Those four **never fire** — two red tests, `storageMatrixNseIndex`
  and `testNestedIndexWriteImpureIndexPrimitiveRhs` — bisected upstream to
  `\varcond(\newTypeOf(sp, nsp))`. The residual they emit is
  character-for-character Lean's `indexWriteResolveBlock`, and Lean's version
  works, so the bug was in taclet instantiation, not in the rule. **Now
  fixed**: a schema variable off the plain `ProgramSVSort.VARIABLE` sort gets
  no name proposal, so `VariableNamer`'s `previousProposals` list carried a
  `null` and `equals` threw; these four are the only taclets minting two fresh
  program variables at *different* data locations, which is what put a `null`
  there. 242 -> 0 failures.
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
| — | `functionCallArgCapture` | done | Lean-only (`unfoldArgument` on solkey's backlog — `docs/net.md` §5.1; the name is solkey's, and the calculus declares no such rule): hoists the leftmost complex call argument into `pv` |
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
| `storageRootWriteValueRhsCapture` | `storageRootWriteValueRhsCapture` | done | nonsimple primitive RHS into a global root; Lean condition excludes `binopUnfoldResult`'s arith-simple cell |
| `fieldWriteValueRhsCapture` | `fieldWriteValueRhsCapture` | done | storage-field lhs instance; memory-lhs instances of KeY's generic `e1.a = nse` are covered by `memoryWriteUnfoldRightSndResult` |
| `indexWriteValueRhsCapture` | `indexWriteValueRhsCapture` | done | storage-index lhs instance; soundness is conditional on non-interference (`valueRhsCaptureAssign_sound`, `hstable`) — see the evaluation-order note below |
| `storageFieldRead_unfold_rightFst` | `storageFieldReadUnfoldRightFst` | existing | |
| `storageFieldReadFind` | `storageFieldReadFind` | existing | |
| `storageFieldWrite_unfold_leftFst` | `storageFieldWriteUnfoldLeftFst` | existing | |
| `storageFieldWriteRootRhs_unfold_leftFst` | `storageFieldWriteUnfoldLeftFst` | existing | merged: Lean's `isSimple rhs` admits a global root, which KeY's `SimpleExpression` excludes — the RootRhs twin is that slice |
| `storageFieldReadBindLocalRoot` | `storageFieldReadBindLocalRoot` | existing | |
| `storageFieldReadStoreRoot` | `storageFieldReadStoreRoot` | existing | |
| `storageFieldRead_unfold_rightSndResult` | `storageFieldReadUnfoldRightSndResult` | existing | was Lean-only; solkey adopted the taclet (result capture no longer folded into the read taclets) |

## Storage index (mapping)

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `storageIndexWriteMappingSave_root` | `storageIndexWriteMappingSave` | existing | merged root/decompose |
| `storageIndexWriteMappingSave_decompose` | `storageIndexWriteMappingSave` | existing | merged |
| `storageIndexReadMappingFind_root` | `storageIndexReadMappingFind` | existing | merged root/decompose |
| `storageIndexReadMappingFind_decompose` | `storageIndexReadMappingFind` | existing | merged |
| `storageIndexReadMappingBindLocalRoot` | `storageIndexReadMappingBindLocalRoot` | existing | |
| `storageIndexWriteMappingCopySource` | `storageIndexWriteMappingCopySource` | existing | |
| `storageIndexWriteStorageRefRhsCapture` | `storageIndexReadUnfoldRightSndResult` / `storageFieldReadUnfoldRightSndResult` | existing | merged (the KeY taclet was renamed from `storageIndexWriteMapRefRhsCapture`); dispatch tests `rhs.simple` first, which *is* the RHS-before-index order — `RuleValidation.storageIndexWriteStorageRefRhsCapture_corresp` |
| `storageIndexReadMappingStoreRoot` | `storageIndexReadMappingStoreRoot` | existing | was Lean-only; solkey adopted the taclet |

## Storage index (array)

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `storageIndexWriteArraySave_root` | `storageIndexWriteArraySaveBox` / `storageIndexWriteArraySaveDiamond` | existing | Lean splits by modality (bounds/revert), KeY by root/decompose |
| `storageIndexWriteArraySave_decompose` | `storageIndexWriteArraySaveBox` / `storageIndexWriteArraySaveDiamond` | existing | merged |
| `storageIndexReadArrayFind_root` | `storageIndexReadArrayFindBox` / `storageIndexReadArrayFindDiamond` | existing | merged |
| `storageIndexReadArrayFind_decompose` | `storageIndexReadArrayFindBox` / `storageIndexReadArrayFindDiamond` | existing | merged |
| `storageIndexReadArrayBindLocalRoot` | `storageIndexReadArrayBindLocalRootBox` / `…Diamond` | existing | |
| `storageIndexReadArrayStoreRoot` | `storageIndexReadArrayStoreRootBox` / `…Diamond` | existing | |
| `storageIndexWriteArrayCopySource` | `storageIndexWriteArrayCopySourceBox` / `…Diamond` | existing | |
| `storageIndexWriteNonSimpleRhsCapture` | `indexWriteValueRhsCapture` (+ `binopUnfoldResult` for arith-simple) | existing | the KeY taclet was replaced by the `*ValueRhsCapture` trio; see the evaluation-order note below |
| `storageIndexWriteNonSimpleIndexCapture` | `storageIndexWriteUnfoldLeftSndIndex` | existing | condition and residual match KeY (simple-RHS precondition included); order vs RHS capture locked in by `RuleValidation.storageEvaluationOrder_rewrite_rhsFirst` (`a[++i] = ++i`) |
| `storageIndexWriteRootRhsNonSimpleIndexCapture` | `storageIndexWriteUnfoldLeftSndIndex` | existing | merged: the Lean condition does not distinguish stack from storage simple RHSs — `RuleValidation.storageIndexWriteRootRhsNonSimpleIndexCapture_corresp` |
| ~~`indexWriteInnerNonSimpleIndexCapture`~~ | `storageIndexWriteUnfoldLeftFst` / `memoryIndexWriteUnfoldLeftFst` | **deleted upstream** (`63c38cfaf6`) | Lean captures the whole inner path, which is **strictly more general**, not "coarser but equivalent": the KeY `\find` was hard-coded to `e1[nse][e2]`, so `m[i++][j][k] = v` matched nothing. It also had no RHS freeze, so it wrote the incremented `i` on `matrix[i++][0] = i`. Never modelled separately in Lean; recorded as a rejected design |
| ~~`indexReadInnerNonSimpleIndexCapture`~~ | `storageIndexReadUnfoldRightFst` / `memoryIndexReadUnfoldRightFst` | **deleted upstream** (`63c38cfaf6`) | same: depth-2 shape-keyed, replaced by the (currently non-firing) receiver capture |
| `storageIndexWrite_unfold_leftFst` | `storageIndexWriteUnfoldLeftFst` | existing | was Lean-only; solkey adopted the taclet |
| `storageIndexWriteRootRhs_unfold_leftFst` | `storageIndexWriteUnfoldLeftFst` | existing | merged: Lean's `isSimple rhs` admits a global root, which KeY's `SimpleExpression` excludes — the RootRhs twin is that slice |
| `storageIndexRead_unfold_rightSndIndex` | `storageIndexReadUnfoldRightSndIndex` | existing | was Lean-only; solkey adopted the taclet |
| `storageIndexRead_unfold_rightSndResult` | `storageIndexReadUnfoldRightSndResult` | existing | was Lean-only; solkey adopted the taclet |
| — | `storageIndexReadUnfoldRightFst` | existing | Lean-only granularity (KeY covers the shape via `storageFieldRead_unfold_rightFst` + `indexReadInnerNonSimpleIndexCapture`) |

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
| `storageRootDelete` | `storageDeleteSimpleTarget` | existing | merged root/field/index simple targets |
| `storageFieldDelete` | `storageDeleteSimpleTarget` | existing | merged |
| `storageIndexDelete` | `storageDeleteSimpleTarget` | existing | merged |
| `storageFieldDelete_unfold_leftFst` | `storageDeleteComplexTarget` | existing | merged |
| `storageIndexDelete_unfold_leftFst` | `storageDeleteComplexTarget` | existing | merged |

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
| `memoryRootDeleteFreshRebind` | `memoryDeleteSimpleTarget` | existing | the interpreter rebinds a fresh default object on root delete; write-after-delete exercised in `Examples/Taclets/MemoryOps.lean` |
| `memoryRootRebind` | `memoryRootAlias` | existing | `memoryRootAlias` is now restricted to memory RHSs, making it exactly KeY `memoryRootRebind`; the storage-RHS case it silently absorbed is `memoryStorageCopy` |
| `memoryStorageCopy` | `memoryStorageCopy` | done | `m = sp;` deep copy (fresh identity + `copySt` in the interpreter); previously absorbed by `memoryRootAlias` |
| `memoryStorageCopyUnfold` | `memoryStorageCopyUnfold` | done | complex storage path captured into the storage alias first; deep paths (`m = alice.account.token`) already step via `storageFieldReadUnfoldRightFst` / `storageIndexReadUnfoldRightFst` |
| `memoryLocalDeclInitDrop` | `memoryLocalDeclInitDrop` | existing | solkey deleted the whole per-RHS decl-init family (`memoryLocalDeclInitRootAlias`, `…StorageCopy`, `…StorageCopyUnfold`, `…FieldReadValue/Memory/_unfold_rightFst`, `…IndexReadValue/Memory`) and adopted the Lean approach: one generic decl-with-init split, then the assignment rules apply |
| — | `storageToMemoryDeclCopyRoot`, `storageToMemoryDeclCopyField`, `storageToMemoryDeclUnfoldRightFst` | existing | now Lean-only decl-specific granularity; their former KeY counterparts (`memoryLocalDeclInitStorageCopy`, `…Unfold`) were removed with the family above |

## Memory field/index write & read

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `memoryFieldWrite` | `memoryFieldWriteStore` | existing | |
| `memoryFieldRead` | `memoryFieldReadHeap` / `memoryFieldReadAliasRoot` | existing | solkey `0f9b99ad55` merged the former `memoryFieldReadValue` (`Field[primitive]`) and `memoryFieldReadMemory` (`Field[reference]`, `read<[Identity]>`) into one rule over a bare `Field`, its result sort resolved by `\hasMemoryFieldSort(a, \sort(alpha))` — the merge Lean had made already |
| `memoryFieldRead_unfold_rightFst` | `memoryFieldReadUnfoldRightFst` | existing | |
| `memoryFieldWriteCaptureSrc` | `memoryFieldWriteCopy` | existing | |
| `memoryFieldWrite_unfold_leftFst` | `memoryFieldWriteUnfoldLeftFst` | existing | |
| `memoryIndexWriteArray` | `memoryIndexWriteStoreBox` / `memoryIndexWriteStoreDiamond` | existing | Lean splits by modality (bounds) |
| `memoryIndexReadArrayValue` | `memoryIndexReadHeapBox` / `…Diamond` | existing | |
| `memoryIndexReadArrayMemory` | `memoryIndexReadHeapBox` / `memoryIndexReadAliasRootBox` / `…Diamond` | existing | |
| `memoryIndexRead_unfold_rightFst` | `memoryIndexReadUnfoldRightFst` | existing | |
| `memoryIndexWrite_unfold_leftFst` | `memoryIndexWriteUnfoldLeftFst` | existing | |
| `memoryIndexWriteMemRefRhsCapture` | `memoryFieldRead*`/`memoryIndexRead*` unfolds + `memoryWriteUnfoldRightSndResult` | existing | merged under the memory-complex-lhs dispatch branch |
| `memoryIndexWriteNonSimpleIndexCapture` | `memoryIndexWriteUnfoldLeftSndIndex` | existing | condition/residual match KeY (`RuleValidation.memoryIndexWriteUnfoldLeftSndIndex_valid`); order vs RHS capture as in the storage case |
| `memoryIndexDeleteNonSimpleIndexCapture` | `memoryDeleteComplexTarget` | existing | merged — `memoryDeleteComplexTargetBlock` captures the index exactly as KeY (`RuleValidation.memoryDeleteComplexTarget_index_valid`) |
| `storageIndexDeleteNonSimpleIndexCapture` | `storageDeleteComplexTarget` | existing | merged — `RuleValidation.storageDeleteComplexTarget_index_valid` |
| `memoryFieldRead_unfold_rightSndResult` | `memoryFieldReadUnfoldRightSndResult` | existing | was Lean-only; solkey adopted the taclet |
| `memoryIndexRead_unfold_rightSndIndex` | `memoryIndexReadUnfoldRightSndIndex` | existing | was Lean-only; solkey adopted the taclet |
| `memoryIndexRead_unfold_rightSndResult` | `memoryIndexReadUnfoldRightSndResult` | existing | was Lean-only; solkey adopted the taclet |
| — | `memoryWriteUnfoldRightSndResult` | existing | Lean-only granularity |

## Memory delete

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `memoryFieldDeletePrimitive` | `memoryDeleteSimpleTarget` | existing | merged |
| `memoryFieldDeleteReference` | `memoryDeleteSimpleTarget` | existing | merged |
| `memoryIndexDeletePrimitive` | `memoryDeleteSimpleTarget` | existing | merged |
| `memoryIndexDeleteReference` | `memoryDeleteSimpleTarget` | existing | merged |
| `memoryFieldDelete_unfold_leftFst` | `memoryDeleteComplexTarget` | existing | merged |
| `memoryIndexDelete_unfold_leftFst` | `memoryDeleteComplexTarget` | existing | merged |

## Memory → storage copies

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `memoryToStorageStoreRoot` | `memoryToStorageStoreRoot` | existing | |
| `memoryToStorageFieldCopyRoot` | `memoryToStorageFieldCopyRoot` | existing | deep-copy of a memory root into a storage slot exercised in `Examples/Taclets/MemoryOps.lean` |
| `memoryToStorageFieldCopyField` | `memoryToStorageFieldCopyRoot` | existing | granularity differs (Lean: SaveField + unfolds); `RuleValidation.memoryToStorageUnfold*` entries |
| `memoryToStorageIndexMappingCopyRoot` | `memoryToStorageIndexMappingCopyRoot` | existing | indexed deep-copy, mapping receiver |
| `memoryToStorageIndexArrayCopyRoot` | `memoryToStorageIndexArrayCopyRootBox` / `…Diamond` | existing | indexed deep-copy, array receiver; Lean splits by modality (bounds/revert) |
| — | `memoryToStorageUnfoldRightFstSource`, `memoryToStorageUnfoldLeftFstTarget`, `memoryToStorageUnfoldLeftSndTargetIndex` | existing | Lean-only unfold steps |

## Value declarations (phase 2)

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `localValueDeclInitDrop` | `localValueDeclInitDrop` | done | same name both sides (Lean was `valueDeclInitSplit` until the renaming that aligned both sides) |
| `valueDeclSkip` | `valueDeclSkip` | done | |
| `localValueAssign` | `localValueAssign` | done | terminal `vp = se;` for simple RHS |

## Binary arithmetic operators (phase 2)

Family pattern per op `X ∈ {addition, subtraction, multiplication, power,
division, modulo}`: `X_unfold_left`, `X_unfold_right`, `X_unfold_result`,
`XAssignment`. Lean names: `XUnfoldLeft`, `XUnfoldRight`, `XUnfoldResult`,
`XAssignment`.

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `addition_unfold_left/right/result`, `additionAssignment` | `additionUnfoldLeft/Right/Result`, `additionAssignment` | done | |
| `subtraction_*`, `subtractionAssignment` | `subtractionUnfoldLeft/Right/Result`, `subtractionAssignment` | done | |
| `multiplication_*`, `multiplicationAssignment` | `multiplicationUnfoldLeft/Right/Result`, `multiplicationAssignment` | done | |
| `power_*`, `powerAssignment` | `powerUnfoldLeft/Right/Result`, `powerAssignment` | done | |
| `division_*`, `divisionAssignment` | `divisionUnfoldLeft/Right/Result`, `divisionAssignment` | done | zero-divisor guard per plan D2 |
| `modulo_*`, `moduloAssignment` | `moduloUnfoldLeft/Right/Result`, `moduloAssignment` | done | zero-divisor guard per plan D2 |

## Comparisons, boolean operators, unary (phase 2)

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `boolEqualityCaptureLhs`, `boolEqualityAssignment` | `boolEqualityCaptureLhs`, `boolEqualityAssignment` | done | |
| `boolEqualityCaptureRhs` | — | **todo** | added by solkey `0f9b99ad55` (`v = se == nse;` → `T pv = nse; v = se == pv;`); Lean reaches the same normal form through the generic binop unfolds, and has no rule of this name |
| `boolInequalityCaptureLhs/CaptureRhs`, `boolInequalityAssignment` | same camelCase | done | |
| `lessThanCaptureLhs/CaptureRhs`, `lessThanAssignment` | same | done | |
| `greaterThanCaptureLhs/CaptureRhs`, `greaterThanAssignment` | same | done | |
| `lessEqualCaptureLhs/CaptureRhs`, `lessEqualAssignment` | same | done | |
| `greaterEqualCaptureLhs/CaptureRhs`, `greaterEqualAssignment` | same | done | |
| `logicalAndCaptureLhs`, `logicalAndAssignment` | same (`binopUnfoldLeft .and` / `binopAssignment .and`) | done | |
| `logicalOrCaptureLhs`, `logicalOrAssignment` | same | done | |
| `logicalAndShortCircuitRhs` | `logicalAndShortCircuitRhs` | done | `v = se && nse;` → `if (se) { v = nse } else { v = false }` — the statement-level image of KeY's ternary residual; the interpreter itself short-circuits, so the rewrite is exact (`RuleValidation.logicalAndShortCircuitRhs_shortCircuits_valid` shows the reverting RHS is skipped) |
| `logicalOrShortCircuitRhs` | `logicalOrShortCircuitRhs` | done | dual (`v = se ? true : nse`) |
| `logicalNotCapture`, `logicalNotAssignment` | same | done | |
| `unaryMinusCapture`, `unaryMinusAssignment` | same | done | |

## Storage compound assignments (phase 3)

Pattern per op `Op ∈ {Add, Sub, Mul, Div, Mod}`:

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `storageRootOpAssign` | `storageRootCompoundAssign op` | done | Div/Mod: zero-divisor guard |
| `storageFieldOpAssign` | `storageFieldCompoundAssign op` | done | |
| `storageIndexArrayOpAssign`, `storageIndexMappingOpAssign` | `storageIndexCompoundAssign op` | done | Lean does not split the compound-assign rule by receiver kind |
| `storageFieldOpAssign_unfold_leftFst` | `storageFieldCompoundAssignUnfoldLeftFst op` | done | |
| `storageIndexOpAssign_unfold_leftFst` | `storageIndexCompoundAssignUnfoldLeftFst op` | done | |
| `memoryField{Add,Sub,Mul,Div,Mod}Assign`, `memoryIndexArray*Assign` | `memoryFieldCompoundAssign op` / `memoryIndexCompoundAssign op` | done | the calculus spells these `memoryFieldOpAssign` / `memoryFieldDivAssign` / `memoryIndexArrayOpAssign`. Landed upstream in solkey `444f029579`, after the revision the sort-annotation table was written against, which is why this family was the one gap the rule audit found. No root form (a memory root binds an identity, not a value cell) and no mapping form (memory has no mappings) |
| `memoryField*Assign_unfold_leftFst`, `memoryIndex*Assign_unfold_leftFst` | `memoryFieldCompoundAssignUnfoldLeftFst op` / `memoryIndexCompoundAssignUnfoldLeftFst op` | done | complex memory path, with the same `rv` freeze as the storage twins; `RuleValidation.memory{Field,Index}CompoundAssignUnfoldLeftFst_*_valid` |
| `localOpAssign` (`localAddAssign`, …) | `localCompoundAssign op` | done | terminal `lv ⊕= se;`; the Div/Mod zero-divisor revert lives in the interpreter's `applyBinOp`; update theorem `localCompoundAssign_update` (Wp/Terminal/UpdateCompound.lean) |
| `{add,sub,mul,div,mod}AssignValueRhsCapture` | `compoundAssignValueRhsCapture op` | done | location-neutral capture of a nonsimple compound-assign RHS into `pv`; soundness `compoundAssignValueRhsCapture_sound` is conditional on the target's old value surviving the RHS's effects (`hstableOld`) — the compound image of the evaluation-order note |

## Increment / decrement (phase 3)

Pattern per `V ∈ {Preincrement, Postincrement, Predecrement, Postdecrement}`:

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `storageRootV` / `storageRootVAssignment` | `storageRootIncDec v` / `storageRootIncDecAssignment v` | done | the calculus calls the family `storageRootIncrement` |
| `storageFieldV` / `storageFieldVAssignment` | `storageFieldIncDec v` / `storageFieldIncDecAssignment v` | done | |
| `storageIndexV` / `storageIndexVAssignment` | `storageIndexIncDec v` / `storageIndexIncDecAssignment v` | done | |
| `storageFieldV_unfold_leftFst` | `storageFieldIncDecUnfoldLeftFst v` | done | |
| `storageIndexV_unfold_leftFst` | `storageIndexIncDecUnfoldLeftFst v` | done | |
| `memoryField{Pre,Post}{in,de}crement[Assignment]`, `memoryIndexArray*` | `memoryFieldIncDec v` / `memoryIndexIncDec v` (+ `…Assignment`, `…UnfoldLeftFst`) | done | the calculus spells this `memoryFieldIncrement`; same upstream commit as the compound-assign family above |
| `localDeclV` (`localDeclPreincrement`, ...) | same | done | `T vp = ++lv;` |
| `localAssignV` (`localAssignPreincrement`, ...) | same | done | `vp = ++lv;` |
| `localV` (`localPreincrement`, ...) | `localIncDec op` | done | bare statement `++lv;` on a stack local; update theorem `localIncDec_update` (Wp/Terminal/UpdateCompound.lean) (`--` cannot be a `sol!` token — decrement instances are exercised via `incDecExpr`) |

## Assert, if-then-else (phase 4)

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `assertConditionCapture` | `assertConditionCapture` | done | |
| `assertSimple` | `assertSimple` | done | terminal in the rewrite layer; the Holds/Violated split is the revert semantics in `Semantics.lean` |
| `requireConditionCapture` | `requireConditionCapture` | done | clone of the assert capture over `Stmt.requireStmt` |
| `requireSimple` | `requireSimple` | done | terminal; the interpreter reverts on false — box `c → φ`, diamond `c ∧ φ` fall out of `check` (solkey `docs/require-assert.md`); the KeY assert/require difference (⊥ vs revert) lives entirely in that layer |
| `ifUnfold` / `ifElseUnfold` | `ifElseUnfold` | done | solkey's statement-level nonsimple-condition capture (`solidityProgramRules.key`); Lean merges the if/if-else pair since `Stmt.ite` always carries both branches (else = `[]`) |
| `ifSplit` / `ifElseSplit` | `SolidityJudgment.ite_split` | lemma | solkey's sequent-level two-goal split on a simple condition (`\add(se = TRUE/FALSE ==>)`); a `BlockStep` cannot produce two goals, so the rewrite layer is intentionally stuck there and the split is the lemma (`JudgmentSplit.lean`; `ite_split_pure` is the exact KeY shape for pure conditions) |
| `ternaryCaptureCond` | `ternaryCaptureCond` | done | `WrappedExpr.mkTernary` + `c ? t : e` in `sol!`; the interpreter short-circuits like `&&`/`||`; the cond excludes the memory-complex-lhs dispatch branch (`memoryWriteUnfoldRightSndResult` claims the whole rhs there); soundness has the trio's `hstable` non-interference condition |
| `ternaryToIf` | `ternaryToIf` | done | `v = se ? e1 : e2;` ⇝ `if (se) v = e1; else v = e2;` — both sides evaluate the same branch in the same state (`ternaryToIf_sound` is an equality up to defeq) |
| `ternaryToIfStorage` | `ternaryToIfStorage` | done | twin for a storage-path target; soundness pinned to the primitive-write dispatch (branch types agree) |
| `ifthenelse_true` (`ifThenElseRules.key`, term-level `\if`) | `ifElseTrue` | done | Lean lifts it to a program rule firing on the literal condition `true` (plan D3b); solkey has no program-rule counterpart — a candidate taclet for solkey (`docs/solkey-feedback.md`) |
| `ifthenelse_false` | `ifElseFalse` | done | same, literal `false` |
| `ifthenelse_negated` | `ifElseNegated` | done | Lean swaps branches for `!se` conditions at the program level; term-level only in KeY |
| `ifthenelse_same_branches` | `SolidityJudgment.ite_same_branches` | lemma | corollary of `ite_split`; a `RuleName` port would overlap `ifElseTrue`/`ifElseFalse` on literal conditions and need `DecidableEq Block` in a guard. |
| `ifthenelse_concrete`–`_concrete4` | — | arch | term-level `\if(φ)\then(true)\else(false)` simplification; `WrappedExpr` has no conditional-expression constructor, and on the meta level Lean's own `if`/`Bool.cond` simp set covers it. |
| `ifExthenelse1_*` (all) | — | arch | commented-out dead code in the KeY source (`\ifEx` deprecated since 2014). |
| `ifthenelse_*_for` (all `_for` variants) | — | arch | formula-sort duplicates of the term-level rules (same `\displayname`, schema vars of sort `\formula`), an artifact of KeY's term/formula distinction; Lean's `Prop`/`Bool` need no such split. (The earlier "loops are outside the fragment" note was wrong — these are not loop rules.) |

## Payments (phase 5)

| KeY taclet | Lean rule | Status | Notes |
| --- | --- | --- | --- |
| `transfer_unfold_leftFstReceiver` | `transferUnfoldLeftFstReceiver` | done | |
| `transfer_unfold_rightSndArgument` | `transferUnfoldRightSndArgument` | done | |
| `transferNoCallbackBox`, `transferNoCallbackDiamond` | `transferNoCallback` | done | solkey `333cc7b353` split the rule by modality; both now debit `selfBalance` (`084de89677`), and the diamond rule owes `0 <= se & se <= selfBalance` as a "sufficient funds" goal — the interpreter's revert condition (`docs/solc-alignment.md`), so the transfer delta is resolved |
| `transferWithCallbackBox`, `transferWithCallbackDiamond` | `transferWithCallback` | done | same split and balance debit; the callback havoc also quantifies over `selfBalance`. KeY's `transferSemantics` *choice*: lives in the alternative rule list `ruleNamesWithCallback` (never coexists with `transferNoCallback` — `candidateWithCallback` / `applicable_eq_candidateWithCallback`; coverage unchanged by `ruleApplies_withCallback_iff`). The rule is terminal; its meaning is the relational layer `CallbackSemantics.ExecC`/`HoldsC`: `holdsC_transfer_split` is the KeY branch split (invariant-on-exit ∧ resume-under-havoc, both storage and net havocked per solkey net.md), `holds_of_holdsC` shows it soundly over-approximates the executable semantics. Examples incl. the negative (trivial-invariant) case: `Examples/Taclets/CallbackOps.lean`. |

## Terminal rules as updates

Every terminal rule (empty residual) has a state update in
`Wp/TerminalUpdate.lean` (`terminalUpdate?`, written in state vocabulary,
not through the interpreter) and a theorem `<rule>_update` in
`Wp/Terminal/Update*.lean` proving `execStmt s stmt = terminalUpdate r
stmt s` under the rule's guard; `Wp/TerminalRules.lean` dispatches them
(`terminalUpdate_sound`, `terminal_step_sound`). The KeY `\replacewith`
update of a terminal taclet is therefore matched by a Lean function, and
"taclet ⇒ update" is a theorem per rule.

## Update algebra (`updateRules.key`)

The Lean model has no update syntax — state change is function
application — so KeY's update calculus splits into (a) point-of-
application laws with real semantic content, ported as `State` lemmas in
`SemanticsProperties.lean`, and (b) the update-monoid normal-form
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
`delAt`/`delNode` are eager over the same walk. There is no pre-state leaf
and no denotation for storage: the `*CopySource` / `…StoreRoot` program rows
below are untouched because the copy they state is mapping-free by
construction (`TypedStmt.Assign.mk`, `stmtTypingOk`), and
`Rules.StorageUpd.push` still merges KeY's three push taclets.

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
and sort, Lean has one rule, and the rule grammar builds a literal list of
elements — so a rule cannot state an update whose shape depends on its target.

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
which `SVal.save` reverts on; `Rules.StorageUpd.push` and `Update.pushStorage`
write the extended array at the array's own path instead. Same for `pop`.

What that whole-array write now *carries* is upstream's `delAt`: both
`storagePopSave` and `storagePushLengthSave` clear the slot at `n` rather
than dropping it, so a mapping nested in a popped element survives into the
next `push`. `SVal.array` holds those recycled slots in a second field and
`Semantics.pushSlot` is the eager `delAt`; `testDeepPopDoesNotResetMappingMember`
is the obligation that turns on it.
