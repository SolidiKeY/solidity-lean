# KeY taclet → Lean `Taclet` mapping

The name-by-name map from solkey's `solidityProgramRules.key` (plus
`ifThenElseRules.key`) to `Solidity.Taclet` (`Calculus/Rules.lean`), then the
symbol table for updates and the data-structure theories. **Pinned to solkey
`f2eb3d98eb`**: 311 program taclets, enumerated in `Calculus/KeyTaclets.lean`.

These tables are the prose companion of `Calculus/RuleShapes.lean`, which
checks the correspondence: `tacletOrigins` gives every constructor a typed
`KeyOrigin` (`.taclet t` or `.merged [t₁, …]`; a missing or misspelled row
fails the build), `unclaimedTaclets` excuses the rest with a reason,
`callbackOrigins` does the same for `CallbackTaclet`, and `taclets_partitioned`
says every taclet is claimed or excused, never both
(`claimedTaclets_count = 300`, `unclaimedTaclets_count = 11`). A rule that
transcribes no taclet is a `LeanTaclet` (`leanTaclets`); there is one,
`functionCallArgCapture`. A taclet may be claimed by two constructors (the
member reads by their `.length` rules, since KeY reads `sp.length` as the
member `length`; `memoryFieldWrite`/`memoryIndexWriteArray` by the value and
reference writes). What stays prose here is what a `KeyOrigin` cannot say:
why a merge is a merge, and the symbol maps of the second half.

Legend (a row with several taclets or constructors lists them in one cell):

- **same** — a constructor of the taclet's own name.
- **find same** — the same name and `\find`, but the replacement differs; the
  note says how.
- **merged** — one constructor covers this taclet with others: an operator
  family, a value/reference source split, a mapping/array receiver split
  (increments and compound assignments only), or two captures one step covers.
- **unclaimed** — no constructor; the note is the reason from
  `unclaimedTaclets`.
- **Lean only** — a `LeanTaclet`: no taclet behind it.

## Modality / sequent rules

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `functionBodyExpand` | `functionBodyExpand` | same | a call carries its callee inlined (`Stmt.call`, KeY's `FunctionBodyStatement`); with every argument simple the premise is KeY's `expand_function_body`. The parameters are the elaborator's fresh names, so KeY's fresh renaming is done once, at elaboration |
| — | `LeanTaclet.functionCallArgCapture` | Lean only | `unfoldArgument`, which solkey's `docs/net.md` lists as missing: the leftmost non-simple argument is captured into a fresh `se` first, so that `Stmt.step` has one rule per call |
| `emptyModality`, `blockEmpty` | — | unclaimed | a program is a list of statements with branch bodies inlined: no nested block to erase, no `{} ; rest` to find; reaching `⟨[ ]⟩` is the analogue |
| `revertDiamond` | `revertDiamond` | same | closes to `false`: a reverted run satisfies no diamond formula |
| `revertBox` | `revertBox` | same | closes to `true`. These two are the **only** rules that tell the modalities apart: the modality is a parameter of `Taclet`, so every other rule fires under either |

## Storage root/field write & read

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `storageRootWriteStore`, `storageRootWriteCopySource`, `storageRootReadSelect` | same names | same | |
| `storageFieldWriteSave`, `storageFieldWriteCopySource` | same names | same | |
| `storageFieldReadBindLocalRoot`, `storageFieldReadStoreRoot` | same names | same | |
| `storageFieldReadFind` | `storageFieldReadFind`, `storageLengthRead` | same | the second at the member `length`: `v = sp.length ⇝ { v := sp.length }`, the term `Term.len` (KeY's `find(storage, sp.size)`) |
| `storageFieldRead_unfold_rightFst` | `storageFieldRead_unfold_rightFst`, `storageLengthRead_unfold_rightFst` | same | the second: `v = nsp.length ⇝ T storage sp = nsp; v = sp.length` (a length is a `Val`, not a typed-syntax member) |
| `storageFieldRead_unfold_rightSndResult` | `storageFieldRead_unfold_rightSndResult` | same | also claims `storageFieldWriteCaptureSrc` |
| `storageFieldWriteCaptureSrc` | `storageFieldRead_unfold_rightSndResult` | merged | the chain also captures a complex storage source into a fresh local |
| `storageFieldWrite_unfold_leftFst` | `storageFieldWrite_unfold_leftFst` | same | `nsp.fld = e ⇝ T se = e; T storage sp = nsp; sp.fld = se`: the value is frozen into `se` before the receiver is captured |
| `storageFieldWriteStorageRef_unfold_leftFst` | `storageFieldWriteStorageRef_unfold_leftFst` | same | the reference-source twin: no freeze (a reference is aliased, not read) |

## Storage index (mapping and array)

Each array rule takes an implicit `ak : ArrTy R E` (`IndexTy.arr ak`), `dyn`
for `T[]` and `fixed` for `T[n]`, so one constructor covers both kinds as
solkey's `Path[…,array]` sort does; the memory index rules take the same
argument.

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `storageIndexWriteMappingSave`, `storageIndexReadMappingFind`, `storageIndexReadMappingBindLocalRoot`, `storageIndexWriteMappingCopySource`, `storageIndexReadMappingStoreRoot` | same names | same | |
| `storageIndexWriteArraySave` | same | same | one rule for both modalities; an out-of-range write reverts in the path's own bounds check (`PTerm.at`, `State.checkIndex`), not as a separate goal |
| `storageIndexReadArrayFind`, `storageIndexReadArrayStoreRoot`, `storageIndexWriteArrayCopySource` | same names | same | |
| `storageIndexReadArrayBindLocalRoot` | same | same | `lsv = darr[ie]`, a non-mapping element (`nonMappingElement`, `SPath.elemMapping darr = false`) |
| `storageIndexReadArrayBindLocalRootMappingElement` | same | same | `lsv = marr[ie]`: KeY's `atMap(ie)` is the same `Seg.at` here, a mapping being what `delete` leaves alone |
| `storageIndexWriteStorageRefRhsCapture` | `storageIndexRead_unfold_rightSndResult` | merged | a reference source at an index is hoisted into `se`, the storage twin of the field case |
| `storageIndexRead_unfold_rightSndResult` | same | same | also claims the row above |
| `storageIndexRead_unfold_rightSndIndex`, `storageIndexRead_unfold_rightFst` | same names | same | |
| `storageIndexWriteCaptureAllNonSimpleIndex` | same | same | `sp[nse] = e ⇝ T se = e; T storage sp' = sp; T ie = nse; sp'[ie] = se`: the simple receiver is bound again, as KeY does |
| `storageIndexWriteStorageRefCaptureAllNonSimpleIndex` | same | find same | `… sp'[ie] = path`: KeY also binds the source to an alias `rv`; a copy source is written as it stands (`kernel-port.md`, Decisions) |
| `storageIndexWriteCaptureAllComplexRecv` | same | same | `nsp[e1] = e2 ⇝ T se = e2; T storage sp = nsp; T ie = e1; sp[ie] = se` |
| `storageIndexWriteStorageRefCaptureAllComplexRecv` | same | find same | the source is not captured, as above |

## Storage push / pop

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `storagePushValue_unfold_leftFstReceiver`, `storagePush_unfold_leftFstReceiver`, `storagePop_unfold_leftFstReceiver`, `storageLocalRootPush_unfold_leftFstReceiver`, `storagePushValue_unfold_rightSndArgument`, `storagePushValueSave`, `storagePushValueCopySource` | same names | same | |
| `storagePushLengthSave` | same | same | `parr.push()`: a primitive element, the slot cleared (`STerm.pushSlot`) |
| `storagePushLengthSaveReferenceElement` | same | same | `rarr.push()`: a struct or array element, the recycled slot taken as it is (`STerm.extend`) |
| `storageLocalRootPushBind`, `storageLocalRootPushBindMappingElement` | same names | same | `lsv = darr.push()` / `marr.push()` |
| `storagePopSave` | same | same | `darr.pop()`, both modalities: the element cleared into the recycled slots (`STerm.pop`) |
| `storagePopSaveMappingElement` | same | same | `marr.pop()`: the element kept (`STerm.shrink`) |

A push is one term, not KeY's two parallel `save`s (see "Deviations").

## Storage local declarations

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `storageLocalDeclInitDrop`, `storageLocalRootRebind`, `storageLocalDeclSkip` | same names | same | |

## Storage delete

solkey leaves `delete` and `pop()` open on a path through a fixed-size array
element (`noFixedArrayElement`, on `storageRootDelete`, `storageFieldDelete`,
`storageIndexDelete`, `storageIndexArrayDelete`, `storagePopSave`). The Lean
constructors have no such restriction and are sound there: `SVal.defaultOf`
keeps a fixed-size array's `n` elements (reset) where it empties a dynamic
one, and `push`/`pop` are written at `.array` only.

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `storageRootDelete` | same | same | `delete(gsp) ⇝ { storage := delAt(storage, gsp) }` |
| `storageFieldDelete`, `storageFieldDelete_unfold_leftFst`, `storageIndexDelete_unfold_leftFst`, `storageIndexDeleteNonSimpleIndexCapture` | same names | same | |
| `storageIndexDelete` | same | same | a mapping entry |
| `storageIndexArrayDelete` | same | same | KeY's `inBounds` split is the path's own bounds check, which reverts |

## Memory allocation, aliasing, declarations

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `memoryReferenceDeclFreshAlloc` | same | same | `T memory mv; ⇝ { mv := freshId(addM(memory)) ‖ memory := addM(memory) }`, the pair KeY writes: `ITerm.alloc` and `MTerm.addM` agree on the minted root because both read the same pre-state |
| `memoryArrayFreshAlloc` | same | same | `mv = new T(se); ⇝ { mv := freshId(copySt(memory, newArr(se))) ‖ memory := copySt(memory, newArr(se)) }`: Lean copies in `newArrVal R n` (defaults, each struct element its own object, as solc allocates) where KeY writes `size`; a non-simple size is captured by the elaborator |
| `newArrayCapture` | same | same | `tgt = new T(se) ⇝ T memory mv = new T(se); tgt = mv`, `tgt` a storage or memory location (`NewLhs`) |
| `memoryRootDeleteFreshRebind` | same | same | `delete mv; ⇝` the allocation pair (see "Memory delete") |
| `memoryRootRebind` | `memoryRootAlias` | merged | `mv₁ = mv₂; ⇝ { mv₁ := mv₂ }`; a storage right-hand side is `memoryStorageCopy` |
| `memoryStorageCopy` | same | same | `mv = sp;` deep copy: fresh identity plus `copySt` |
| `memoryStorageCopyUnfold` | same | same | a complex storage path is captured first |
| `memoryLocalDeclInitDrop` | same | same | one generic decl-with-init split; the assignment rules take over |

## Memory field/index write & read

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `memoryFieldWrite` | `memoryFieldWriteStore`, `memoryFieldWriteCopy` | merged | Lean's sorts are not generic: a value source and a reference-path source are two rules |
| `memoryIndexWriteArray` | `memoryIndexWriteStore`, `memoryIndexWriteCopy` | merged | likewise |
| `memoryFieldRead` | `memoryFieldReadHeap`, `memoryFieldReadAliasRoot`, `memoryLengthRead` | merged | the same split on reads (a value lands on a local, a reference on a memory alias); `memoryLengthRead` is the member `length` (`Term.mlen`, KeY's `read(memory, mv, size)`) |
| `memoryIndexReadArrayValue` | `memoryIndexReadHeap` | merged | |
| `memoryIndexReadArrayMemory` | `memoryIndexReadAliasRoot` | merged | |
| `memoryFieldRead_unfold_rightFst` | `memoryFieldRead_unfold_rightFst`, `memoryLengthRead_unfold_rightFst` | same | |
| `memoryIndexRead_unfold_rightFst`, `memoryIndexRead_unfold_rightSndIndex` | same names | same | |
| `memoryFieldWrite_unfold_leftFst` | same | same | also claims the row below |
| `memoryFieldWriteMemRef_unfold_leftFst` | `memoryFieldWrite_unfold_leftFst` | merged | `msrc` is a value or a memory reference, one rule for both |
| `memoryIndexWriteCaptureAllComplexRecv` | same | same | `nmp[e1] = e2 ⇝ T se = e2; T memory mv = nmp; T ie = e1; mv[ie] = se` |
| `memoryIndexWriteMemRefCaptureAllComplexRecv` | same | find same | `… mv[ie] = mpath`: a memory path is a source as it stands |
| `memoryIndexWriteCaptureAllNonSimpleIndex` | same | find same | `mv[nse] = e ⇝ T se = e; T ie = nse; mv[ie] = se`: KeY rebinds the receiver (`T memory mv' = mv`), which for an untyped memory local would leave its array type free |
| `memoryIndexWriteMemRefCaptureAllNonSimpleIndex` | same | find same | `mv[nse] = mpath ⇝ T ie = nse; mv[ie] = mpath` |
| `memoryFieldWriteCaptureSrc`, `memoryIndexWriteMemRefRhsCapture`, `memoryFieldRead_unfold_rightSndResult`, `memoryIndexRead_unfold_rightSndResult` | — | unclaimed | KeY captures a memory reference into an alias before using it as a source; here a memory path is a source as it stands (`mpath`), so `memoryFieldWriteCopy` writes it in one step. A value read is captured by the value-RHS rules below |

## Memory delete

`Stmt.deleteMem p` deletes a memory local, a member or an element. KeY's
primitive/reference split (`\hasMemoryFieldSort(fld, alphaPrim)`,
`Path[…,primitiveElement]`) is the type the rule fixes: `T := Ty.prim p`
against `T := Ty.ref R` (the stems in `RuleSyntax.lean`'s table). KeY's
`inBounds` split of an index delete is the write's bounds check, which reverts.

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `memoryRootDeleteFreshRebind` | same | same | listed above, with the allocation rules |
| `memoryFieldDeletePrimitive` | same | same | `{ memory := write(memory, mv.pfld, defVal(T)) }` |
| `memoryFieldDeleteReference` | same | same | `{ memory := write(addM(memory), mv.rfld, freshId(addM(memory))) }`: the member gets a fresh default object |
| `memoryIndexDeletePrimitive`, `memoryIndexDeleteReference`, `memoryFieldDelete_unfold_leftFst`, `memoryIndexDelete_unfold_leftFst`, `memoryIndexDeleteNonSimpleIndexCapture` | same names | same | |

## Memory → storage copies

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `memoryToStorageStoreRoot`, `memoryToStorageIndexMappingCopyRoot`, `memoryToStorageField_unfold_leftFst` | same names | same | |
| `memoryToStorageFieldCopyRoot` | same | same | also claims the row below |
| `memoryToStorageFieldCopyField` | `memoryToStorageFieldCopyRoot` | merged | the one member-source shape, read directly |
| `memoryToStorageIndexArrayCopyRoot` | same | same | both modalities |
| `memoryToStorageIndexCaptureAllComplexRecv` | same | find same | `nsp[e] = mpath ⇝ T storage sp = nsp; T ie = e; sp[ie] = mpath`: the memory source stands (KeY: `T memory rv = src`) |
| `memoryToStorageIndexCaptureAllNonSimpleIndex` | same | find same | `sp[nse] = mpath ⇝ T storage sp' = sp; T ie = nse; sp'[ie] = mpath` |

## Value declarations and value-RHS capture

KeY writes the value-RHS captures once, at any receiver; Lean states one
instance per receiver kind, the memory ones claiming the same taclet as the
storage ones.

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `localValueDeclInitDrop`, `valueDeclSkip` | same names | same | |
| `localValueAssign` | same | same | terminal `v = se;` |
| `storageRootWriteValueRhsCapture` | same | same | `gsp = nse; ⇝ T se = nse; gsp = se;` |
| `fieldWriteValueRhsCapture` | `fieldWriteValueRhsCapture`, `memoryFieldWriteUnfoldSource` | same | the second is the memory instance |
| `indexWriteValueRhsCapture` | `indexWriteValueRhsCapture`, `memoryIndexWriteUnfoldSource` | same | likewise |

## Operators

One constructor per **shape**, not per operator: `op : BinOp` is a free
variable, so an instance is `binopAssignment (op := .add)`. The comparison and
boolean operators share the arithmetic constructors.

| KeY taclets | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `{addition,subtraction,multiplication,power,division,modulo}_unfold_left`, `{boolEquality,boolInequality,lessThan,greaterThan,lessEqual,greaterEqual,logicalAnd,logicalOr}CaptureLhs` | `binopUnfoldLeft` | merged | `v = nse ⊕ e; ⇝ T se = nse; v = se ⊕ e;` |
| `{addition,…,modulo}_unfold_right`, `{boolEquality,boolInequality,lessThan,greaterThan,lessEqual,greaterEqual}CaptureRhs` | `binopUnfoldRight` | merged | requires `¬ op.shortCircuits`; `&&`/`||` have the short-circuit rows below |
| `{addition,subtraction,multiplication,power,division,modulo}Assignment`, `{boolEquality,boolInequality,lessThan,greaterThan,lessEqual,greaterEqual,logicalAnd,logicalOr}Assignment` | `binopAssignment` | merged | terminal `v = se₁ ⊕ se₂;`; `**` is checked `uint` exponentiation (`op := .pow`); solkey has no `**=` taclets |
| `logicalAndShortCircuitRhs`, `logicalOrShortCircuitRhs` | same names | same | `v = se && nse; ⇝ if (se) { v = nse; v = v && true; } else { v = false; }`, and its dual |
| `logicalNotCapture`, `unaryMinusCapture` | `unopCapture` | merged | |
| `logicalNotAssignment`, `unaryMinusAssignment` | `unopAssignment` | merged | |
| `ternaryCaptureCond` | same | same | |
| `ternaryToIf` | same | same | also claims the row below |
| `ternaryToIfStorage` | `ternaryToIf` | merged | one rule for a local or storage target; a memory target is lowered the same way, a conditional never being a write's source (`Val.notTernary`) |

## Compound assignment

Pattern per `⊕ ∈ {Add, Sub, Mul, Div, Mod}`; one constructor per receiver
shape, `op` free. Mapping and array stay **separate** here, unlike increments.

| KeY taclets | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `local{Add,…,Mod}Assign` | `localOpAssign` | merged | terminal `v ⊕= se;` |
| `storageRoot…Assign` | `storageRootOpAssign` | merged | |
| `storageField…Assign` | `storageFieldOpAssign` | merged | |
| `storageIndexMapping…Assign` | `storageIndexMappingOpAssign` | merged | |
| `storageIndexArray…Assign` | `storageIndexArrayOpAssign` | merged | no bounds split: the update reverts in the path's bounds check |
| `memoryField…Assign` | `memoryFieldOpAssign` | merged | |
| `memoryIndexArray…Assign` | `memoryIndexArrayOpAssign` | merged | no root or mapping form: a memory root binds an identity, memory has no mappings |
| `storageField…Assign_unfold_leftFst` | `storageFieldOpAssignUnfoldLeftFst` | merged | `nsp.fld ⊕= se; ⇝ T storage sp = nsp; sp.fld ⊕= se;` |
| `storageIndex…Assign_unfold_leftFst` | `storageIndexOpAssignUnfoldLeftFst` | merged | |
| `memoryField…Assign_unfold_leftFst` | `memoryFieldOpAssignUnfoldLeftFst` | merged | |
| `memoryIndex…Assign_unfold_leftFst` | `memoryIndexOpAssignUnfoldLeftFst` | merged | |
| `{add,sub,mul,div,mod}AssignValueRhsCapture` | `compoundAssignValueRhsCapture` | merged | location-neutral capture of a non-simple RHS |

## Increment / decrement

Pattern per `{Pre,Post}{increment,decrement}`. A decrement is `x−−`/`−−x` in
`sol{ … }`; an `++`/`−−` inside an expression is captured by the elaborator
(`uint se1; se1 = i++;`), so it reaches these rules as a statement. Here a
mapping and an array receiver **do** share one constructor: solkey splits the
receiver kind, Lean does not.

| KeY taclets (all four `Pre/Post × increment/decrement`) | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `local…` | `localIncrement` | merged | bare `v⊕⊕;` on a stack local |
| `storageRoot…`, `storageField…` | `storageRootIncrement`, `storageFieldIncrement` | merged | |
| `storageIndexMapping…`, `storageIndexArray…` (8) | `storageIndexIncrement` | merged | one constructor over both receiver kinds |
| `memoryField…`, `memoryIndexArray…` | `memoryFieldIncrement`, `memoryIndexArrayIncrement` | merged | |
| `storageField…_unfold_leftFst`, `storageIndex…_unfold_leftFst`, `memoryField…_unfold_leftFst`, `memoryIndex…_unfold_leftFst` | `storageFieldIncrementUnfoldLeftFst`, `storageIndexIncrementUnfoldLeftFst`, `memoryFieldIncrementUnfoldLeftFst`, `memoryIndexIncrementUnfoldLeftFst` | merged | |
| `localAssign…`, `localDecl…` (8) | `localAssignIncrement` | merged | `vp = v⊕⊕;`; KeY has one taclet for the assignment and one for the declaration, Lean reaches the declaration through `localValueDeclInitDrop` |
| `storageRoot…Assignment`, `storageField…Assignment`, `storageIndexMapping…Assignment`, `storageIndexArray…Assignment` (8), `memoryField…Assignment`, `memoryIndexArray…Assignment` | `storageRootIncrementAssignment`, `storageFieldIncrementAssignment`, `storageIndexIncrementAssignment`, `memoryFieldIncrementAssignment`, `memoryIndexArrayIncrementAssignment` | merged | |

## Assert, require, if-then-else

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `assertConditionCapture`, `assertSimple` | same names | same | terminal; the box/diamond split on a reverted run is the modality semantics, not a rule |
| `requireConditionCapture` | same | same | the assert capture over `Stmt.require` |
| `requireSimple` | same | same | `require(se); ⇝ se = true ⟹ ⟨[ ]⟩ ; se = false ⟹ ⟨[ revert(); ]⟩` |
| `ifElseUnfold` | same | same | also claims `ifUnfold` |
| `ifUnfold` | `ifElseUnfold` | merged | `Stmt.ite` always has both branches (an absent `else` is `[]`) |
| `ifElseSplit` | same | same | `if (se) thn else els; ⇝ se = true ⟹ ⟨[ thn ]⟩ ; se = false ⟹ ⟨[ els ]⟩`: a `.split` premise is the two-goal shape. Also claims `ifSplit` |
| `ifSplit` | `ifElseSplit` | merged | |
| `ifTrue`, `ifFalse`, `ifElseTrue`, `ifElseFalse`, `ifElseNegated` | — | unclaimed | `concrete_solidity` strategy shortcuts. A literal is simple, so `ifElseSplit` applies (one goal assumes `true = false`); `!se` is not simple, so `ifElseUnfold` captures it. The table has no strategy |

## Payments

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `transfer_unfold_leftFstReceiver`, `transfer_unfold_rightSndArgument` | same names | same | |
| `transferNoCallbackBox`, `transferNoCallbackDiamond` | `transferNoCallback` | merged | one terminal rule for both modalities, a guarded update (`Premise.guard`): funds check `0 <= se ∧ se <= selfBalance ⟹ { selfBalance := selfBalance - se ‖ net := store(net, at(sadr), net(sadr) - se) } ⟨[ ]⟩`, else `⟨[ revert(); ]⟩`. The arithmetic is KeY's `int` (`IntOp`); the modalities part at `revert();` (`revertBox`, `revertDiamond`), so the diamond's "sufficient funds" goal is what is left of it |
| `transferWithCallbackBox` | `CallbackTaclet.transferWithCallbackBox` | same | a constructor of `CallbackTaclet`, sound for the callback reading (`holdsC`), not of `Taclet`. The premise has `transferNoCallback`'s shape (funds check `F`, booking `U`), read as KeY's goals (`CallbackTaclet.sound`): `F → {U} I` ("invariant on exit") and `F → {U} {havoc} (I → ⟨[ ω ]⟩ φ)` ("resume after callback"; `{havoc}` is KeY's anonymising update, read by `CbResume`). The box assumes `F` where KeY does not, which only weakens its goals. Used by `ProvesC` |
| `transferWithCallbackDiamond` | `CallbackTaclet.transferWithCallbackDiamond` | same | as the box, plus KeY's "sufficient funds" goal `F` (`ProvesC.callback`'s `funds`) |

## Update algebra (`updateRules.key`)

An update is a term (`Upd C`, a list of `UpdElem`s read against the
pre-state), so KeY's update rules are rules here too: `UpdRule` in
`Calculus/UpdateRules.lean`, each an equivalence over `holds`, plus box forms;
on sequents they are `Proves` constructors (`Calculus/Logic.lean`), usable with
the program still to run. A side condition KeY's rule lacks exists because a
term here can halt and KeY's cannot (`Calculus/UpdateRules.lean`, "What halting
changes").

| KeY rule | Lean | Status | Notes |
| --- | --- | --- | --- |
| `sequentialToParallel1-3` | `UpdRule.sequentialToParallel`, `Proves.merge`; `Proves.mergeStorage` | done | `{u}{u2}φ ⇝ {u ‖ {u}u2}φ` for `u` of locals (`Upd.envOnly`); `mergeStorage` over a storage write, for terms whose every storage read is a `storage` term (`stExplicit`) |
| `applyOnElementary`, `applyOnParallel` | `UpdElem.subst`, `Upd.subst` | functions | `{u}` pushed into right-hand sides |
| `applyOnPV`, `applyOnPVLastInParallel`, `applyOnDifferentPV`, `applyOnDifferentPVLastInParallel` | `Fml.subst` (`Upd.lastWrite`) | functions | the last write of a local wins; an unwritten local is kept |
| `simplifyUpdate1-3` | `UpdRule.simplifyUpdate`, `Upd.dropEffectless`, `Proves.simplify` | done | only elements that cannot halt are dropped (`UpdElem.total`) |
| `applySkip1-3`, `applyOnSkip` | `UpdRule.applySkip` | done | `skip` is `[]` |
| `parallelWithSkip1-2` | — | arch | `‖` is `++`, `skip` is `[]`: nothing to rewrite |
| `applyOnRigidFormula` | `UpdRule.applyOnRigid` | done | an equivalence, for an update that cannot halt (`Upd.total`) and a formula reading no variable at another sort than the update writes it (`Fml.sortedFor`) |
| `applyOnRigidFormula`, under the box | `Proves.applyOnRigidBox`, `Proves.applyStorageBox` (`{storage := s}`); `sol_apply_upd` | done | one direction, **no totality premise**: the last update of the context is applied to a first-order goal and dropped; a halting box update proves what follows |
| `elimSelfUpdate*` | `UpdElem.elimSelf_box`, `UpdElem.elimSelf_diamond` | done, one direction each | commented out in KeY; `x := x` halts when `x` holds no value, so it is no equivalence |
| `simplifyIfThenElseUpdate1-4`, `commuteSimpleUpdates` | — | arch | commented-out dead code in KeY |

### Closing the first-order goal

What symbolic execution leaves is closed by first-order steps derived through
`Proves.close` (`Calculus/Rewrite.lean`), each needing a context with no
diamond (`Hyp.boxOnly`). A program comparison produces `Fml.eqD a b` —
`defined(a) ∧ defined(b) ∧ a ≐ b` — because a term here can halt; `a ≐ b`
(`Fml.eq`) is the total Theory equation, KeY's `=`.

| KeY rule | Lean | Status | Notes |
| --- | --- | --- | --- |
| `eqClose` | `Proves.eqRefl`; `Proves.eqClose` (`v ≐ v`), `Proves.eqDClose` (`v = v`) | done | `t ≐ t` for any term, halting or not (`StValue.Equiv.refl`) |
| `andRight` | `Proves.andSplit`, `Proves.andSplitUpd` (behind an update) | done | |
| — | `Proves.eqDSplit` | Lean only | `a = b` from `defined(a)`, `defined(b)`, `a ≐ b`: `Fml.eqD` unfolded |
| — | `Proves.definedWritten` | Lean only | `defined(x)` behind a box update whose last binder of `x` is `x := t`: what `applyOnRigidBox` forgets |
| — | `Proves.definedLit` | Lean only | a literal is defined |
| any theory taclet on a sequent | `Proves.theoryRw` (`Calculus/Logic.lean`), `rw [h]`/`sol_rw` (`Calculus/Rewrite.lean`) | done | a Theory equation `h : Term.Theq t t'` rewrites every total equation of the sequent (`Fml.rwEq`), with no soundness proof per rule |
| the same, inside an update | `Proves.updRw`, `sol_rw` | done | an update's right-hand side runs in the interpreter, so the rewrite asks `Term.EvalRefines t t'`, which a Theory equation onto a literal gives (`Term.EvalRefines.of_theq`); box updates only |

## The data-structure theories

The rows above are the *program* calculus. Its updates are written over
symbols — `find`, `save`, `selectSt`, `read`, `write`, `addM` — that solkey
declares in `structHeader.key`/`memoryHeader.key` and defines nowhere; their
meaning is the taclet sets of `structRules.key`, `memoryRules.key` and
`structMemoryRules.key`. `Solidity/Theory/` is that meaning, a term algebra
with one theorem per taclet. Paths are `Semantics.Seg` on both sides: a member
constant is `Seg.field n`, `at(i)` is `Seg.at i`, `size` is
`Seg.field "length"`, `consr(p, a)` is `p ++ [a]`; `listRules.key` needs no
module, it is `List`.

**The storage copy fold is not followed, by decision.** solkey folded `copyAt`
into `save`: `save(st, nil, v)` is an irreducible leaf that the eight copy
rules write and `selectOnSaveEmpty*` read through (`c80a54494c`,
`8c5c69ca25`). `Theory/Storage.lean` keeps `save` with the collapsing leaf
(`save(st, nil, v) = (Struct) v`, `saveOnEmpty`) for a word write and
`delAt`'s write. A struct or array written over a location is `copyTo`
(`Theory/Copy.lean`), `save` with a `copyAt` leaf, whose read laws
`selectOnCopy*` are upstream's `selectOnSaveEmpty*`. So the fold's semantics
is modelled, but as two writes rather than one lazy leaf.
`docs/solkey-feedback.md` carries the request that solkey drop the fold.

### The update vocabulary (`Solidity/Update.lean`)

The sorts are KeY's, renamed to plain Lean identifiers; an element's
right-hand side is a term read in the pre-state, and a rule's premise nests
them as KeY's `\replacewith` updates do.

| KeY sort | Here | Notes |
| --- | --- | --- |
| a value | `Term` | a constant, a stack local, `a ⊕ b`, `find(s, p)`, `read(m, a)`, `select(s, r)` (`Term.find` at a state variable), an array's length (`Term.len`, `Term.mlen`), `c ? a : b`, `selectSt(net, at(a))` (`Term.net`), `selectSt(oldNet, at(a))` (`Term.netOf`) |
| `Path[storage]` | `PTerm` | a state variable (`.root`), an alias (`.pv`), `.field`/`.at` |
| `Storage` | `STerm` | `.storage`, `.save`, `.delAt`; `.push`/`.pushSlot`/`.pop`/`.shrink`/`.extend` for the array writes |
| what a storage `save` writes | `SValT` | a value (`.val`), a subtree read from a storage (`.find`), or a memory object copied back (`.copyMem`, KeY's `copyMem(mtSt, m, i)`) |
| `Identity` | `ITerm` | a memory local (`.pv`), a reference read out of memory (`.read`), `freshId(addM(m))` (`.alloc`, carrying the `RefTy`; a concrete struct's prints `freshId(addM(m, S))`), `freshId(copySt(m, v))` (`.copy`) |
| a member or element of a memory object | `MAddr` | `.field`/`.at` |
| `Memory` | `MTerm` | `.memory`, `.write(m, a, v)`, `.addM` (eager: the type rides along; a concrete struct's prints `addM(m, S)`, KeY's `addM(mem, idp)`), `.copySt(m, v)` |
| what a memory `write` writes | `MValT` | a value (`.val`) or a reference (`.ref`) |
| one elementary update | `UpdElem` | `.val`, `.path`, `.mref`, `.storage`, `.memory`; `.store` for `old := storage`; `.selfBalance`/`.net` for a transfer's `selfBalance := selfBalance ± a` and `net := store(net, at(r), net(r) ± a)` (the two written together); `.saveNet` for `oldNet := net` |

### `structRules.key` → `Theory/Storage.lean` (`Struct`, `StValue`)

| KeY taclet | Lean theorem | Status |
| --- | --- | --- |
| `defaultValueStruct` | `defaultValueStruct`, `defaultValueInt`, `defaultValueBool` | done: `defaultValue<[α]>` is `st mtSt`, the `Struct` default, read through the caller's cast |
| `selectOnStore`, `selectOnEmptyStorage`, `findDefinitionEmpty` | same names | done |
| `saveOnEmptyStorage` | same | done, with an `isEmpty(flds)` split upstream lacks (the collapsing leaf) |
| `saveOnStoreCons` | same | done, likewise; `(Struct) v0` is `asStruct v0` |
| `findDefinitionElement`, `findDefinitionMapElement`, `findDefinitionSize`, `findDefinitionMemberPrim`, `findDefinitionMemberValue` | `findDefinitionCons` | done: `atMap(i)` is `Seg.at i`, `size` is `Seg.field "length"` |
| `findDefinitionMemberStruct`, `findDefinitionMemberCons` | `findDefinitionCons` | done **without the tag**: upstream wraps the member read in `typed(fieldShape(m), …)`, which is not modelled (below) |
| `saveOnEmptyPrim` | `saveOnEmptyPrimInt`, `saveOnEmptyPrimBool` | done, as two cast readings at the end of a walk: `storeSt`'s third argument is the supersort, so a primitive leaf is stored verbatim |
| `selectOnSaveEmptyRef`, `selectOnSaveEmptyFixed` | `selectOnCopyRef` | done over the copying write, `save(st, nil, v)` being `copyTo s [] (st n)` = `copyAt s n` (`copyTo_nil`); `StValue.selectOnSaveEmptyRef` is the same equation over the collapsing `save` |
| `selectOnSaveEmptyIndexStruct` | `selectOnCopyIndexNew`, `selectOnCopyIndexClear`, `selectOnCopyIndexKeep`, `selectOnCopySize` | done with **no length invariant**: the branch is picked by `inRange` on the two nodes' lengths (`lenOf`). The collapsing-`save` versions `selectOnSaveEmptyIndexStruct`/`Clear`/`Keep` remain, the last two under the invariant |
| `selectOnSaveEmptyDefault` | `selectOnCopyDefault` | done: a word member of the new node is the word |
| `selectOnSaveEmptyMap` | `selectOnCopyMap` | done: a mapping copied over a mapping keeps the old entries. Unreachable from a program: solc ≥ 0.7 and solkey's parser reject the copy, and `Src.copy` cannot build it |
| `selectOnSaveCons` | same | done, **unconditional** (a total definition needs no `isStruct` guard) |
| `delFieldRef`, `delFieldIndexStruct` | same names | done: `delField s a = delValue (selectSt s a)`, the reset picked by the value's sort since a `Seg` has none |
| `delFieldDefault` | `delFieldDefault`, `delFieldDefault_asBool` | done |
| `delFieldStValueCast` | `delValueCast`, `delValueCast_asInt`, `delValueCast_asBool` | done: the cast pushed through the reset |
| `delFieldMap`, `delFieldFixed` | same names | done one selector down (both sides literal terms), the member's kind (mapping, `.arr true`) being a premise: a `Seg` has no sort, the node carries it |
| `selectStDelNodeMap` | `selectDelNodeMap`, `selectStDelNodeMap` | done one selector down: `selectDelNodeMap` is the rule (the member is a mapping, whatever the node); `selectStDelNodeMap` the node-kind form (`selectStDelNodeKeep`) |
| `selectStDelNodeRef` | `selectStDelNodeRef` (from `selectStDelNodeSelect`) | done at a member the node does not keep (`keepsOnDelete`): one theorem, `selectSt (delNode s) a = delValue (selectSt s a)`, covers `Ref`, `Default` and the in-bounds index; `selectOnDelNode` is the general form |
| `selectStDelNodeIndexStruct` | `selectStDelNodeIndexStruct`, `selectStDelNodeSelect`, `selectStDelNodeKeep`, `selectStDelNodeIndexKeep` | done: the in-bounds branch under `keepsOnDelete` (at an array, KeY's `i < size`, `keepsOnDelete_at`); the keep branch past the length and at an absent slot |
| `selectStDelNodeDefault` | `selectStDelNodeDefault`, `selectStDelNodeDefault_asBool` | done, at a member the node does not keep |
| `selectStDelNodeFixed` | `selectStDelNodeFixed` (through `selectSt_delNode_fixed`) | done one selector down, at a member the node does not keep whose kind is a fixed-size array |
| `selectStDelNodeFixed{Element,Size,Value}` | `selectStDelNodeFixedElement`, `selectStDelNodeFixedSize`, `selectStDelNodeFixedValue` (+`_asBool`) | done, over `delNodeFixed` (`delNode` with the `length` member stored back) |
| `selectStDelNodeFixedMap` | — | **derived**: `selectStDelNodeFixedElement` then `selectStDelNodeMap`; past the length the slot is kept (`selectStDelNodeKeep`) |
| `delAtEmpty` | same | done |
| `selectOnDelAtCons` | same | done, through `selectOnSaveCons`: `delAt` is eager, `save st p (delValue (find st p))` |
| `fieldShapeDef` | `fieldShapeDef` (`fieldShape`, `Shape.ofTy`) | done: `#shapeOf` is `Shape.ofTy`, over a member table the caller supplies (a `Seg.field` carries a name, not the declaration) |
| `selectOnTyped{Struct,FixedSize,DynSize,LeafSize,MapSize,Element,Member}`, `typedTyped` | — | **not modelled**: only `selectOnTypedFixedSize` reads the tag; a declared `T[n]` has shape `fixedArr` (`Shape.ofTy_fixed`) but the elaborator writes its `.length` as the literal `n`, so no program reads it, and `typed` would be one more `Struct` constructor through every proof. A delete keeps a fixed-size array's length without it (`keepsOnDelete`) |
| `findStValueCast`, `selectStValueCast` | `asStruct_st`, `asStruct_prim`, `find_append` | done: the cast is the inverse of the injection `st` |
| `sizeNotNegative` | — | **arch**: an `\add` of a reachability fact; a bounds check is a *guard* on the program taclet, not a term-algebra theorem |
| `saveOnEmpty`, `selectOnSaveEmpty` (gone upstream with the fold) | same names | Lean only: the collapsing leaf, `save(st, nil, v) ⇝ v` |
| `delValueStruct`, `delValueDefault` (gone upstream, replaced by `delField`) | same names | Lean only: the lemmas under `delField` |
| `copyAtEmpty`, `selectOnCopyAtCons`, `mergePrim`, `selectStMerge{Map,Ref,IndexStruct,Default}`, `mergeStValueCast` (gone upstream with the fold) | `selectOnCopyAt` | `Struct.copyAt` is `copyTo`'s leaf, read one member at a time by `selectOnCopyAt` (`copyRead`, by the two nodes' kinds and lengths); the `selectOnCopy*` rows above are its rules |

**Beyond the taclets.** solkey has no `find(save(…), …)` rule: a read of a
write goes through `findDefinitionCons` then `selectOnSaveCons`, a selector at
a time. `Theory/Storage.lean` packages the cases over `save` —
`find_save_same`, `find_save_extends` (below the write), `find_save_prefix`
(above it), `find_save_frame` (off it, over `diverges`) — and `find_append`
composes reads along `++`. Over `delAt`: `find_delAt_same`,
`find_delAt_field` (`findDelAt`), `find_delAt_frame`, `find_delAt_extends`,
`find_delAt_member` and `find_delAt_below` (a read below a deleted path is the
reset of the read before it, on a node with no kinds in it).

`save` recurses on the path over `storeAt`, the one-segment walk, and stores
the value verbatim at the last segment (the supersort argument again); `delAt`
is eager over the same walk, down to the lazy leaf `delNode`. Storage terms
denote in this algebra (`Term.denote`, over `State.abs`), and `Theory/Bridge/`
relates every write to the interpreter's: a word write and a push literally, a
copy, a delete and a pop up to `StValue.Equiv`.

### `memoryRules.key` → `Theory/Memory.lean`

Identities are KeY's path identities `idC(idp, flds)`; `MTerm.addM` carries the
root it allocates, which may be `shaped(idp, sh)` (`IdentityPrim.shaped`,
`Theory/Terms.lean`).

| KeY taclet | Lean theorem | Status |
| --- | --- | --- |
| `readOnWrite`, `readFromEmptyMemory`, `readOnAddM`, `newFromEmptyMemory`, `newFromWrite`, `newFromAdd`, `idCCDef`, `shapeAtNil`, `shapeAtMap`, `idShapeDef`, `defaultDefIdentity` | same names | done (`defaultDefIdentity` through `MemValue.asIdentity`) |
| `defaultValueInt`, `defaultValueBool`, `defValResolve` | `MemValue.asPrim`, `defaultDefInt`, `defValResolvePrim` | done as casts |
| `defaultDefElement`, `defaultDefMember` | same names (`MemValue.asIntAt`) | done: split by field so `defaultSize` has the length to itself; the cast takes the location |
| `defaultSize` | `defaultSize` (`defaultSizeUnshaped` for a bare root) | done |
| `readREmpty`, `readRCons` | same names (`Memory.readR`, `readRId`) | done |
| `sizeOfFixed`, `sizeOfDyn`, `sizeOfLeaf` | same names (`shapeSize`: `sizeOf` is Lean's own) | done; `mapOf` has no taclet and is `0` |
| `shapeAtFixed`, `shapeAtFixedMapElement` | `shapeAtFixed` | done: `atMap(i)` is `Seg.at i` |
| `shapeAtDyn`, `shapeAtDynMapElement` | `shapeAtDyn` | done, likewise |
| `shapeAtLeafElement`, `shapeAtLeafMapElement` | `shapeAtLeafElement` | **differs** on an ill-typed path: upstream `shapeAt(leaf, cons(at(pk), xs)) ⇝ leaf` drops `xs`; here the walk goes on from `leaf`, which makes `shapeAtSuffix` hold |
| `shapeAtMember` | `shapeAtMember` | done, for a member other than `size` (not a `MemberField`) |
| — | `shapeAtSuffix` | Lean only: the tail-first rule; solkey recurses head-first |

### `structMemoryRules.key` → `Theory/CrossDomain.lean`

| KeY taclet | Lean theorem | Status |
| --- | --- | --- |
| `findOnCopy` | `StValue.findCopyMem`, `StValue.findCopyMem_asBool` | done, at the primitive sorts, as the taclet is |
| `selectOnCopyMemPrim` | `StValue.selectOnCopyMemPrim` (`_asBool`) | done, through `find`: `selectSt` on a view stays structural |
| `selectOnCopyMemRef` | `StValue.selectOnCopyMemRef`, `StValue.findCopyMemStruct` | done, for a non-primitive slot; a never-written slot is the view at `defaultDefIdentity`'s identity |
| `readFromCopyToStorage` | `Memory.readCopySt` | done |
| `readFromCopyToStorageIdentity` | `Memory.readCopyStIdentity` | done |
| — | `Memory.readCopyStOther` | Lean only: the split form of the frame |

The views are constructors of the two sorts, as KeY declares them
(`copyMem(Struct, Memory, Identity)`, `copySt(Memory, IdentityPrim, Struct)`),
which makes `Struct`, `StValue` and `Memory` one mutual inductive
(`Theory/Terms.lean`). A view nested in a view is not modelled: `readIn` reads
its copied struct with `findSt`, which stops at a view and keeps every
definition structural; no example nests one and no taclet rewrites under one.

### The Theory's laws as rules (`Calculus/TheoryLaws.lean`)

A law of the two storage modules, read through `Term.denote`, is a
`Term.Theq` between the terms that denote its sides, hence a rule on a
sequent (`rw [findOnSave]`) with no soundness proof of its own. Side
conditions are syntactic `Bool`s on the `PTerm`s, closed by `rfl`
(`PTerm.hasSeg`, `PTerm.diverges`). solkey has none of these as a taclet;
they are the rules `Theory/Rewrite.lean` lists as Lean-only, stated on terms.

| Law | Theory lemma | Printed rule (`TheoryRule`) | Notes |
| --- | --- | --- | --- |
| `findOnSave` | `find_copyTo_same` (`Theory/Copy.lean`) | `findOnSave` | `find(save(s, p, v), p) ≐ v` for a literal word `v`: a copy reads back the new value laid over the old, which is `v` only for a word |
| `findOnSaveFrame` | `find_copyTo_frame` | `findOnSaveDifferent` | any written value, `p` diverging from `q` |
| `findOnDelAt` | `find_delAt_same`, `delValueDefault` | `findDelAt` | where `find(s, p) ≐ w` for a word `w`, the delete reads its default |
| `findOnDelAtSave` | `findOnDelAt` over `findOnSave` | `findDelAt` | a delete over a written word |
| `findOnDelAtFrame` | `find_delAt_frame` | `findDelAtOutside` | |
| `findOnPushFrame`, `findOnPopFrame` | `find_pushT_frame`, `find_popT_frame` (`Theory/Copy.lean`) | — | a push or pop is one term here, not two saves |

### The names

`Theory/Rewrite.lean` enumerates the theory's rules under their printed names
in its signature, `lemmaNames` mapping each `TheoryRule` constructor
to the theorems above; theorems keep their upstream names, which is what makes
this file a map.
The printed rules with no constructor — the `typed`
rows, `selectStDelNodeFixedMap` (derived), and the four arithmetic expansions
listed as not implemented — are excused in `Theory/Rewrite.lean` by name.

### Deviations

Where the theory or a taclet differs from KeY, each stated once at its row:

- **Eager against lazy.** `MTerm.addM` carries the allocated `RefTy` (KeY's
  `readOnAddM` resolves a fresh object's slot to `default<[α]>` at the
  reader's sort; `Semantics.allocDefault` materializes the object), and
  `defaultValue<[α]>` is `st mtSt`, resolved by the caller's cast.
- **A push is one term.** `STerm.push s p v` *is* `save(save(s, p[p.length], v),
  p.length, p.length + 1)`, where KeY writes two parallel `save`s: a program
  can perform neither write alone. The slot it lands on is recycled or a
  fresh default (`Semantics.pushAt`); a mapping nested in a popped element
  survives into the next push either way (`storagePush*`/`storagePop*` rows).
- **Deletes are keyed on the node's kind**, not the field's sort (`delField`,
  `delNode`, `keepsOnDelete`): a `Seg` carries no `MapField`/`FixedField`, so
  those rules are stated one selector down with the kind as a premise; `delete`
  through a fixed-size array element is open in KeY and sound here ("Storage delete").
- **Memory paths are sources as they stand**, so KeY's four memory capture taclets are
  unclaimed and the `MemRef` index captures are `find same` (see their rows).
- **`fieldShape` takes the member table**, and `shapeAt` follows
  `shapeAtSuffix` rather than solkey's `shapeAtLeafElement`; the two agree on
  every well-typed path.
- **`typed` is not modelled**, and the storage copy fold is not followed (top
  of this section).
