# KeY taclet → Lean `Taclet` mapping

The name-by-name map from solkey's `solidityProgramRules.key` (plus
`ifThenElseRules.key`) to `Solidity.Taclet` (`Calculus/Rules.lean`), then the
symbol table for updates and the data-structure theories. **Pinned to solkey
`100f7f24c3`**: 313 program taclets, enumerated in `Calculus/KeyTaclets.lean`.

These tables are the prose companion of `Calculus/RuleShapes.lean`, which
checks the correspondence: `tacletOrigins` gives every constructor a typed
`KeyOrigin` (`.taclet t` or `.merged [t₁, …]`; a missing or misspelled row
fails the build), `unclaimedTaclets` excuses the rest with a reason,
`callbackOrigins` does the same for `CallbackTaclet`, and `taclets_partitioned`
says every taclet is claimed or excused, never both
(`claimedTaclets_count = 300`, `unclaimedTaclets_count = 13`). A rule that
transcribes no taclet is a `LeanTaclet` (`leanTaclets`); there are three,
`functionCallArgCapture`, `tryCallDiamond` and `transferDiamond`. A taclet may be claimed by two constructors (the
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
| `assertConditionCapture` | same | same | |
| `assertSimple` | same | same | KeY's two branches: "Holds" `se = true ⟹ ⟨[ ]⟩` and "Violated" `se = true` (`Premise.check`, `Proves.check`); a failed `assert` panics (`Halt.panic`), which neither modality accepts (`Modality.afterRun`) |
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
| `transferNoCallbackBox` | same name | same | the box only, one terminal update (`UpdElem.pay`): `{ net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) } ⟨[ ]⟩`, solkey's `\if(sadr = self) \then(net) \else(storeSt(…))`, with no guard: the amount is read as a word by the element itself, which halts where it is not, as the interpreter does (`transferAt`). The arithmetic is KeY's `int`. Whether the world pays is the compiler theorem's (`Evm.compile_correct`), where a refused payment is a revert of the machine alone; the contract's own entry is never moved (`Evm.Sim.netSelf`) |
| `transferNoCallbackDiamond` | — | not ported | a payment under the diamond closes to `false` (`LeanTaclet.transferDiamond`); KeY's "non-negative amount" goal and its diamond booking have no counterpart |
| `transferWithCallbackBox` | `CallbackTaclet.transferWithCallbackBox` | same | a constructor of `CallbackTaclet`, sound for the callback reading (`holdsC`), not of `Taclet`. The premise is `transferNoCallbackBox`'s booking `U`, read as KeY's two goals (`CallbackTaclet.sound`): `{U} I` ("invariant on exit") and `{U} {havoc} (I → [ ω ] φ)` ("resume after callback"; `{havoc}` is KeY's anonymising update, read by `CbResume`). Used by `ProvesC` |
| `transferWithCallbackDiamond` | — | not ported | as `transferNoCallbackDiamond`: no diamond over a payment is derived |

## External calls (`try`/`catch`)

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `tryCallNoCallbackBox` | same | same | one goal per clause (`Premise.branches`, `Proves.branches`): "call succeeded", "Error caught", "Panic caught", "other failure caught". KeY declares the return locals and the `Panic` code without an initializer, leaving them unconstrained; here they are bound under `∀` (`Fml.alls`, `Hyp.all`), since a Lean declaration is its default. `s#call` is an `ExtCall`, whose receiver and arguments are simple: the elaborator captures any other before the `try` |
| `tryCallWithCallbackBox` | `CallbackTaclet.tryCallWithCallbackBox` | same | read by `ProvesC.tryCall` (`CallbackTaclet.sound_branches`): `I` where control leaves ("invariant on exit"), the success block after `{havoc}` and `I` ("call succeeded"), each `catch` block from where the call was made |
| — | `LeanTaclet.tryCallDiamond` | Lean only | a diamond `try` closes to `false`; solkey has no rule. The call may revert in the caller (no code at the address, data that does not decode), which no clause catches and no formula rules out |
| — | `LeanTaclet.transferDiamond` | Lean only | a diamond payment closes to `false`; solkey's diamond rules are not ported. Whether the world pays is the compiler theorem's, not the calculus's |

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
| `sequentialToParallel1-3` | `UpdRule.sequentialToParallel`, `Proves.merge`; `Proves.mergeStorage`; + under a branch (`LineRw.mergeIn`, `Calculus/ChainBranches.lean`) | done | `{u}{u2}φ ⇝ {u ‖ {u}u2}φ` for `u` of locals (`Upd.envOnly`); `mergeStorage` over a storage write, for terms whose every storage read is a `storage` term (`stExplicit`); in a chain also at the first spine under `∧`, `→`, `¬` |
| `applyOnElementary`, `applyOnParallel` | `UpdElem.subst`, `Upd.subst` | functions | `{u}` pushed into right-hand sides |
| `applyOnPV`, `applyOnPVLastInParallel`, `applyOnDifferentPV`, `applyOnDifferentPVLastInParallel` | `Fml.subst` (`Upd.lastWrite`) | functions | the last write of a local wins; an unwritten local is kept |
| `simplifyUpdate1-3` | `UpdRule.simplifyUpdate`, `Upd.dropEffectless`, `Proves.simplify` | done | only elements that cannot halt are dropped (`UpdElem.total`) |
| `applySkip1-3`, `applyOnSkip` | `UpdRule.applySkip` | done | `skip` is `[]` |
| `parallelWithSkip1-2` | — | arch | `‖` is `++`, `skip` is `[]`: nothing to rewrite |
| `applyOnRigidFormula` | `UpdRule.applyOnRigid`; + through `∧`, `→`, `¬` (`Fml.push`, `Calculus/ChainBranches.lean`) | done | an equivalence, for an update that cannot halt (`Upd.total`) and a formula reading no variable at another sort than the update writes it (`Fml.sortedFor`); `Fml.push` substitutes each rigid leaf and keeps any other part under the update |
| `applyOnRigidFormula`, under the box | `Proves.applyOnRigidBox`, `Proves.applyStorageBox` (`{storage := s}`); `sol_apply_upd`; + through `∧`, `→`, `¬` (`Fml.pushBox`) | done | one direction, **no totality premise**: the last update of the context is applied to a first-order goal and dropped; a halting box update proves what follows; `Fml.pushBox` keeps an antecedent and a negated part whole under the box, where no direction holds with the update substituted |
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
| `eqClose` | `Proves.eqRefl`; `Proves.eqClose` (`v ≐ v`), `Proves.eqDClose` (`v = v`); on two literals in a chain, `Fml.concrete` (`Calculus/ChainBranches.lean`) | done | `t ≐ t` for any term, halting or not (`StValue.Equiv.refl`); `v ≐ w` for distinct literals folds to `false` |
| `concrete_and_1-4`, `concrete_impl_1-4`, `concrete_not_2` | `Fml.concrete`, `LineRw.concrete` (`Calculus/ChainBranches.lean`) | done | `true ∧ A ⇝ A`, `false → A ⇝ true`, `A → false ⇝ ¬A`, `¬false ⇝ true`, …, bottom-up through `¬`, `∧`, `→`; `concrete_not_1` (`¬true ⇝ false`) rewrites nothing, `false` being `¬true` |
| `andRight` | `Proves.andSplit`, `Proves.andSplitUpd` (behind an update) | done | |
| — | `Proves.eqDSplit` | Lean only | `a = b` from `defined(a)`, `defined(b)`, `a ≐ b`: `Fml.eqD` unfolded |
| — | `Proves.definedWritten` | Lean only | `defined(x)` behind a box update whose last binder of `x` is `x := t`: what `applyOnRigidBox` forgets |
| — | `Proves.definedLit`; `Fml.concrete` (`defined(v) ⇝ true`) | Lean only | a literal is defined |
| any theory taclet on a sequent | `Proves.rewrite` (`Calculus/Logic.lean`), `rw [r]`/`sol_rw` (`Calculus/Rewrite.lean`) | done | a term taclet `r : TermTaclet t t'` rewrites every total equation of the sequent (`Fml.rwEq`); `TermTaclet.sound` proves each rule once, from its Theory lemma |
| the same, inside an update | `Proves.updRw`, `sol_rw` | done | an update's right-hand side runs in the interpreter, so the rewrite asks `Term.EvalRefines t t'`, which a Theory equation onto a literal gives (`Term.EvalRefines.of_theq`); box updates only |

### The closer's clauses (`Calculus/Closer.lean`)

`sol_prove` closes a leaf inside one `Bool`, `LFml.close` over the leaf's
reduction, proved sound once (`LFml.close_holds`): a KeY first-order or
arithmetic taclet it subsumes is a clause of that function, not a proof
step.  "closer clause X" names the definition the clause lives in.

| KeY taclet | Lean | Status | Notes |
| --- | --- | --- | --- |
| `add_literals`, `sub_literals`, `mul_literals`, `div_literals`, `pow_literals` | closer clause `foldBin` | subsumed | the interpreter's checked operation on two literals, `/` and `%` truncating as solc does, out of range left unfolded (it reverts) |
| `less_literals`, `leq_literals`, `greater_literals`, `qeq_literals`, `equal_literals` | closer clause `foldBin` | subsumed | comparisons of two literals |
| `eqClose` (and `t <= t`, `t < t`) | closer clauses `foldSame`, `Facts.eqHolds` | subsumed | `t == t`, `t <= t` fold to `true`, `t < t` to `false`; an equation closes on equal normal forms |
| `ifthenelse_true`, `ifthenelse_false` | closer clause `foldIte` | subsumed | a conditional on a literal |
| `boolean_equal`, `true_to_not_false`, `concrete_not_*` | closer clauses `foldUn`, `Facts.decomp` | subsumed | `!` on a literal; a premise `!c ≐ b` gives `c ≐ !b` |
| `applyEq`, `applyEqRigid` | closer clauses `Facts.eqnK`, `substE` | subsumed | a premise `t ≐ v` rewrites `t` to a literal or a local everywhere after it, decomposed through `&&`, `\|\|`, `==`, `!=` |
| `closeFalse`, `replace_known_left` | closer clauses `Facts.refute`, `Facts.apart` | subsumed | a premise refuted (two literals apart, a side that halts, a pair the premises keep apart) closes the leaf |
| `cut`, `cut_direct` on a `bool` | closer clause `Facts.split` | subsumed | a case split on a `bool` local or a condition compared with a literal |
| `selectOnTypedStruct`, `selectOnTypedMember`, `selectOnTypedElement`, `selectOnTypedMapSize`, `selectOnTypedFixedSize`, `selectOnTypedLeafSize` | closer clauses `LPath.ty`, `Facts.retsW`, `Facts.halts` | subsumed | under `wt(storage)` a read at a path the layout types returns, of its type's kind; a test for a shape the layout says is not there halts |
| `selectOnTypedDynSize` | closer clause `Facts.lo` | partly | a length is at least `0` (`values.length + 1 > 0` after a `push`); no bound above, so `values.length - 1` after a `push` is not known to fit a `uint` (`storagePushReadBack` stays pending) |
| `selectOnSaveCons` on a `size` write, `selectOnDelAtCons` past the end | `LStor.arr` with `arrKey`, `arrRead`, `arrLength` (`Calculus/Decide.lean`) | subsumed | a read below a pushed or popped array compares its index with the old length: the pushed word or default there, the old element below it; the length after is the old one plus or minus one, counted unchecked |
| `selectOnSaveEmptyRef`, `selectOnSaveEmptyFixed`, `selectOnSaveEmptyIndexStruct`, `selectOnSaveEmptyDefault` | `LStor.copy` with `copyLeaf`, `copyKeys`, `overlay_findLive_fields`, `overlay_findLive_nomap` | subsumed | a read below a copy reads the source, through members and key by key (an element of a fixed-size or dynamic array, as solc's element-wise copy leaves it); the target's elements past the source's length are past the end |
| `selectOnSaveEmptyMap` below a key of a copy | `copyKeys` | partly | where the source has a mapping at a key, the read is kept whole (a mapping met in both keeps the target's entries); a copy of a well-typed program meets none, solc rejects it |
| `selectOnDelAtCons`, `selectStDelNodeRef`, `selectStDelNodeMap`, `selectStDelNodeIndexStruct`, `selectStDelNodeDefault` on the slot a `push()` of a struct or an array recycles | `LStor.slotU` with `delLeaf` (`Calculus/Decide.lean`) | subsumed | after a `pop` of the same array, the element it removed, cleared (kept for an array of mappings); after a `delete` of the array, its old first element, cleared; over any other write the read is kept whole |
| `selectOnTypedStruct`, `selectOnTypedMember`, `selectOnTypedElement`, `selectStDelNodeDefault` on that slot of the initial storage | closer clauses `Facts.slotTy`, `Facts.slot_find`, `Facts.slotIn` | subsumed | a read below the slot a `push()` takes, of an array of the initial storage or of it after its `delete`, or below an element up to the old length, is typed by the element type: canonical under `wt(storage)`, a default where the type's structs are canonical (`defaultForTy_canonB`); it returns where the index is at most the old length |
| `inEqSimp_*` on bounds by constants | closer clauses `Facts.range`, `Facts.addCmp`, `foldCmp`, `Facts.fitsArith` | subsumed | a local's type range, a premise `t op k` narrowing `t`, intervals added through `+`, `-` |
| `inEqSimp_*` on differences, `polySimp_*` | — | open | no bound on `y - x` for two symbolic terms, no polynomial normal form; `(x - a) + a` cancels (`LTerm.arith`) |

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
| a value | `Term` | a constant, a stack local, `a ⊕ b`, `find(s, p)`, `read(m, a)`, `select(s, r)` (`Term.find` at a state variable), an array's length (`Term.len`, printed `p.length` at `storage` and `find(s, p.length)` elsewhere; `Term.mlen`), `c ? a : b`, `selectSt(net, at(a))` (`Term.net`), `selectSt(oldNet, at(a))` (`Term.netOf`), `delValue(t)` (`Term.delValue`, KeY's `delValue<[α]>`), `wt(s)` (`Term.wt`/`Op1.wt`, KeY's `wellFormed(heap)`: `true` on a storage the contract can be in, stated `defined(wt(storage))`, the premise of an obligation) |
| `Path[storage]` | `PTerm` | a state variable (`.root`), an alias (`.pv`), `.field`/`.at`; `p[i]@S` (`.atIn`) and `p[p.length]@S` (`.nextIn`) for an index check or a push slot merged under a storage write, their check performed in `S` (no KeY counterpart: KeY's `at(i)` is unchecked) |
| `Storage` | `STerm` | `.storage`, `.save`, `.delAt`; `.push`/`.pushSlot`/`.pop`/`.shrink`/`.extend` for the array writes; `.select` for `selectSt<[Struct]>(s, r)`, the struct at a member, written `select(s, r)` |
| what a storage `save` writes | `SValT` | a value (`.val`), a subtree read from a storage (`.find`), a memory object copied back (`.copyMem`, KeY's `copyMem(mtSt, m, i)`), or a fresh array (`.newArr`; a concrete one prints `newArr(T, n)`, `T` the array type) |
| `Identity` | `ITerm` | a memory local (`.pv`), a reference read out of memory (`.read`), `freshId(addM(m))` (`.alloc`, carrying the `RefTy`; a concrete one prints it, `freshId(addM(m, Person))`, `freshId(addM(m, uint[]))`), `freshId(copySt(m, v))` (`.copy`) |
| a member or element of a memory object | `MAddr` | `.field`/`.at` |
| `Memory` | `MTerm` | `.memory`, `.write(m, a, v)`, `.addM` (eager: the type rides along; a concrete one prints `addM(m, T)`, `T` a struct `Person` or an array type `uint[]`, `Token[3]`, where KeY writes `addM(mem, shaped(idp, #shapeOf(mv)))`: the type in place of its shape), `.copySt(m, v)` |
| what a memory `write` writes | `MValT` | a value (`.val`) or a reference (`.ref`) |
| one elementary update | `UpdElem` | `.val`, `.path`, `.mref`, `.storage`, `.memory`; `.store` for `old := storage`; `.pay` for a transfer's booking `net := if(r = this) then net else store(net, at(r), net(r) - a)`; `.net` for `net := store(net, at(r), net(r) ± a)`, with `.selfBalance` for a `payable` function's booking of `msg.value` (`selfBalance := selfBalance + a`); `.saveNet` for `oldNet := net` |

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
reset of the read before it, on a node with no kinds in it). On a sequent,
`findMemberCons` and `selectOnSaveMember` (`Calculus/TermTaclets.lean`) take
solkey's walk a member at a time, over `select(s, r)` (`STerm.select`).

`save` recurses on the path over `storeAt`, the one-segment walk, and stores
the value verbatim at the last segment (the supersort argument again); `delAt`
is eager over the same walk, down to the lazy leaf `delNode`. Storage terms
denote in this algebra (`Tm.denote`, over `State.abs`), and `Theory/Bridge/`
relates every write to the interpreter's: a word write and a push literally, a
copy, a delete and a pop up to `StValue.Equiv`.

### `memoryRules.key` → `Theory/Memory.lean`

Identities are KeY's path identities `idC(idp, flds)`; `MTerm.addM` carries the
root it allocates, which may be `shaped(idp, sh)` (`IdentityPrim.shaped`,
`Theory/Terms.lean`).

| KeY taclet | Lean theorem | Status |
| --- | --- | --- |
| `readOnWrite`, `readFromEmptyMemory`, `readOnAddM`, `newFromEmptyMemory`, `newFromWrite`, `newFromAdd`, `idCCDef`, `shapeAtNil`, `shapeAtMap`, `idShapeDef`, `initIdentity` | same names | done (`initIdentity` through `MemValue.asIdentity`) |
| `defaultValueInt`, `defaultValueBool`, `defValResolve` | `MemValue.asPrim`, `defaultDefInt`, `defValResolvePrim` | done as casts |
| `initElement`, `initMember` | same names (`MemValue.asIntAt`) | done: split by field so `initSize` has the length to itself; the cast takes the location |
| `initSize` | `initSize` (`initSizeUnshaped` for a bare root) | done |
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
| `selectOnCopyMemRef` | `StValue.selectOnCopyMemRef`, `StValue.findCopyMemStruct` | done, for a non-primitive slot; a never-written slot is the view at `initIdentity`'s identity |
| `readFromCopyToStorage` | `Memory.readCopySt` | done |
| `readFromCopyToStorageIdentity` | `Memory.readCopyStIdentity` | done |
| — | `Memory.readCopyStOther` | Lean only: the split form of the frame |

The views are constructors of the two sorts, as KeY declares them
(`copyMem(Struct, Memory, Identity)`, `copySt(Memory, IdentityPrim, Struct)`),
which makes `Struct`, `StValue` and `Memory` one mutual inductive
(`Theory/Terms.lean`). A view nested in a view is not modelled: `readIn` reads
its copied struct with `findSt`, which stops at a view and keeps every
definition structural; no example nests one and no taclet rewrites under one.

### The Theory's laws as term taclets (`Calculus/TermTaclets.lean`)

A rule on terms is a constructor of `TermTaclet`, applied on a sequent by
name (`rw [findOnSave]`, `Proves.rewrite`); `TermTaclet.sound` reads its two
terms through `Tm.denote` and closes the case by the Theory lemma below.
Side conditions are syntactic `Bool`s on the `PTerm`s, closed by `rfl`
(`PTerm.hasSeg`, `PTerm.diverges`), or a hypothesis of the chain
(`STerm.KindFreeAt`). solkey has none of these as a taclet;
they are the rules `Theory/Rewrite.lean` lists as Lean-only, stated on terms.

| Term taclet | Theory lemma | Printed rule (`TheoryRule`) | Notes |
| --- | --- | --- | --- |
| `findOnSave` | `find_copyTo_same` (`Theory/Copy.lean`) | `findOnSave` | `find(save(s, p, v), q) ≐ v` for a literal word `v`, `q` the path `p` its checks aside (`PTerm.sameSegs`: `p[i]@S` is `p[i]`): a copy reads back the new value laid over the old, which is `v` only for a word |
| `findOnSaveFrame` | `find_copyTo_frame` | `findOnSaveDifferent` | any written value, `p` diverging from `q` |
| `findMemberCons` | `find_cons` | — | solkey's `consRcons`, `consRnil`, `findDefinitionMemberCons`/`Prim`: `find(s, r.p) ≐ find(select(s, r), p)`, the path read from its head (`PTerm.shift?`), at any depth |
| `selectOnSaveMember` | `StValue.selectOnSaveCons` | — | solkey's `selectOnSaveCons` at `a1 = a2`: `find(select(save(s, r.p, v), r), q) ≐ find(save(select(s, r), p, v), q)` |
| `selectOnSaveFrame` | `StValue.selectOnSaveCons` | — | solkey's `selectOnSaveCons` at `a1 ≠ a2`: a write under another root is not seen from `r` |
| `selectOnDelAtMember`, `selectOnDelAtFrame` | `StValue.selectOnSaveCons`, `find_cons` | — | the same for a delete, `delAt(s, p)` being `save(s, p, delValue(find(s, p)))` |
| `selectOnSaveMemberIn`, `selectOnSaveFrameIn`, `selectOnDelAtMemberIn`, `selectOnDelAtFrameIn` | the same, `SCtx.fill_denote` | — | the four in a storage context `K` of saves, deletes and selects (`SCtx`), which the arrow finds: solkey rewrites a storage term wherever it stands |
| `findOnDelAt` | `find_delAt_same`, `delValueDefault` | `findDelAt` | where `find(s, p) ≐ w` for a word `w`, the delete reads its default at `p` (`sameSegs`) |
| `findOnDelAtSave` | `findOnDelAt` over `findOnSave` | `findDelAt` | a delete over a written word, the three paths one path their checks aside |
| `findOnDelAtValue` | `find_delAt_same` | `findDelAt` | `find(delAt(s, p), q) ≐ delValue(find(s, q))`, `q` the path `p` its checks aside: the delete's effect at its own path, the value left for a later law (`delValueLit`, or a read below a mapping member) |
| `delValueLit` | `delValueDefault` | `delValueDefault` | `delValue(w) ≐ default(w)` for a literal word |
| `findOnDelAtBelow` | `find_delAt_below`, `delValueDefault` | `findDelAtFields` | a word at or below a deleted node reads its default, where the deleted storage writes the word there (`STerm.findLit?`) and the node is no mapping (`STerm.KindFreeAt`, a premise of the chain: a mapping keeps its members) |
| `findOnDelAtFrame` | `find_delAt_frame` | `findDelAtOutside` | |
| `findOnPushFrame`, `findOnPopFrame` | `find_pushT_frame`, `find_popT_frame` (`Theory/Copy.lean`) | — | a push or pop is one term here, not two saves |
| `lenOnSaveFrame`, `lenOnDelAtFrame` | `find_copyTo_frame`, `find_delAt_frame` | `findOnSaveDifferent`, `findDelAtOutside` at `p.size` | `len(save(s, q, v), p) ≐ len(s, p)`, `len(delAt(s, q), p) ≐ len(s, p)` where `q` leaves `p.length` (`PTerm.divergesLen`): a length is a read at `p.length`, one term here (`Term.len`) |

### The laws of memory reads (`EvalLaw`, `Calculus/ChainRewrites.lean`)

A memory read (`read`, `copyMem`, `copySt`) denotes its run, so a law of one
is no Theory equation but a refinement of the interpreter: where the read
returns, its replacement returns the same (`EvalLaw.sound`,
`Term.EvalRefines`).  A chain applies one in an update's right-hand side
under any modality where the update holds the write the law reads back
(`Upd.coversEval`, `LineRw.lawUpdEval`).

| Law | Interpreter lemma | KeY taclet | Notes |
| --- | --- | --- | --- |
| `readOnWrite` | `readAddr_writeAddr_same` (`Calculus/ReadWrite.lean`) | `readOnWrite` | `read(write(m, a, v), a) ⇝ v` for a literal `v` |
| `findCopyMem` | `copyMem_member` | `findOnCopy` over `findOnSave` | `find(save(s, p, copyMem(mtSt, m, i)), p.f) ⇝ read(m, i.f)`: the printed trace's one step from the `find` into memory |
| `readCopySt` | `copyStToM_member` | `readFromCopyToStorage` | `read(copySt(m, find(s, p)), freshId(copySt(m, find(s, p))).f) ⇝ find(s, p.f)` |
| `readAddEqual` | `copyStToM_default_readPath` (`Calculus/ReadWrite.lean`) | `readAddEqual` | `read(addM(m, R), a) ⇝ default` for a primitive member or fixed element at a fresh path of the allocation (`Tm.freshPath?`, `RefTy.memberTy`) |
| `readAddDifferent` | `readAddr_heapExt`, `allocDefault_heapExt` | `readAddDifferent` | `read(addM(m, R), a) ⇝ read(m, a)` where `a`'s identity is allocated strictly earlier on `m`'s spine (`Tm.boundedIn`) |
| `readAddDifferentIdentity` | the same | `readAddDifferent` at `Identity` | the twin at the identity sort |
| `readWriteDifferent` | `writeAddr_setObj` | `readWriteDifferent` | `read(write(m, a, v), b) ⇝ read(m, b)` where `a` and `b` never meet (`MAddr.apart?`: different members, a member and an element, one object at different literal indices) |
| `readWriteDifferentIdentity` | the same | `readWriteDifferent` at `Identity` | the twin at the identity sort |
| `readOnWriteIdentity` | `readAddr_writeAddr_same` | `readOnWrite` at `Identity` | `read(write(m, a, ref(i)), a) ⇝ i` |
| — | — | `idC(ρ, [account])` | no law: a reference member of a fresh root, `read(addM(m, R), freshId(addM(m, R)).account)`, is the normal form, since KeY's `idC` has no `ITerm` counterpart |

The merges that feed them (`Calculus/StateParts.lean`): `{memory := M}{V}`
substitutes `M` for `memory` in `V` (`Upd.mergeMem`, with the locals of a
`{carol := freshId(copySt(…)) ‖ memory := copySt(…)}`), and
`{L ‖ storage := s}{V}` substitutes the locals and `s` in one pass, into
memory reads too (`Tm.substSt`, `Upd.mergeStL`), which `applyStorageBox`'s
`withSt` keeps out of; the shadowed `storage := s` goes where `V` writes the
storage over it.  A law is stated at the value or the identity sort
(`EvalLaw : Tm C u → Tm C u → Prop`) and rewrites at that sort inside every
right-hand side, memory reads included (`Tm.rwEv`, `Upd.rwEv_holds`).

### The literal laws (`LitLaw`, `Calculus/Literals.lean`)

KeY's `*_literals` taclets (`integerSimplificationRules.key`) fold an
operation on two literals.  Each is a constructor of `LitLaw`, stated as the
interpreter computes it, and exact (`LitLaw.exact`): its left side returns
the literal on the right in every state.  So a chain applies one anywhere,
under any modality: in an update's right-hand sides (`LineRw.lit`, no premise
on the update) and in the equations and `defined(…)`s of the line's
propositional skeleton (`LineRw.litEq`).

| Law | KeY taclet | Notes |
| --- | --- | --- |
| `add_literals` | `add_literals` | `a + b ⇝ a + b` folded, where the sum is in `uint` range (`checkArith`; out of range the sum reverts and is its own normal form) |
| `sub_literals` | `sub_literals` | `a - b ⇝ a - b` folded, in `uint` range |
| `leq_literals` | `leq_literals` | `a <= b ⇝ true`/`false` |
| `less_literals` | `less_literals` | `a < b ⇝ true`/`false` |

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
  `readOnAddM` resolves a fresh object's slot to `init<[α]>` at the
  reader's sort; `Semantics.allocDefault` materializes the object), and
  `defaultValue<[α]>` is `st mtSt`, resolved by the caller's cast.
- **An index check is explicit after a merge.** KeY's `at(i)` is unchecked
  and `p[p.length]` reads the length in the state; here `p[i]` and
  `p[p.length]` check against the storage of the state they run in, so merged
  under `{storage := S}` they become `p[i]@S` and `p[p.length]@S`
  (`Tm.substSt`), the check performed in `S`.  The laws read them as `p[i]`
  (`PTerm.sameSegs`, `PTerm.diverges` on shapes); `p[p.length]@S` is its own
  path.
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
