# KeY taclet → Lean `Taclet` mapping

The name-by-name map from solkey's `solidityProgramRules.key` (plus
`ifThenElseRules.key`) to `Solidity.Taclet` (`Calculus/Rules.lean`), then the
symbol table for updates and the data-structure theories. **Pinned to solkey
`1b4341a303`**: 323 program taclets, enumerated in `Calculus/KeyTaclets.lean`.

These tables are the prose companion of `Calculus/RuleShapes.lean`, which
checks the correspondence: `tacletOrigins` gives every constructor a typed
`KeyOrigin` (`.taclet t` or `.merged [t₁, …]`; a missing or misspelled row
fails the build), `unclaimedTaclets` excuses the rest with a reason,
`callbackOrigins` does the same for `CallbackTaclet`, and `taclets_partitioned`
says every taclet is claimed or excused, never both
(`claimedTaclets_count = 308`, `unclaimedTaclets_count = 15`). A rule that
transcribes no taclet at the pin is a `LeanTaclet` (`leanTaclets`); there are nine,
`functionCallArgCapture`, `tryCallDiamond`, `transferDiamond`, `whileUnwind`,
`loopExit`, `whileInvariantBox`, `whileInvariantDiamond`, `whileClose` and
`whileNoVariantDiamond`. A taclet may be claimed by two constructors (the
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
- **⊢ rule** — no `Taclet` constructor: a `Proves` constructor or a derived
  theorem (`Calculus/Proves.lean`, `Calculus/Symex.lean`) is the rule.  A
  `solidityProgramRules.key` taclet is listed in `RuleShapes.unclaimedTaclets`;
  a row from another `.key` file names that file.

**`\sameUpdateLevel`.** solkey `78f42fde33` adds it
to the four allocation taclets (`memoryReferenceDeclFreshAlloc`,
`memoryRootDeleteFreshRebind`, `memoryArrayFreshAlloc`, `memoryStorageCopy`);
the memory index and delete taclets with an `\add` carry it already. In KeY
it lets a taclet with an `\add` fire under the update prefix of its `\find`,
the added formula read under the same updates. Here the updates of a goal sit
in its context (`Proves.update` appends `.upd m U` to `Γ`) and a premise's
hypothesis is appended after them (`.pre c`), so every rule fires at the
goal's update level and reads what it adds there: nothing to port.

## Modality / sequent rules

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `functionBodyExpand` | `functionBodyExpand` | same | a call with targets (`fbs`, `CallRet.isRets`: a tuple assignment's call, a specification obligation's `result = f(x̄)`, KeY's `FunctionBodyStatement`) carries its callee inlined (`Stmt.call`), closed over a frame of its own; with every argument simple the premise is KeY's `expand_function_body`, the targets the statements after it (`t = r;`, KeY's `function-frame{…} t0 = r0;` without the frame), and the frame ends with the expansion (`Premise.inline`: `functionFrameEmpty`, claimed merged). The parameters are positions in that frame (named by the elaborator's fresh names in the binders, `Args`/`CallRet`; `Syntax/Elab.lean`), so KeY's fresh renaming is done once, at elaboration; the returns start at their defaults (solc's), where KeY's `R ri;` leaves them unconstrained.  An unnamed return is `_ret` (one) or `_ret0`, `_ret1`, … (several), KeY's `ret0`, `ret1`, …; the solc import names them the same way (`Frontend/Import.lean`, `retNames`).  A deployment, `constructor(x̄);`, is one with no targets (`CallRet.rets []`, `elabCtor`): its body is the state variables' initializers (`x = e;`, in declaration order), then the constructor's modifiers and body, as solkey `a764703bf1`'s `ExpandFunctionBody` prepends them after the renaming |
| `internalCallExpand` | `internalCallExpand` | same | any other call (`ic`: `f(a);`, `y = f(a);`, a memory return `T memory p = f(a);`, KeY's `InternalCall`, decision 19 of `docs/intrinsic.md`), same premise, frame end and soundness (`Stmt.sound_call`). **Lean only:** it also inlines a callee with modifiers (`wrapMods`), where KeY's `InternalCall` refuses one and leaves the call stuck; and it waits for simple arguments (`functionCallArgCapture`), where KeY's binds `T p = arg` as written. A bare call of a function of several returns declares them in its body (`CallRet.none`) |
| `blockReturn`, `functionFrameReturn` | — | unclaimed (architectural) | returns are lowered at elaboration (`lowerReturns`: a `return` in a block splices the block into the statements after it, which is `blockReturn`'s effect), so there is no `return` in `Stmt` to rewrite |
| `functionFrameEmpty` | `functionBodyExpand`, `internalCallExpand` | merged | a call's body is a frame closed over its parameters and returns (`Stmt.call`, `Syntax/Scoped.lean`); the expansion's premise (`Premise.inline`) drops the frame under the return variables it exports once the body is done, which is `function-frame{} ⇝` with nothing printed (the frame's end is a `Thin`, `Calculus/Delab.lean`).  Claimed since the intrinsic refactor; the SolKey reader excuses the row, the pairing being one its shapes cannot see (decision 74) |
| — | `LeanTaclet.functionCallArgCapture` | Lean only | `unfoldArgument`, which solkey's `docs/net.md` lists as missing: the leftmost non-simple argument is captured into a fresh `se` first, so that `Stmt.step` has one rule per call |
| `emptyModality` | `Proves.empty` (also `Proves.emptyModality`) | ⊢ rule | `⟨[ ]⟩ φ ⇝ φ` under either modality, as KeY's `#allmodal`; the proof tree prints the step under this name (`Calculus/ProofTree.lean`) |
| `impRight` (`propRule.key`) | `Proves.intro` (also `Proves.impRight`) | ⊢ rule | `⟹ a → φ` becomes `a ⟹ φ` |
| `allRight` (`firstOrderRules.key`) | `Proves.allIntro` (also `Proves.allRight`) | ⊢ rule | `⟹ ∀ T x; φ` becomes `∀ T x ⟹ φ`: the local holds any value of `T`, KeY's skolem constant (`Hyps.all`) |
| `closeFalse`, `cut` (`propRule.key`) | `Proves.closeFalse` | ⊢ rule (deviation) | a context the logic refutes (`Γ ⟹ false`) closes any goal. KeY's `closeFalse` has no premise and finds a literal `false ⟹`; solkey derives Lean's rule as `cut` on `false`, its TRUE goal `Γ, false ⟹ φ` closed by `closeFalse`, its FALSE goal `Γ ⟹ false, φ` Lean's premise weakened.  The scoped walk closes a split's branch so when its condition is ground under its updates (`Hyps.groundS`, `Calculus/LeafDerive.lean`, and `Seq.refutes`, `Calculus/ProvesDerive.lean`); inside the closer, `Facts.refute` (below) |
| `closeTrue` (`propRule.key`) | `Proves.closeTrue` | ⊢ rule | `⟹ true`, behind a context with no diamond update (`Hyps.boxOnly`; scope ends may stand in it) |
| `blockEmpty` | `blockEmpty` (stated by hand); `Frames.pop .block`, `Frames.exit` | same | a block `{ body }` (`Stmt.block`) steps into its body under a block frame, printed `}` (`Fml.show`, `Calculus/Delab.lean`); each branch of a split ends with one too.  When the body is done, `Frames.exit` pops its locals and goes on with the rest, which is `blockEmpty`'s `{} ; rest ⇝ rest` (`Proves.empty`).  Unclaimed until the intrinsic refactor, when a program had no nested block (`docs/intrinsic.md`, M6a) |
| — | `Frames.pop .capture`, `Premise.unfold`'s `Ext` (the capture pop) | Lean only | the scope of the fresh `se`/`sp`/`ie` a rule declares (`T storage sp = nsp; v = sp.fld;`): popped after the rule's statements, so the rest `ω` is never re-typed (Gate G0's condition 6).  KeY's fresh program variables are global and need no end.  Printed as nothing (`Fml.show`, `Delab`), so a premise reads as the solkey taclet; `dl{ … }` inserts it (`RuleSyntax.lean`'s `schemaTacletCore`, under `open scoped Solidity.Schema`) |
| `localValueDeclInitDrop`, `storageLocalDeclInitDrop` | `Premise.bind` (`Stmt.step`'s `declLocal`/`declStorage` arms), `Fml.bind`, `Proves.bind`/`bindIntro` (the hidden binder) | Lean only (the binder) | `T v = e; ⇝ v = e;`: the declared local is put in scope by a binder ("for every value of `v : T`") in front of the assignment, printed as nothing, so the premise reads as solkey's `⟨[ v = e; ]⟩`; KeY's `\addprogvars(v)` |
| `memoryLocalDeclInitDrop` | `Premise.bind` at a memory type (`Stmt.step`'s `declMem` arm with an initializer), `Fml.bind` (the hidden binder) | Lean only (the binder) | `T memory mv = r; ⇝ mv = r;`, the binder as in the row above.  It ranges over the objects of `mv`'s type and over an unset `mv` (decision 17', `docs/intrinsic.md`), as an alias may be unset (`storageLocalDeclSkip`): no statement leaves a memory local unset, but the premise's `mv = r;` from an unset `mv` runs as the declaration does even where `r` allocates, which no existing object gives (`sound_declMemInit`).  A read through an unset memory local reverts (`State.memRefT`, `MPath.mvalT`), as through an unset alias |
| `revertDiamond` | `revertDiamond` | same | closes to `false`: a reverted run satisfies no diamond formula |
| `revertBox` | `revertBox` | same | closes to `true`. Only revert, send, transfer and try (`revertBox`/`revertDiamond`, `sendNoCallbackBox`/`sendNoCallbackDiamond`, `transferNoCallbackBox`/`transferDiamond`, `tryCallNoCallbackBox`/`tryCallDiamond`) and the loop invariant rules tell the modalities apart: the modality is a parameter of `Taclet`, so every other rule fires under either |

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
| `storageLocalDeclInitDrop`, `storageLocalRootRebind` | same names | same | |
| `storageLocalDeclSkip` | same | deviation | `T storage lsv; ⇝ {lsv := unset} ⟨[ ]⟩`, where KeY's `\replacewith` is the empty program: the alias is bound to no path (`Binding.unset`, `UpdElem.unset`), so a read or a write through it reverts, and a loop's next iteration does not see the previous one's binding.  solc rejects such a read statically; Lean only, the printer shows `lsv := unset`.  The update declares the alias (`Upd.decl lsv Rhs.unset`, `Rhs.unset`): the local is in scope after it, at its alias type, bound to no path |

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
| `memoryRootRebind` | same | same | `mv₁ = mv₂; ⇝ { mv₁ := mv₂ }`; a storage right-hand side is `memoryStorageCopy` |
| `memoryStorageCopy` | same | same | `mv = sp;` deep copy: fresh identity plus `copySt` |
| `memoryStorageCopyUnfold` | same | same | a complex storage path is captured first |
| `memoryLocalDeclInitDrop` | same | same | one generic decl-with-init split; the assignment rules take over |

## Memory field/index write & read

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `memoryFieldWrite` | `memoryFieldWrite`, `memoryFieldWriteCopy` | merged | Lean's sorts are not generic: a value source and a reference-path source are two rules |
| `memoryIndexWriteArray` | `memoryIndexWriteArray`, `memoryIndexWriteCopy` | merged | likewise; KeY's `inBounds`/`outOfBounds` split is the write's own bounds check, which reverts |
| `memoryFieldRead` | `memoryFieldRead`, `memoryFieldReadAliasRoot`, `memoryLengthRead` | merged | the same split on reads (a value lands on a local, a reference on a memory alias); `memoryLengthRead` is the member `length` (`Term.mlen`, KeY's `read(memory, mv, size)`) |
| `memoryIndexReadArrayValue` | same | same | KeY's `inBounds`/`outOfBounds` split is the read's own bounds check, which reverts |
| `memoryIndexReadArrayMemory` | same | same | likewise |
| `memoryFieldRead_unfold_rightFst` | `memoryFieldRead_unfold_rightFst`, `memoryLengthRead_unfold_rightFst` | same | |
| `memoryIndexRead_unfold_rightFst`, `memoryIndexRead_unfold_rightSndIndex` | same names | same | |
| `memoryFieldWrite_unfold_leftFst` | same | same | also claims the row below |
| `memoryFieldWriteMemRef_unfold_leftFst` | `memoryFieldWrite_unfold_leftFst` | merged | `msrc` is a value or a memory reference, one rule for both |
| `memoryIndexWriteCaptureAllComplexRecv` | same | same | `nmp[e1] = e2 ⇝ T se = e2; T memory mv = nmp; T ie = e1; mv[ie] = se` |
| `memoryIndexWriteMemRefCaptureAllComplexRecv` | same | find same | `… mv[ie] = mpath`: a memory path is a source as it stands |
| `memoryIndexWriteCaptureAllNonSimpleIndex` | same | find same | `mv[nse] = e ⇝ T se = e; T ie = nse; mv[ie] = se`: KeY rebinds the receiver (`T memory mv' = mv`); the receiver is already a simple memory local, typed by its position, so the rebinding would only rename it: left out to keep the rule text and its fresh names (a deviation in shape) |
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
| `localValueDeclInitDrop` | same | same | |
| `valueDeclSkip` | same | find same | `T v; ⇝ { v := defVal(T) } ⟨[ ]⟩`: KeY drops the declaration (`\addprogvars(v)`) and leaves `v` unconstrained; a Lean declaration is its default, as solc's |
| `localValueAssign` | same | same | terminal `v = se;` |
| `storageRootWriteValueRhsCapture` | same | same | `gsp = nse; ⇝ T se = nse; gsp = se;` |
| `fieldWriteValueRhsCapture` | `fieldWriteValueRhsCapture`, `memoryFieldWriteUnfoldSource` | same | the second is the memory instance |
| `indexWriteValueRhsCapture` | `indexWriteValueRhsCapture`, `memoryIndexWriteUnfoldSource` | same | likewise |

## Operators

One constructor per **shape**, not per operator: `op : BinOp` is a free
variable, so an instance is `binopAssignment (op := .add)`. The comparison and
boolean operators share the arithmetic constructors. The proof tree prints a
node of an operator family as KeY's taclet at its operator
(`RuleShapes.operatorOrder`, `keyTacletAt`): `binopAssignment` at `==` is
`boolEqualityAssignment`.

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
| `localAssign…`, `localDecl…` (8) | `localAssignIncrement` | merged | `v = lv⊕⊕;`; KeY has one taclet for the assignment and one for the declaration, Lean reaches the declaration through `localValueDeclInitDrop` |
| `storageRoot…Assignment`, `storageField…Assignment`, `storageIndexMapping…Assignment`, `storageIndexArray…Assignment` (8), `memoryField…Assignment`, `memoryIndexArray…Assignment` | `storageRootIncrementAssignment`, `storageFieldIncrementAssignment`, `storageIndexIncrementAssignment`, `memoryFieldIncrementAssignment`, `memoryIndexArrayIncrementAssignment` | merged | |

## Assert, require, if-then-else

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `assertConditionCapture` | same | same | |
| `assertSimple` | same | same | KeY's two branches: "Holds" `se = true ⟹ ⟨[ ]⟩` and "Violated" `se = true` (`Premise.check`, `Proves.check`); a failed `assert` panics (`Halt.panic`), which neither modality accepts (`Modality.afterRunTR`) |
| `requireConditionCapture` | same | same | the assert capture over `Stmt.require` |
| `requireSimple` | same | find same | reshaped: `require(se); ⇝ se = true ⟹ ⟨[ ]⟩ ; se = false ⟹ ⟨[ revert(); ]⟩`. KeY writes each goal as a disjunction, "Holds" `se = FALSE \| ⟨[ ]⟩ post` and "Reverts" `se = TRUE \| ⟨[ revert(); ]⟩ post`; for a `bool` each is the implication Lean's `.split` premise states with the condition in the context: KeY's two goals under either modality (`Proves.split`) |
| `ifElseUnfold` | same | same | also claims `ifUnfold` |
| `ifUnfold` | `ifElseUnfold` | merged | `Stmt.ite` always has both branches (an absent `else` is `[]`) |
| `ifElseSplit` | same | same | `if (se) thenStm else elseStm; ⇝ "if s#se true": se = true ⟹ ⟨[ thenStm ]⟩ ; "if s#se false": se = false ⟹ ⟨[ elseStm ]⟩`: a `.split` premise is the two-goal shape. The labels are the taclet's text (`Taclet.branchLabels`); the proof tree fills in `s#se` with the node's condition, as KeY's `NodeInfo.setBranchLabel` does (`if true true`). The derivation has KeY's two goals under either modality (`Proves.split`; `splitBox` in a walk is the same rule): the condition is a typed `bool`, so no third goal says it is one.  Also claims `ifSplit` |
| `ifSplit` | `ifElseSplit` | merged | |
| `ifTrue`, `ifFalse`, `ifElseTrue`, `ifElseFalse`, `ifElseNegated` | — | unclaimed | `concrete_solidity` strategy shortcuts. A literal is simple, so `ifElseSplit` applies (one goal assumes `true = false`); `!se` is not simple, so `ifElseUnfold` captures it. The table has no strategy |

## Payments

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `transfer_unfold_leftFstReceiver`, `transfer_unfold_rightSndArgument` | same names | same | |
| `transferNoCallbackBox` | same name | same | the box only, one terminal update (`UpdElem.pay`): `{ net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) } ⟨[ ]⟩`, solkey's `\if(sadr = self) \then(net) \else(storeSt(…))`, with no guard: the amount is read as a word by the element itself, which halts where it is not, as the interpreter does (`transferAt`). The arithmetic is KeY's `int`. Whether the world pays is the compiler theorem's (`Evm.compile_correct`), where a refused payment is a revert of the machine alone; the contract's own entry is never moved (`Evm.Sim.netSelf`) |
| `transferNoCallbackDiamond` | — | not ported | KeY's two goals, "non-negative amount" `0 <= se` and "transfer booked" (the box's booking under the diamond), have no counterpart: a payment under the diamond closes to `false` instead (`LeanTaclet.transferDiamond`, below), which is sound and proves less |
| `transferWithCallbackBox` | `CallbackTaclet.transferWithCallbackBox` | same | a constructor of `CallbackTaclet`, sound for the callback reading (`holdsC`), not of `Taclet`. The premise is `transferNoCallbackBox`'s booking `U`, read as KeY's two goals (`holdsC_transferCb`): `{U} I` ("invariant on exit") and `{U} {havoc} (I → [ ω ] φ)` ("resume after callback"; `{havoc}` is KeY's anonymising update, read by `ExecS.transferResume`). Used by `ProvesC` |
| `transferWithCallbackDiamond` | — | not ported | as `transferNoCallbackDiamond`: no diamond over a payment is derived |
| `send_unfold_leftFstReceiver`, `send_unfold_rightSndArgument` | same names | same | the transfer captures over `Stmt.send` (`pv = sadr.send(se);`, `pv` a `bool` local): the receiver first, then the amount, each into a fresh `uint se`, as for `transfer`. `bool ok = r.send(a);` is `bool ok; ok = r.send(a);`, so Lean fires `valueDeclSkip` where solkey fires `localValueDeclInitDrop` (same node count; the default is set, then overwritten by the send) |
| `sendNoCallbackBox` | same name | same | a `Premise.cases` with no formula goal and solkey's two labelled goals (`Proves.cases`): "send succeeded" `{ net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) ‖ pv := true } ⟨[ ]⟩` and "send failed" `{ pv := false } ⟨[ ]⟩` (KeY's `TRUE`/`FALSE`). Sound for the typed run, which is one of the two updates (`sendStep_sound`, `Calculus/SoundControl.lean`): `TRun.send` (`Semantics/Run.lean`) books and sets `pv` true when the transaction's oracle (`TxEnv.ext` at `sendKey`) has no entry or `ok`, and sets `pv` false otherwise. The calculus reads none of the oracle. The amount is read as a word by the `.pay` element, which halts on a negative amount where solkey's box books a credit (`docs/solkey-feedback.md` §7); `bool ok = r.send(a);` fires `valueDeclSkip` where solkey fires `localValueDeclInitDrop`. A `call{value:}` lowered to this rule (row below) is read without its callback, a deviation from solc |
| `sendNoCallbackDiamond` | same name | same | the box's two goals after "non-negative amount" `0 <= se`, the formula goal of `Premise.cases`. Sound for the same reason, unlike a diamond over `transfer`: a refused send returns `false` in the run, where a refused transfer reverts the machine. Lean does not need the formula goal for soundness (a negative amount reverts in `sendT` and in `UpdElem.pay` alike, so the "send succeeded" goal already fails there) and keeps it as solkey's goal |
| `sendWithCallbackBox` | `CallbackTaclet.sendWithCallbackBox` | same | a `CallbackTaclet` constructor whose premise is `sendNoCallbackBox`'s two updates, read by `ProvesC.send` as KeY's three goals (`holdsC_sendCb`): "invariant on exit" `{ net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) } I` under the box; "send succeeded" `{ net := … ‖ pv := true } {havoc} (I → [ ω ] φ)`, KeY's `{storage := storageSk ‖ net := netSk ‖ pv := TRUE}` with the booking written first, as for the transfer (the `{havoc}` overwrites it); and "send failed" `{ pv := false } [ ω ] φ`. The callback reading (`ExecS.sendHalt`/`sendFailed`/`sendViolated`/`sendResume`) lets every send fail, whatever the transaction's oracle says: the callee may revert, and what it did with it. Its deterministic run is one of these (`Stmt.exec_run`). The amount is read as a word by the `.pay` element, which halts on a negative amount where solkey's box books a credit (`docs/solkey-feedback.md` §7); `bool ok = r.send(a);` fires `valueDeclSkip` where solkey fires `localValueDeclInitDrop` |
| `sendWithCallbackDiamond` | — | unclaimed | as `transferWithCallbackDiamond`: the callback reading is the box's only |
| `(bool ok, ) = a.call{value: v}("")` | — | front end | not a taclet: solkey's parser lowers exactly this shape to `bool ok = a.send(v);` (`SolJSONParser.isValueCall`), and so does the solc import (`Frontend/SolcJson.lean`, `valueCall?`). **Deviation from solc**, solkey's as well: a value call forwards all gas, so the callee may re-enter and write storage; the send rules' no-callback reading (`holds`) is the EVM's only under the 2300-gas stipend of `send`, and a lowered value call is covered by the callback reading (`holdsC`, `sendWithCallbackBox`) alone (`docs/solc-alignment.md`) |

## External calls (`try`/`catch`)

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `tryCallNoCallbackBox` | same | same | one goal per clause (`Premise.branches`, `Proves.branches`): "call succeeded", "Error caught", "Panic caught", "other failure caught". KeY declares the return locals and the `Panic` code without an initializer, leaving them unconstrained; here they are bound under `∀` (`Fml.alls`, `Hyps.all`), since a Lean declaration is its default. `s#call` is an `ExtCall`, whose receiver and arguments are simple: the elaborator captures any other before the `try` |
| `tryCallWithCallbackBox` | `CallbackTaclet.tryCallWithCallbackBox` | same | read by `ProvesC.tryCall` (`holdsC_tryCb`): `I` where control leaves ("invariant on exit"), the success block after `{havoc}` and `I` ("call succeeded"), each `catch` block from where the call was made |
| — | `LeanTaclet.tryCallDiamond` | Lean only | a diamond `try` closes to `false`; solkey has no rule. The call may revert in the caller (no code at the address, data that does not decode), which no clause catches and no formula rules out |
| — | `LeanTaclet.transferDiamond` | Lean only | a diamond payment closes to `false`; solkey's diamond rules are not ported. Whether the world pays is the compiler theorem's, not the calculus's |

## Loops

solkey's loop taclets were added in `ed7849d5b6`, after the pinned
`1b4341a303`; `docs/loops.md`
gives their shapes and the stages that port them.

| KeY taclet | Lean | Status | Notes |
| --- | --- | --- | --- |
| `whileUnwind` | `LeanTaclet.whileUnwind` | bounded (past the pin) | `/// @custom:key unwind n + 1 while (cond) body` ⇝ `if (cond) { body; /// @custom:key unwind n while (cond) body; }`, KeY's `s#cond`, `s#body` as `cond`, `body`. solkey's strategy unwinds a loop with no specification without a bound; here the annotation counts the unwindings down (`LoopAnn.unwind`), so that symbolic execution ends. Sound by `Premise.sound_whileUnwind` (`TLoop.run_unfold`, `Calculus/SoundLoops.lean`). A `LeanTaclet` until the solkey pin moves past `ed7849d5b6`, then a `Taclet` |
| — | `LeanTaclet.loopExit` | Lean only | a loop at its bound (`unwind 0`, the annotation of a loop with no clause): a check (`Premise.check`, `Proves.check`; walk: `apply checkLean r`), "loop exited" the rest with `cond = false` assumed, "unwound to the end" `cond = false` (`Fml.eqD`, so a condition that halts is not false). Sound by `Premise.sound_loopExit`. Not `assert(!cond)`, which would make running out of unwindings a panic of the program |
| `whileInvariantBox` | `LeanTaclet.whileInvariantBox` | ported (past the pin) | `[ /// @custom:key invariant inv while (cond) body; ]` ⇝ "invariant initially valid": `inv = TRUE`; "invariant preserved and used": `{anon(body)} (inv = TRUE → { b := cond } (b = TRUE ⟹ ⟨[ body ]⟩ inv = TRUE ; b = FALSE ⟹ ⟨[ ]⟩))`. KeY's `s#b` (`bType b = cond;`) is a fresh local (printed `se`), `#loopAnon` is `{anon(body)}` (`Fml.anonHavoc`: `{anon(xs)}` of the body's frame `Prog.frame`, with `{havoc}` when the body writes storage or pays). `TRUE` is `Fml.eqD` (defined and equal). Premise `Premise.inv`; in a walk the scoped `Proves.inv` (a `Proves` step by `Taclet.toStep`; `apply invBox r`, `apply invLean r` under the diamond), its goals `init`, and `thn`, `els` past the context's `{anon(body)}` (`Hyps.anonHavoc`): solkey's two goals. A condition, invariant or variant that needs a capture (a call, a cast, a narrow operation, a constructor, an `++`) is refused at elaboration (`loopExpr`), where solkey evaluates it per iteration. Sound by `Premise.sound_whileInvBox` (`Calculus/SoundLoops.lean`, `TLoop.run_induct`) |
| `whileInvariantDiamond` | `LeanTaclet.whileInvariantDiamond` | ported (past the pin) | the box's premise with `{ variant := dec ‖ b := cond }` and the body's postcondition `inv = TRUE ∧ { b := cond } (b = TRUE → 0 <= dec ∧ dec < variant)`: KeY's skolem `variant` a fresh local (printed `ie`), the variant checked only where the condition holds again. Lean reads `dec` where KeY compares it, so it must be defined where the invariant holds; and under the diamond the cover (`b` is `TRUE` or `FALSE`, `Premise.inv`). Sound by `Premise.sound_whileInvDiamond` (`TLoop.run_variant`) |
| — | `LeanTaclet.whileClose` | Lean only | a loop with an invariant whose body has no frame (`Prog.frame`: it writes memory, pushes, pops, rebinds an alias or calls out), under either modality, closes to `false`: sound, and nothing about it is derived. solkey refuses only memory-writing bodies (and unwinds them); a push, a pop or a call it frames as writing storage and the ledger, so those refusals are Lean's own (`Stmt.within`) |
| — | `LeanTaclet.whileNoVariantDiamond` | Lean only | a loop with an invariant and no `decreases` closes to `false` under the diamond (solkey unwinds it). `Stmt.inSolkey` is `false` on every loop |
| `LoopLowering` (meta-construct) | `lowerLoops` (`Syntax/Elab.lean`) | elaborator | `break`/`continue`/`return` in a loop to the flags `brk`/`cnt`/`ret`, `for` and `do … while` to `while`, shape for shape |

## Function contracts

| solkey | Lean | Status | Notes |
|---|---|---|---|
| `useContract_g` (planned: one per specified function, behind `functionTreatment:contract`; not at the pin) | `useContract` (`Calculus/FunContract.lean`) | ⊢ rule | a derived theorem, sound from the typed run (`useContract_of_valid`, from `FunContract.ofValid`), not a `Taclet`. Goals "pre" `[ params := args ] requires` and "post" `[ params := args ] {old := storage ‖ oldNet := net} {havoc} ∀ T r. (ensures → [ res = r; ..ω ] φ)`, `{havoc}` for a `nonpayable` callee only (`Fml.anonC`; `pure`/`view` by `Prog.within`). Box only |
| the obligation `requires -> [g(args)@C] ensures` (planned) | `FunContract.obligation` (the formula), `FunContract.ofValid` (a contract from its proof) | — | over the callee's block `T r; body`, the parameters free; `ensures ∧ typed(r)` (KeY's `inUInt(result)`) |

## Update algebra (`updateRules.key`)

An update is a term (`Upd C Γ Δ`, a list of `UpdElem`s read against the
pre-state), so KeY's update rules are rules here too: `UpdRuleS` in
`Calculus/UpdRuleScoped.lean`, each one way over the typed state
(`UpdRuleS.sound`; why not both ways is its docstring's "One way"), at the
positive positions of a formula; on sequents they are `Proves.merge` and
steps derived from `Proves.closeHolds` (`Calculus/UpdateRules.lean`), usable
with the program still to run. A side condition KeY's rule lacks exists
because a term here can halt and KeY's cannot, or because a local is a
position (`Calculus/UpdRuleScoped.lean`, "What the scope changes").

| KeY rule | Lean | Status | Notes |
| --- | --- | --- | --- |
| `sequentialToParallel1-3` | `UpdRuleS.sequentialToParallel`, `Proves.merge`; + under a branch (`FmlRw.mergeIn`) | done | `{u}{u2}φ ⇝ {u ‖ {u}u2}φ`.  On the sequent (`Proves.merge`, `Calculus/Proves.lean`; read as `refine merge rfl ?_` and `Proves.mergeStorage`, `core_merge`): one rule for both rows, `{U}{V}φ ⇝ {W}φ` with `W = Upd.seqPar U V` (`Calculus/Graft.lean`): `V`'s locals read as `U` leaves them (`Upd.held`), the rest as in the row below.  **Lean only:** it merges past the hidden binders between the two updates (`Hyps.binds`), the earlier update moved under them (`Upd.liftBinds?`, scope ends included), which KeY, with no binders, does not need.  **On a chain's scoped line** while the program is open: the spine's merge (`Fml.mergeRun`, `Calculus/Merge.lean`), one over a storage write, a memory write, or locals then a memory write (`FmlRw.stateMerge`, `MergeNameS`: `Upd.mergeSt?`, `Upd.mergeMem?`, `Upd.mergeMemL?`, `Calculus/StatePartsScoped.lean`), and one under `∧`, `→` (`FmlRw.mergeIn`, `Calculus/RewriteScoped.lean`); `sol_merge` on a scoped goal: `Fml.simpUpdsS` (`Calculus/UpdRuleScoped.lean`), past hidden binders too (`Fml.mergeB`); one direction each.  `UpdRuleS.sequentialToParallel` is the taclet's shape (`Upd.seqPar`); `sol_upd .sequentialToParallel` is the **Lean-only** `UpdRuleS.mergeHidden` (`Fml.mergeB`: through hidden binders, the scope ends after absorbed, `UpdRuleS.absorbPops`) |
| `sequentialToParallel1-3` over a storage write | `Proves.merge` (spelled `refine Proves.mergeStorage ?_`) | done | `{storage := s}{V}φ ⇝ {storage := s ‖ {storage := s}V}φ`: `V`'s `storage` is replaced by the storage `U` last wrote (`Upd.lastSt`), where `U` writes no other global part, sound because a storage term changes only the storage of the state it is read in (`Tm.eval_st_glob`); any other merge reading the global part needs `U` to write none (`Upd.envOnly`), else it is refused |
| `sequentialToParallel1-3`, a chain's line past the program | `FmlRw.mergePast` (`Calculus/RewritePast.lean`) | done (W9.4) | the scoped line's spine merged, `n + 1` updates from a position, innermost first (`Fml.mergeRunP`); through a hidden binder the binder absorbed into the update that sets its local before reading it (`Upd.absorb`, `holds_bind_absorb`), else the update moved under it (`Upd.liftG?`), else every binder absorbed (`Fml.absorbAllMergeP`: a local its update sets after declaring others is declared first, which reorders the printed parallel update, a Lean-only deviation); a storage write a later one shadows dropped (`Upd.dropSh`) |
| `sequentialToParallel1-3`, read backwards | `Fml.prepS` (`Calculus/LeafDerive.lean`) | Lean only | `sol_prove`'s leaf closer (W9.3) reads two parallel elements and the allocation's pair as they are (`ElemS.parOk`, `pairLS`), so nothing splits them; a leaf the fragment does not read is prepared (`Fml.prepS`, `holds_of_prepS`): a push with its returned alias split into the push and then the alias (`Upd.pushSplit`, `holds_push_alias`), and, **Lean only**, a hidden binder of a value read as the `∀` it is (`Fml.bindAsAll`) |
| — (KeY keeps an update on its formula) | `Proves.updIntro` | arch | `⟹ {U} φ` becomes `{U} ⟹ φ`: the update joins the context, where every rule reads it, the sequent KeY writes with the update on the formula. A specification's `{ old := storage }` enters the derivation so |
| `applyOnElementary`, `applyOnParallel` | `Tm.substH`, `UpdElem.substH`, `Upd.graft` (`Calculus/Graft.lean`) | functions | `{u}` pushed into right-hand sides |
| `applyOnPV`, `applyOnPVLastInParallel`, `applyOnDifferentPV`, `applyOnDifferentPVLastInParallel` | `Upd.held` (`Calculus/Graft.lean`), `Fml.substU` | functions | the last write of a local wins; an unwritten local is kept.  On a chain's scoped line while the program is open, where the update is not applied whole: `FmlRw.applyOnPV` (`Calculus/RewriteScoped.lean`), a local the update leaves holding a literal (`Upd.held`, `Held.litVal?`) read as that literal in the atoms of the propositional skeleton below it, the update kept in front; one direction (`Fml.applyOnPVTop_sound`) |
| `simplifyUpdate1-3` | `UpdRuleS.simplifyUpdate`, `Proves.simplify` (`Calculus/UpdateRules.lean`) | done | under the box, the elements of the last update that set a local the update pops later are dropped (`Upd.simp`), derived from `Proves.closeHolds`.  Shadowed writes (`Upd.simpS`, `Calculus/UpdRuleScoped.lean`): a write a later one to the same local overwrites goes (`Upd.unsetAt`), and a declaration so overwritten takes the later right-hand side (`Upd.redecl`), any element under the box, one that cannot halt under the diamond (`holds_upd_shadow`); `UpdRuleS.simplifyUpdate` is the taclet's shape (`{u}φ ⇝ {u.simpS m}φ`); `sol_upd .simplifyUpdate` is the **Lean-only** `UpdRuleS.absorbPops` then it (`Fml.simpAt`, `Fml.simpAt_rule`), and on a chain's scoped line `FmlRw.simplifyUpdate` (with the scope ends after the update merged in first where the line under it is an update).  The walks are recursors with `match` twins (`Upd.shadow`/`Upd.shadowM`, `Upd.unsetAt`, `Upd.redecl`).  **Not yet** while the program is open: an element setting a local the formula does not read, which needs the formula strengthened out of that local's scope (past the program, the row below) |
| `simplifyUpdate1-3`, a chain's line past the program | `FmlRw.simplifyPast` (`Calculus/RewritePast.lean`) | done (W9.4) | every declaration nothing reads afterwards dropped with its writes (`every`, `Upd.thinIO`, `Fml.thinS?`), else the ones the update ends itself; the scope ends after it merged in where the line under it is an update (`Fml.absorbIf`); a hidden binder in front absorbed or dropped (`Fml.dropBindTop`); a dropped write must not halt (`Rhs.totalB`) |
| `applySkip1-3`, `applyOnSkip` | `UpdRuleS.applySkip` | done | `skip` is `[]`; for a formula with no modality (`Fml.modalFree`, `holds_congr_reads`) |
| `parallelWithSkip1-2` | — | arch | `‖` is `++`, `skip` is `[]`: nothing to rewrite |
| `applyOnRigidFormula` | `UpdRuleS.applyOnRigid` (`Fml.substU`); + through `∧`, `→`, `¬` (`FmlRw.applyOnRigid`, `Calculus/RewriteScoped.lean`) | done | one direction (`UpdRuleS.sound`), for an update that cannot halt (`Upd.totalB`) or under the box.  On a scoped line while the program is open: `FmlRw.applyOnRigid`, one direction, for an update that cannot halt (`Upd.totalS`) or under the box; the first-order parts applied (`Fml.substU`), the update kept in front of the rest (`Fml.pushS`) |
| `applyOnRigidFormula`, under the box | `Proves.applyOnRigidBox`; `sol_apply_upd` | done | one direction, **no totality premise**: the last update of the context is applied to a first-order goal and dropped (`Fml.substU`, `Tm.denote_substH`), for a goal reading no global part the update writes; a halting box update proves what follows; derived from `Proves.closeHolds`.  On a chain's scoped line while the program is open, `~[applyOnRigidBox]~>` is `FmlRw.applyOnRigid`: under the box any update, under the diamond or `m` one that cannot halt (proposal 105); `~[applyStorageBox]~>` is `FmlRw.applyStorageBox`, the box's only and an update of the storage and locals only (`Fml.pushStAt`, `Upd.stOnly`) |
| `applyOnRigidFormula` on a lone storage write, a chain's line past the program | `FmlRw.applyStorageBoxP` (`Calculus/RewritePast.lean`) | done (W9.4), box only | `{storage := S}_□ φ ⇝ φ[S/storage]` for a first-order `φ` (`Fml.substSt`, the storage merge's `Tm.substP`) |
| `elimSelfUpdate*` | — | not ported | commented out in KeY (`Calculus/UpdRuleScoped.lean`) |
| `simplifyIfThenElseUpdate1-4`, `commuteSimpleUpdates` | — | arch | commented-out dead code in KeY |

### Closing the first-order goal

What symbolic execution leaves is closed by first-order steps derived from
`Proves.closeHolds` (`Calculus/UpdateRules.lean`), each needing a context with no
diamond (`Hyps.boxOnly`). A program comparison produces `Fml.eqD a b` —
`defined(a) ∧ defined(b) ∧ a ≐ b` — because a term here can halt; `a ≐ b`
(`Fml.eq`) is the total Theory equation, KeY's `=`.

| KeY rule | Lean | Status | Notes |
| --- | --- | --- | --- |
| — | `Proves.closeHolds` (`Calculus/Proves.lean`) | Lean only | with no modality left anywhere in the sequent (`Fml.modalFree`), what is left is proved over the typed reading (`holds`).  Every step after the program (`Calculus/UpdateRules.lean`: `andSplit`, `eqDSplit`, `definedWritten`, `definedLit`, `eqRefl`, `eqClose`, `eqDClose`, `applyOnRigidBox`, `simplify`) is derived from it; `rewrite` is a rule (`Proves.rewrite`), and `Proves.rewrite'` only writes its result out |
| `close` on `I ⟹ I` (`propRule.key`), at a callback's resume | `Proves.assumeInv` (`Calculus/CallbackSound.lean`) | done | the invariant assumed past a frame end that drops every local (`…, {havoc}, I ⟹ I`) is the goal past the program's scope ends: both the same closed first-order formula (`Fml.closedB`, `Frames.popsOnly`), the scope ends printing as nothing; derived from `Proves.closeHolds` |
| — | `Proves.openInv` (`Calculus/CallbackSound.lean`) | Lean only | at a leaf, each assumed invariant past its frame end is read at the scope it is assumed in (`Hyps.openInv`, `Fml.reclose?`), a closed first-order formula the closer reads; KeY's invariant is a formula over global symbols and needs no reopening.  Derived from `Proves.closeHolds` |
| — (KeY's anonymising update `{storage := storageSk ‖ net := netSk}`, its skolem constants fresh) | `CloseS.holds_havoc` (`Calculus/CloseScoped.lean`), `Close.State.havoc_eq_mk` (`Calculus/CloseLemmas.lean`), `close_rw_s` | Lean only | `{havoc} φ` read as `φ` for every storage `st` and ledger `nt` (universally bound in place of fresh skolems); the state written as `State.mk` so that `getEnv_mk`/`readAddr_mk` read its locals and heap; a snapshot `old`/`oldNet` taken before it is a local and keeps the storage it took |
| `findOnSave` (a scoped leaf) | `CloseS.wp_box_write`, `wp_box_write_prim` (`Calculus/CloseFrame.lean`), `close_rw_s` | done (W9.8.4) | a box write names the storage it leaves: `find(st', r)` is the written value (`Storage.writeVal`: a word itself, a struct overlaid on what was there) |
| `findOnSaveFrame`, `lenOnSaveFrame` (a scoped leaf) | `CloseS.wp_box_write`: `Storage.find_save_frame`, `len_save_frame`, `checkIndex_save_frame` | done (W9.8.4) | a read, a length and an index check at a path diverging from the write's (`StValue.diverges`) read the storage before it; below the written path by `Path.append` |
| `findOnDelAt`, `findOnDelAtFrame` (a scoped leaf) | `CloseS.wp_box_delete` (`Calculus/CloseFrame.lean`) | done (W9.8.4) | the deleted path reads its default (`SVal.dflt`), a diverging path the storage before |
| `readOnWrite` (a scoped leaf) | `CloseS.wp_box_writeT`, `Grown.writeT_facts`, `MAddrT.apart_resolve` (`Calculus/CloseFrame.lean`) | done (W9.8.4) | a memory write reads back at its address and leaves an address apart from it (`MAddrT.Apart`) unchanged |
| `copyStToMem`/`copyMemToSt` member reads (a scoped leaf) | `SVal.copyStToM_field`, `MVal.copyMToSt_field`, `CloseS.readId_copySt_field`, `copyMToSt_find_field` | done (W9.8.4) | a member of a copy reads the member copied, by the erasure (`Close.copyStToM_member`, `Close.copyMem_member`) |
| — (a total path in a diamond) | `CloseS.wp_diamond_write_total`, `wp_diamond_delete_total`, `wp_find_total` (and `_root`), `Storage.write_ne_none_total` | Lean only (W9.8.4) | a write, delete or read at a path with no index (`Path.total`) does not halt, so a diamond leaf reads it as the box does; a deployment's storage (`Storage.find_init_total`) likewise |
| `selectOnEmptyStorage` at a root and below it (a deployment's storage) | `CloseS.find_init_ofRoot`, `CloseS.find_init_append` (`Calculus/CloseFrame.lean`), `close_rw_s` | done (W9.8.4) | the typed empty storage (`Storage.init`) reads a root, and a path through no array slot below it (`Path.total`), at its type's default (`Storage.find_init_total`) |
| — (an index checked at a mapping root; a checked index) | `CloseS.atT_map_root`, `CloseS.atT_bind` (`Calculus/CloseScoped.lean`), `close_rw_s` | Lean only (W9.8.4) | a key of a mapping at a root is always a slot (the check passes), so two reads of `balances[0]` name one reference; any other index is its check, then the slot's reference: the typed `Storage.atT` unfolded so the closer compares references |
| `storeSt`/`selectSt` on the ledger (`netHeader.key`) | `Close.lookupBy_setBy_int` (`Calculus/CloseLemmas.lean`), `close_rw_s`, `close_rw` | done | a ledger entry after a write: the written amount at that address, the old entry elsewhere, the entries KeY `int`s (`Srt.kint`) |
| — (a push's room under the diamond) | `roomM` (`Calculus/DecideScoped.lean`), `roomM_holds`; the closer's `Facts.narrowS` (`Calculus/Closer.lean`) | Lean only (W9.8.5) | a diamond's reduction keeps a push's room, `len(s, q) < 2^256 - 1 = true`, as a premise of what follows the update (an update that returns had room, one with none is out of gas); the closer narrows a guarded length below its guards by that bound (`LTerm.unseq`). KeY's `int` lengths need no room |
| `eqClose` | `Proves.eqRefl`; `Proves.eqClose` (`v ≐ v`), `Proves.eqDClose` (`v = v`); on two literals in a chain, `FmlRw.concrete` (`Fml.litCS`) | done | `t ≐ t` for any term, halting or not (`StValue.Equiv.refl`); `v ≐ w` for distinct literals folds to `false` |
| `concrete_and_1-4`, `concrete_impl_1-4`, `concrete_not_2` | `FmlRw.concrete` (`Calculus/RewriteScoped.lean`, `Fml.concreteAlongS`) | done | on a chain's scoped line while the program is open: `true ∧ A ⇝ A`, `false → A ⇝ true`, `A → false ⇝ ¬A`, `¬false ⇝ true`, …, bottom-up through `¬`, `∧`, `→`, `false` being `¬true`; `concrete_not_1` (`¬true ⇝ false`) rewrites nothing |
| `andRight` | `Proves.andSplit` | done | |
| — | `Proves.eqDSplit` | Lean only | `a = b` from `defined(a)`, `defined(b)`, `a ≐ b`: `Fml.eqD` unfolded |
| — | `Proves.definedWritten` (`Calculus/UpdateRules.lean`) | Lean only | `defined(x)` for any `.val` local, behind a context with no diamond (`Hyps.boxOnly`), with **no update asked**: a typed local always holds a value of its type, which KeY's `defined` does not need |
| — | `Proves.definedLit`; `FmlRw.concrete` (`Fml.litCS`: `defined(v) ⇝ true`) | Lean only | a literal is defined |
| any theory taclet on a sequent | `Proves.rewrite` (`Calculus/Proves.lean`, a rule), `rw [r]`/`sol_rw` (`Calculus/RewriteSyntax.lean`) | done | a term taclet `r : TermTaclet t t'` (`Calculus/TermLib.lean`) or a `Tm.Theq` at the empty scope rewrites every closed side of an equation of the sequent's preconditions and goal reading `t` there (`Tm.closedAs`; `Hyps.rwEqC`, `Fml.rwEqC`, `Calculus/SeqRewrite.lean`), a modality open or not, `core_rw`; `TermTaclet.sound` proves each rule once, from its Theory lemma; decision 90 |
| the same, inside an update | `Proves.updRw`, `sol_rw` | done | an update's right-hand side runs in the interpreter, so the rewrite asks `Tm.EvalRefines t t'`, which a Theory equation onto a literal gives (`Tm.EvalRefines.of_theq`); on the **last** box update of the context only, its closed occurrences of `t` read at the empty scope (`Upd.rwC`, `holds_upd_rwC`, `core_rw`); on a chain's scoped line while the program is open, any box update of its spine (`FmlRw.lawUpd`, `Calculus/RewriteScoped.lean`, a `TermTaclet`) |
| the same, inside an update, on a chain's line past the program | `FmlRw.lawUpdS` (`Calculus/RewriteLaws.lean`) | done (W9.4), any modality | a term taclet (`TermTaclet`), a memory law (`EvalLaw`) or a literal law (`LitLaw`) at an update's right-hand sides, its two sides read at the update's scope (`LawPair`); exact where the update holds the write it reads back (`LawCov.covered`, `Upd.covers`; `LawCov.ref`, `Upd.coversRef`; `LawCov.eval`, `Upd.coversEval`) or member-wise (`LawCov.eqv`, `Tm.sameBase`) (`Calculus/TermLaws.lean`) |

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
| `closeFalse` (in the closer), `replace_known_left` | closer clauses `Facts.refute`, `Facts.apart` | subsumed | a premise refuted (two literals apart, a side that halts, a pair the premises keep apart) closes the leaf |
| `cut`, `cut_direct` on a `bool` | closer clause `Facts.split` | subsumed | a case split on a `bool` local or a condition compared with a literal |
| `selectOnShape{Struct,Element,Member,Size}`, `wfFixedSize`, `wfDynSize`, `wf{Fixed,Dyn,Map}Elem` | closer clauses `LPath.ty`, `Facts.retsW`, `Facts.halts` | subsumed | under `wt(storage)` a read at a path the layout types returns, of its type's kind; a test for a shape the layout says is not there halts |
| `sizeNotNegative` | closer clause `Facts.lo` | subsumed | a length is at least `0` (`values.length + 1 > 0` after a `push`), KeY's `\add(0 <= selectSt<[int]>(st, size) ==>)`. The closer does not read the slot at `(len + 1) - 1` after a `push` as the one pushed (`storagePushReadBack`, valid in the model, stays underived: `divergent` in `tests/solkey/expected.tsv`) |
| `findDefinition*`, then `selectOnSaveCons` (`a1 = a2` down the written path, `a1 ≠ a2` off it), `saveOnEmptyPrim` at the word | `.save` arm of `LStor.readU`: `cmpSegs`, then `saveLeaf` (`Calculus/Decide.lean`) | subsumed | the read compared with the write a segment at a time (`cmpSegs`; two keys the terms do not settle, `keyCmp`, are one `kite`): the word written where the paths are equal (`.eq`), the old read where they diverge (`.diverge`); above or below the word the read halts (`.err`, Lean only: a struct is no word, a word has no members). `save_readU_sim` (`findLive_saveLive_same`, `findLive_saveLive_diverge`, `save_through`); the Theory's `findDefinitionCons`, `selectOnSaveCons`, `saveOnStoreCons` (`Theory/Storage.lean`) |
| `selectOnDelAtCons`, then `delFieldDefault`, `delFieldRef`, `delFieldMap`, `delFieldFixed`, `selectStDelNode{Map,Ref,Fixed,Element,Member,Size}`, `selectStDelNodeFixed{Element,Size,Value}` below the deleted node | `.delAt` arm of `LStor.readU`: `cmpSegs`, then `delLeaf` and `delBelow` | subsumed | at the deleted path the old word's default (`.zero`); below it, through a member the deleted value's member, at a key the old entry where the node above is a mapping (`selectStDelNodeMap`), the reset element where it is a fixed-size array (`selectStDelNodeFixedElement`), and nothing where it is a dynamic one, which is emptied; apart, the old read. The node's kind is a test on the storage below (`mapU`), not the field's sort. `del_readU_sim`, `delBelow_sim`; the Theory's `selectOnDelAtCons`, `find_delAt_same`, `find_delAt_below` |
| — (Lean only: KeY's reads are total, the interpreter's halt where a location is not there) | `.save`/`.delAt` arms of `LStor.hasU` (`saveHas`, `delHas`) | Lean only | a write leaves its path and every location above it there, none below a word; a delete as `delBelow` walks it below the path; apart, as before. `save_hasU_sim`, `del_hasU_sim` |
| `selectOnDelAtCons`, `selectStDelNodeSize` (with `fixed`) and `selectStDelNodeFixedSize` at `size` | `.save`/`.delAt` arms of `LStor.lenU` (`saveMap`, `delLen`, `lenEnd`) | subsumed | a write keeps the length of every array above it; a delete leaves a fixed-size array's length (`selectStDelNodeFixedSize`) and a dynamic array's `0` (`selectStDelNodeSize`) at its path, as `delBelow` walks it below. `save_lenU_sim`, `del_lenU_sim` |
| — (Lean only: KeY reads a mapping or a fixed-size array off the field's sort, `MapField`/`FixedField`) | `.save`/`.delAt` arms of `LStor.mapU` (`saveMap`, `delMap`) | Lean only | the kind of the node at `Q`: a write keeps the shape of every location above it, a delete the shape of its default. `save_mapU_sim`, `del_mapU_sim` |
| — (Lean only: KeY's `save` and `delAt` are total, the interpreter's halt) | `.save`/`.delAt` arms of `LStor.okE`, the run guard | Lean only | the write returns where the storage below does, the value written and the path return, and the location is there (`hasU`); a write through a `length` segment is kept whole (`.sok`). `save_okE_sim`, `del_okE_sim` (`save_ok_iff_find_ok`). `LStor.cpokU` passes a word written over a word (its row is with the memory clauses below) |
| `selectOnSaveCons` on a `size` write, `selectOnDelAtCons` past the end | `LStor.arr` with `arrKey`, `arrRead`, `arrLength` (`Calculus/Decide.lean`) | subsumed | a read below a pushed or popped array compares its index with the old length: the pushed word or default there, the old element below it; the length after is the old one plus or minus one, counted unchecked |
| `selectOnSaveEmptyRef`, `selectOnSaveEmptyFixed`, `selectOnSaveEmptyIndexStruct`, `selectOnSaveEmptyIndexPrim`, `selectOnSaveEmptyMember`, `selectOnSaveEmptySize` | `LStor.copy` with `copyLeaf`, `copyKeys`, `overlay_findLive_nomap` | subsumed | a read below a copy reads the source, through members and key by key (an element of a fixed-size or dynamic array, as solc's element-wise copy leaves it); the target's elements past the source's length are past the end |
| `selectOnSaveEmptyMap` below a key of a copy | `copyKeys` | partly | where the source has a mapping at a key, the read is kept whole (a mapping met in both keeps the target's entries); a copy of a well-typed program meets none, solc rejects it |
| `selectOnDelAtCons`, `selectStDelNodeRef`, `selectStDelNodeMap`, `selectStDelNodeIndexStruct`, `selectStDelNode{Element,Member}` on the slot a `push()` of a struct or an array recycles | `LStor.slotU` with `delLeaf` (`Calculus/Decide.lean`) | subsumed | after a `pop` of the same array, the element it removed, cleared (kept for an array of mappings); after a `delete` of the array, its old first element, cleared; over any other write the read is kept whole |
| `selectOnShape{Struct,Element,Member}`, `selectStDelNode{Element,Member}`, `selectOnDelAtCons` (`a1 ≠ a2`, a `delete` at another root) on that slot of the initial storage | closer clauses `Facts.slotTy`, `Facts.slot_find`, `Facts.slotIn` | subsumed | a read below the slot a `push()` takes, of an array of the initial storage or of it after its `delete`, with `delete`s at other roots below it (`Facts.offDel`), or below an element up to the old length, is typed by the element type: canonical under `wt(storage)`, a default where the type's structs are canonical (`defaultForTy_canonB`); it returns where the index is at most the old length |
| `storageFieldWriteSave`, `storagePushValueSave` with `sp` a stale alias: through an index, bound before the storage last changed (`SymB.stale`), dangling after a `pop` or still live | `SymB.stale`, `Tm.staleWriteS`, `LStor.stale` (`Calculus/Decide.lean`) | subsumed | KeY's `consr(sp, at(ie))` names a slot, checked only when `storageIndexReadArrayBindLocalRoot` bound it: the alias keeps its slot-level path, and a write or a push of a word through it is KeY's plain `save` there (`staleSave`); exact by `RelU.stale_write`, `RelU.stale_push`; the Theory's `save` is `SVal.abs_save` (`Theory/Bridge/Save.lean`), the push `State.abs_pushAt_const` (`Theory/Bridge/Push.lean`) |
| — (Lean only: KeY's `save` is total, the interpreter's halts where the slot is not there) | the run guard `staleOk` in `LStor.okE` | Lean only | the write returns where the live location does (`hasU`; a push, where the live array has the operation, `arrOk`), or where the index is the array's length and the first slot past the end has the location (`slotHasU`; a push, an array there, `slotLenU`); elsewhere the guard is the write itself. `stale_okE_sim`, `staleOp_okE_sim` (`save_ok_of_find_ok`, `find_past_end`) |
| `selectOnSaveCons` (`a1 = a2`, `a1 ≠ a2`) under a word written through a stale alias | `.stale none` arms of `LStor.readU`, `hasU`, `lenU`, `mapU` with `staleRead`, `staleHas`, `saveMap` | subsumed | as after a live write, but the word is guarded by the old location's presence; `stale_readU_sim`, `stale_hasU_sim`, `stale_lenU_sim`, `stale_mapU_sim` by `Calculus/SlotLemmas.lean`'s `findLive_save_live`, `findLive_save_prefix`, `findLive_save_diverge`, `findLive_save_above`, `findLive_save_below`, `save_cons_shape`; the Theory's `selectOnSaveCons`, `saveOnStoreCons` (`Theory/Storage.lean`) |
| `selectOnSaveCons` on the `size` write of `storagePushValueSave` through a stale alias | `.stale (some op)` arm of `LStor.lenU` (`arrLength`) | partly | where the slot path is live the push is the live one and the length is `.arr`'s (`staleOp_live`); where it is not, a read at or below it halts on both sides, above or apart it is the old one (`staleOp_lenU_sim`; `findLive_save_live`, `findLive_save_prefix`, `findLive_save_diverge`, `save_cons_shape`); the other readers keep a read through such a push whole; the Theory's `selectOnSaveCons` (`Theory/Storage.lean`), the push `State.abs_pushAt_const` (`Theory/Bridge/Push.lean`) |
| `storagePushLengthSaveReferenceElement` (`size ≠ at(n)`: the recycled slot is the old one), then `selectOnSaveCons` at a write through a stale alias | `.stale` arms of `LStor.slotU`, `slotHasU`, `slotLenU` | partly | the slot compared with the written location: the word where it is the slot's location, the old slot where a word write is apart (through a push apart from the slot, the read itself); through a push at the slot, the word at the old length (`slotLenU`, kept by `orElse` with the read itself) and the length one more. `stale_slotU_sim`, `stalePush_slotU_sim`, `stale_slotHasU_sound`, `stale_slotLenU_sound`, `stalePush_slotLenU_sound` by `findLive_save_past_end`, `find_slot_head`, `find_save_diverge_tail`, `apply_push_find`, `apply_push_findLive_array`; the Theory's `selectOnSaveCons` |
| `storagePopSave`'s `delAt(at(n-1))`, then `selectOnDelAtCons`, `delFieldIndexStruct`, `selectStDelNode{Element,Member}`, on that slot | `pop` arms of `LStor.slotHasU`, `slotLenU` with `delHas`, `delLen` | subsumed | as `slotU`'s, the location and the length of the popped element, cleared or kept; `pop_slotHasU_sound`, `pop_slotLenU_sound` (`AOp.apply_pop_eq`, `delSlotHas_sim`, `delSlotLen_sim`); the Theory's `selectOnDelAtCons`, `delFieldIndexStruct`, `selectStDelNodeDefault` (`Theory/Storage.lean`) |
| `selectStDelNodeIndexStruct`, its `iv ≥ size` branch | `slotU`'s `.delAt` arm at old length `0`, where the storage holds a stale write | subsumed | a `delete` of an empty dynamic array keeps its slots past the end (`defaultOf_array_nil`); `del_slotU_sim`; the Theory's `selectStDelNodeKeep` (`keepsOnDelete` past the length, `Theory/Terms.lean`) |
| `selectOnSaveEmptyIndexStruct`, branches 2 and 3, under the folded copy of `storageRootWriteCopySource` or `storageFieldWriteCopySource` | `slotU`'s `.copy` arm, where the storage holds a stale write | partly | below the old length the old element there, cleared; at it the old slot (branch 3 only at the new length equal to the old one, the first slot past the old end; a longer copy keeps the read whole); where a length does not return, or the new one is longer, the read itself. `copy_slotU_sim` by `overlay_shadow_lt`, `overlay_shadow_eq`; the Theory's `selectOnCopyIndexClear`, `selectOnCopyIndexKeep` (`Theory/Copy.lean`). A copy within one storage has its guard checked once (`LStor.okE`) |
| `findDefinitionSize`, then `selectOnSaveCons` on `size`, below a recycled array | `arrLength`'s slot (`LStor.slotLenU`, kept by `orElse` with the read itself), where the storage holds a stale write | subsumed | `arrLength_sim`, `arr_lenU_sim`, `LStor.slotLenU_sound` (`apply_push_find`, `slot_head_diverge`); the Theory's `findDefinitionCons`, `selectOnSaveCons` (`Theory/Storage.lean`) |
| `selectOnShapeSize`, `wfFixedSize`, `wfDynSize` below the slot a `push()` takes | closer clauses `Facts.retsW` (`.len`, `tyArr`), `Facts.slotTy` | subsumed | the length of an array the slot facts type returns; the `.len` case of `Facts.retsW_sound` by `Facts.slot_resolve`; the Theory does not model the shape taclets (the `wf`/shape row below) |
| — (Lean only: a cost and regression guard) | `LStor.dangles` | Lean only | the slot readers look past a `delete` of an empty array, past a copy, and below a recycled array's length only where the storage holds a write through a stale alias, so every other leaf's reduction (`elim`) is as before |
| — (Lean only: not gated) | closer clause `Facts.nfH` in `Facts.orc` | Lean only | a conditional (`kite`) the simplifier asks about is also normalised with the facts' halting, at every leaf, not only one with a stale write; a stale push's slot length needs it. No base reduction builds an `orElse` with a `kite` on its left, so it closes more goals and changes no earlier one |
| `inEqSimp_*` on bounds by constants | closer clauses `Facts.range`, `Facts.addCmp`, `foldCmp`, `Facts.fitsArith` | subsumed | a local's type range, a premise `t op k` narrowing `t`, intervals added through `+`, `-` |
| `inEqSimp_*` on differences, `polySimp_*` | — | open | no bound on `y - x` for two symbolic terms, no polynomial normal form; `(x - a) + a` cancels (`LTerm.arith`) |

### The closer's memory clauses (`Calculus/MemRead.lean`)

The clauses `sol_decide` reads memory with.  Each row is one solkey taclet,
named as solkey names it — of `memoryRules.key`, `structMemoryRules.key`,
and the program rules of `solidityProgramRules.key` that write memory — or,
under "—", a guard only Lean has, because the interpreter's memory
operations halt where KeY's are total.  Theory's memory has no heap
denotation, so a clause's soundness is the interpreter lemma, and the Theory
lemma is the taclet's transcription (`Theory/Memory.lean`,
`Theory/CrossDomain.lean`).  A name is `LId`, `idC(freshIdp, flds)` with the
allocation's ordinal for `freshIdp`.

The agreement column is `Calculus/MemTheory.lean`.  A memory is read as a
Theory term (`LMem.toTheory`: `pre(heap)` at its bottom, the `k`-th
allocation the root `shaped(ofNat(k), sh)`), and wherever `readT` or `readI`
answers, its answer is `Memory.readIn`'s, cast at the sort read
(`LMem.readT_agree`, `LMem.readI_agree`; with the interpreter,
`LMem.read_agree`).  Only `readT` and `readI` are checked; the elimination
reader `LMem.readU` (`Calculus/Decide.lean`) has no agreement theorem.  Where
the lemma named there rewrites with the row's Theory lemma, that citation is
checked; a cell marked "(by definition)" names the definition the lemma
unfolds instead, of which the row's Theory lemma is an instance, and that
citation is not checked by name.  A default below a struct member needs the
Theory's global member table to be the declarations of the members along the
read's path (`DeclAlong`, a hypothesis on that read alone: no one table is
every struct's, since `Basket.items` is `uint[]` and `FixedTriple.items`
`uint[3]`).  "—" there means the clause is not one of the two readers (a view
reader, a guard), or the Theory has no term for it (`new`).

The translation (`Calculus/Decide.lean`) builds a leaf's memory from its
updates and reads it with these rows: a copy from storage into memory, and
a copy of memory back into storage as its view, which the reads below it
see through.

| KeY taclet | closer clause | interpreter lemma | Theory lemma | agreement (step 8) | status |
| --- | --- | --- | --- | --- | --- |
| `readOnWrite` | `LMem.readT`/`readU`, `.write` arm: same name and selector gives the word written, apart recurses, a symbolic index one `kite` | `LMem.readT_sim`, `LMem.readU_sim`, `selRel_same`, `selRel_apart`, `MemNames.Births.eval_inj` | `Memory.readOnWrite` | `LMem.readT_agree`, `.write` arm (`readT` only; `readU` unchecked) | used |
| `readOnWrite` at an `Identity` | `LMem.readI`, `.write` arm; a symbolic index, or a word written at the same slot, is refused (`none`) where KeY's is an if-then-else | `LMem.readI_sim` | `Memory.readOnWrite`, `Memory.readId` | `LMem.readI_agree`, `.write` arm | used |
| `readOnAddM` `\then` | the allocation arms at the read's root: the default (`dfltSel`), or the length and elements of `new T[](n)` (`newSel`) | `dflt_read_sim`, `new_read_sim` | `Memory.readOnAddM`, `Memory.readAddEqual` | `LMem.readT_agree`, `.addM` arm; `newSel_agree` (`readT` only) | used |
| `readOnAddM` `\else` | the allocation arms at another root: the read passes | `alloc_frame`, `LSel.read_heapExt`, `MemNames.Births.eval_interval` | `Memory.readOnAddM`, `Memory.readAddDifferent` | `LMem.readT_agree`, `LMem.readI_agree`, `.addM` arms; `newT_other` | used |
| `initMember` | `dfltSel`, `.fld`: the default of the member's declared type (`Ty.at`) | `dfltSel_sim`, `slot_default` | `Memory.initMember` | `dfltSel_agree` | used |
| `initElement` | `dfltSel`, `.idx`: the element's default below a fixed length (`ltR`) | `dfltSel_sim`, `slot_default` | `Memory.initElement` | `dfltSel_agree` | used |
| `initSize` | `dfltSel` at `.size` | `dfltSel_sim`, `MemNames.copiedTo_len` | `Memory.initSize` | `dfltSel_agree` | used |
| `defaultValueInt` | `dfltWord`: the default of the declared primitive (`PrimTy.default`) | `dfltSel_sim` | `Memory.defaultDefInt` | `dfltWord_cast` (by definition: `castLike`, `MemValue.asIntAt`) | subsumed |
| `defaultValueBool` | `dfltWord`, likewise | `dfltSel_sim` | `MemValue.asBool` | `dfltWord_cast` (by definition: `castLike`, `MemValue.asBool`) | subsumed |
| `defValResolve` | none built: a default is read at the type the path declares, and the delete rules write the typed default `defVal(T)` where KeY's `memoryIndexDeletePrimitive` writes an untyped `defVal`, so the resolution happens at the write and `cast(defVal)` never occurs | `dfltSel_sim` | `Memory.defValResolvePrim`, `Memory.defValResolveIdentity` | `dfltWord_cast`; for an identity, `readId_fresh` (by definition) | subsumed |
| `idShapeDef` | a root's shape is its allocation's type, read down the path by `Ty.memberTy` | `dfltSel_sim` | `idShapeDef` | `LMem.readT_agree_shapes` (by definition: `LMem.shapes`, each root carries its allocation's shape) | subsumed |
| `sizeOfFixed` | `dfltSel` at `.size` of `T[n]`: `n` | `dfltSel_sim` | `sizeOfFixed` | `dfltSel_agree` | used |
| `sizeOfDyn` | `dfltSel` at `.size` of `T[]`: `0` | `dfltSel_sim` | `sizeOfDyn` | `dfltSel_agree` | used |
| `sizeOfLeaf` | `dfltSel` at `.size` of no array: the term halts where KeY gives `0`; no well-typed program reads the length of a struct or a primitive | `dfltSel_sim` | `sizeOfLeaf` | vacuous: no value to agree on | unreached |
| `shapeAtNil` | `Ty.memberTy` of the empty path | — | `shapeAtNil` | `shapeAt_memberTy` (by definition) | subsumed |
| `shapeAtFixed`, `shapeAtFixedMapElement` | `Ty.at` of an element of `T[n]` | — | `shapeAtFixed` | `shapeStep_at` (by definition: `shapeStep`) | subsumed |
| `shapeAtDyn`, `shapeAtDynMapElement` | `newSel` below an element of `new T[](n)`: the element type's | — | `shapeAtDyn` | `newSel_agree` (by definition: `shapeStep`) | subsumed |
| `shapeAtMember` | `Ty.at` of a struct member (`structDef`) | — | `shapeAtMember` | `shapeStep_at`, under `DeclAlong` (by definition: `shapeStep`) | subsumed |
| `shapeAtMap`, `shapeAtLeafElement`, `shapeAtLeafMapElement` | not reached: memory holds no mapping (`allocOk`), and `Ty.at` has no segment below a primitive | — | `shapeAtMap`, `shapeAtLeafElement` | — | unreached |
| `initIdentity` | `LMem.readI` at the root's allocation: the name one segment longer | `readI_alloc`, `resolveR_snoc_sim`, `MemNames.birth_slot` | `Memory.initIdentity` | `LMem.readI_agree`, `.addM` and `.newArr` arms (`readId_fresh`) | used |
| `idCCDef` | an allocation's root is the name `⟨k, []⟩` | `evalR_last` | `Memory.idCCDef` | `newSel_agree` (the length of `new T[](n)` is written at `idCC`) | used |
| `readFromEmptyMemory` | the `.init` arm: no answer.  The bottom of a leaf's memory is the pre-state heap `pre(heap)`, not `mtMem`, and the readers refuse there (every name a leaf uses names a root the leaf allocated) | — | `Memory.readFromEmptyMemory` | vacuous: `readT` and `readI` never answer at `init` | unreached |
| `readREmpty` | `LMem.walk` on a one-segment path: the read itself | `LMem.walk_sim` | `Memory.readREmpty` | — (a view reader) | used |
| `readRCons` | `LMem.walk`: `readI` for each leading segment, the read on the last | `LMem.walk_sim`, `MVal.readPath_snoc` | `Memory.readRCons`, `Memory.readR_eq_firsts_last` | — (a view reader) | used |
| `newFromAdd` | none: a root is fresh by its ordinal (`LMem.nAlloc`), its object by its birth interval (deviation: no `new` term) | `MemNames.Births.eval_interval`, `MemNames.copyStToM_interval` | `Memory.newFromAdd`, `Memory.newAddDifferent` | — (distinct ordinals are distinct roots, `rootT_inj`) | deviation |
| `newFromWrite` | none, likewise: a write keeps the births (`LMem.run`) | `LMem.run_births` | `Memory.newFromWrite` | — | deviation |
| `newFromEmptyMemory` | none, likewise: the first allocation is ordinal `0`, above the state's `nextId` | `MemNames.Births.Ok.nil` | `Memory.newFromEmptyMemory` | — | deviation |
| `findOnCopy` | the `.view` arm of `LStor.readU` (`Calculus/Decide.lean`) | `view_read_sim`, `MemNames.copyMToSt_readPath` | `StValue.findCopyMem` | — (a view reader) | used |
| `selectOnCopyMemPrim` | the last segment of `LStor.readU`/`lenU` on a view | `view_read_sim`, `view_len_sim` | `StValue.selectOnCopyMemPrim` | — (a view reader) | used |
| `selectOnCopyMemRef` | a leading segment of a read on a view, through `readI`; `LStor.hasU` on a view | `view_has_sim`, `MemNames.copyMToSt_readPath` | `StValue.selectOnCopyMemRef`, `StValue.findCopyMemStruct` | — (a view reader) | used |
| `readFromCopyToStorage` | `copySel`: the storage read one segment further | `copy_read_sim`, `MemNames.copyStToM_readPath` | `Memory.readCopySt`, `Memory.readCopyStOther` | `LMem.readT_agree`, `.copySt` arm: `copySel_agree`, `copy_word`, with `SVal.abs_find` | used |
| `readFromCopyToStorageIdentity` | `LMem.readI` below a copy; `nameG`'s `refT` | `copy_ref_rets`, `MemNames.copyStToM_readPath` | `Memory.readCopyStIdentity` | `LMem.readI_agree`, `.copySt` arm (by definition: `readCopySt`, then `readId_fresh`) | used |
| `findDefinitionSize` (`structRules.key`) | `copySel` at `size`: `.len` of the storage subtree | `copy_read_sim`, `MemNames.copyStToM_lenPath` | `findDefinitionCons` | `copy_len` (by definition: `findSt_readAt`, `SVal.abs_find`) | used |
| `memoryReferenceDeclFreshAlloc` | the pair `{x := freshId(addM(…)) ‖ memory := addM(…)}` kept whole (`pairLS`, `allocPairS?`): `x` names the root `⟨nAlloc, []⟩` (deviation: KeY's two sequential updates `{mv := idC(shaped(freshIdp, #shapeOf(mv)), nil)}{memory := addM(…)}` over one Skolem `freshIdp` (`\skolemTerm`, `\sameUpdateLevel`)) | `RelU.two` (with `RelU.pairKey`), `LMem.run_addM`, `allocDefault_heap`, `evalR_last` | — | `toTheory_addM` | deviation |
| `memoryRootDeleteFreshRebind` | the same pair | the same | — | `toTheory_addM` | deviation |
| `memoryArrayFreshAlloc` | the same pair over `LMem.newArr`, one node for `write(addM(…), size, n)` (deviation) | `RelU.two` (with `RelU.pairKey`), `LMem.run_newArr`, `new_read_sim`, `MemNames.copyStToM_newArr_at`, `copyStToM_newArr_len` | `Memory.readOnWrite`, `Memory.readAddEqual`, `Memory.initElement` | `toTheory_newArr` (`newT`: the `addM` and the write of its length), `newSel_agree` | deviation |
| `memoryStorageCopy` (after `memoryStorageCopyUnfold`) | the same pair over KeY's `copySt(addM(memory, shaped(freshIdp, #shapeOf(mv))), shaped(freshIdp, #shapeOf(mv)), find<[Struct]>(storage, sp))`: the node `LMem.copySt` (`pairMemS`).  Deviation: `LMem.toTheory` omits the `addM` (no read below the copy sees it, `readCopySt` shadows the root) and leaves the root unshaped, a copy's lengths being read from storage; `Memory.new` of the image counts the root as fresh | `RelU.pairCopy_key`, `LMem.run_copySt`, `copy_ref`, `live_bridge` | `Memory.readCopySt` | `toTheory_copySt` | deviation |
| `memoryFieldDeleteReference` | `freshRefS`: the reference `write(addM(memory), a, freshId(addM(memory)))` writes is the root the allocation under the write takes | `writeValS_ok`, `freshRefS_cases` | — | — | used |
| `memoryIndexDeleteReference` | `freshRefS`, at an element | `writeValS_ok`, `freshRefS_cases` | — | — | used |
| `memoryToStorageStoreRoot` | the translation: `save(storage, p, copyMem(mtSt, m, i))` is `LStor.copy` of the view `LStor.view m i` at its root `viewRoot` (`Op3.toL`), then the copy rows of the storage closer (`copyLeaf`, `copyKeys`) | `RelU.stor_eval` (its `copyMem` arm), `evalS_save_copyMem`, `write_bridge`, `copyMem_of_heap` | `StValue.findCopyMem` | — | used |
| `memoryToStorageFieldCopyRoot` | the same, at a member of a storage path | the same | `StValue.findCopyMem` | — | used |
| `memoryToStorageFieldCopyField` | the same, from a member of a memory object (`readI` names it) | the same, with `LMem.readI_sim` | `StValue.findCopyMem` | — | used |
| `memoryToStorageIndexMappingCopyRoot` | the same, at a mapping key | the same | `StValue.findCopyMem` | — | used |
| `memoryToStorageIndexArrayCopyRoot` | the same, at an array index | the same | `StValue.findCopyMem` | — | used |
| — (Lean only: memory holds no mapping) | `LStor.mapU .map` of a view is `.err` | `view_noMap`, `MemNames.copyMToSt_noMap` | — | — | used |
| — (Lean only: `copyMem` halts on a cycle) | `LMem.refDesc`: every reference written names an older root; `okE` of a view is the run guard and `nameG` where it holds, kept whole elsewhere | `LMem.refDesc_desc`, `view_okE_sim`, `MemNames.copyMem_ok_desc` | — | — | used |
| — (Lean only: KeY's memory operations are total, the interpreter's halt) | `LMem.okU`, the run guard: each allocation at its ordinal (`LMem.nAlloc`) of a type `allocOk` admits, each copy from storage of a subtree that copies and is no word, each write's `writeG` and value | `LMem.okU_sim`, `MemNames.copyStToM_ok_noMap`, `Ty.mapFree_sound`, `LMem.writeG_sim` | — | — | used |
| — (Lean only: the program rules' `\add(0 <= ie & ie < read(memory, mv, size))`; a member write needs a struct) | `LMem.writeG`, `structG`, `nameG` | `LMem.writeG_sim`, `structG_sim`, `nameG_sim` | — | — | used |
| — (Lean only: `copyStToM` halts on a mapping) | `LTerm.cpok`, reduced by `LStor.cpokU` through each word written over a word, down to `cpok init q` | `LStor.cpokU_sim`, `save_cpok_sim`, `cps_findLive_savePrim`, `copyStToM_ok_any` | — | — | used |
| — (Lean only: `wt` gives a copyable value) | `Facts.cpokInit` (`Calculus/Closer.lean`): `cpok init q` returns where the layout types `q` at a type with no mapping | `Facts.retsW_sound`, `MemNames.copyStToM_ok_noMap` | — | — | used |
| — (Lean only: a copy from storage halts on a mapping, and a word copies to no object) | `Decide.copyG`, the guard of a copy's pair: `cpok`, and the subtree no word; a copy from storage is in the fragment only in its pair (`pairInS`), where the identity's `asRef` refuses a word | `RelU.pairCopy_key`, `copy_ref`, `live_bridge` | — | — | used |
| — (Lean only: a view keeps no guard) | `Decide.memL`: a copy of memory is in the fragment where the memory's and the identity's guards are literals; a `push` of a memory object is not | `RelU.stor_eval` | — | — | used |
| — (Lean only: a view is a one-root tree) | `LStor.hasU` of a view at `viewRoot` is `true` (`isViewRoot`): a view that returns has its root | `view_hasU_sim`, `view_findLive` | — | — | used |
| — (Lean only: a read walks every write) | `memSize`: a leaf whose memory holds more writes and allocations is left outside (`LMem.within`) | — | — | — | used |

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
| a value | `Term` | a constant, a stack local, `a ⊕ b`, `find(s, p)` (`Term.find`; `select(s, r)` reads the same, and is how a value read prints as a `save`'s value, where `find` is the copy `SValT.find`; KeY writes `find` there, and has no `select`: the spelling is Lean's, also under `pp.sol.key`, and is told from `STerm.select` by its sort), `read(m, a)`, an array's length (`Term.len`, printed `p.length` at `storage` and `find(s, p.length)` elsewhere; `Term.mlen`), `c ? a : b`, `selectSt(net, at(a))` (`Term.net`), `selectSt(oldNet, at(a))` (`Term.netOf`), `delValue(t)` (`Term.delValue`, the default of a word; solkey replaced its `delValue<[α]>` by `delField<[α]>(st, a)`, which is `delValue(selectSt(st, a))` here), `wt(s)` (`Term.wt`/`Op1.wt`, KeY's `wellFormed(heap)`: `true` on a storage the contract can be in, stated `defined(wt(storage))`, the premise of an obligation); `Op1.toInt`, a `uint` read as a KeY `int` (total: solkey writes nothing, its `msgValue` and ledger entries being `int`s, `netHeader.key`; inserted by the reader where a term of fixed type `uint` meets a KeY `int`, `NTm.widen`/`resolvePairV`, and printed bare where the other operand shows the sort, `toInt(…)` where none does) |
| KeY's `int` | `Srt.kint` (Lean's `Int`) | the ledger's entries (`net(a)`, `x[a]`: `Op1.net`, `Tm.netOf`), `toInt`, a literal (`Op0.zlit`), a logical variable (`Tm.pvZ`, a formula's parameter read only at the sort: `RawFml.kintParams`), `+`, `-`, `*` (`Op2.zbin`, unbounded) and the comparisons (`Op2.zcmp`, to `bool`; an equation `a = b` on KeY `int`s is `a == b = true`, `NRead.eqK`).  Apart from Solidity's `int256` (`val .int`); `sol_decide` leaves it outside its fragment, as the ledger |
| `Path[storage]` | `PTerm` | a state variable (`.root`), an alias (`.pv`), `.field`/`.at`; `p[i]@S` (`.atIn`) and `p[p.length]@S` (`.nextIn`) for an index check or a push slot merged under a storage write, their check performed in `S` (no KeY counterpart: KeY's `at(i)` is unchecked) |
| `Storage` | `STerm` | `.storage`, `.mtSt` (KeY's `mtSt`, a deployment's storage: Lean-only reading, every root of the contract present at its default, where KeY's has none and `selectOnEmptyStorage` answers the default; reads agree), `.save`, `.delAt`; `.push`/`.pushSlot`/`.pop`/`.shrink`/`.extend` for the array writes; `.select` for `selectSt<[Struct]>(s, r)`, the struct at a member, written `select(s, r)` |
| what a storage `save` writes | `SValT` | a value (`.val`), a subtree read from a storage (`.find`, printed `find(s, p)`; a value read there prints `select(s, p)`), a memory object copied back (`.copyMem`, KeY's `copyMem(mtSt, m, i)`), or a fresh array (`.newArr`; a concrete one prints `newArr(T, n)`, `T` the array type) |
| `Identity` | `ITerm` | a memory local (`.pv`), a reference read out of memory (`.read`), `freshId(addM(m))` (`.alloc`, carrying the `RefTy`; a concrete one prints it, `freshId(addM(m, Person))`, `freshId(addM(m, uint[]))`), `freshId(copySt(m, v))` (`.copy`) |
| a member or element of a memory object | `MAddr` | `.field`/`.at` |
| `Memory` | `MTerm` | `.memory`, `.write(m, a, v)`, `.addM` (eager: the type rides along; a concrete one prints `addM(m, T)`, `T` a struct `Person` or an array type `uint[]`, `Token[3]`, where KeY writes `addM(mem, shaped(idp, #shapeOf(mv)))`: the type in place of its shape), `.copySt(m, v)` |
| what a memory `write` writes | `MValT` | a value (`.val`) or a reference (`.ref`) |
| one elementary update | `UpdElem` | `.val`, `.path`, `.mref`, `.storage`, `.memory`; `.store` for `old := storage`; `.pay` for a transfer's booking (and a taken send's) `net := if(r = this) then net else store(net, at(r), net(r) - a)`; `.net` for `net := store(net, at(r), net(r) ± a)`, with `.selfBalance` for a `payable` function's booking of `msg.value` (`selfBalance := selfBalance + a`); `.saveNet` for `oldNet := net`; a deployment's (`Problem.deployUpd`, `spec!{constructor}`): `.netMt` for solkey's `net := storeSt(mtSt, at(r), selectSt<[int]>(mtSt, at(r)) + a)`, printed `storeSt(mtSt, at(r), a)` (Lean-only shortening: the read of `mtSt` is `0`, `selectOnEmptyStorage`), `.setBalance` for `selfBalance := a`, `.saveNetMt` for `oldNet := mtSt`; `.unset` for `lsv := unset`, an alias bound to no path (Lean only, `storageLocalDeclSkip`) |

### `structRules.key` → `Theory/Storage.lean` (`Struct`, `StValue`)

| KeY taclet | Lean theorem | Status |
| --- | --- | --- |
| `defaultValueStruct` | `defaultValueStruct`, `defaultValueInt`, `defaultValueBool` | done: `defaultValue<[α]>` is `st mtSt`, the `Struct` default, read through the caller's cast |
| `selectOnStore`, `selectOnEmptyStorage`, `findDefinitionEmpty` | same names | done |
| `saveOnEmptyStorage` | same | done, with an `isEmpty(flds)` split upstream lacks (the collapsing leaf) |
| `selectOnEmptyStorage`, `saveOnEmptyStorage` in the closer | `sol_close_mt` (`Calculus/Close.lean`, `Calculus/CloseScoped.lean`) | Phase 1, Lean-only: `mtSt` evaluates to the roots at their defaults (`CloseS.eval_mtSt`), and the storage evaluators are unfolded over that list; no `LStor` clause yet, so `sol_prove` refuses `mtSt` (`Op0.inL`) |
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
| `selectOnShape{Size,Struct,Element,Member}`, `wf{Leaf,Shape,FixedSize,DynSize,FixedElem,FixedElemMap,DynElem,DynElemMap,MapElem,SaveRight,StoreRight,DelAtRight,DelNodeRight,DelNodeFixedRight,FixedRight,DynRight,MapRight}`, `fixed{Save,Store,DelNode,DelNodeFixed,DelAt,ShapeFixed,ShapeDyn,Empty}`, `wfFixedIsFixed`, `wfDynIsNotFixed`, `selectStDelNodeSize`, `selectOnSaveEmptySize` | `wellTypedStorageB`, `SVal.hasTy` (`Typing/Storage.lean`) | **not modelled as taclets**: the shaped empty storage and `wellformed(storage)` are the storage's well-typedness here, clause for clause; a declared `T[n]` has shape `fixedArr` (`Shape.ofTy_fixed`) but the elaborator writes its `.length` as the literal `n`, so no program reads it, and shapes as nodes and `wf` would be one more `Struct` constructor and a predicate through every proof. A delete keeps a fixed-size array's length without it (`keepsOnDelete`) |
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
`findMemberCons` and `selectOnSaveMember` (`Calculus/TermLib.lean`) take
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

### The Theory's laws as term taclets (`Calculus/TermLib.lean`)

A rule on terms is a constructor of `TermTaclet` (W9.1), on scoped terms
`Tm C Γ .val`, applied on a sequent by name (`rw [findOnSave]`,
`Proves.rewrite`); `TermTaclet.sound` reads its two terms through the scoped
`Tm.denote` and closes the case by the Theory lemma below (`Tm.Theq`).
Side conditions are syntactic `Bool`s on scoped paths, closed by `rfl`
(`Tm.hasSeg`, `Tm.diverges`, `Tm.sameSegs`, `Tm.shift?`, `Tm.findLit?`),
or a hypothesis of the chain (`Tm.KindFreeAt`); `SCtxS` is a storage
context. solkey has none of these as a taclet; they are the rules
`Theory/Rewrite.lean` lists as Lean-only, stated on terms.

| Term taclet | Lean (`TermTaclet`) | Theory lemma | Printed rule (`TheoryRule`) | Notes |
| --- | --- | --- | --- | --- |
| `findOnSave` | `TermTaclet.findOnSave` | `find_copyTo_same` (`Theory/Copy.lean`) | `findOnSave` | `find(save(s, p, v), q) ≐ v` for a literal word `v`, `q` the path `p` its checks aside (`Tm.sameSegs`: `p[i]@S` is `p[i]`): a copy reads back the new value laid over the old, which is `v` only for a word |
| `findOnSaveFrame` | `TermTaclet.findOnSaveFrame` | `find_copyTo_frame` | `findOnSaveDifferent` | any written value, `p` diverging from `q` |
| `findMemberCons` | `TermTaclet.findMemberCons` | `find_cons` | — | solkey's `consRcons`, `consRnil`, `findDefinitionMemberCons`/`Prim`: `find(s, r.p) ≐ find(select(s, r), p)`, the path read from its head (`Tm.shift?`), at any depth |
| `findOnSave` in a storage of members | `TermTaclet.findOnSaveIn` | `find_copyTo_same` | `findOnSave` | `findIn(saveIn(s, p, v), p) ≐ v` for a word `v`, under a `select` (`sts`): the same law at `Contract.ofStruct` |
| `findMemberCons` in a storage of members | `TermTaclet.findMemberConsIn` | `find_cons` | — | `findIn(s, f.p) ≐ findIn(select(s, f), p)` under a `select` (`Tm.shiftIn?`) |
| `selectOnSaveMember` | `TermTaclet.selectOnSaveMember` | `StValue.selectOnSaveCons` | — | solkey's `selectOnSaveCons` at `a1 = a2`: `find(select(save(s, r.p, v), r), q) ≐ find(save(select(s, r), p, v), q)` |
| `selectOnSaveFrame` | `TermTaclet.selectOnSaveFrame` | `StValue.selectOnSaveCons` | — | solkey's `selectOnSaveCons` at `a1 ≠ a2`: a write under another root is not seen from `r` |
| `selectOnDelAtMember`, `selectOnDelAtFrame` | `TermTaclet.selectOnDelAtMember`, `TermTaclet.selectOnDelAtFrame` | `StValue.selectOnSaveCons`, `find_cons` | — | the same for a delete, `delAt(s, p)` being `save(s, p, delValue(find(s, p)))` |
| `selectOnSaveMemberIn`, `selectOnSaveFrameIn`, `selectOnDelAtMemberIn`, `selectOnDelAtFrameIn` | `TermTaclet.selectOnSaveMemberIn`, `TermTaclet.selectOnSaveFrameIn`, `TermTaclet.selectOnDelAtMemberIn`, `TermTaclet.selectOnDelAtFrameIn` | the same, `SCtxS.fill_denote` | — | the four in a storage context `K` of saves, deletes and selects (`SCtxS`), which the arrow finds: solkey rewrites a storage term wherever it stands |
| `selectOnSaveMember`, `selectOnSaveFrame`, `selectOnDelAtMember`, `selectOnDelAtFrame` at a member | `TermTaclet.selectOnSaveMemberAt`, `TermTaclet.selectOnSaveFrameAt`, `TermTaclet.selectOnDelAtMemberAt`, `TermTaclet.selectOnDelAtFrameAt` | `StValue.selectOnSaveCons`, `find_cons` (`Tm.selectOnSaveMemberAt_denote`, …) | — | the four one `select` down, in a storage of members: `selectIn(saveIn(s, f.p, v), f)` is `saveIn(selectIn(s, f), p, v)`, a write under another member `f' ≠ f` unseen; in a storage context `K` |
| `findOnDelAt` | `TermTaclet.findOnDelAt` | `find_delAt_same`, `delValueDefault` | `findDelAt` | where `find(s, p) ≐ w` for a word `w`, the delete reads its default at `p` (`sameSegs`) |
| `findOnDelAtSave` | `TermTaclet.findOnDelAtSave` | `findOnDelAt` over `findOnSave` | `findDelAt` | a delete over a written word, the three paths one path their checks aside |
| `findOnDelAtValue` | `TermTaclet.findOnDelAtValue` | `find_delAt_same` | `findDelAt` | `find(delAt(s, p), q) ≐ delValue(find(s, q))`, `q` the path `p` its checks aside: the delete's effect at its own path, the value left for a later law (`delValueLit`, or a read below a mapping member) |
| `delValueLit` | `TermTaclet.delValueLit` | `delValueDefault` | `delValueDefault` | `delValue(w) ≐ default(w)` for a literal word |
| `findOnDelAtBelow` | `TermTaclet.findOnDelAtBelow` | `find_delAt_below`, `delValueDefault` | `findDelAtFields` | a word at or below a deleted node reads its default, where the deleted storage writes the word there (`Tm.findLit?`) and the node is no mapping (`Tm.KindFreeAt`, a premise of the chain: a mapping keeps its members) |
| `findOnDelAtBelow` in a storage of members | `TermTaclet.findOnDelAtBelowIn` | `find_delAt_below`, `delValueDefault` | `findDelAtFields` | `findIn(delAtIn(s, p), q) ≐ defVal` under a `select`: `q` below the member path `p` by members (`Tm.extendsIn`), `s`'s member-wise writes giving the word there (`Tm.findLitIn?`), the node no mapping (`Tm.KindFreeAt`, at a storage of members and a member path, `Srt.pathAt`); a chain's `~[findOnDelAtBelow]~>` names both.  Past the program it is covered where the update holds the delete (`Upd.coversLit`, `Tm.findDelBelowAt`: a read by members below a delete returns) |
| `findOnDelAtFrame` | `TermTaclet.findOnDelAtFrame` | `find_delAt_frame` | `findDelAtOutside` | |
| `findOnPushFrame`, `findOnPopFrame` | `TermTaclet.findOnPushFrame`, `TermTaclet.findOnPopFrame` | `find_pushT_frame`, `find_popT_frame` (`Theory/Copy.lean`) | — | a push or pop is one term here, not two saves.  Past the program they do not rewrite inside an update's right-hand sides (a law rewrite there asks both sides push-free, `Tm.pushFree`, W9.8.5), only in its equations' sides |
| `lenOnSaveFrame`, `lenOnDelAtFrame` | `TermTaclet.lenOnSaveFrame`, `TermTaclet.lenOnDelAtFrame` | `find_copyTo_frame`, `find_delAt_frame` | `findOnSaveDifferent`, `findDelAtOutside` at `p.size` | `len(save(s, q, v), p) ≐ len(s, p)`, `len(delAt(s, q), p) ≐ len(s, p)` where `q` leaves `p.length` (`Tm.divergesLen`): a length is a read at `p.length`, one term here (`Term.len`) |

### The laws of memory reads (`EvalLaw`, `Calculus/TermLaws.lean`)

A memory read (`read`, `copyMem`, `copySt`) denotes its run, so a law of one
is no Theory equation but a refinement of the interpreter: where the read
returns, its replacement returns the same (`EvalLaw.sound`,
`Tm.EvalRefinesAt`).  A chain's line past the program applies one in an
update's right-hand side under any modality where the update holds the
write the law reads back (`Upd.coversEval`, `LawCov.eval`, `FmlRw.lawUpdS`).

| Law | Interpreter lemma | KeY taclet | Notes |
| --- | --- | --- | --- |
| `readOnWrite` | `readAddr_writeAddr_same` (`Calculus/ReadWrite.lean`) | `readOnWrite` | `read(write(m, a, v), a) ⇝ v` for a literal `v` |
| `findCopyMem` | `copyMem_member` | `findOnCopy` over `findOnSave` | `find(save(s, p, copyMem(mtSt, m, i)), p.f) ⇝ read(m, i.f)`: the printed trace's one step from the `find` into memory |
| `readCopySt` | `copyStToM_member` | `readFromCopyToStorage` | `read(copySt(m, find(s, p)), freshId(copySt(m, find(s, p))).f) ⇝ find(s, p.f)` |
| `readAddEqual` | `copyStToM_default_readPath` (`Calculus/ReadWrite.lean`) | `readAddEqual` | `read(addM(m, R), a) ⇝ default` for a primitive member or fixed element at a fresh path of the allocation (`Tm.freshPath?`, `RefTy.memberTy`) |
| `readAddDifferent` | `readAddr_heapExt`, `allocDefault_heapExt` | `readAddDifferent` | `read(addM(m, R), a) ⇝ read(m, a)` where `a`'s identity is allocated strictly earlier on `m`'s spine (`Tm.boundedIn`) |
| `readAddDifferentIdentity` | the same | `readAddDifferent` at `Identity` | the twin at the identity sort |
| `readWriteDifferent` | `writeAddr_setObj` | `readWriteDifferent` | `read(write(m, a, v), b) ⇝ read(m, b)` where `a` and `b` never meet (`Tm.apart?`: different members, a member and an element, one object at different literal indices) |
| `readWriteDifferentIdentity` | the same | `readWriteDifferent` at `Identity` | the twin at the identity sort |
| `readOnWriteIdentity` | `readAddr_writeAddr_same` | `readOnWrite` at `Identity` | `read(write(m, a, ref(i)), a) ⇝ i` |
| — | — | `idC(ρ, [account])` | no law: a reference member of a fresh root, `read(addM(m, R), freshId(addM(m, R)).account)`, is the normal form, since KeY's `idC` has no `ITerm` counterpart |

The merges that feed them (`Calculus/StatePartsScoped.lean`):
`{memory := M}{V}` substitutes `M` for `memory` in `V` (`Upd.mergeMem?`,
`Tm.withMemS`; with the locals of a
`{carol := freshId(copySt(…)) ‖ memory := copySt(…)}`, `Upd.mergeMemL?`),
and `{L ‖ storage := s}{V}` substitutes the locals and `s` in one pass, into
memory reads too (`Upd.mergeSt?`, `Tm.substStS`); past the program a
storage write a later one shadows is dropped (`Upd.dropSh`).  A law is
stated at the value or the identity sort (`EvalLaw : Tm C Γ u → Tm C Γ u →
Prop`) and rewrites at that sort inside every right-hand side, memory reads
included (`holds_upd_rwG`, `Calculus/RewriteLaws.lean`).

### The literal laws (`LitLaw`, `Calculus/TermLaws.lean`)

KeY's `*_literals` taclets (`integerSimplificationRules.key`) fold an
operation on two literals.  Each is a constructor of `LitLaw`, stated as the
interpreter computes it, and exact (`LitLaw.exact`): its left side returns
the literal on the right in every state.  So a chain applies one anywhere,
under any modality.  While the program is open: in an update's right-hand
sides, with no premise on the update (`FmlRw.lit`,
`Calculus/RewriteScoped.lean`: `holds_upd_rwC_iff`), and in the equations
and `defined(…)`s of the line's propositional skeleton (`FmlRw.litEq`, an
equivalence: `Fml.lawAlongS_holds`), where a term taclet rewrites a whole
side too (`FmlRw.lawEq`).  Past the program: in an update's right-hand
sides (`FmlRw.lawUpdS`, `Calculus/RewriteLaws.lean`).

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
  (`Tm.substStS`), the check performed in `S`.  The laws read them as `p[i]`
  (`Tm.sameSegs`, `Tm.diverges` on shapes); `p[p.length]@S` is its own
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
- **Scope ends and hidden binders are Lean only and print as nothing**: the
  capture pop after a rule's fresh locals (`Frames.pop .capture`), a block's
  and a call frame's end, and the binder a declaration with an initializer
  puts in front of its assignment (`Premise.bind`).  KeY's program variables
  are global and need neither (their rows above).
- **Unset locals**: `T storage lsv;` binds `lsv := unset` (`storageLocalDeclSkip`),
  and the hidden binder of `memoryLocalDeclInitDrop` ranges over an unset
  memory local too (decision 17'); a read through either reverts.
- **`typed` is not modelled**, and the storage copy fold is not followed (top
  of this section).
