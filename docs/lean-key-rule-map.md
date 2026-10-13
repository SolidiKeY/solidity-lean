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
| `transferNoCallbackBox` | same name | same | the box only, one terminal update (`UpdElem.pay`): `{ net := if(sadr = this) then net else store(net, at(sadr), net(sadr) - se) } ⟨[ ]⟩`, solkey's `\if(sadr = self) \then(net) \else(storeSt(…))`, with no guard: the amount is read as a word by the element itself, which halts where it is not. The arithmetic is KeY's `int`. Whether the world pays is the compiler theorem's (`Evm.compile_correct`), where a refused payment is a revert of the machine alone; the contract's own entry is never moved (`Evm.Sim.netSelf`) |
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
| `tryCallNoCallbackBox` | same | same | one goal per clause (`Premise.branches`, `Proves.branches`): "call succeeded", "Error caught", "Panic caught", "other failure caught". KeY declares the return locals and the `Panic` code without an initializer, leaving them unconstrained; here they are bound under `∀` (`Hyps.all`), since a Lean declaration is its default. `s#call` is an `ExtCall`, whose receiver and arguments are simple: the elaborator captures any other before the `try` |
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
| `sequentialToParallel1-3`, read backwards | `Upd.toLS` (`Calculus/DecideScoped.lean`) | Lean only | `sol_prove`'s leaf closer reads a parallel update element by element, each in the update's pre-state (`UpdElem.toLS`), so nothing splits it: an allocation's pair and a push with its returned alias are read as they are; **Lean only**, a hidden binder of a value is read as the `∀` it is (`LFml.allB`) |
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
| — (KeY's anonymising update `{storage := storageSk ‖ net := netSk}`, its skolem constants fresh) | `CloseS.holds_havoc` (`Calculus/CloseScoped.lean`), `close_rw_s` | Lean only | `{havoc} φ` read as `φ` for every storage `st` and ledger `nt` (universally bound in place of fresh skolems); a snapshot `old`/`oldNet` taken before it is a local and keeps the storage it took |
| `findOnSave` (a scoped leaf) | `CloseS.wp_box_write`, `wp_box_write_prim` (`Calculus/CloseFrame.lean`), `close_rw_s` | done (W9.8.4) | a box write names the storage it leaves: `find(st', r)` is the written value (`Storage.writeVal`: a word itself, a struct overlaid on what was there) |
| `findOnSaveFrame`, `lenOnSaveFrame` (a scoped leaf) | `CloseS.wp_box_write`: `Storage.find_save_frame`, `len_save_frame`, `checkIndex_save_frame` | done (W9.8.4) | a read, a length and an index check at a path diverging from the write's (`Theory.diverges`, `Theory/Segs.lean`) read the storage before it; below the written path by `Path.append` |
| `findOnDelAt`, `findOnDelAtFrame` (a scoped leaf) | `CloseS.wp_box_delete` (`Calculus/CloseFrame.lean`) | done (W9.8.4) | the deleted path reads its default (`SVal.dflt`), a diverging path the storage before |
| `readOnWrite` (a scoped leaf) | `CloseS.wp_box_writeT`, `Grown.writeT_facts`, `MAddrT.apart_resolve` (`Calculus/CloseFrame.lean`) | done (W9.8.4) | a memory write reads back at its address and leaves an address apart from it (`MAddrT.Apart`) unchanged |
| `copyStToMem`/`copyMemToSt` member reads (a scoped leaf) | `SVal.copyStToM_field`, `MVal.copyMToSt_field`, `CloseS.readId_copySt_field`, `copyMToSt_find_field` | done (W9.8.4) | a member of a copy reads the member copied, by the erasure (`Close.copyStToM_member`, `Close.copyMem_member`) |
| — (a total path in a diamond) | `CloseS.wp_diamond_write_total`, `wp_diamond_delete_total`, `wp_find_total` (and `_root`), `Storage.write_ne_none_total` | Lean only (W9.8.4) | a write, delete or read at a path with no index (`Path.total`) does not halt, so a diamond leaf reads it as the box does; a deployment's storage (`Storage.find_init_total`) likewise |
| `selectOnEmptyStorage` at a root and below it (a deployment's storage) | `CloseS.find_init_ofRoot`, `CloseS.find_init_append` (`Calculus/CloseFrame.lean`), `close_rw_s` | done (W9.8.4) | the typed empty storage (`Storage.init`) reads a root, and a path through no array slot below it (`Path.total`), at its type's default (`Storage.find_init_total`) |
| — (an index checked at a mapping root; a checked index) | `CloseS.atT_map_root`, `CloseS.atT_bind` (`Calculus/CloseScoped.lean`), `close_rw_s` | Lean only (W9.8.4) | a key of a mapping at a root is always a slot (the check passes), so two reads of `balances[0]` name one reference; any other index is its check, then the slot's reference: the typed `Storage.atT` unfolded so the closer compares references |
| `storeSt`/`selectSt` on the ledger (`netHeader.key`) | `Close.lookupBy_setBy_int` (`Calculus/CloseLemmas.lean`), `close_rw_s` | done | a ledger entry after a write: the written amount at that address, the old entry elsewhere, the entries KeY `int`s (`Srt.kint`) |
| — (a push's room under the diamond) | `Upd.exhL`, `guardM` (`Calculus/DecideScoped.lean`), `Upd.exhL_sound`, `guardM_holds` (`Calculus/DecideTyped.lean`) | Lean only (W10.4) | a push at a full array is out of gas, which both modalities accept: under the diamond the update's guard is asked only where the array is not full (`fullL`), and what follows only where the update lands; the elimination's push asserts `len < 2^256 - 1` (`maxLen`). KeY's `int` lengths need no room |
| `eqClose` | `Proves.eqRefl`; `Proves.eqClose` (`v ≐ v`), `Proves.eqDClose` (`v = v`); on two literals in a chain, `FmlRw.concrete` (`Fml.litCS`) | done | `t ≐ t` for any term, halting or not (`Fml.eq` compares `Tm.denote`s by `=`); `v ≐ w` for distinct literals folds to `false` |
| `concrete_and_1-4`, `concrete_impl_1-4`, `concrete_not_2` | `FmlRw.concrete` (`Calculus/RewriteScoped.lean`, `Fml.concreteAlongS`) | done | on a chain's scoped line while the program is open: `true ∧ A ⇝ A`, `false → A ⇝ true`, `A → false ⇝ ¬A`, `¬false ⇝ true`, …, bottom-up through `¬`, `∧`, `→`, `false` being `¬true`; `concrete_not_1` (`¬true ⇝ false`) rewrites nothing |
| `andRight` | `Proves.andSplit` | done | |
| — | `Proves.eqDSplit` | Lean only | `a = b` from `defined(a)`, `defined(b)`, `a ≐ b`: `Fml.eqD` unfolded |
| — | `Proves.definedWritten` (`Calculus/UpdateRules.lean`) | Lean only | `defined(x)` for any `.val` local, behind a context with no diamond (`Hyps.boxOnly`), with **no update asked**: a typed local always holds a value of its type, which KeY's `defined` does not need |
| — | `Proves.definedLit`; `FmlRw.concrete` (`Fml.litCS`: `defined(v) ⇝ true`) | Lean only | a literal is defined |
| any theory taclet on a sequent | `Proves.rewrite` (`Calculus/Proves.lean`, a rule), `rw [r]`/`sol_rw` (`Calculus/RewriteSyntax.lean`) | done | a term taclet `r : TermTaclet t t'` (`Calculus/TermLib.lean`) or a `Tm.Theq` at the empty scope rewrites every closed side of an equation of the sequent's preconditions and goal reading `t` there (`Tm.closedAs`; `Hyps.rwEqC`, `Fml.rwEqC`, `Calculus/SeqRewrite.lean`), a modality open or not, `core_rw`; `TermTaclet.sound` proves each rule once, from its Theory lemma; decision 90 |
| the same, inside an update | `Proves.updRw`, `sol_rw` | done | an update's right-hand side runs in the interpreter, so the rewrite asks `Tm.EvalRefines t t'`, which a Theory equation onto a literal gives (`Tm.EvalRefines.of_theq`); on the **last** box update of the context only, its closed occurrences of `t` read at the empty scope (`Upd.rwC`, `holds_upd_rwC`, `core_rw`); on a chain's scoped line while the program is open, any box update of its spine (`FmlRw.lawUpd`, `Calculus/RewriteScoped.lean`, a `TermTaclet`) |
| the same, inside an update, on a chain's line past the program | `FmlRw.lawUpdS` (`Calculus/RewriteLaws.lean`) | done (W9.4), any modality | a term taclet (`TermTaclet`), a memory law (`EvalLaw`) or a literal law (`LitLaw`) at an update's right-hand sides, its two sides read at the update's scope (`LawPair`); exact where the update holds the write it reads back (`LawCov.covered`, `Upd.covers`; `LawCov.ref`, `Upd.coversRef`; `LawCov.eval`, `Upd.coversEval`) or member-wise (`LawCov.eqv`, `Tm.sameBase`) (`Calculus/TermLaws.lean`) |

### The closer's clauses (`Calculus/Closer.lean`)

`sol_prove` closes a leaf inside one `Bool`: the reduction (`Fml.toLS`),
the reads of writes eliminated (`LFml.elimF`), memory read
(`Calculus/MemRead.lean`) and `LFml.close` over what is left, proved sound
once (`LFml.close_valid`, `LFml.decideMem_valid`): a KeY first-order or
arithmetic taclet it subsumes is a clause of that function, not a proof
step.  The terms are typed (W10.4): a value is in its type's range and the
storage has the shape its contract declares, so no clause reads a layout.
"closer clause X" names the definition the clause lives in.

| KeY taclet | Lean | Status | Notes |
| --- | --- | --- | --- |
| `add_literals`, `sub_literals`, `mul_literals`, `div_literals`, `pow_literals` | `fold2` (`Calculus/Decide.lean`, where a term is built), closer clause `Facts.fold2` | subsumed | the interpreter's checked operation on two literals (`BinOp.evalT`), `/` and `%` truncating as solc does, out of range folded to `err` (it reverts); a power folded up to the exponent 256 (`expBig`). `fold2_eval`, `Facts.fold2_eval` |
| `less_literals`, `leq_literals`, `greater_literals`, `qeq_literals`, `equal_literals` | `fold2`, `Facts.fold2` | subsumed | comparisons of two literals |
| `eqClose` | closer clauses `Facts.fold2`, `Facts.direct` | subsumed | `a == a` folds to `true` and `a != a` to `false` on a term that returns; an equation closes on equal normal forms that return |
| `ifthenelse_true`, `ifthenelse_false` | closer clause `Facts.fold3` | subsumed | a conditional on a literal, or with one branch twice |
| `boolean_equal`, `true_to_not_false`, `concrete_not_*` | `fold1`; closer clauses `eqBoolLit`, `Facts.boolDecomp` | subsumed | `!` on a literal; `x == true` read as `x`, `x == false` as `!x`; a boolean premise taken apart |
| `applyEq`, `applyEqRigid` | closer clauses `Facts.addEqR` (`orient`), `Facts.rw`, `Facts.rebuild` | subsumed | a premise `t ≐ v` rewrites `t` to a literal or a lower position everywhere after it, a constant included; every fact is read again under the others (`Facts.rebuild`, KeY's `applyEq` on the antecedent), the pairs apart kept |
| `closeFalse` (in the closer), `replace_known_left` | closer clauses `Facts.refuteEq`, `Facts.apart` | subsumed | a premise refuted (two literals apart, a side that halts, a pair the premises keep apart) closes the leaf; a comparison of a pair kept apart folds (`a == b` to `false`, `a != b` to `true`, `Facts.fold2`) |
| `cut`, `cut_direct` on a `bool` | closer clauses `boolSplit`, `LTm.pick`, `Facts.proveEqN` | subsumed | a case split on a `bool` local, or on a key comparison the normal forms leave open (KeY's `cut` on `k = j`), at most `closeFuel` deep |
| `selectOnShape{Struct,Element,Member,Size}`, `wfFixedSize`, `wfDynSize`, `wf{Fixed,Dyn,Map}Elem` | none | subsumed | a typed storage has its contract's shape (`Storage C`): a read at a path its type gives returns, and `has` at a member or a mapping's entry is its base's (`hasOf`, `hasN`) |
| `sizeNotNegative` | closer clause `Facts.range` | subsumed | a length is at least `0`, its type's range (`PrimTy.lo`), KeY's `\add(0 <= selectSt<[int]>(st, size) ==>)`. The slot at `(len + 1) - 1` after a `push` is the one pushed: `(a + b) - b` cancels (`Facts.cancel`) and `len < len + 1` folds (`Facts.ltSucc`, Lean only), so `storagePushReadBack` is derived (W10.4) |
| `arrayLengthNonNegative` with a bound a premise gives | closer clauses `Facts.hasIdxDyn`, `Facts.hasRange` | subsumed | a dynamic array has a slot at every index its ranges put below its length |
| `inEqSimp_*` on bounds by constants | closer clauses `Facts.range`, `Facts.rangeOp`, `Facts.arithOk`, `ltDec`, `leDec`, `Facts.cmpFold`, `Facts.lessBnd`, `Facts.cmpBnds`, `Facts.neEdge`, `Facts.neBnd` | subsumed | a value's type range, a premise `t op k` or `t ≠ k` narrowing `t`, ranges added through `+`, `-`; a comparison whose ranges decide it folds, and an addition or subtraction whose operands' ranges keep it in its type returns |
| `polySimp_*` on `(a + b) - b`, `(a - b) + b` | closer clauses `Facts.cancel`, `Facts.cancelAdd` | partly | the sum or difference cancelled to `a` where it returns |
| — (KeY's polynomial normal form) | closer clause `isTwo` in `Facts.fold2` (`evalT_two_mul`) | Lean only | `2 * a` read as `a + a`: both check the one integer `2·a` against the range |
| — | closer clause `Facts.ltSucc` | Lean only | `a < a + c` for a positive literal `c` reads `true` where the sum returns |
| — (a guard is Lean's) | closer clause `kiteBool?` | Lean only | `c = true ? true : false` read as `c` |
| — (a guard is Lean's) | closer clauses `kiteAssert`, `assertArg?`, `Facts.addAsserts` | Lean only | a guard `kite(c, true, a, err)` that returns, like `assert(c)`, gives the premise `c ≐ true` |
| `inEqSimp_*` on differences, `polySimp_*` in general | — | open | no bound on `y - x` for two symbolic terms, no polynomial normal form |
| — (Lean only: a cost bound) | `Seq.closeSize`, `Seq.stackSize` (`Calculus/DecideComplete.lean`), `LFml.fits`, `LFml.stDepth` | Lean only | a leaf whose reduction is past `closeSize` nodes, or stacks more than `stackSize` storage updates, is left to the walk |

### The storage readers (`Calculus/Decide.lean`)

`sol_decide`'s elimination (`LTm.elim`) is the typed Theory read
symbolically: a storage term is eliminated to its guard and a reader of its
observations (`SFun`; word, live length, presence, `CK`), each write a
`save` at its symbolic path (`SPath`) of the value there with the operation
made on it.  A read is compared with a write by `relSegs` (the symbolic
`Path.strip?`, two keys the terms do not settle one `kite`: `keyCmp`,
`keyTree`); at or below the write it is the operation's reading of the rest,
apart from it the old read (`writeAt`).  Each reader is proved to read the
observations of the value it stands for (`VRd.Rep`, `SRd.Rep`,
`Calculus/DecideEval.lean`) through the bridges of `Theory/Typed/Obs.lean`
(`Storage.obs_write`, `obs_delete`, `obs_push`, `obs_pop`, …); the Theory
law is cited by its solkey name.  Under the premises the readers compare
what the premises say (`LFml.elimF`, `Calculus/ElimFacts.lean`).

| KeY taclet | Lean | Status | Notes |
| --- | --- | --- | --- |
| `findDefinition*`, then `selectOnSaveCons` (`a1 = a2` down the written path, `a1 ≠ a2` off it), `saveOnEmptyPrim` at the word | `SFun.save`, `writeAt` with `relSegs`, `ovRS`, `svalRd` | subsumed | the read compared with the write a segment at a time: the written value's reading of the rest at or below it (a word the word written), the old read apart. `SFun.save_rep`, `writeAt_rep`, `relSegs_sound`, `ovRS_rep`, `svalRd_rep`; the Theory's `Obs.findOnSave`, `findOnSavePrefix`, `findOnSaveFrame`, `lenOnSaveFrame` |
| `selectOnDelAtCons`, then `delFieldDefault`, `delFieldRef`, `delFieldMap`, `delFieldFixed`, `selectStDelNode{Map,Ref,Fixed,Element,Member,Size}`, `selectStDelNodeFixed{Element,Size,Value}` below the deleted node | `SFun.delAt`, `writeAt` with `delRS` | subsumed | the symbolic `TVal.delR`: at and below the deleted path the default, a mapping's entries and a dynamic array's slots past its live end kept, a fixed-size array's length kept and a dynamic one's `0`; the node's kind is its type. `SFun.delAt_rep`, `delRS_rep`; the Theory's `Obs.findOnDelAt`, `findOnDelAtFrame`, `lenOnDelAtFrame`, `Obs.delAt_word_below` |
| `selectOnSaveEmptyRef`, `selectOnSaveEmptyFixed`, `selectOnSaveEmptyIndexStruct`, `selectOnSaveEmptyIndexPrim`, `selectOnSaveEmptyMember`, `selectOnSaveEmptySize`, `selectOnSaveEmptyDefault` | `SFun.save` with `ovRS`, the source read by `Op2.elim` at `sfind` (`SRd.at`) | subsumed | the symbolic `TVal.ovR`: member by member, element by element over the old slots, the old elements past the new length deleted, the old slots past both kept. `ovRS_rep`, `sfind_rep`; the Theory's `Obs.copyTo` (`SVal.obs_overlay`) |
| `selectOnSaveEmptyMap` below a key of a copy | `ovRS` at a key | subsumed | a mapping met in both keeps the target's entries; a well-typed program copies none, solc rejects it |
| `selectOnSaveCons` on a `size` write, `selectOnDelAtCons` past the end (`storagePushValueSave`, `storagePopSave`) | `SFun.push` with `pushRd`, `SFun.pop` with `popRd`, `SFun.extend` with `extendRd` | subsumed | the symbolic `TVal.pushA`, `popA`, `extendA`: a read below the array compares its index with the old length, the pushed value (stripped, `stripRS`) there, the old element below it; a pop deletes the last element unless `keep`; the length one more or one less (`LTm.succK`, `predK`). `SFun.push_rep`, `SFun.pop_rep`, `SFun.extend_rep`, `pushRd_rep`, `popRd_rep`, `extendRd_rep`; the Theory's `Obs.findOnPushFrame`, `findOnPopFrame` |
| `storageFieldWriteSave`, `storagePushValueSave` with `sp` a stale alias (bound before the storage last changed, dangling after a `pop`) | the alias's path, its index checked in the storage it was bound in (`pathAtIn`), then `SFun.save`/`SFun.push` at it | subsumed | KeY's `consr(sp, at(ie))` names a slot, checked only when `storageIndexReadArrayBindLocalRoot` bound it: the write is a plain `save` there.  The observations keep an array's slots past its live end (`SLoc.dangling`, `TVal.delR`), so no reader of its own is needed. `pathIdx_rep`, `SFun.save_rep` |
| `storagePushLengthSaveReferenceElement` (`size ≠ at(n)`: the recycled slot is the old one) | `extendRd`, the slot past the end made live as it is | subsumed | a word's slot reset, a missing slot at its default (`TVal.extendA`); a push through a stale alias lands in the recycled array, its length read off the slot. `extendRd_rep` (`Storage.obs_pushPlace`) |
| `selectStDelNodeIndexStruct`, its `iv ≥ size` branch | `delRS` at an index past the live end | subsumed | a `delete` keeps the slots past the end (`TVal.delR`). `delRS_rep` |
| `selectOnSaveEmptyIndexStruct`, branches 2 and 3, under the folded copy of `storageRootWriteCopySource` or `storageFieldWriteCopySource` | `ovRS` at an index | subsumed | below the new length the new element, past it and below the old length the old element deleted, past both the old slot (`TVal.ovR`). `ovRS_rep` |
| — (Lean only: KeY's `save` and `delAt` are total, the interpreter's halt) | `SFun.ok`, the guard of each storage operation | Lean only | a write returns where the storage below does, its path and value return and the location is there (the `has` observation); a push where the array is not full (`maxLen`); an index checked where it is a key or below the length (`boundG`). `SFun.save_rep` (`Storage.write_isSome`), `SFun.push_rep` (`Storage.push_isSome`) |
| — (Lean only: a read the elimination cannot follow) | `ElimM.ofOrig`, `SFun.ofOrig` | Lean only | a storage term it has no reading for (`mtSt`, a memory read, a path it cannot follow) is kept as it is and read as a term (`fbRd`): exact, left to the closer |

### The closer's memory clauses (`Calculus/MemRead.lean`)

The clauses `sol_decide` reads memory with.  Each row is one solkey taclet,
named as solkey names it — of `memoryRules.key`, `structMemoryRules.key`,
and the program rules of `solidityProgramRules.key` that write memory — or,
under "—", a guard only Lean has, because the interpreter's memory
operations halt where KeY's are total.  A memory term of the reduction is
the tree of its writes and allocations as the program built it
(`write(m, a, v)`, `addM(m, R)` with its root `alloc(m, R)`, `copySt(m, S)`
with its root `copy(m, S)`), and a read walks it from the newest node down
(`LTm.memRes`, `memReadN`, `memIReadN`, `lenAtN`), comparing addresses
without running anything.  Each rewrite is an equation of reads
(`LTm.memRes_eval`): the readers are proved on the typed heap directly, with
no agreement module of their own, and the Theory column is the law of
`Theory/Typed/Mem.lean` under its solkey name (section "The laws by solkey's
names"), with the lemma it restates.  A name is an identity term: KeY's
`idC(freshIdp, flds)` is the path `LTm.freshPath?` reads below the root
`alloc(m, R)` of `addM(m, R)`.

| KeY taclet | closer clause | soundness | Theory law | status |
| --- | --- | --- | --- | --- |
| `readOnWrite` | `memReadN`, `.write` arm: the address written (`LTm.beqR`) reads the word written | `memReadN_eval`, `LTm.read_write_same` | `Grown.readOnWrite` (`Grown.writeT_facts`) | used; an address neither the same term nor apart keeps the read, where KeY's is an if-then-else |
| `readOnWrite` at an `Identity` | `memIReadN`, `.write` arm | `memIReadN_eval`, `LTm.iread_write_same` | `Grown.readOnWrite` | used |
| `readOnWrite` `\else` | the `.write` arms: an address apart (`LTm.apart?`: two members, a member and an element, two literal indices of one identity) reads below | `LTm.read_write_apart`, `LTm.iread_write_apart'`, `LTm.apart?_resolve` | `Grown.readOnWriteFrame` (`Grown.writeT_facts`) | used |
| `readOnAddM` `\else` | the `.addM` arms: an address whose object is older than the allocation (`LTm.boundedIn`: allocated on the spine below it, or read out of a memory there) reads below | `LTm.read_addM_old`, `LTm.iread_addM_old`, `LTm.boundedIn_eval` | `Grown.readOnAddMFrame` (`Grown.readAddM_old`) | used |
| `readOnAddM` `\then`, `initMember`, `defaultValueInt`, `defaultValueBool` | `memReadN`, `.addM` arm: an address at a member path of the fresh root (`LTm.freshPath?`, `Ty.memberTy`) of a primitive type reads its default (`PrimTy.dflt`) | `LTm.read_addM_fresh`, `LTm.freshPath_eval` | `Heap.initMember` | used |
| `initElement` | the same, at a literal index of a fixed-size array (`Op2.freshStepL`) | `LTm.read_addM_fresh` | — | used |
| `initSize`, `sizeOfDyn` | `lenAtN`, `.addM` arm: a fresh dynamic array's length is `0` | `lenAtN_eval` (`Heap.allocDefault_array_len`) | `Heap.initSize` | used |
| `sizeOfFixed` | none: a fixed-size array's length is its type's `n` (`lenCond`) | `lenCond_iff` | — | subsumed |
| `sizeOfLeaf` | none: no well-typed program reads the length of a struct or a primitive | — | — | unreached |
| `defValResolve` | none built: a default is read at the type the path declares (`PrimTy.dflt`), so `cast(defVal)` never occurs | `LTm.read_addM_fresh` | — | subsumed |
| `idShapeDef`, `shapeAtNil`, `shapeAtFixed`, `shapeAtFixedMapElement`, `shapeAtDyn`, `shapeAtDynMapElement`, `shapeAtMember` | none: an allocation carries its type (`addM(m, R)`), read down the path by `Ty.memberTy` | `LTm.freshPath_eval` | — | subsumed |
| `shapeAtMap`, `shapeAtLeafElement`, `shapeAtLeafMapElement` | not reached: memory holds no mapping (`alloc`'s and `addM`'s `mapFree` premise), and no path goes below a primitive | — | — | unreached |
| `idCCDef` | an allocation's root is `alloc(m, R)`, at the empty path (`Op1.freshStepL`) | `LTm.freshPath_eval` | — | used |
| `initIdentity` | `LTm.freshPath?` (`Op2.freshStepL`): an identity read out of the fresh object, `iread(addM(m, R), a)`, is named by `a`'s path, KeY's `idC` one segment longer | `LTm.freshPath_eval` | not restated: a reference member is allocated with its parent | used |
| `readFromEmptyMemory`, `newFromEmptyMemory` | none: the bottom of a leaf's memory is the global part's heap (`memory`), not `mtMem` | — | not restated | unreached |
| `readREmpty`, `readRCons` | none: a path is read one address at a time (`mfield`, `mat`), each a read of its own | — | not restated | subsumed |
| `newFromAdd` | `LTm.identApart?`: two identities differ where one is fresh over a memory (`LTm.freshOver?`) the other is older than (`LTm.boundedIn`) | `LTm.identApart?_ne`, `LTm.freshOver?_eval` | `Grown.alloc_fresh` (`Grown.alloc_id_ge`, Lean only) | deviation: no `new` term |
| `newFromWrite` | none, likewise: a memory on the spine below another grows to it (`LTm.onSpine_grows`) | — | — | deviation |
| `readFromCopyToStorage` `\then` | `copyFieldRd?`: a member of a copy's root reads the storage it copied there (`find(st, q.f)`), which the elimination then reads (`LFml.closeMem`) | `copyFieldRd?_eval` | `SVal.readFromCopyToStorage` (`SVal.copyStToM_field`) | used |
| `readFromCopyToStorage` `\else`, `readFromCopyToStorageIdentity` `\else` | the `.copySt` arms: an address whose object is older reads below | `LTm.read_copySt_old`, `LTm.iread_copySt_old` | `Grown.readFromCopyToStorageFrame` (`Grown.readCopySt_old`) | used; the premise is the object older than the copy, where KeY's is `idp1 ≠ idp2` |
| `readFromCopyToStorageIdentity` `\then` | none: an identity member of a copy is kept as its read | — | — | open (its `\else` is the row above) |
| `findDefinitionSize` (`structRules.key`) on a copy | `lenAtN`, `.copySt` arm: a copy of `new T[](n)` has length `n` | `lenAtN_eval` (`newArrT_copy_len`) | — | partly: a copy of a storage array keeps its length read |
| `findOnCopy`, `selectOnCopyMemPrim`, `selectOnCopyMemRef` | `copyMemRd`, `memRd` (`Calculus/Decide.lean`): a memory object read as the stored value it copies to, down the segments (a member's address, an element within its array's length, an object's identity read there) | `memRd_rep`, `copyMem_rep` (`Calculus/DecideEval.lean`) | `MVal.findOnCopy` (`MVal.copyMToSt_field`) | used |
| `memoryToStorageStoreRoot`, `memoryToStorageFieldCopyRoot`, `memoryToStorageFieldCopyField`, `memoryToStorageIndexMappingCopyRoot`, `memoryToStorageIndexArrayCopyRoot` | `save(storage, p, copyMem(m, i))` eliminated as any `save` (`SFun.save`, `ovRS`), its value read by `copyMemRd` | `SFun.save_rep`, `copyMem_rep` | `MVal.findOnCopy` | used |
| `memoryReferenceDeclFreshAlloc`, `memoryRootDeleteFreshRebind`, `memoryArrayFreshAlloc`, `memoryStorageCopy` (after `memoryStorageCopyUnfold`) | the pair `{x := alloc(m, R) ‖ memory := addM(m, R)}` (a copy: `copy(m, S)`, `copySt(m, S)`), both elements read in the update's pre-state (`UpdElem.toLS`): `x` names the root the allocation takes | `Upd.toLS_sound` | — | deviation: KeY's two sequential updates over one Skolem `freshIdp` (`\skolemTerm`, `\sameUpdateLevel`) |
| `memoryFieldDeleteReference`, `memoryIndexDeleteReference` | the reference written is a fresh root's identity, read back by `memIReadN` and compared by `LTm.identApart?` | `memIReadN_eval` | — | used |
| — (Lean only: KeY's memory operations are total, the interpreter's halt) | `MemQ`, `memCondN`: a memory term returns where each write lands (a member of an object of the memory, an element within its array's bounds: `lenCond`, the program rules' `\add(0 <= ie & ie < read(memory, mv, size))`) and each copy's source returns (`svConds`) | `memCondN_sound`, `lenCond_iff` | — | used |
| — (Lean only: a guard of a memory) | `guardQ`, `guardL`, `seqMemL`: a guard `d; a` read as the words its memory's returning comes to, a word the closer folds to `true` dropped | `guardQ_sound`, `guardL_eval`, `seqMemL_eval` | — | used |
| — (Lean only: a read walks every write) | `memFuel`: a read walks at most 64 writes and allocations down, then is kept | — | — | used |

## The data-structure theories

The rows above are the *program* calculus. Its updates are written over
symbols — `find`, `save`, `selectSt`, `read`, `write`, `addM` — that solkey
declares in `structHeader.key`/`memoryHeader.key` and defines nowhere; their
meaning is the taclet sets of `structRules.key`, `memoryRules.key` and
`structMemoryRules.key`. `Solidity/Theory/` is that meaning on typed values,
each taclet a law stated under its solkey name: a storage is its
observations at typed locations (`Theory/Typed/Obs.lean`), a memory a heap
grown from the global part's (`Theory/Typed/Mem.lean`).  Paths are typed
(`Path T U`): a member is `.field`, `at(i)` an index, `size` the live
length, read as its own observation; `listRules.key` needs no module, it is
`List`.  The side conditions on two paths of segments (`Theory.diverges`,
`Theory.lengthSeg`) are `Theory/Segs.lean`'s.

**The storage copy fold is followed eagerly.** solkey folded `copyAt` into
`save`: `save(st, nil, v)` is an irreducible leaf that the eight copy rules
write and `selectOnSaveEmpty*` read through (`c80a54494c`, `8c5c69ca25`).
Here a copy is one `save` too (`Obs.copyTo`), of the new value laid over the
old one, computed from the type (`TVal.overlay`, one component at a time:
`TVal.ovR`): no lazy leaf, so the `selectOnSaveEmpty*` rows are the reads of
that overlay.  `docs/solkey-feedback.md` carries the request that solkey drop
the fold.

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

### `structRules.key` → `Theory/Typed/Obs.lean`

The laws are stated once over any location family (`ObsLoc`: a state
variable's path, a dangling one, a path below a value), and each is total:
a location not there reads the default word, length `0`, and `has = false`.
Each operation of the interpreter is, read by its observations, the
operation here (`Storage.obs_save`, `obs_write`, `obs_delete`, `obs_push`,
`obs_pop`, `SVal.obs_overlay`, …).

| KeY taclet | Lean | Status |
| --- | --- | --- |
| `findDefinition*`, `selectOnSaveCons` (`a1 = a2`), `saveOnEmptyPrim` | `Obs.findOnSave`, `Obs.findOnSavePrefix` (`find_save_same`, `find_save_below`) | done: a word written reads back; a read above a save sees the save made below it |
| `selectOnSaveCons` (`a1 ≠ a2`) | `Obs.findOnSaveFrame`, `Obs.lenOnSaveFrame` (`find_save_frame`) | done, the frame's premise the decidable `(ObsLoc.strip? p q).isNone` |
| `selectOnDelAtCons`, `delField*`, `selectStDelNode*`, `selectStDelNodeFixed*` | `Obs.delAt` (`TVal.del`, `TVal.delR`), `Obs.findOnDelAt`, `Obs.findOnDelAtFrame`, `Obs.lenOnDelAtFrame`, `Obs.delAt_word_below` | done: the reset is computed from the type, a mapping's entries and an array's slots past its live end kept; no premise on the node's kind |
| `selectOnSaveEmpty*` (the copy fold) | `Obs.copyTo` (`TVal.overlay`, `TVal.ovR`) | done eagerly (above) |
| `storagePushValueSave`, `storagePopSave` (two `save`s each) | `Obs.push` (`TVal.pushA`), `Obs.pop` (`TVal.popA`), `Obs.extend` (`TVal.extendA`); `Obs.findOnPushFrame`, `Obs.findOnPopFrame` | done: a push or a pop is one operation, its frame `save`'s |
| `selectSt<[Struct]>(s, r)` | `Obs.select`, `Obs.select_save`, `Obs.select_copyTo`, `Obs.select_delAt` and their `_ne` | done: the struct at a root as a storage of its members |
| `selectOnEmptyStorage`, `saveOnEmptyStorage`, `defaultValue*` | `Storage.obs` of the typed empty storage (`Storage.init`) | done: a location reads its type's default |
| `selectOnEmptyStorage`, `saveOnEmptyStorage` in the closer | `sol_close_mt` (`Calculus/Close.lean`, `Calculus/CloseScoped.lean`) | Lean only: `mtSt` evaluates to the roots at their defaults (`CloseS.eval_mtSt`); `sol_decide` keeps `mtSt` as a term it does not read (`SFun.ofOrig`) |
| `selectOnShape*`, `wf*`, `fixed*`, `wfFixedIsFixed`, `wfDynIsNotFixed`, `fieldShapeDef` | `wellTypedStorageB`, `SVal.hasTy` (`Typing/Storage.lean`) | **not modelled as taclets**: a typed storage is in its contract's shape, clause for clause |
| `sizeNotNegative` | — | **arch**: a length is a `uint`, at least `0` by its type (the closer's `Facts.range`) |

### `memoryRules.key`, `structMemoryRules.key` → `Theory/Typed/Mem.lean`

A memory is a heap grown from the global part's (`Grown H`), an address an
identity with a member or an element (`MAddrT T`); each law is a statement
about `Grown.readT`, `writeT` and the allocations, generic in the types it
is read at.  The section "The laws by solkey's taclets" restates each by its
solkey taclet's name (a `\else` as the name with `Frame`), proved by the
lemma beside it.

| KeY taclet | Lean theorem | Status |
| --- | --- | --- |
| `readOnWrite` `\then` | `Grown.readOnWrite` (`Grown.writeT_facts`) | done |
| `readOnWrite` `\else` | `Grown.readOnWriteFrame` (`Grown.writeT_facts`) | done |
| `readOnAddM` `\else` | `Grown.readOnAddMFrame` (`Grown.readAddM_old`) | done |
| — (the freshness behind `newFromAdd`) | `Grown.alloc_fresh` (`Grown.alloc_id_ge`) | Lean only: an allocation's identity is past every older one |
| `readOnAddM` `\then`, then `initMember` | `Heap.initMember` | done: a member of a fresh struct reads its type's default |
| `initSize`, `sizeOfDyn` | `Heap.initSize` (`Heap.allocDefault_array_len`) | done |
| `readFromCopyToStorage` `\then` | `SVal.readFromCopyToStorage` (`SVal.copyStToM_field`) | done |
| `readFromCopyToStorage` `\else`, `readFromCopyToStorageIdentity` `\else` | `Grown.readFromCopyToStorageFrame` (`Grown.readCopySt_old`) | done: the premise is the object older than the copy, where KeY's is `idp1 ≠ idp2` |
| `findOnCopy` (a one-member path), `selectOnCopyMemPrim` | `MVal.findOnCopy` (`MVal.copyMToSt_field`) | done |
| `readFromEmptyMemory`, `newFromEmptyMemory` | — | not restated: memory grows from the global part's heap, never from an empty one |
| `readREmpty`, `readRCons` | — | not restated: a path is read one address at a time |
| `initIdentity` | — | not restated: a reference member is allocated with its parent, so it is a member read like a word |
| `defaultValueInt`, `defaultValueBool`, `defValResolve`, `idShapeDef`, `shapeAt*`, `sizeOf*`, `idCCDef` | — | not restated: an allocation carries its type, and a default is read at the type the path declares |

### The Theory's laws as term taclets (`Calculus/TermLib.lean`)

A rule on terms is a constructor of `TermTaclet` (W9.1), on scoped terms
`Tm C Γ .val`, applied on a sequent by name (`rw [findOnSave]`,
`Proves.rewrite`); `TermTaclet.sound` reads its two terms through the scoped
`Tm.denote` and closes the case by the Theory lemma below (`Tm.Theq`).
Side conditions are syntactic `Bool`s on scoped paths, closed by `rfl`
(`Tm.hasSeg`, `Tm.diverges`, `Tm.sameSegs`, `Tm.shift?`, `Tm.findLit?`),
or a hypothesis of the chain (`Tm.KindFreeAt`); `SCtxS` is a storage
context. solkey has none of these as a taclet: they are Lean-only rules
stated on terms, each sound by the typed law it cites.

| Term taclet | Lean (`TermTaclet`) | Theory lemma | Printed rule (the untyped Theory's, deleted at W10.4) | Notes |
| --- | --- | --- | --- | --- |
| `findOnSave` | `TermTaclet.findOnSave` | `Obs.findOnSave` (`Theory/Typed/Obs.lean`) | `findOnSave` | `find(save(s, p, v), q) ≐ v` for a literal word `v`, `q` the path `p` its checks aside (`Tm.sameSegs`: `p[i]@S` is `p[i]`): a copy reads back the new value laid over the old, which is `v` only for a word |
| `findOnSaveFrame` | `TermTaclet.findOnSaveFrame` | `Obs.findOnSaveFrame` | `findOnSaveDifferent` | any written value, `p` diverging from `q` |
| `findMemberCons` | `TermTaclet.findMemberCons` | `Obs.select` (by definition: `select(s, r)` reads below `r`) | — | solkey's `consRcons`, `consRnil`, `findDefinitionMemberCons`/`Prim`: `find(s, r.p) ≐ find(select(s, r), p)`, the path read from its head (`Tm.shift?`), at any depth |
| `findOnSave` in a storage of members | `TermTaclet.findOnSaveIn` | `Obs.findOnSave` | `findOnSave` | `findIn(saveIn(s, p, v), p) ≐ v` for a word `v`, under a `select` (`sts`): the same law at `Contract.ofStruct` |
| `findMemberCons` in a storage of members | `TermTaclet.findMemberConsIn` | `Obs.select` | — | `findIn(s, f.p) ≐ findIn(select(s, f), p)` under a `select` (`Tm.shiftIn?`) |
| `selectOnSaveMember` | `TermTaclet.selectOnSaveMember` | `Obs.select_copyTo` | — | solkey's `selectOnSaveCons` at `a1 = a2`: `find(select(save(s, r.p, v), r), q) ≐ find(save(select(s, r), p, v), q)` |
| `selectOnSaveFrame` | `TermTaclet.selectOnSaveFrame` | `Obs.select_copyTo_ne` | — | solkey's `selectOnSaveCons` at `a1 ≠ a2`: a write under another root is not seen from `r` |
| `selectOnDelAtMember`, `selectOnDelAtFrame` | `TermTaclet.selectOnDelAtMember`, `TermTaclet.selectOnDelAtFrame` | `Obs.select_delAt`, `Obs.select_delAt_ne` | — | the same for a delete, `delAt(s, p)` being `save(s, p, delValue(find(s, p)))` |
| `selectOnSaveMemberIn`, `selectOnSaveFrameIn`, `selectOnDelAtMemberIn`, `selectOnDelAtFrameIn` | `TermTaclet.selectOnSaveMemberIn`, `TermTaclet.selectOnSaveFrameIn`, `TermTaclet.selectOnDelAtMemberIn`, `TermTaclet.selectOnDelAtFrameIn` | the same, `SCtxS.fill_denote` | — | the four in a storage context `K` of saves, deletes and selects (`SCtxS`), which the arrow finds: solkey rewrites a storage term wherever it stands |
| `selectOnSaveMember`, `selectOnSaveFrame`, `selectOnDelAtMember`, `selectOnDelAtFrame` at a member | `TermTaclet.selectOnSaveMemberAt`, `TermTaclet.selectOnSaveFrameAt`, `TermTaclet.selectOnDelAtMemberAt`, `TermTaclet.selectOnDelAtFrameAt` | `Obs.select_copyTo`, `Obs.select_delAt` and their `_ne` (`Tm.selectOnSaveMemberAt_denote`, …) | — | the four one `select` down, in a storage of members: `selectIn(saveIn(s, f.p, v), f)` is `saveIn(selectIn(s, f), p, v)`, a write under another member `f' ≠ f` unseen; in a storage context `K` |
| `findOnDelAt` | `TermTaclet.findOnDelAt` | `Obs.findOnDelAt` | `findDelAt` | where `find(s, p) ≐ w` for a word `w`, the delete reads its default at `p` (`sameSegs`) |
| `findOnDelAtSave` | `TermTaclet.findOnDelAtSave` | `findOnDelAt` over `findOnSave` | `findDelAt` | a delete over a written word, the three paths one path their checks aside |
| `findOnDelAtValue` | `TermTaclet.findOnDelAtValue` | `Obs.findOnDelAt` | `findDelAt` | `find(delAt(s, p), q) ≐ delValue(find(s, q))`, `q` the path `p` its checks aside: the delete's effect at its own path, the value left for a later law (`delValueLit`, or a read below a mapping member) |
| `delValueLit` | `TermTaclet.delValueLit` | by definition (`Op1.denote` of `delValue`) | `delValueDefault` | `delValue(w) ≐ default(w)` for a literal word |
| `findOnDelAtBelow` | `TermTaclet.findOnDelAtBelow` | `Obs.delAt_word_below` (`TVal.delR`) | `findDelAtFields` | a word at or below a deleted node reads its default, where the deleted storage writes the word there (`Tm.findLit?`) and the delete resets every word below `p` (`Tm.KindFreeAt`, a premise of the chain: a mapping's entries and an array's slots past its end are kept, `TVal.delR`) |
| `findOnDelAtBelow` in a storage of members | `TermTaclet.findOnDelAtBelowIn` | `Obs.delAt_word_below` | `findDelAtFields` | `findIn(delAtIn(s, p), q) ≐ defVal` under a `select`: `q` below the member path `p` by members (`Tm.extendsIn`), `s`'s member-wise writes giving the word there (`Tm.findLitIn?`), the node no mapping (`Tm.KindFreeAt`, at a storage of members and a member path, `Srt.pathAt`); a chain's `~[findOnDelAtBelow]~>` names both.  Past the program it is covered where the update holds the delete (`Upd.coversLit`, `Tm.findDelBelowAt`: a read by members below a delete returns) |
| `findOnDelAtFrame` | `TermTaclet.findOnDelAtFrame` | `Obs.findOnDelAtFrame` | `findDelAtOutside` | |
| `findOnPushFrame`, `findOnPopFrame` | `TermTaclet.findOnPushFrame`, `TermTaclet.findOnPopFrame` | `Obs.findOnPushFrame`, `Obs.findOnPopFrame` | — | a push or pop is one term here, not two saves.  Past the program they do not rewrite inside an update's right-hand sides (a law rewrite there asks both sides push-free, `Tm.pushFree`, W9.8.5), only in its equations' sides |
| `lenOnSaveFrame`, `lenOnDelAtFrame` | `TermTaclet.lenOnSaveFrame`, `TermTaclet.lenOnDelAtFrame` | `Obs.lenOnSaveFrame`, `Obs.lenOnDelAtFrame` | `findOnSaveDifferent`, `findDelAtOutside` at `p.size` | `len(save(s, q, v), p) ≐ len(s, p)`, `len(delAt(s, q), p) ≐ len(s, p)` where `q` leaves `p.length` (`Tm.divergesLen`): a length is a read at `p.length`, one term here (`Term.len`) |

### The laws of memory reads (`EvalLaw`, `Calculus/TermLaws.lean`)

A memory read (`read`, `copyMem`, `copySt`) denotes its run, so a law of one
is no Theory equation but a refinement of the interpreter: where the read
returns, its replacement returns the same (`EvalLaw.sound`,
`Tm.EvalRefinesAt`).  A chain's line past the program applies one in an
update's right-hand side under any modality where the update holds the
write the law reads back (`Upd.coversEval`, `LawCov.eval`, `FmlRw.lawUpdS`).

| Law | Interpreter lemma | KeY taclet | Notes |
| --- | --- | --- | --- |
| `readOnWrite` | `Heap.readAddr_writeAddr_same` (`Theory/Typed/Mem.lean`) | `readOnWrite` `\then` | `read(write(m, a, v), a) ⇝ v` for a literal `v` |
| `findOnCopy` | `copyMem_member` | `findOnCopy` over `findOnSave` | `find(save(s, p, copyMem(mtSt, m, i)), p.f) ⇝ read(m, i.f)`: the printed trace's one step from the `find` into memory |
| `readFromCopyToStorage` | `copyStToM_member` | `readFromCopyToStorage` `\then` | `read(copySt(m, find(s, p)), freshId(copySt(m, find(s, p))).f) ⇝ find(s, p.f)` |
| `readOnAddM` | `copyStToM_default_readPath` (`Calculus/ReadWrite.lean`) | `readOnAddM` `\then`, then `initMember`, `initElement` | `read(addM(m, R), a) ⇝ default` for a primitive member or fixed element at a fresh path of the allocation (`Tm.freshPath?`, `RefTy.memberTy`) |
| `readOnAddMFrame` | `readAddr_heapExt`, `allocDefault_heapExt` | `readOnAddM` `\else` | `read(addM(m, R), a) ⇝ read(m, a)` where `a`'s identity is allocated strictly earlier on `m`'s spine (`Tm.boundedIn`) |
| `readOnAddMFrameIdentity` | the same | `readOnAddM` `\else` at `Identity` | the twin at the identity sort |
| `readOnWriteFrame` | `writeAddr_setObj` | `readOnWrite` `\else` | `read(write(m, a, v), b) ⇝ read(m, b)` where `a` and `b` never meet (`Tm.apart?`: different members, a member and an element, one object at different literal indices) |
| `readOnWriteFrameIdentity` | the same | `readOnWrite` `\else` at `Identity` | the twin at the identity sort |
| `readOnWriteIdentity` | `Heap.readAddr_writeAddr_same` | `readOnWrite` `\then` at `Identity` | `read(write(m, a, ref(i)), a) ⇝ i` |
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

The typed laws keep solkey's names (`Grown.readOnWrite`, `MVal.findOnCopy`,
…; a taclet's `\else` as its name with `Frame`, and the storage laws
`Obs.findOnSave`/`findOnSaveFrame` name `selectOnSaveCons`'s two
branches), which is what makes this file a map; a law with no
solkey counterpart is marked Lean only at its row.  The untyped Theory's
enumeration of its printed rules (`TheoryRule`, `lemmaNames`) was deleted
with it at W10.4.

### Deviations

Where the theory or a taclet differs from KeY, each stated once at its row:

- **Eager against lazy.** `addM(m, R)` carries the allocated `RefTy` (KeY's
  `readOnAddM` resolves a fresh object's slot to `init<[α]>` at the
  reader's sort; `Semantics.allocDefault` materializes the object), and a
  default is read at the type its path declares; a copy is computed from
  the type (`TVal.overlay`), not a lazy leaf.
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
- **Deletes are computed from the type** (`TVal.delR`): a mapping's entries
  and an array's slots past its live end are kept, with no premise on the
  node's kind; `delete` through a fixed-size array element is open in KeY
  and sound here ("Storage delete").
- **Memory paths are sources as they stand**, so KeY's four memory capture taclets are
  unclaimed and the `MemRef` index captures are `find same` (see their rows).
- **Shapes are types.** An allocation carries its type and a path is
  typed, so `fieldShape`, `shapeAt` and the `wf` taclets are not modelled:
  a typed storage and heap are in the shape their types declare.
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
