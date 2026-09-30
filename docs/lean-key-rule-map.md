# KeY taclet → Lean `Taclet` mapping

The name-by-name map from solkey's `solidityProgramRules.key` (plus
`ifThenElseRules.key`) to `Solidity.Taclet`, the inductive of
`Solidity/Calculus/Rules.lean`. One row per taclet, grouped by family as
solkey's file groups them.

**Pinned to solkey `f2eb3d98eb`** (311 program taclets, four `\heuristics`
classes; `Calculus/KeyTaclets.lean` is the vendored enumeration). Every rule
of `Calculus/Rules.lean` is a constructor of one inductive `Taclet C k m s p`,
written `dl{ ⟨[ s; ]⟩ ⇝ p }` and named as solkey names the taclet(s) it
transcribes — an operator family or a receiver/source-kind split is one
constructor for several taclets, and a taclet the calculus has no strategy
for (the five literal-condition `if` shortcuts) or no counterpart to (the
nested blocks `emptyModality`/`blockEmpty` erase, the four memory captures)
has none.  The callback semantics of `transfer` is a second inductive,
`CallbackTaclet` (`Rules.lean`), sound for the callback reading of the
modalities (`Calculus/Callback.lean`) rather than for `Stmt.run`.

## This file is machine-checked

The correspondence below is not this file's alone to keep straight;
`Solidity/Calculus/RuleShapes.lean` checks it against the environment:

- **`tacletOrigins`** — one row per `Taclet` constructor, naming the taclet(s)
  it transcribes as a typed `KeyOrigin` (`.taclet t` or `.merged [t₁, …]`)
  over the `KeyTaclet` enumeration. `#check_constructor_table` fails the build
  if a constructor is missing a row or a row names one that does not exist —
  a misspelled or renamed taclet is a type error, not a stale table cell.
- **`unclaimedTaclets`** — the taclets no constructor claims, each with the
  reason it is excused (quoted in the tables below).
- **`callbackOrigins`** — the same for `CallbackTaclet`'s two constructors.
- **`taclets_partitioned`** — every one of the 311 taclets is claimed by some
  row or excused, never both: `claimedTaclets_count = 300`,
  `unclaimedTaclets_count = 11`.  Every row claims a taclet: a rule with none
  is a `LeanTaclet`, not a `Taclet` (`RuleShapes.leanTaclets`), and there is
  one, `functionCallArgCapture`, below. A taclet may be claimed by two constructors
  (`memoryFieldWrite`/`memoryIndexWriteArray` by the value write and the
  reference copy; the member reads by the `.length` rules, since KeY reads
  `sp.length` as the member `length`) — the tables below list both.

What stays prose here is what a typed `KeyOrigin` cannot say: *why* a merge is
a merge, and the symbol-by-symbol map for the update vocabulary and the
data-structure theories in the second half of this file.

**The storage copy fold is not followed, by decision.** solkey's storage copy
changed twice (`c80a54494c`/`8c5c69ca25`): the eight copy rules now write
`save(…)` again, `save(st, nil, v)` is a leaf every write leaves rather than
collapsing, and it is read through by member sort so that a struct written
over a location keeps the location's mapping members.
`Solidity/Theory/Storage.lean` keeps the **pre-fold** algebra instead —
`save(st, ∅, v) = (Struct) v` — because the two
readings differ only on a storage-to-storage copy of a mapping-carrying type,
which solc ≥ 0.7 and solkey's own parser reject and this package's
`Src.copy` cannot build. `docs/solkey-feedback.md` carries the
request that solkey drop the fold.

## Status legend

- **`same`** — a `Taclet` constructor of the exact same name.
- **`merged into` `X`** (or `X` and `Y`) — constructor `X` (and `Y`) covers
  this taclet along with others: an operator family, a value-vs-reference
  source split, a mapping-vs-array receiver split (increment/compound-assign
  only — the reads, writes, saves and finds keep the receiver split, see
  below), or two taclets KeY separates by capture order that one Lean rule
  covers in a single step.
- **`unclaimed`** — no constructor claims this taclet; the note gives the
  reason from `RuleShapes.unclaimedTaclets`.
- **`Lean only`** — a `LeanTaclet` constructor: a rule that transcribes no
  taclet; the note says why the calculus has it.

## Modality / sequent rules

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `functionBodyExpand` | `functionBodyExpand` | same | a call carries its callee inlined (`Stmt.call`, KeY's `FunctionBodyStatement`), and with every argument simple the premise is KeY's `expand_function_body`: the parameters declared with the arguments, the return variable declared, the body, `res = r`. The parameters are the elaborator's fresh names, so the fresh renaming KeY's transformer does at the rule is done once, at elaboration |
| — | `LeanTaclet.functionCallArgCapture` | Lean only | `unfoldArgument`, which solkey's `docs/net.md` lists as missing: the leftmost argument that is not simple is captured into a fresh `se` first. KeY's expansion binds a parameter to any expression; here `functionBodyExpand` takes simple ones, so that `Stmt.step` has one rule per call and the capture is its own step |
| `emptyModality` | — | unclaimed | a program is a list of statements with branch bodies inlined, so there is no nested block to erase; a derivation reaching `⟨[ ]⟩` is the Lean analogue |
| `blockEmpty` | — | unclaimed | no `{} ; rest` to find, for the same reason |
| `revertDiamond` | `revertDiamond` | same | the diamond closes to `false`: a reverted run satisfies no diamond formula |
| `revertBox` | `revertBox` | same | the box closes to `true`: a reverted run satisfies every box formula. `revertBox`/`revertDiamond` are the **only** rules that tell the two modalities apart — every other rule's `⟨[ ]⟩` fires under either, unlike the old table's box/diamond twins (there are none left: the modality is a parameter of `Taclet`, not a naming convention) |

## Storage root/field write & read

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `storageRootWriteStore` | `storageRootWriteStore` | same | |
| `storageRootWriteCopySource` | `storageRootWriteCopySource` | same | |
| `storageRootReadSelect` | `storageRootReadSelect` | same | |
| `storageFieldWriteSave` | `storageFieldWriteSave` | same | |
| `storageFieldWriteCopySource` | `storageFieldWriteCopySource` | same | |
| `storageFieldWriteCaptureSrc` | `storageFieldRead_unfold_rightSndResult` | merged into `storageFieldRead_unfold_rightSndResult` | the SndResult chain also captures a complex storage source into a fresh local |
| `storageFieldRead_unfold_rightFst` | `storageFieldRead_unfold_rightFst` and `storageLengthRead_unfold_rightFst` | same | the second at the member `length`: `v = nsp.length ⇝ T storage sp = nsp; v = sp.length` (a length is a `Val`, not a member of the typed syntax) |
| `storageFieldReadFind` | `storageFieldReadFind` and `storageLengthRead` | same | the second at the member `length`: `v = sp.length ⇝ { v := sp.length }`, the term `Term.len` (KeY's `find(storage, sp.size)`) |
| `storageFieldWrite_unfold_leftFst` | `storageFieldWrite_unfold_leftFst` | same | `nsp.fld = e ⇝ T se = e; T storage sp = nsp; sp.fld = se`: the value source `e` is frozen into `se` before the receiver is captured |
| `storageFieldWriteStorageRef_unfold_leftFst` | `storageFieldWriteStorageRef_unfold_leftFst` | same | the reference-source twin: `nsp.fld = path ⇝ T storage sp = nsp; sp.fld = path`, no freeze (a reference is aliased, not read) |
| `storageFieldReadBindLocalRoot` | `storageFieldReadBindLocalRoot` | same | |
| `storageFieldReadStoreRoot` | `storageFieldReadStoreRoot` | same | |
| `storageFieldRead_unfold_rightSndResult` | `storageFieldRead_unfold_rightSndResult` | same | also claims `storageFieldWriteCaptureSrc` above |

## Storage index (mapping)

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `storageIndexWriteMappingSave` | `storageIndexWriteMappingSave` | same | |
| `storageIndexReadMappingFind` | `storageIndexReadMappingFind` | same | |
| `storageIndexReadMappingBindLocalRoot` | `storageIndexReadMappingBindLocalRoot` | same | |
| `storageIndexWriteMappingCopySource` | `storageIndexWriteMappingCopySource` | same | |
| `storageIndexWriteStorageRefRhsCapture` | `storageIndexRead_unfold_rightSndResult` | merged into `storageIndexRead_unfold_rightSndResult` | a reference source at an index is hoisted into `se` before the write, the storage twin of the field-write case above |
| `storageIndexReadMappingStoreRoot` | `storageIndexReadMappingStoreRoot` | same | |

## Storage index (array)

Each array rule takes an implicit `ak : ArrTy R E` (`IndexTy.arr ak`), `dyn`
for `T[]` and `fixed` for `T[n]`, so one constructor covers both kinds as
solkey's `Path[…,array]` sort does (`PathSVSort` puts a static array in the
`array` category). The memory index rules take the same argument as `mk`.

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `storageIndexWriteArraySave` | `storageIndexWriteArraySave` | same | one rule for both modalities; an out-of-range write reverts in the path's own bounds check (`PTerm.at`, `State.checkIndex`), not as a separate bounds goal |
| `storageIndexReadArrayFind` | `storageIndexReadArrayFind` | same | |
| `storageIndexReadArrayBindLocalRoot` | `storageIndexReadArrayBindLocalRoot` | same | `lsv = darr[ie]`: an element that is not a mapping (`nonMappingElement`, `SPath.elemMapping darr = false`); the bounds check is the path's own (`PTerm.at`) |
| `storageIndexReadArrayBindLocalRootMappingElement` | `storageIndexReadArrayBindLocalRootMappingElement` | same | `lsv = marr[ie]`: an array of mappings; KeY's `atMap(ie)` is the same `Seg.at` here, a mapping being what `delete` leaves alone |
| `storageIndexReadArrayStoreRoot` | `storageIndexReadArrayStoreRoot` | same | |
| `storageIndexWriteArrayCopySource` | `storageIndexWriteArrayCopySource` | same | |
| `storageIndexWriteCaptureAllNonSimpleIndex` | `storageIndexWriteCaptureAllNonSimpleIndex` | same | `sp[nse] = e ⇝ T se = e; T storage sp' = sp; T ie = nse; sp'[ie] = se`: the simple receiver is bound again, as KeY does |
| `storageIndexWriteStorageRefCaptureAllNonSimpleIndex` | `storageIndexWriteStorageRefCaptureAllNonSimpleIndex` | find agrees | `sp[nse] = path ⇝ T storage sp' = sp; T ie = nse; sp'[ie] = path`: KeY also binds the source to an alias `rv`; a copy source is written as it stands (`path`, `kernel-port.md` Decisions) |
| `storageIndexWriteCaptureAllComplexRecv` | `storageIndexWriteCaptureAllComplexRecv` | same | `nsp[e1] = e2 ⇝ T se = e2; T storage sp = nsp; T ie = e1; sp[ie] = se` (was `storageIndexWrite_unfold_leftFst`) |
| `storageIndexWriteStorageRefCaptureAllComplexRecv` | `storageIndexWriteStorageRefCaptureAllComplexRecv` | find agrees | `nsp[e] = path ⇝ T storage sp = nsp; T ie = e; sp[ie] = path`; the source is not captured, as the row above |
| `storageIndexRead_unfold_rightSndIndex` | `storageIndexRead_unfold_rightSndIndex` | same | |
| `storageIndexRead_unfold_rightSndResult` | `storageIndexRead_unfold_rightSndResult` | same | also claims `storageIndexWriteStorageRefRhsCapture` above |
| `storageIndexRead_unfold_rightFst` | `storageIndexRead_unfold_rightFst` | same | |

## Storage push / pop

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `storagePushValue_unfold_leftFstReceiver` | `storagePushValue_unfold_leftFstReceiver` | same | |
| `storagePush_unfold_leftFstReceiver` | `storagePush_unfold_leftFstReceiver` | same | |
| `storagePop_unfold_leftFstReceiver` | `storagePop_unfold_leftFstReceiver` | same | |
| `storageLocalRootPush_unfold_leftFstReceiver` | `storageLocalRootPush_unfold_leftFstReceiver` | same | |
| `storagePushValue_unfold_rightSndArgument` | `storagePushValue_unfold_rightSndArgument` | same | |
| `storagePushValueSave` | `storagePushValueSave` | same | |
| `storagePushValueCopySource` | `storagePushValueCopySource` | same | |
| `storagePushLengthSave` | `storagePushLengthSave` | same | `parr.push()`: a primitive element, the slot cleared (`delAt`) |
| `storagePushLengthSaveReferenceElement` | `storagePushLengthSaveReferenceElement` | same | `rarr.push()`: a struct or array element, the recycled slot taken as it is (`STerm.extend` at `E`) |
| `storageLocalRootPushBind` | `storageLocalRootPushBind` | same | `lsv = darr.push()` |
| `storageLocalRootPushBindMappingElement` | `storageLocalRootPushBindMappingElement` | same | `lsv = marr.push()`: `atMap` is `Seg.at`, as above |
| `storagePopSave` | `storagePopSave` | same | `darr.pop()`, one rule for both modalities: the element cleared into the recycled slots |
| `storagePopSaveMappingElement` | `storagePopSaveMappingElement` | same | `marr.pop()`: `save(storage, marr.length, marr.length - 1)`, the element kept (`STerm.shrink`, `popAt` with `keep`) |

## Storage local declarations

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `storageLocalDeclInitDrop` | `storageLocalDeclInitDrop` | same | |
| `storageLocalRootRebind` | `storageLocalRootRebind` | same | |
| `storageLocalDeclSkip` | `storageLocalDeclSkip` | same | |

## Storage delete

solkey leaves `delete` and `pop()` open on a path through a fixed-size array
element (`noFixedArrayElement`, on `storageRootDelete`, `storageFieldDelete`,
`storageIndexDelete`, `storageIndexArrayDelete`, `storagePopSave`): its
`at(i)` carries no field kind. The Lean constructors have no such restriction
and are sound there, since `SVal.defaultOf` keeps a fixed-size array's `n`
elements (reset) where it empties a dynamic one; `push`/`pop` are written at
`.array` only, so neither applies to a `T[n]` receiver.

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `storageRootDelete` | `storageRootDelete` | same | `delete(gsp) ⇝ { storage := delAt(storage, gsp) }` |
| `storageFieldDelete` | `storageFieldDelete` | same | |
| `storageIndexDelete` | `storageIndexDelete` | same | `delete map[ie]`: a mapping entry |
| `storageIndexArrayDelete` | `storageIndexArrayDelete` | same | `delete arr[ie]`: KeY's `inBounds` split is the path's own bounds check, which reverts |
| `storageFieldDelete_unfold_leftFst` | `storageFieldDelete_unfold_leftFst` | same | |
| `storageIndexDelete_unfold_leftFst` | `storageIndexDelete_unfold_leftFst` | same | |
| `storageIndexDeleteNonSimpleIndexCapture` | `storageIndexDeleteNonSimpleIndexCapture` | same | |

## Memory allocation, aliasing, declarations

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `memoryReferenceDeclFreshAlloc` | `memoryReferenceDeclFreshAlloc` | same | `T memory mv; ⇝ { mv := freshId(addM(memory)) ‖ memory := addM(memory) }`, the pair KeY writes |
| `memoryArrayFreshAlloc` | `memoryArrayFreshAlloc` | same | `mv = new T(se); ⇝ { mv := freshId(copySt(memory, newArr(se))) ‖ memory := copySt(memory, newArr(se)) }`: KeY writes `size` into a fresh shaped identity, Lean copies in the storage value `newArrVal R n` (`n` defaults, each struct element its own object, as solc allocates); a non-simple size is captured by the elaborator (KeY's taclet takes a `SimpleExpression`) |
| `newArrayCapture` | `newArrayCapture` | same | `tgt = new T(se) ⇝ T memory mv = new T(se); tgt = mv`, `tgt` a storage or a memory location (`NewLhs`) |
| `memoryRootDeleteFreshRebind` | `memoryRootDeleteFreshRebind` | same | `delete mv; ⇝ { mv := freshId(addM(memory)) ‖ memory := addM(memory) }`, the allocation pair (see "Memory delete" below) |
| `memoryRootRebind` | `memoryRootAlias` | merged into `memoryRootAlias` | `mv₁ = mv₂; ⇝ { mv₁ := mv₂ }`; a storage right-hand side is the row below instead |
| `memoryStorageCopy` | `memoryStorageCopy` | same | `mv = sp;` deep copy: fresh identity plus `copySt` |
| `memoryStorageCopyUnfold` | `memoryStorageCopyUnfold` | same | a complex storage path is captured first |
| `memoryLocalDeclInitDrop` | `memoryLocalDeclInitDrop` | same | one generic decl-with-init split; the assignment rules take it from there, so there is no per-source-kind decl-init family |

## Memory field/index write & read

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `memoryFieldWrite` | `memoryFieldWriteStore` and `memoryFieldWriteCopy` | merged into `memoryFieldWriteStore` and `memoryFieldWriteCopy` | Lean's sorts are not generic, so KeY's one write is two rules: a value source and a reference-path source |
| `memoryFieldRead` | `memoryFieldReadHeap`, `memoryFieldReadAliasRoot` and `memoryLengthRead` | merged into `memoryFieldReadHeap` and `memoryFieldReadAliasRoot` | same split, on the read side (a value lands on a local, a reference on a memory alias); `memoryLengthRead` is the member `length` (`v = mv.length ⇝ { v := mv.length }`, `Term.mlen`, KeY's `read(memory, mv, size)`) |
| `memoryFieldRead_unfold_rightFst` | `memoryFieldRead_unfold_rightFst` and `memoryLengthRead_unfold_rightFst` | same | |
| `memoryFieldWriteCaptureSrc` | — | unclaimed | KeY captures a memory reference into an alias before writing it; here a memory path is a source as it stands (`mpath`), so `memoryFieldWriteCopy` writes it in one step |
| `memoryFieldWrite_unfold_leftFst` | `memoryFieldWrite_unfold_leftFst` | same | also claims the reference-receiver row below |
| `memoryFieldWriteMemRef_unfold_leftFst` | `memoryFieldWrite_unfold_leftFst` | merged into `memoryFieldWrite_unfold_leftFst` | `msrc` is a value or a memory reference, so one rule covers both |
| `memoryIndexWriteArray` | `memoryIndexWriteStore` and `memoryIndexWriteCopy` | merged into `memoryIndexWriteStore` and `memoryIndexWriteCopy` | as `memoryFieldWrite` |
| `memoryIndexReadArrayValue` | `memoryIndexReadHeap` | merged into `memoryIndexReadHeap` | |
| `memoryIndexReadArrayMemory` | `memoryIndexReadAliasRoot` | merged into `memoryIndexReadAliasRoot` | |
| `memoryIndexRead_unfold_rightFst` | `memoryIndexRead_unfold_rightFst` | same | |
| `memoryIndexWriteCaptureAllComplexRecv` | `memoryIndexWriteCaptureAllComplexRecv` | same | `nmp[e1] = e2 ⇝ T se = e2; T memory mv = nmp; T ie = e1; mv[ie] = se` |
| `memoryIndexWriteMemRefCaptureAllComplexRecv` | `memoryIndexWriteMemRefCaptureAllComplexRecv` | find agrees | `nmp[e] = mpath ⇝ T memory mv = nmp; T ie = e; mv[ie] = mpath`: a memory path is a source as it stands |
| `memoryIndexWriteMemRefRhsCapture` | — | unclaimed | a reference source at an index is written directly, as `memoryFieldWriteCaptureSrc` above |
| `memoryIndexWriteCaptureAllNonSimpleIndex` | `memoryIndexWriteCaptureAllNonSimpleIndex` | find agrees | `mv[nse] = e ⇝ T se = e; T ie = nse; mv[ie] = se`: KeY binds the receiver again (`T memory mv' = mv`), which for an untyped memory local would leave its array type free, and renames nothing else |
| `memoryIndexWriteMemRefCaptureAllNonSimpleIndex` | `memoryIndexWriteMemRefCaptureAllNonSimpleIndex` | find agrees | `mv[nse] = mpath ⇝ T ie = nse; mv[ie] = mpath` |
| `memoryFieldWriteUnfoldSource` (Lean-side name for the value capture below `fieldWriteValueRhsCapture`'s storage form) | `fieldWriteValueRhsCapture` | merged into `fieldWriteValueRhsCapture` | see "Value-RHS capture" in the arithmetic section below: the location-neutral capture rule also claims the memory case |
| `memoryIndexWriteUnfoldSource` | `indexWriteValueRhsCapture` | merged into `indexWriteValueRhsCapture` | same, at an index |
| `memoryFieldRead_unfold_rightSndResult` | — | unclaimed | as `memoryFieldWriteCaptureSrc`: a memory path is a source as it stands |
| `memoryIndexRead_unfold_rightSndIndex` | `memoryIndexRead_unfold_rightSndIndex` | same | |
| `memoryIndexRead_unfold_rightSndResult` | — | unclaimed | as `memoryFieldWriteCaptureSrc` |

## Memory delete

`Stmt.deleteMem p` deletes a memory path: a memory local (`delete mv;`), a
member or an element.  KeY's primitive/reference split
(`\hasMemoryFieldSort(fld, alphaPrim)`, `Path[…,primitiveElement]`) is the
type the rule fixes: `delete mv.pfld`/`delete pmv[ie]` at `T := Ty.prim p`,
`delete mv.rfld`/`delete rmv[ie]` at `T := Ty.ref R` (the stems in
`RuleSyntax.lean`'s table).  KeY's `inBounds` split of an index delete is the
bounds check of the write, which reverts.

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `memoryRootDeleteFreshRebind` | `memoryRootDeleteFreshRebind` | same | listed above, with the allocation rules |
| `memoryFieldDeletePrimitive` | `memoryFieldDeletePrimitive` | same | `{ memory := write(memory, mv.pfld, defVal(T)) }` |
| `memoryFieldDeleteReference` | `memoryFieldDeleteReference` | same | `{ memory := write(addM(memory), mv.rfld, freshId(addM(memory))) }`: the member gets a fresh default object |
| `memoryIndexDeletePrimitive` | `memoryIndexDeletePrimitive` | same | |
| `memoryIndexDeleteReference` | `memoryIndexDeleteReference` | same | |
| `memoryFieldDelete_unfold_leftFst` | `memoryFieldDelete_unfold_leftFst` | same | |
| `memoryIndexDelete_unfold_leftFst` | `memoryIndexDelete_unfold_leftFst` | same | |
| `memoryIndexDeleteNonSimpleIndexCapture` | `memoryIndexDeleteNonSimpleIndexCapture` | same | |

## Memory → storage copies

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `memoryToStorageStoreRoot` | `memoryToStorageStoreRoot` | same | |
| `memoryToStorageFieldCopyRoot` | `memoryToStorageFieldCopyRoot` | same | also claims the row below |
| `memoryToStorageFieldCopyField` | `memoryToStorageFieldCopyRoot` | merged into `memoryToStorageFieldCopyRoot` | the one member-source shape read directly |
| `memoryToStorageIndexMappingCopyRoot` | `memoryToStorageIndexMappingCopyRoot` | same | |
| `memoryToStorageIndexArrayCopyRoot` | `memoryToStorageIndexArrayCopyRoot` | same | one rule for both modalities |
| `memoryToStorageField_unfold_leftFst` | `memoryToStorageField_unfold_leftFst` | same | |
| `memoryToStorageIndexCaptureAllComplexRecv` | `memoryToStorageIndexCaptureAllComplexRecv` | find agrees | `nsp[e] = mpath ⇝ T storage sp = nsp; T ie = e; sp[ie] = mpath`; the memory source stands (KeY: `T memory rv = src`); `simplify_prog_expensive` |
| `memoryToStorageIndexCaptureAllNonSimpleIndex` | `memoryToStorageIndexCaptureAllNonSimpleIndex` | find agrees | `sp[nse] = mpath ⇝ T storage sp' = sp; T ie = nse; sp'[ie] = mpath`; `simplify_prog_expensive` |

## Value declarations

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `localValueDeclInitDrop` | `localValueDeclInitDrop` | same | |
| `valueDeclSkip` | `valueDeclSkip` | same | |
| `localValueAssign` | `localValueAssign` | same | terminal `v = se;` |

## Binary arithmetic operators

Family pattern per op `⊕ ∈ {addition, subtraction, multiplication, power,
division, modulo}`: `⊕_unfold_left`, `⊕_unfold_right`, `⊕Assignment`. One Lean
constructor per **shape**, not per operator — `binopUnfoldLeft`,
`binopUnfoldRight`, `binopAssignment` — with `op : BinOp` a free variable of
the type, so an instance is `binopAssignment (op := .add)` and so on. These
three constructors are shared with the comparison and boolean operators below.

| KeY taclets | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `addition_unfold_left`, `subtraction_unfold_left`, `multiplication_unfold_left`, `power_unfold_left`, `division_unfold_left`, `modulo_unfold_left` | `binopUnfoldLeft` | merged into `binopUnfoldLeft` | `v = nse ⊕ e; ⇝ T se = nse; v = se ⊕ e;` |
| `addition_unfold_right`, `subtraction_unfold_right`, `multiplication_unfold_right`, `power_unfold_right`, `division_unfold_right`, `modulo_unfold_right` | `binopUnfoldRight` | merged into `binopUnfoldRight` | requires `¬ op.shortCircuits`, true of every arithmetic op |
| `additionAssignment`, `subtractionAssignment`, `multiplicationAssignment`, `powerAssignment`, `divisionAssignment`, `moduloAssignment` | `binopAssignment` | merged into `binopAssignment` | terminal `v = se₁ ⊕ se₂;`; `**` (`BinOp.pow`) is checked `uint` exponentiation, so `power*` is claimed at `op := .pow`; solkey has no `powAssign` (`**=`) taclets, so there is no `localOpAssign (op := .pow)` instance on the KeY side either |

## Comparisons, boolean operators, unary

| KeY taclets | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `boolEqualityCaptureLhs`, `boolInequalityCaptureLhs`, `lessThanCaptureLhs`, `greaterThanCaptureLhs`, `lessEqualCaptureLhs`, `greaterEqualCaptureLhs`, `logicalAndCaptureLhs`, `logicalOrCaptureLhs` | `binopUnfoldLeft` | merged into `binopUnfoldLeft` | |
| `boolEqualityCaptureRhs`, `boolInequalityCaptureRhs`, `lessThanCaptureRhs`, `greaterThanCaptureRhs`, `lessEqualCaptureRhs`, `greaterEqualCaptureRhs` | `binopUnfoldRight` | merged into `binopUnfoldRight` | no short-circuit (`&&` / logical-or) instance: their right operand is evaluated only when the left does not decide, which is the short-circuit row below |
| `boolEqualityAssignment`, `boolInequalityAssignment`, `lessThanAssignment`, `greaterThanAssignment`, `lessEqualAssignment`, `greaterEqualAssignment`, `logicalAndAssignment`, `logicalOrAssignment` | `binopAssignment` | merged into `binopAssignment` | |
| `logicalAndShortCircuitRhs` | `logicalAndShortCircuitRhs` | same | `v = se && nse; ⇝ if (se) { v = nse; v = v && true; } else { v = false; }` |
| `logicalOrShortCircuitRhs` | `logicalOrShortCircuitRhs` | same | dual |
| `logicalNotCapture`, `unaryMinusCapture` | `unopCapture` | merged into `unopCapture` | one constructor for both unary operators |
| `logicalNotAssignment`, `unaryMinusAssignment` | `unopAssignment` | merged into `unopAssignment` | |
| `ternaryCaptureCond` | `ternaryCaptureCond` | same | |
| `ternaryToIf` | `ternaryToIf` | same | also claims the row below |
| `ternaryToIfStorage` | `ternaryToIf` | merged into `ternaryToIf` | one rule for a local or a storage-path target; a memory-path target is lowered the same way, no separate taclet needed since a conditional is never a write's source (`isValueSource` excludes it) |

## Value-RHS capture (location-neutral)

KeY's value-RHS-capture taclets are written once, at any receiver; Lean
states one instance per receiver kind, and the memory instances are claimed
jointly with the storage ones above and in "Memory field/index write & read".

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `storageRootWriteValueRhsCapture` | `storageRootWriteValueRhsCapture` | same | `gsp = nse; ⇝ T se = nse; gsp = se;` |
| `fieldWriteValueRhsCapture` | `fieldWriteValueRhsCapture` | same | also claims `memoryFieldWriteUnfoldSource` |
| `indexWriteValueRhsCapture` | `indexWriteValueRhsCapture` | same | also claims `memoryIndexWriteUnfoldSource` |

## Storage compound assignments

Pattern per op `⊕ ∈ {Add, Sub, Mul, Div, Mod}`. Lean has one constructor per
**receiver shape**, `op` a free variable of the type.

| KeY taclets | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `localAddAssign`, `localSubAssign`, `localMulAssign`, `localDivAssign`, `localModAssign` | `localOpAssign` | merged into `localOpAssign` | terminal `v ⊕= se;` |
| `storageRootAddAssign`, …SubAssign, …MulAssign, …DivAssign, …ModAssign | `storageRootOpAssign` | merged into `storageRootOpAssign` | |
| `storageFieldAddAssign`, … | `storageFieldOpAssign` | merged into `storageFieldOpAssign` | |
| `storageIndexMappingAddAssign`, … | `storageIndexMappingOpAssign` | merged into `storageIndexMappingOpAssign` | mapping and array stay **separate** constructors here, unlike increment/decrement below |
| `storageIndexArrayAddAssign`, … | `storageIndexArrayOpAssign` | merged into `storageIndexArrayOpAssign` | no bounds split: the update reverts in the path's bounds check (`PTerm.at`) |
| `memoryFieldAddAssign`, … | `memoryFieldOpAssign` | merged into `memoryFieldOpAssign` | |
| `memoryIndexArrayAddAssign`, … | `memoryIndexArrayOpAssign` | merged into `memoryIndexArrayOpAssign` | no root or mapping form: a memory root binds an identity, memory has no mappings |
| `storageFieldAddAssign_unfold_leftFst`, … | `storageFieldOpAssignUnfoldLeftFst` | merged into `storageFieldOpAssignUnfoldLeftFst` | `nsp.fld ⊕= se; ⇝ T storage sp = nsp; sp.fld ⊕= se;` |
| `storageIndexAddAssign_unfold_leftFst`, … | `storageIndexOpAssignUnfoldLeftFst` | merged into `storageIndexOpAssignUnfoldLeftFst` | |
| `memoryFieldAddAssign_unfold_leftFst`, … | `memoryFieldOpAssignUnfoldLeftFst` | merged into `memoryFieldOpAssignUnfoldLeftFst` | |
| `memoryIndexAddAssign_unfold_leftFst`, … | `memoryIndexOpAssignUnfoldLeftFst` | merged into `memoryIndexOpAssignUnfoldLeftFst` | |
| `addAssignValueRhsCapture`, `subAssignValueRhsCapture`, `mulAssignValueRhsCapture`, `divAssignValueRhsCapture`, `modAssignValueRhsCapture` | `compoundAssignValueRhsCapture` | merged into `compoundAssignValueRhsCapture` | location-neutral capture of a nonsimple compound-assign RHS, as the plain-assignment value capture above |

## Increment / decrement

Pattern per `V ∈ {Preincrement, Postincrement, Predecrement, Postdecrement}`.
A decrement is written `x−−`/`−−x` in `sol{ … }` (two U+2212: `--` opens a
Lean comment); an `++`/`−−` inside an expression is captured by the
elaborator (`uint se1; se1 = i++;`), so it reaches these rules as a
statement.
Here (unlike compound assignment) a mapping and an array receiver **do**
share one constructor: solkey splits the receiver kind, Lean does not.

| KeY taclets | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `localPreincrement`, `localPredecrement`, `localPostincrement`, `localPostdecrement` | `localIncrement` | merged into `localIncrement` | bare statement `v⊕⊕;` on a stack local |
| `storageRootPreincrement`, … | `storageRootIncrement` | merged into `storageRootIncrement` | |
| `storageFieldPreincrement`, … | `storageFieldIncrement` | merged into `storageFieldIncrement` | |
| `storageIndexMappingPreincrement`, `storageIndexArrayPreincrement`, … (all 8 mapping/array × pre/post × in/decrement) | `storageIndexIncrement` | merged into `storageIndexIncrement` | one constructor over both receiver kinds |
| `memoryFieldPreincrement`, … | `memoryFieldIncrement` | merged into `memoryFieldIncrement` | |
| `memoryIndexArrayPreincrement`, … | `memoryIndexArrayIncrement` | merged into `memoryIndexArrayIncrement` | |
| `storageFieldPreincrement_unfold_leftFst`, … | `storageFieldIncrementUnfoldLeftFst` | merged into `storageFieldIncrementUnfoldLeftFst` | |
| `storageIndexPreincrement_unfold_leftFst`, … | `storageIndexIncrementUnfoldLeftFst` | merged into `storageIndexIncrementUnfoldLeftFst` | |
| `memoryFieldPreincrement_unfold_leftFst`, … | `memoryFieldIncrementUnfoldLeftFst` | merged into `memoryFieldIncrementUnfoldLeftFst` | |
| `memoryIndexPreincrement_unfold_leftFst`, … | `memoryIndexIncrementUnfoldLeftFst` | merged into `memoryIndexIncrementUnfoldLeftFst` | |
| `localAssignPreincrement`, …, `localDeclPreincrement`, … (assign and decl forms, all 8) | `localAssignIncrement` | merged into `localAssignIncrement` | `vp = v⊕⊕;`; KeY has one taclet for the assignment and one for the declaration, Lean reaches the declaration form via `localValueDeclInitDrop` then this rule |
| `storageRootPreincrementAssignment`, … | `storageRootIncrementAssignment` | merged into `storageRootIncrementAssignment` | |
| `storageFieldPreincrementAssignment`, … | `storageFieldIncrementAssignment` | merged into `storageFieldIncrementAssignment` | |
| `storageIndexMappingPreincrementAssignment`, `storageIndexArrayPreincrementAssignment`, … (all 8) | `storageIndexIncrementAssignment` | merged into `storageIndexIncrementAssignment` | |
| `memoryFieldPreincrementAssignment`, … | `memoryFieldIncrementAssignment` | merged into `memoryFieldIncrementAssignment` | |
| `memoryIndexArrayPreincrementAssignment`, … | `memoryIndexArrayIncrementAssignment` | merged into `memoryIndexArrayIncrementAssignment` | |

## Assert, if-then-else

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `assertConditionCapture` | `assertConditionCapture` | same | |
| `assertSimple` | `assertSimple` | same | terminal; the box/diamond split on a reverted run is the modality semantics, not a rule |
| `requireConditionCapture` | `requireConditionCapture` | same | clone of the assert capture over `Stmt.requireStmt` |
| `requireSimple` | `requireSimple` | same | `require(se); ⇝ se = true ⟹ ⟨[ ]⟩ ; se = false ⟹ ⟨[ revert(); ]⟩` |
| `ifUnfold` | `ifElseUnfold` | merged into `ifElseUnfold` | `Stmt.ite` always carries both branches (an absent `else` is `[]`), so `ifUnfold`/`ifElseUnfold` are one rule |
| `ifElseUnfold` | `ifElseUnfold` | same | |
| `ifTrue` | — | unclaimed | `concrete_solidity` shortcut on a literal condition. A literal is simple, so `ifElseSplit` applies and one of its goals assumes `true = false`; these five are strategy (which rule set to try automatically), and the Lean table has none |
| `ifFalse` | — | unclaimed | as `ifTrue` |
| `ifElseTrue` | — | unclaimed | as `ifTrue` |
| `ifElseFalse` | — | unclaimed | as `ifTrue` |
| `ifElseNegated` | — | unclaimed | `!se` is not simple, so `ifElseUnfold` captures it instead; still a strategy shortcut with no table analogue |
| `ifSplit` | `ifElseSplit` | merged into `ifElseSplit` | |
| `ifElseSplit` | `ifElseSplit` | same | now an ordinary `Taclet` constructor with a `.split` premise: `if (se) thn else els; ⇝ se = true ⟹ ⟨[ thn ]⟩ ; se = false ⟹ ⟨[ els ]⟩`. There is no separate block-rewriting layer that gets "stuck" on two goals — a `.split` premise *is* the two-goal shape, so this is a proper rule rather than a lemma bolted on beside the table |

## Payments

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `transfer_unfold_leftFstReceiver` | `transfer_unfold_leftFstReceiver` | same | |
| `transfer_unfold_rightSndArgument` | `transfer_unfold_rightSndArgument` | same | |
| `transferNoCallbackBox` | `transferNoCallback` | merged into `transferNoCallback` | one terminal rule for both modalities, a guarded update (`Premise.guard`): `0 <= se ∧ se <= selfBalance ⟹ { selfBalance := selfBalance - se ‖ net := store(net, at(sadr), net(sadr) - se) } ⟨[ ]⟩ ; ¬(0 <= se ∧ se <= selfBalance) ⟹ ⟨[ revert(); ]⟩`. The update is KeY's, its arithmetic KeY's `int` (`IntOp`); the funds check is the guard, and its `revert();` branch is where the modalities part (`revertBox`, `revertDiamond`), so the diamond's "sufficient funds" goal is what is left of it |
| `transferNoCallbackDiamond` | `transferNoCallback` | merged into `transferNoCallback` | |
| `transferWithCallbackBox` | `CallbackTaclet.transferWithCallbackBox` | same | the other `transferSemantics`: a constructor of `CallbackTaclet`, not of `Taclet`. Its premise has `transferNoCallback`'s shape, the funds check `F` and the booking `U`, read as KeY's goals (`CallbackTaclet.sound`): `F → {U} I` ("invariant on exit"), and `F → {U} {havoc} (I → ⟨[ ω ]⟩ φ)`, the rest from every state the callee may leave in which `I` holds ("resume after callback" — `{havoc}` is KeY's anonymising update with skolem symbols; `CbResume` reads it). The box assumes `F` where KeY does not, which only weakens its goals. Used in `ProvesC`, the calculus under the callback reading |
| `transferWithCallbackDiamond` | `CallbackTaclet.transferWithCallbackDiamond` | same | as the box, plus KeY's "sufficient funds" goal `F` (`ProvesC.callback`'s `funds`) |

## Update algebra (`updateRules.key`)

An update is a term (`Upd C`, a list of `UpdElem`s applied against the
pre-state, `Update.lean`), so KeY's update rules are rules here too:
`Calculus/UpdateRules.lean`, each an equivalence over `holds` (`UpdRule`),
plus the box forms; on sequents they are constructors of `Proves`
(`Calculus/Logic.lean`), so a derivation uses them with the program still
to run. Where a rule
has a side condition KeY's lacks, it is because a term here can halt and
KeY's cannot (the module docstring, "What halting changes").

| KeY rule | Lean | Status | Notes |
| --- | --- | --- | --- |
| `sequentialToParallel1-3` | `UpdRule.sequentialToParallel`, `Proves.merge`; `Proves.mergeStorage` | done | `{u}{u2}φ ⇝ {u ‖ {u}u2}φ` for `u` an update of locals (`Upd.envOnly`); over a storage write (`mergeStorage`) for terms whose every storage read is a `storage` term (`stExplicit`) |
| `applyOnElementary`, `applyOnParallel` | `UpdElem.subst`, `Upd.subst` | functions | `{u}` pushed into an update's right-hand sides |
| `applyOnPV`, `applyOnPVLastInParallel`, `applyOnDifferentPV`, `applyOnDifferentPVLastInParallel` | `Fml.subst` (`Upd.lastWrite`) | functions | the last write of a local wins; a local the update does not write is kept |
| `simplifyUpdate1-3` | `UpdRule.simplifyUpdate`, `Upd.dropEffectless`, `Proves.simplify` | done | only elements that cannot halt are dropped (`UpdElem.total`): dropping one drops its halting too |
| `applySkip1-3`, `applyOnSkip` | `UpdRule.applySkip` | done | `skip` is `[]` |
| `parallelWithSkip1-2` | — | arch | `‖` is `++` and `skip` is `[]`: nothing to rewrite |
| `applyOnRigidFormula` | `UpdRule.applyOnRigid` | done | as an equivalence, for an update that cannot halt (`Upd.total`) and a formula reading no variable at another sort than the update writes it (`Fml.sortedFor`, which KeY's sorts give for free) |
| `applyOnRigidFormula`, under the box | `Proves.applyOnRigidBox` (an update of locals, or locals and a storage write under a storage-free goal), `Proves.applyStorageBox` (`{storage := s}`); `sol_apply_upd` | done | one direction, **no totality premise**: the last update of the context applied to a first-order goal and dropped. A halting box update proves what follows, and the goal's equations are read in the Theory, where a term that halts still denotes |
| `elimSelfUpdate*` | `UpdElem.elimSelf_box`, `UpdElem.elimSelf_diamond` | done, one direction each | commented out in the KeY source; `x := x` halts when `x` holds no value, so it is no equivalence here |
| `simplifyIfThenElseUpdate1-4`, `commuteSimpleUpdates` | — | arch | commented-out dead code in the KeY source |

### Closing the first-order goal

What symbolic execution leaves is closed with KeY's first-order steps, derived
through `Proves.close` (`Calculus/Rewrite.lean`),
each needing only a context with no diamond (`Hyp.boxOnly`). The formula
`a = b` a program comparison produces is `Fml.eqD a b` — `defined(a) ∧
defined(b) ∧ a ≐ b` — because a term here can halt and KeY's `=` is between
terms that cannot; `a ≐ b` (`Fml.eq`) is the total Theory equation, KeY's `=`.

| KeY rule | Lean | Status | Notes |
| --- | --- | --- | --- |
| `eqClose` | `Proves.eqRefl`; `Proves.eqClose` (`v ≐ v`), `Proves.eqDClose` (`v = v`) | done | `t ≐ t` for any term, halting or not (`StValue.Equiv.refl`) |
| `andRight` | `Proves.andSplit`, `Proves.andSplitUpd` (behind an update) | done | |
| — | `Proves.eqDSplit` | Lean only | `a = b` from `defined(a)`, `defined(b)` and `a ≐ b`: `Fml.eqD` unfolded |
| — | `Proves.definedWritten` | Lean only | `defined(x)` behind a box update whose last binder of `x` is `x := t`: what `applyOnRigidBox` forgets, that the update ran |
| — | `Proves.definedLit` | Lean only | a literal is defined |
| any theory taclet on a sequent | `Proves.theoryRw` (`Calculus/Logic.lean`), `rw [h]`/`sol_rw` (`Calculus/Rewrite.lean`) | done | a Theory equation `h : Term.Theq t t'` rewrites every total equation of the sequent (`Fml.rwEq`), with no soundness proof per rule; the laws are the next section's |
| the same, inside an update | `Proves.updRw` (`Calculus/Logic.lean`), `sol_rw` | done | an update's right-hand side runs in the interpreter, so the rewrite there asks `Term.EvalRefines t t'` (where `t` returns, `t'` returns the same value), which a Theory equation onto a literal gives (`Term.EvalRefines.of_theq`); box updates only |

## The data-structure theories

The rows above are `solidityProgramRules.key`, the *program* calculus. Its
updates are written over symbols — `find`, `save`, `selectSt`, `read`,
`write`, `addM` — that solkey declares in `structHeader.key`/`memoryHeader.key`
and defines nowhere: their whole meaning is the taclet sets of
`structRules.key`, `memoryRules.key` and `structMemoryRules.key`.
`Solidity/Theory/` is that meaning, as a term algebra with one theorem per
taclet.

Paths are `Semantics.Seg` on both sides: a member constant is `Seg.field n`,
`at(i)` is `Seg.at i`, `size` is `Seg.field "length"`, `consr(p, a)` is
`p ++ [a]`. `listRules.key` therefore needs no module — it is `List`.

### The update vocabulary (`Solidity/Update.lean`)

`Update.lean`'s inductives are the signature, not an enumeration of update
shapes: an update element's right-hand side is a *term*, read in the
pre-state, and a rule's premise nests them as KeY's `\replacewith` updates do.
The sorts are KeY's, renamed to plain Lean identifiers (no `Rules.` prefix —
there is no `Rules.StTerm`/`Rules.MemTerm` any more, the mutual inductive
block in `Update.lean` **is** the signature):

| KeY sort | Here | Notes |
| --- | --- | --- |
| a value | `Term` | a constant, a stack local, `a ⊕ b`, `find(s, p)`, `read(m, a)`, `select(s, r)` (`Term.find` at a state variable), the length of an array (`Term.len`), `c ? a : b`, `selectSt(net, at(a))` (`Term.net`) and `selectSt(oldNet, at(a))` (`Term.netOf`) |
| `Path[storage]` | `PTerm` | a state variable (`.root`), an alias (`.pv`), `.field`/`.at` |
| `Storage` | `STerm` | `.storage`, `save`/`.save`, `delAt`/`.delAt`; a push and a pop are `.push`/`.pushSlot`/`.pop`/`.extend`, **not** two plain `save`s stacked — see below |
| what a storage `save` writes | `SValT` | a value (`.val`), a subtree read out of a storage (`.find`), or a memory object copied back (`.copyMem`, KeY's `copyMem(mtSt, m, i)`) |
| `Identity` | `ITerm` | a memory local (`.pv`), a reference read out of memory (`.read`), `freshId(addM(m))` (`.alloc`, carrying the allocated `RefTy`; a concrete struct's prints `freshId(addM(m, S))`), `freshId(copySt(m, v))` (`.copy`) |
| a member or element of a memory object | `MAddr` | `.field`/`.at` |
| `Memory` | `MTerm` | `.memory`, `write(m, a, v)` (`.write`), `addM(m)` (`.addM`, eager: the type rides along; a concrete struct's prints `addM(m, S)`, KeY's `addM(mem, idp)`), `copySt(m, v)` (`.copySt`) |
| what a memory `write` writes | `MValT` | a value (`.val`) or a reference (`.ref`) |
| one elementary update | `UpdElem` | `.val`/`.path`/`.mref`/`.storage`/`.memory`, plus `.transfer` for `{selfBalance := selfBalance - a ‖ net := …}`, the pair that moves together; `.store` for `old := storage`, `.saveNet` for `oldNet := net`, and `.book` for a specification's `{net := storeSt(net, at(msgSender), … + msgValue) ‖ selfBalance := selfBalance + msgValue}` |

**An allocation is still the two parallel elements KeY writes** —
`memoryReferenceDeclFreshAlloc`'s premise is
`{ mv := freshId(addM(memory)) ‖ memory := addM(memory) }` — evaluated against
the same pre-state, so `ITerm.alloc` and `MTerm.addM` agree on which root gets
minted without either re-deriving the other's answer.  A rule's `R` and an
array print `addM(memory)`; a concrete struct prints as KeY's two-argument
`addM(mem, idp)` does, `{ carol := freshId(addM(memory, Person)) ‖ memory :=
addM(memory, Person) }`, which `dl!{ … }` reads back.

**A push is one term, not two saves in a nested update.** KeY writes
`arr.push(se)` as two saves in one parallel update, the new slot `at(n)` and
the new length `size`, both reading the pre-state; here `STerm.push s p v`
*is* `save(save(s, p[p.length], v), p.length, p.length + 1)` as a single
constructor, because a *program* can perform neither write alone (there is no
statement for "write one past the end" or "assign `a.length`"): the length
grows by the push, and the slot it lands on is a recycled one or a fresh
default (`Semantics.pushAt`). `STerm.pushSlot` is the bare `push()` of a
primitive element (`storagePushLengthSave`, the slot cleared), `STerm.extend`
of a struct or array element (`storagePushLengthSaveReferenceElement`, the
recycled slot taken as it is, so a write through a reference to the popped
element is read back), and `STerm.pop`/`STerm.shrink` the duals
(`storagePopSave` clears the element into the recycled slots,
`storagePopSaveMappingElement` keeps it). A mapping nested in a popped
element survives into the next `push` either way.

**Memory `delete` has no update to spell.** All eight memory-delete taclets
are unclaimed (see "Memory delete" above), so nothing in `Update.lean`
corresponds to KeY's `write(addM(memory, r), mv, fr, idC(r, nil))` shape for
a deleted reference member; if memory `delete` is ported later, its update
belongs here.

### `structRules.key` → `Theory/Storage.lean` (`Struct`, `StValue`)

The theory tables track solkey `f2eb3d98eb`'s `structRules.key`,
`structHeader.key`, `memoryRules.key` and `memoryHeader.key`, which moved on
from the program-taclet pin above: the `delValue` family became `delField`,
`delNodeFixed` and the `Shape` sort arrived (for a fixed-size array's
length), `selectStDelNodeIndexStruct` became length-guarded, and
`findDefinitionCons` split by field sort.

| KeY taclet | Lean theorem | Status |
| --- | --- | --- |
| `defaultValueStruct` | `defaultValueStruct`, with `defaultValueInt`/`defaultValueBool` | done: `defaultValue<[α]>` is `st mtSt`, the `Struct` default, read through the caller's cast |
| `selectOnStore` | `selectOnStore` | done |
| `selectOnEmptyStorage` | `selectOnEmptyStorage` | done |
| `saveOnEmptyStorage` | `saveOnEmptyStorage` | done, in the pre-fold shape (an `isEmpty(flds)` split) |
| `saveOnStoreCons` | `saveOnStoreCons` | done, in the pre-fold shape: the `isEmpty(flds)` split is back, since the leaf collapses; `(Struct) v0` is `asStruct v0` |
| `findDefinitionEmpty` | `findDefinitionEmpty` | done |
| `findDefinitionElement`, `findDefinitionMapElement`, `findDefinitionSize`, `findDefinitionMemberPrim`, `findDefinitionMemberValue` | `findDefinitionCons` | done: the old single rule, split upstream by field sort; `atMap(i)` is `Seg.at i` and `size` is `Seg.field "length"` |
| `findDefinitionMemberStruct`, `findDefinitionMemberCons` | `findDefinitionCons` | done **without the tag**: upstream wraps the struct read through a member in `typed(fieldShape(m), …)`; `typed` is not modelled (below), and without it these are `findDefinitionCons` |
| ~~`saveOnEmpty`~~ (pre-fold) | `saveOnEmpty` | done — gone upstream with the `copyAt`→`save` fold and kept here: `save(st, nil, v) ⇝ v`, the collapsing leaf |
| ~~`selectOnSaveEmpty`~~ (pre-fold) | `selectOnSaveEmpty` | done as the pre-fold rule over the collapsing `save` — a member of `save(st, nil, v)` is a member of `(Struct) v`. The word write and `delAt`'s write collapse; a struct or array written over a location is the copying `copyTo` (`Theory/Copy.lean`), whose rules are the `selectOnSaveEmpty*` rows below |
| `saveOnEmptyPrim` | `saveOnEmptyPrimInt`, `saveOnEmptyPrimBool` | done, as the two cast readings at the end of a walk: `storeSt`'s third argument is the supersort, so the primitive leaf is stored verbatim |
| `selectOnSaveEmptyRef`, `selectOnSaveEmptyFixed` | `selectOnCopyRef` | done over the copying write, `save(st, nil, v)` being `copyTo s [] (st n)` = `copyAt s n` (`copyTo_nil`), for every `Seg`, with both nodes struct-like as the premise; `StValue.selectOnSaveEmptyRef` is the same equation over the collapsing `save` |
| `selectOnSaveEmptyIndexStruct` | `selectOnCopyIndexNew`, `selectOnCopyIndexClear`, `selectOnCopyIndexKeep`, `selectOnCopySize` | done over the copying write with **no length invariant**: the branch is picked by `inRange` on the two nodes' lengths (`lenOf`), and the length read is the new array's. The collapsing-`save` versions `selectOnSaveEmptyIndexStruct`/`Clear`/`Keep` remain, the last two under the invariant |
| `selectOnSaveEmptyDefault` (upstream it is `selectOnSaveEmpty`'s primitive case) | `selectOnCopyDefault` | done: a word member of the new node is the word |
| `selectOnSaveEmptyMap` | `selectOnCopyMap` | done: a mapping copied over a mapping keeps the old entries, both nodes' kinds the premise. Unreachable from a program — solc ≥ 0.7 and solkey's own parser reject the copy, and `Src.copy` cannot build it |
| `selectOnSaveCons` | `selectOnSaveCons` | done, and **unconditional** (a total definition needs no `isStruct` guard) |
| `delFieldRef`, `delFieldIndexStruct` | `delFieldRef`, `delFieldIndexStruct` | done: `delField s a = delValue (selectSt s a)`, the reset picked by the value's sort since a `Seg` has none |
| `delFieldDefault` | `delFieldDefault`, `delFieldDefault_asBool` | done |
| `delFieldStValueCast` | `delValueCast`, `delValueCast_asInt`, `delValueCast_asBool` | done as the cast pushed through the reset (was `delValueStValueCast`) |
| `delFieldMap` | `delFieldMap` | done one selector down (both sides literal terms), the member's kind being a mapping as the premise: a `Seg` has no sort, the node carries it |
| `delFieldFixed` | `delFieldFixed` | done one selector down, the member's kind being a fixed-size array (`.arr true`) as the premise |
| ~~`delValueStruct`~~, ~~`delValueDefault`~~ | `delValueStruct`, `delValueDefault` | gone upstream (replaced by `delField`); kept as the lemmas under it |
| `selectStDelNodeMap` | `selectDelNodeMap`, `selectStDelNodeMap` | done one selector down: `selectDelNodeMap` is the rule (the member is a mapping, whatever the node); `selectStDelNodeMap` is the node-kind form, every member of a deleted mapping kept (`selectStDelNodeKeep`) |
| `selectStDelNodeRef` | `selectStDelNodeRef` (from `selectStDelNodeSelect`) | done at a member the node does not keep (`keepsOnDelete`, false for every member of a struct and every field but `length` of a non-mapping): one theorem, `selectSt (delNode s) a = delValue (selectSt s a)`, covers `Ref`, `Default` and the in-bounds index; `selectOnDelNode` is the general form, `selectStDelNodeKeep` the kept members |
| `selectStDelNodeIndexStruct` | `selectStDelNodeIndexStruct`, `selectStDelNodeSelect`, `selectStDelNodeKeep`, `selectStDelNodeIndexKeep` | done: the in-bounds branch under the `keepsOnDelete` premise, which at an array is KeY's guard `i < size` (`keepsOnDelete_at`); the keep branch past the length (`selectStDelNodeKeep`) and at an absent slot (`selectStDelNodeIndexKeep`) |
| `selectStDelNodeDefault` | `selectStDelNodeDefault`, `selectStDelNodeDefault_asBool` | done, at a member the node does not keep |
| `selectStDelNodeFixed` | `selectStDelNodeFixed` (through `selectSt_delNode_fixed`) | done one selector down, at a member the node does not keep whose kind is a fixed-size array |
| `selectStDelNodeFixedMap` | — | **derived**: two rules in a row — `selectStDelNodeFixedElement` takes an in-bounds element to `delNode` of it and `selectStDelNodeMap` keeps a deleted mapping's members; past the length the slot is kept outright (`selectStDelNodeKeep`) |
| `selectStDelNodeFixed{Element,Size,Value}` | `selectStDelNodeFixedElement`, `selectStDelNodeFixedSize`, `selectStDelNodeFixedValue` (+`_asBool`) | done, over `delNodeFixed` (`delNode` with the `length` member stored back); `Element` and `Value` at a member the node does not keep |
| `delAtEmpty` | `delAtEmpty` | done |
| `selectOnDelAtCons` | `selectOnDelAtCons` | done, through `selectOnSaveCons`: `delAt` is eager, `save st p (delValue (find st p))`; the leaf is `delField st a1` |
| `fieldShapeDef` | `fieldShapeDef` (`fieldShape`, `Shape.ofTy`) | done: `#shapeOf` is `Shape.ofTy`, over a member table the caller supplies (a `Seg.field` carries the name, not the declaration) |
| `selectOnTyped{Struct,FixedSize,DynSize,LeafSize,MapSize,Element,Member}`, `typedTyped` | — | **not modelled**: the only rule that reads the tag is `selectOnTypedFixedSize`; a declared `T[n]` has shape `fixedArr` (`Shape.ofTy_fixed`), but the elaborator writes its `.length` as the literal `n`, so no program reads it, and `typed` would be one more `Struct` constructor through every proof (`Theory/Storage.lean`, "Shapes"). A delete keeps a fixed-size array's length without it: the node's kind says what it is (`keepsOnDelete`) |
| ~~`copyAtEmpty`~~, ~~`selectOnCopyAtCons`~~, ~~`mergePrim`~~, ~~`selectStMerge{Map,Ref,IndexStruct,Default}`~~, ~~`mergeStValueCast`~~ | `selectOnCopyAt` | gone upstream with the fold; here `Struct.copyAt` is `copyTo`'s leaf, read one member at a time by `selectOnCopyAt` (`copyRead`, by the two nodes' kinds and lengths), and the `selectOnCopy*` rows above are its rules |
| `findStValueCast`, `selectStValueCast` | `asStruct_st`, `asStruct_prim`, `find_append` | done as the cast being the inverse of the injection `st` |
| `sizeNotNegative` | — | **arch**: an `\add` of a reachability fact, not a rewrite; a bounds check on an array index is a *guard* on the program-level taclet, not a term-algebra theorem |

**Beyond the taclets.** solkey has no `find(save(…), …)` rule at all: a read of
a write is reached by `findDefinitionCons` then `selectOnSaveCons`, one
selector at a time. `Theory/Storage.lean` packages the four cases over
`save` — `find_save_same`, `find_save_extends` (below the write, through the
cast `find<[Struct]>` makes), `find_save_prefix` (above it) and
`find_save_frame` (off it, over `diverges`) — and `find_append` composes reads
along `++`. Over `delAt` the same: `find_delAt_same` and
`find_delAt_field` (`findDelAt`), `find_delAt_frame`, `find_delAt_extends`,
`find_delAt_member` (one member below a deleted path, at a member the node
does not keep), and `find_delAt_below` (a read below a deleted path is the
reset of the read before it, through any path, on a node with no kinds in it).

**`storeAt` and the two sorts.** `save` is a recursion on the path over
`storeAt`, the one-segment walk. It returns `Struct`, as KeY's does, and
stores the written value verbatim at the last segment: `storeSt`'s third
argument is the supersort `StValue`, so a primitive leaf is kept as itself
and `find` reads it back at the caller's sort — which is what
`saveOnEmptyPrim` does in KeY. `delAt` is eager over the same walk, down to
the lazy leaf at the deleted node (`delNode`, the `delSt` leaf). The storage terms
denote in this algebra (`Term.denote`, over `State.abs`, `Update.lean`), and
`Theory/Bridge/` relates every write to the interpreter's — a word write and
a push literally, a copy, a delete and a pop up to `StValue.Equiv`.

### `memoryRules.key` → `Theory/Memory.lean`

Identities are KeY's path identities `idC(idp, flds)`, so the chain-walking
rows have counterparts and `MTerm.addM` carries the root it allocates. A root
may be `shaped(idp, sh)` (`IdentityPrim.shaped`, `Theory/Terms.lean`).

| KeY taclet | Lean theorem | Status |
| --- | --- | --- |
| `readOnWrite` | `readOnWrite` | done |
| `readFromEmptyMemory` | `readFromEmptyMemory` | done |
| `readOnAddM` | `readOnAddM` | done |
| `newFromEmptyMemory` | `newFromEmptyMemory` | done |
| `newFromWrite` | `newFromWrite` | done |
| `newFromAdd` | `newFromAdd` | done |
| `defaultValueInt`, `defaultValueBool`, `defValResolve` | `MemValue.asPrim`, `defaultDefInt`, `defValResolvePrim` | done as casts |
| `defaultDefElement`, `defaultDefMember` | `defaultDefElement`, `defaultDefMember` (`MemValue.asIntAt`) | done: the old single `defaultDef`, split by field so that `defaultSize` has the length to itself; the cast takes the location |
| `defaultSize` | `defaultSize` (and `defaultSizeUnshaped` for a bare root) | done |
| `defaultDefIdentity` | `defaultDefIdentity` (`MemValue.asIdentity`) | done |
| `idCCDef` | `idCCDef` | done |
| `readREmpty`, `readRCons` | `readREmpty`, `readRCons` (`Memory.readR`, `readRId`) | done |
| `sizeOfFixed`, `sizeOfDyn`, `sizeOfLeaf` | `sizeOfFixed`, `sizeOfDyn`, `sizeOfLeaf` (`shapeSize`: `sizeOf` is Lean's own) | done; `mapOf` has no taclet and is `0` |
| `shapeAtNil` | `shapeAtNil` | done |
| `shapeAtFixed`, `shapeAtFixedMapElement` | `shapeAtFixed` | done: `atMap(i)` is `Seg.at i` |
| `shapeAtDyn`, `shapeAtDynMapElement` | `shapeAtDyn` | done, likewise |
| `shapeAtMap` | `shapeAtMap` | done |
| `shapeAtLeafElement`, `shapeAtLeafMapElement` | `shapeAtLeafElement` | **differs** on an ill-typed path: upstream `shapeAt(leaf, cons(at(pk), xs)) ⇝ leaf` drops `xs`; here the walk goes on from `leaf`, which is what makes `shapeAtSuffix` hold (upstream it fails on `leaf·at(i)·m`) |
| `shapeAtMember` | `shapeAtMember` | done, for a member other than `size` (not a `MemberField`) |
| — | `shapeAtSuffix` | the tail-first rule; no taclet upstream (solkey recurses head-first) |
| `idShapeDef` | `idShapeDef` | done |

### `structMemoryRules.key` → `Theory/CrossDomain.lean`

| KeY taclet | Lean theorem | Status |
| --- | --- | --- |
| `findOnCopy` | `StValue.findCopyMem`, `StValue.findCopyMem_asBool` | done, at the primitive sorts, as the taclet is |
| `selectOnCopyMemPrim` | `StValue.selectOnCopyMemPrim` (`_asBool`) | done, through `find`: `selectSt` on a view stays structural and reads nothing |
| `selectOnCopyMemRef` | `StValue.selectOnCopyMemRef`, `StValue.findCopyMemStruct` | done, for a slot that is not a primitive (the sort premise); a never-written slot is the view at `defaultDefIdentity`'s identity, so a member memory created implicitly is read through |
| `readFromCopyToStorage` | `Memory.readCopySt` | done |
| `readFromCopyToStorageIdentity` | `Memory.readCopyStIdentity` | done |
| — | `Memory.readCopyStOther` | the split form of the frame |

The views are constructors of the two sorts, as KeY declares them
(`Struct copyMem(Struct, Memory, Identity)`,
`Memory copySt(Memory, IdentityPrim, Struct)`), which makes `Struct`,
`StValue` and `Memory` one mutual inductive — `Theory/Terms.lean`. A read
through a `copyMem` view is `Memory.viewRead`: `readR`'s walk, with the last
slot a primitive or the view one field further down.

What this does not model is a view nested in a view: `readIn` reads its
copied struct with `findSt`, the reader that stops at a view, which is what
keeps every definition structural and so kernel-reducible. No worked example
nests one and no taclet rewrites under one.

### The Theory's laws as rules (`Calculus/TheoryLaws.lean`)

A law of the two storage modules, read through `Term.denote`, is a
`Term.Theq` between the terms that denote its sides, and so a rule on a
sequent (`rw [findOnSave]`) with no soundness proof of its own. Each is
stated at the terms `Update.lean` has; its side conditions are syntactic
`Bool`s on the `PTerm`s, closed by `rfl` (`PTerm.hasSeg`: never the empty
path; `PTerm.diverges`: members and literal indices that diverge as lists).

| Law | Theory lemma | Printed rule (`TheoryRule`) | Notes |
| --- | --- | --- | --- |
| `findOnSave` | `find_copyTo_same` (`Theory/Copy.lean`) | `findOnSave` | `find(save(s, p, v), p) ≐ v` for a literal word `v`: a copy reads back the new value laid over the old, which is `v` only for a word |
| `findOnSaveFrame` | `find_copyTo_frame` | `findOnSaveDifferent` | any written value, `p` diverging from `q` |
| `findOnDelAt` | `find_delAt_same`, `delValueDefault` (`Theory/Storage.lean`) | `findDelAt` | where `find(s, p) ≐ w` for a word `w`, the delete reads its default |
| `findOnDelAtSave` | `findOnDelAt` over `findOnSave` | `findDelAt` | a delete over a written word |
| `findOnDelAtFrame` | `find_delAt_frame` | `findDelAtOutside` | |
| `findOnPushFrame` | `find_pushT_frame` (`Theory/Copy.lean`) | — | a push is one term here (`STerm.push`), not two saves |
| `findOnPopFrame` | `find_popT_frame` | — | likewise a pop |

solkey has none of these as a taclet (it reaches a read of a write one
selector at a time, "Beyond the taclets" above); they are the rules
`Theory/Rewrite.lean` lists as Lean-only, stated on terms.

### The names for these rules

`Theory/Rewrite.lean` is the enumeration of the theory's rules under the
printed names, with `lemmaNames`
mapping each `TheoryRule` constructor to the theorem(s) above. The theorems
keep their upstream (KeY) names — that is what makes this file, and
`Theory/Rewrite.lean`'s own docstring says so explicitly, a map — and the
join is stated against the printed
`\namedRwRule` declarations rather than left as prose. The printed rules with no
constructor — the `typed` rows marked **not modelled** above,
`selectStDelNodeFixedMap` (**derived**), and the four arithmetic expansions
listed as not implemented — are excused in `Theory/Rewrite.lean` by name, each with its
reason.

### Deviations, collected

Two places where a term carries something KeY's does not, both because KeY is
lazy and the interpreter is eager:

* `MTerm.addM` carries the allocated `RefTy` beside its root. KeY's
  `readOnAddM` resolves a never-written slot of a fresh object to
  `default<[α]>` at the reader's sort; `Semantics.allocDefault` materializes
  the object at allocation, so the term has to know its type to denote.
* `Theory/Storage.lean` renders `defaultValue<[α]>` as `st mtSt`, the `Struct`
  default, resolved by the caller's cast (`asInt (st mtSt) = 0`) rather than
  by the sort the read asks for.

And three where the theory reads a rule differently, each argued at its row:

* The reset a `delete` picks is keyed on the *node's kind*, not the field's
  sort (`delField`, `delNode`, `keepsOnDelete`): a `Seg` carries no
  `MapField`/`FixedField`, so the rules that pick the mapping-preserving and
  length-preserving reset are stated one selector down, with the kind of the
  node they read as a premise.
* `fieldShape` takes the member table as an argument: KeY's member constants
  know their declaration, a `Seg.field` only its name.
* `shapeAt` follows `shapeAtSuffix` rather than solkey's
  `shapeAtLeafElement`, which drops the rest of the path under an indexed
  `leaf`; the two agree on every well-typed path.
