# KeY taclet → Lean `Taclet` mapping

The name-by-name map from solkey's `solidityProgramRules.key` (plus
`ifThenElseRules.key`) to `Solidity.Taclet`, the inductive of
`Solidity/Calculus/Rules.lean`. One row per taclet, grouped by family as
solkey's file groups them.

**Pinned to solkey `8c5c69ca25`** (310 program taclets, three `\heuristics`
classes; `Calculus/KeyTaclets.lean` is the vendored enumeration). Every rule
of `Calculus/Rules.lean` is a constructor of one inductive `Taclet C k m s p`,
written `dl{ ⟨[ s; ]⟩ ⇝ p }` and named as solkey names the taclet(s) it
transcribes — an operator family or a receiver/source-kind split is one
constructor for several taclets, and a taclet the typed syntax cannot express
(no calls, no `new`, no memory `delete`, the callback semantics of
`transfer`, the five literal-condition `if` shortcuts) has none.

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
- **`taclets_partitioned`** — every one of the 310 taclets is claimed by some
  row or excused, never both: `claimedTaclets_count = 287`,
  `unclaimedTaclets_count = 23`. A taclet may be claimed by two constructors
  (a `*CaptureAll` by the `_unfold_leftFst` and the `NonSimpleIndexCapture` of
  its family; `memoryFieldWrite`/`memoryIndexWriteArray` by the value write
  and the reference copy) — the tables below list both.

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
`TypedStmt.Assign.mk` cannot build. `docs/solkey-feedback.md` carries the
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

## Modality / sequent rules

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `functionBodyExpand` | — | unclaimed | the typed syntax has no calls |
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
| `storageFieldRead_unfold_rightFst` | `storageFieldRead_unfold_rightFst` | same | |
| `storageFieldReadFind` | `storageFieldReadFind` | same | |
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

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `storageIndexWriteArraySave` | `storageIndexWriteArraySave` | same | one rule for both modalities; an out-of-range write reverts inside `SVal.save`, not as a separate bounds goal |
| `storageIndexReadArrayFind` | `storageIndexReadArrayFind` | same | |
| `storageIndexReadArrayBindLocalRoot` | `storageIndexReadArrayBindLocalRoot` | same | |
| `storageIndexReadArrayStoreRoot` | `storageIndexReadArrayStoreRoot` | same | |
| `storageIndexWriteArrayCopySource` | `storageIndexWriteArrayCopySource` | same | |
| `storageIndexWriteNonSimpleIndexCapture` | `storageIndexWriteNonSimpleIndexCapture` | same | `sp[nse] = e ⇝ T se = e; T ie = nse; sp[ie] = se`; also claimed jointly with the row below by `storageIndexWriteCaptureAll` |
| `storageIndexWriteStorageRefNonSimpleIndexCapture` | `storageIndexWriteStorageRefNonSimpleIndexCapture` | same | the reference-source twin, no freeze |
| `storageIndexWrite_unfold_leftFst` | `storageIndexWrite_unfold_leftFst` | same | `nsp[e1] = e2 ⇝ T se = e2; T storage sp = nsp; T ie = e1; sp[ie] = se` |
| `storageIndexWriteStorageRef_unfold_leftFst` | `storageIndexWriteStorageRef_unfold_leftFst` | same | the reference-source twin |
| `storageIndexWriteCaptureAll` | `storageIndexWrite_unfold_leftFst` and `storageIndexWriteNonSimpleIndexCapture` | merged into `storageIndexWrite_unfold_leftFst` and `storageIndexWriteNonSimpleIndexCapture` | KeY captures a nonsimple receiver **and** a nonsimple index in one step; Lean's `unfold_leftFst` already captures the whole receiver (its index capture is `T ie = e1`), and the index-only case is the other rule — both claim it |
| `storageIndexWriteStorageRefCaptureAll` | `storageIndexWriteStorageRef_unfold_leftFst` and `storageIndexWriteStorageRefNonSimpleIndexCapture` | merged into `storageIndexWriteStorageRef_unfold_leftFst` and `storageIndexWriteStorageRefNonSimpleIndexCapture` | the reference-source twin of the row above |
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
| `storagePushLengthSave` | `storagePushLengthSave` | same | |
| `storageLocalRootPushBind` | `storageLocalRootPushBind` | same | |
| `storagePopSave` | `storagePopSave` | same | one rule for both modalities |

## Storage local declarations

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `storageLocalDeclInitDrop` | `storageLocalDeclInitDrop` | same | |
| `storageLocalRootRebind` | `storageLocalRootRebind` | same | |
| `storageLocalDeclSkip` | `storageLocalDeclSkip` | same | |

## Storage delete

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `storageRootDelete` | `storageRootDelete` | same | `delete(gsp) ⇝ { storage := delAt(storage, gsp) }` |
| `storageFieldDelete` | `storageFieldDelete` | same | |
| `storageIndexDelete` | `storageIndexDelete` | same | `isArray sp ∨ isMapping sp`, one rule for both |
| `storageFieldDelete_unfold_leftFst` | `storageFieldDelete_unfold_leftFst` | same | |
| `storageIndexDelete_unfold_leftFst` | `storageIndexDelete_unfold_leftFst` | same | |
| `storageIndexDeleteNonSimpleIndexCapture` | `storageIndexDeleteNonSimpleIndexCapture` | same | |

## Memory allocation, aliasing, declarations

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `memoryReferenceDeclFreshAlloc` | `memoryReferenceDeclFreshAlloc` | same | `T memory mv; ⇝ { mv := freshId(addM(memory)) ‖ memory := addM(memory) }`, the pair KeY writes |
| `memoryArrayFreshAlloc` | — | unclaimed | nor `new T[](n)`: a memory array is made by declaration or by copy from storage |
| `memoryRootDeleteFreshRebind` | — | unclaimed | no memory `delete`: `Stmt.delete` takes a storage location (see "Memory delete" below) |
| `memoryRootRebind` | `memoryRootAlias` | merged into `memoryRootAlias` | `mv₁ = mv₂; ⇝ { mv₁ := mv₂ }`; a storage right-hand side is the row below instead |
| `memoryStorageCopy` | `memoryStorageCopy` | same | `mv = sp;` deep copy: fresh identity plus `copySt` |
| `memoryStorageCopyUnfold` | `memoryStorageCopyUnfold` | same | a complex storage path is captured first |
| `memoryLocalDeclInitDrop` | `memoryLocalDeclInitDrop` | same | one generic decl-with-init split; the assignment rules take it from there, so there is no per-source-kind decl-init family |

## Memory field/index write & read

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `memoryFieldWrite` | `memoryFieldWriteStore` and `memoryFieldWriteCopy` | merged into `memoryFieldWriteStore` and `memoryFieldWriteCopy` | Lean's sorts are not generic, so KeY's one write is two rules: a value source and a reference-path source |
| `memoryFieldRead` | `memoryFieldReadHeap` and `memoryFieldReadAliasRoot` | merged into `memoryFieldReadHeap` and `memoryFieldReadAliasRoot` | same split, on the read side (a value lands on a local, a reference on a memory alias) |
| `memoryFieldRead_unfold_rightFst` | `memoryFieldRead_unfold_rightFst` | same | |
| `memoryFieldWriteCaptureSrc` | — | unclaimed | KeY captures a memory reference into an alias before writing it; here a memory path is a source as it stands (`mpath`), so `memoryFieldWriteCopy` writes it in one step |
| `memoryFieldWrite_unfold_leftFst` | `memoryFieldWrite_unfold_leftFst` | same | also claims the reference-receiver row below |
| `memoryFieldWriteMemRef_unfold_leftFst` | `memoryFieldWrite_unfold_leftFst` | merged into `memoryFieldWrite_unfold_leftFst` | `msrc` is a value or a memory reference, so one rule covers both |
| `memoryIndexWriteArray` | `memoryIndexWriteStore` and `memoryIndexWriteCopy` | merged into `memoryIndexWriteStore` and `memoryIndexWriteCopy` | as `memoryFieldWrite` |
| `memoryIndexReadArrayValue` | `memoryIndexReadHeap` | merged into `memoryIndexReadHeap` | |
| `memoryIndexReadArrayMemory` | `memoryIndexReadAliasRoot` | merged into `memoryIndexReadAliasRoot` | |
| `memoryIndexRead_unfold_rightFst` | `memoryIndexRead_unfold_rightFst` | same | |
| `memoryIndexWrite_unfold_leftFst` | `memoryIndexWrite_unfold_leftFst` | same | also claims the three rows below |
| `memoryIndexWriteMemRef_unfold_leftFst` | `memoryIndexWrite_unfold_leftFst` | merged into `memoryIndexWrite_unfold_leftFst` | `msrc` value-or-reference, as the field case |
| `memoryIndexWriteCaptureAll` | `memoryIndexWrite_unfold_leftFst` and `memoryIndexWriteNonSimpleIndexCapture` | merged into `memoryIndexWrite_unfold_leftFst` and `memoryIndexWriteNonSimpleIndexCapture` | as `storageIndexWriteCaptureAll` |
| `memoryIndexWriteMemRefCaptureAll` | `memoryIndexWrite_unfold_leftFst` and `memoryIndexWriteNonSimpleIndexCapture` | merged into `memoryIndexWrite_unfold_leftFst` and `memoryIndexWriteNonSimpleIndexCapture` | the reference-source twin of the row above |
| `memoryIndexWriteMemRefRhsCapture` | — | unclaimed | a reference source at an index is written directly, as `memoryFieldWriteCaptureSrc` above |
| `memoryIndexWriteNonSimpleIndexCapture` | `memoryIndexWriteNonSimpleIndexCapture` | same | also claims the reference-source row below |
| `memoryIndexWriteMemRefNonSimpleIndexCapture` | `memoryIndexWriteNonSimpleIndexCapture` | merged into `memoryIndexWriteNonSimpleIndexCapture` | |
| `memoryFieldWriteUnfoldSource` (Lean-side name for the value capture below `fieldWriteValueRhsCapture`'s storage form) | `fieldWriteValueRhsCapture` | merged into `fieldWriteValueRhsCapture` | see "Value-RHS capture" in the arithmetic section below: the location-neutral capture rule also claims the memory case |
| `memoryIndexWriteUnfoldSource` | `indexWriteValueRhsCapture` | merged into `indexWriteValueRhsCapture` | same, at an index |
| `memoryFieldRead_unfold_rightSndResult` | — | unclaimed | as `memoryFieldWriteCaptureSrc`: a memory path is a source as it stands |
| `memoryIndexRead_unfold_rightSndIndex` | `memoryIndexRead_unfold_rightSndIndex` | same | |
| `memoryIndexRead_unfold_rightSndResult` | — | unclaimed | as `memoryFieldWriteCaptureSrc` |

## Memory delete

Every memory-delete taclet is **unclaimed**: `Stmt.delete` takes a storage
location, and the typed syntax has no memory `delete` (`docs/kernel-port.md`,
"Port later"). This is a genuine gap against solkey, not an architectural
impossibility — unlike `emptyModality`/`blockEmpty` there is no reason memory
`delete` *could not* be added later; it simply has not been.

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `memoryRootDeleteFreshRebind` | — | unclaimed | listed above, with the allocation rules |
| `memoryFieldDeletePrimitive` | — | unclaimed | |
| `memoryFieldDeleteReference` | — | unclaimed | |
| `memoryIndexDeletePrimitive` | — | unclaimed | |
| `memoryIndexDeleteReference` | — | unclaimed | |
| `memoryFieldDelete_unfold_leftFst` | — | unclaimed | |
| `memoryIndexDelete_unfold_leftFst` | — | unclaimed | |
| `memoryIndexDeleteNonSimpleIndexCapture` | — | unclaimed | |

## Memory → storage copies

| KeY taclet | `Taclet` constructor | Status | Notes |
| --- | --- | --- | --- |
| `memoryToStorageStoreRoot` | `memoryToStorageStoreRoot` | same | |
| `memoryToStorageFieldCopyRoot` | `memoryToStorageFieldCopyRoot` | same | also claims the row below |
| `memoryToStorageFieldCopyField` | `memoryToStorageFieldCopyRoot` | merged into `memoryToStorageFieldCopyRoot` | the one member-source shape read directly |
| `memoryToStorageIndexMappingCopyRoot` | `memoryToStorageIndexMappingCopyRoot` | same | |
| `memoryToStorageIndexArrayCopyRoot` | `memoryToStorageIndexArrayCopyRoot` | same | one rule for both modalities |
| `memoryToStorageField_unfold_leftFst` | `memoryToStorageField_unfold_leftFst` | same | |
| `memoryToStorageIndex_unfold_leftFst` | `memoryToStorageIndex_unfold_leftFst` | same | also claims the row below |
| `memoryToStorageIndexNonSimpleIndexCapture` | `memoryToStorageIndexNonSimpleIndexCapture` | same | also claims `memoryToStorageIndexCaptureAll` |
| `memoryToStorageIndexCaptureAll` | `memoryToStorageIndex_unfold_leftFst` and `memoryToStorageIndexNonSimpleIndexCapture` | merged into `memoryToStorageIndex_unfold_leftFst` and `memoryToStorageIndexNonSimpleIndexCapture` | as `storageIndexWriteCaptureAll` |

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
| `additionAssignment`, `subtractionAssignment`, `multiplicationAssignment`, `powerAssignment`, `divisionAssignment`, `moduloAssignment` | `binopAssignment` | merged into `binopAssignment` | terminal `v = se₁ ⊕ se₂;`; solkey has no `powAssign` (`**=`) taclets, so there is no `localOpAssign (op := .pow)` instance on the KeY side either |

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
| `storageIndexArrayAddAssign`, … | `storageIndexArrayOpAssign` | merged into `storageIndexArrayOpAssign` | no bounds split: the update reverts inside `SVal.save` |
| `memoryFieldAddAssign`, … | `memoryFieldOpAssign` | merged into `memoryFieldOpAssign` | |
| `memoryIndexArrayAddAssign`, … | `memoryIndexArrayOpAssign` | merged into `memoryIndexArrayOpAssign` | no root or mapping form: a memory root binds an identity, memory has no mappings |
| `storageFieldAddAssign_unfold_leftFst`, … | `storageFieldOpAssignUnfoldLeftFst` | merged into `storageFieldOpAssignUnfoldLeftFst` | `nsp.fld ⊕= se; ⇝ T storage sp = nsp; sp.fld ⊕= se;` |
| `storageIndexAddAssign_unfold_leftFst`, … | `storageIndexOpAssignUnfoldLeftFst` | merged into `storageIndexOpAssignUnfoldLeftFst` | |
| `memoryFieldAddAssign_unfold_leftFst`, … | `memoryFieldOpAssignUnfoldLeftFst` | merged into `memoryFieldOpAssignUnfoldLeftFst` | |
| `memoryIndexAddAssign_unfold_leftFst`, … | `memoryIndexOpAssignUnfoldLeftFst` | merged into `memoryIndexOpAssignUnfoldLeftFst` | |
| `addAssignValueRhsCapture`, `subAssignValueRhsCapture`, `mulAssignValueRhsCapture`, `divAssignValueRhsCapture`, `modAssignValueRhsCapture` | `compoundAssignValueRhsCapture` | merged into `compoundAssignValueRhsCapture` | location-neutral capture of a nonsimple compound-assign RHS, as the plain-assignment value capture above |

## Increment / decrement

Pattern per `V ∈ {Preincrement, Postincrement, Predecrement, Postdecrement}`.
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
| `transferNoCallbackBox` | `transferNoCallback` | merged into `transferNoCallback` | one terminal rule for both modalities now, `sadr.transfer(se); ⇝ { transfer(sadr, se) }`; no separate "sufficient funds" goal — an unfunded transfer reverts inside `Update.transferAt` itself, the same move as the array-bounds and division-by-zero cases elsewhere in the table |
| `transferNoCallbackDiamond` | `transferNoCallback` | merged into `transferNoCallback` | |
| `transferWithCallbackBox` | — | unclaimed | the callback semantics of `transfer` (the callee may re-enter); the typed syntax has no calls, so there is nothing for a re-entrant callee to run |
| `transferWithCallbackDiamond` | — | unclaimed | |

## Update algebra (`updateRules.key`)

The Lean model has no update syntax — state change is function application —
so KeY's update calculus splits into (a) point-of-application laws with real
semantic content, ported as `State` lemmas in `Semantics/Properties.lean`,
and (b) the update-monoid normal-form machinery, which is definitional
function composition in Lean and has no Lean counterpart to name.

| KeY rule | Lean analogue | Status | Notes |
| --- | --- | --- | --- |
| `applyOnPV` / `applyOnPVLastInParallel` | `State.getEnv_setEnv_self`, `State.getNet_setNet_self`; storage: `State.findStorage_saveStorage_same` | lemma | read after write at the point of application |
| `applyOnDifferentPV` / `applyOnDifferentPVLastInParallel` | `State.getEnv_setEnv_ne`, `State.getNet_setNet_ne`; storage: `State.saveStorage_frame` | lemma | frame under a distinct location |
| `simplifyUpdate1`–`3` | `State.setEnv_setEnv_absorb`, `State.setNet_setNet_absorb` (core: `setBy_setBy_self`) | lemma | the syntactic `\dropEffectlessElementaries` procedure is meaningless without update terms; its semantic law is overwrite absorption |
| `sequentialToParallel1-3`, `applyOnParallel`, `applyOnElementary`, `applyOnSkip`, `applySkip1-3`, `parallelWithSkip1-2` | — | arch | the update monoid normal form: `Upd C` is `List (UpdElem C)` applied left to right against the pre-state (`Upd.apply`), so sequencing and parallelism are the list structure itself, not something to normalize |
| `simplifyIfThenElseUpdate1-4`, `commuteSimpleUpdates`, `elimSelfUpdate*` | — | arch | commented-out dead code in the KeY source |

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
| a value | `Term` | a constant, a stack local, `a ⊕ b`, `find(s, p)`, `read(m, a)`, `select(s, r)` (`Term.find` at a state variable), the length of an array (`Term.len`), `c ? a : b` |
| `Path[storage]` | `PTerm` | a state variable (`.root`), an alias (`.pv`), `.field`/`.at` |
| `Storage` | `STerm` | `.storage`, `save`/`.save`, `delAt`/`.delAt`; a push and a pop are `.push`/`.pushSlot`/`.pop`/`.extend`, **not** two plain `save`s stacked — see below |
| what a storage `save` writes | `SValT` | a value (`.val`), a subtree read out of a storage (`.find`), or a memory object copied back (`.copyMem`, KeY's `copyMem(mtSt, m, i)`) |
| `Identity` | `ITerm` | a memory local (`.pv`), a reference read out of memory (`.read`), `freshId(addM(m))` (`.alloc`, carrying the allocated `RefTy`), `freshId(copySt(m, v))` (`.copy`) |
| a member or element of a memory object | `MAddr` | `.field`/`.at` |
| `Memory` | `MTerm` | `.memory`, `write(m, a, v)` (`.write`), `addM(m)` (`.addM`, eager: the type rides along), `copySt(m, v)` (`.copySt`) |
| what a memory `write` writes | `MValT` | a value (`.val`) or a reference (`.ref`) |
| one elementary update | `UpdElem` | `.val`/`.path`/`.mref`/`.storage`/`.memory`, plus `.transfer` for `{selfBalance := selfBalance - a ‖ net := …}`, the pair that moves together |

**An allocation is still the two parallel elements KeY writes** —
`memoryReferenceDeclFreshAlloc`'s premise is
`{ mv := freshId(addM(memory)) ‖ memory := addM(memory) }` — evaluated against
the same pre-state, so `ITerm.alloc` and `MTerm.addM` agree on which root gets
minted without either re-deriving the other's answer.

**A push is one term, not two saves in a nested update.** KeY writes
`arr.push(se)` as two saves in one parallel update, the new slot `at(n)` and
the new length `size`, both reading the pre-state; here `STerm.push s p v`
*is* `save(save(s, p[p.length], v), p.length, p.length + 1)` as a single
constructor, because a *program* can perform neither write alone (there is no
statement for "write one past the end" or "assign `a.length`"), so the
soundness proofs need to compare a rule's update against `SVal.saveExt`
(the length-extending write) rather than plain `SVal.save`. `STerm.pushSlot`
is the bare `push()`'s slot write (`storagePushLengthSave`, recycling a
popped slot or the type's default), and `STerm.pop` the dual. What that
whole-array write *carries* is solkey's `delAt`: both `storagePopSave` and
`storagePushLengthSave` clear the slot at `n` rather than dropping it, so a
mapping nested in a popped element survives into the next `push`.

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
| ~~`selectOnSaveEmpty`~~ (pre-fold) | `selectOnSaveEmpty` | done as the pre-fold rule — a member of `save(st, nil, v)` is a member of `(Struct) v` |
| `saveOnEmptyPrim` | `saveOnEmptyPrimInt`, `saveOnEmptyPrimBool` | done, as the two cast readings at the end of a walk: `storeSt`'s third argument is the supersort, so the primitive leaf is stored verbatim |
| `selectOnSaveEmptyRef`, `selectOnSaveEmptyFixed` | `selectOnSaveEmptyRef` | done, for every `Seg`: the right-hand side collapses to the pre-fold one |
| `selectOnSaveEmptyIndexStruct` | `selectOnSaveEmptyIndexStruct`, `selectOnSaveEmptyIndexClear`, `selectOnSaveEmptyIndexKeep` | done: the in-bounds branch as stated; the clear and keep branches under the length invariant (nothing stored past an array's length), the clear one at every primitive read below the element |
| `selectOnSaveEmptyDefault` (upstream it is `selectOnSaveEmpty`'s primitive case) | `selectOnSaveEmpty` | done |
| `selectOnSaveEmptyMap` | — | **arch**: upstream a mapping member of a written location stays the location's own; here the leaf collapses and a mapping member is a subtree like any other. Unreachable — solc ≥ 0.7 and solkey's own parser reject the copy, and `TypedStmt.Assign.mk` cannot build it |
| `selectOnSaveCons` | `selectOnSaveCons` | done, and **unconditional** (a total definition needs no `isStruct` guard) |
| `delFieldRef`, `delFieldIndexStruct` | `delFieldRef`, `delFieldIndexStruct` | done: `delField s a = delValue (selectSt s a)`, the reset picked by the value's sort since a `Seg` has none |
| `delFieldDefault` | `delFieldDefault`, `delFieldDefault_asBool` | done |
| `delFieldStValueCast` | `delValueCast`, `delValueCast_asInt`, `delValueCast_asBool` | done as the cast pushed through the reset (was `delValueStValueCast`) |
| `delFieldMap` | — | **arch**: a `Seg` carries no `MapField` |
| `delFieldFixed` | — | **arch**: no fixed-size array in the language model, so no `FixedField` |
| ~~`delValueStruct`~~, ~~`delValueDefault`~~ | `delValueStruct`, `delValueDefault` | gone upstream (replaced by `delField`); kept as the lemmas under it |
| `selectStDelNodeMap` | — | **arch**: a `Seg` carries no `MapField`, so a mapping member of a deleted node is reset here; the mapping-preserving `delete` is the interpreter's `SVal.defaultOf` |
| `selectStDelNodeRef` | `selectStDelNodeRef` (from `selectStDelNodeSelect`) | done, unconditional and for every `Seg`: one theorem, `selectSt (delNode s) a = delValue (selectSt s a)`, covers `Ref`, `Default`, the in-bounds index and an absent member |
| `selectStDelNodeIndexStruct` | `selectStDelNodeIndexStruct`, `selectStDelNodeIndexKeep` | done: the in-bounds branch (`delNode` of the element, now that `delNode` resets index members in place instead of dropping them) unconditionally; the keep branch under the length invariant |
| `selectStDelNodeDefault` | `selectStDelNodeDefault`, `selectStDelNodeDefault_asBool` | done |
| `selectStDelNodeFixed`, `selectStDelNodeFixed{Map,Element,Size,Value}` | — | **arch**: `delNodeFixed` is reached only through a `FixedField`, and there is none |
| `delAtEmpty` | `delAtEmpty` | done |
| `selectOnDelAtCons` | `selectOnDelAtCons` | done, through `selectOnSaveCons`: `delAt` is eager, `save st p (delValue (find st p))`; the leaf is `delField st a1` |
| `fieldShapeDef` | `fieldShapeDef` (`fieldShape`, `Shape.ofTy`) | done: `#shapeOf` is `Shape.ofTy`, over a member table the caller supplies (a `Seg.field` carries the name, not the declaration) |
| `selectOnTyped{Struct,FixedSize,DynSize,LeafSize,MapSize,Element,Member}`, `typedTyped` | — | **not modelled**: the only rule that reads the tag is `selectOnTypedFixedSize`; no declared shape is a `fixedArr` (`Shape.ofTy_ne_fixedArr`), and `typed` would be a fifth `Struct` constructor through every proof (`Theory/Storage.lean`, "Shapes") |
| ~~`copyAtEmpty`~~, ~~`selectOnCopyAtCons`~~, ~~`mergePrim`~~, ~~`selectStMerge{Map,Ref,IndexStruct,Default}`~~, ~~`mergeStValueCast`~~ | — | gone upstream with the fold; not modelled here for the reason `selectOnSaveEmptyMap` is not |
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
and `find_delAt_below` (a read below a deleted path is the reset of the read
before it, through any path).

**`storeAt` and the two sorts.** `save` is a recursion on the path over
`storeAt`, the one-segment walk. It returns `Struct`, as KeY's does, and
stores the written value verbatim at the last segment: `storeSt`'s third
argument is the supersort `StValue`, so a primitive leaf is kept as itself
and `find` reads it back at the caller's sort — which is what
`saveOnEmptyPrim` does in KeY. `delAt`/`delNode` are eager over the same
walk. There is no denotation of storage *writes* (only reads are related to
the interpreter): the `*CopySource`/`…StoreRoot` program rows are untouched
because the copy they state is mapping-free by construction
(`TypedStmt.Assign.mk`, `stmtTypingOk`).

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

### The names for these rules

`Theory/Rewrite.lean` is the enumeration of the theory's rules under the
printed names, with `lemmaNames`
mapping each `TheoryRule` constructor to the theorem(s) above. The theorems
keep their upstream (KeY) names — that is what makes this file, and
`Theory/Rewrite.lean`'s own docstring says so explicitly, a map — and the
join is stated against the printed
`\namedRwRule` declarations rather than left as prose. The printed rules with no
constructor — the `MapField`, `FixedField` and `typed` rows marked **arch** or
**not modelled** above, and the four arithmetic expansions listed
as not implemented — are excused in `Theory/Rewrite.lean` by name, each with its reason.

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

* The reset a `delete` picks is keyed on the *value's* sort, not the field's
  (`delField`, `delNode`): a `Seg` carries no `MapField`/`FixedField`, so the
  mapping-preserving and length-preserving rules have no statement.
* `fieldShape` takes the member table as an argument: KeY's member constants
  know their declaration, a `Seg.field` only its name.
* `shapeAt` follows `shapeAtSuffix` rather than solkey's
  `shapeAtLeafElement`, which drops the rest of the path under an indexed
  `leaf`; the two agree on every well-typed path.
