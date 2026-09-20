/-!
# The KeY taclets, as a Lean type

`solidityProgramRules.key` is the calculus solkey actually runs: 310 named
taclets.  This module is that list of names, one constructor each, plus the
`\heuristics` annotation each one carries.  It exists so that a rule in
`Rules.lean` can say *which* KeY taclet it transcribes with a typed
`KeyOrigin` rather than a string — a misspelling is then a type error, and
"which taclets does Lean claim?" is a `decide` rather than a grep.

## Regenerating

The enumeration is mechanical: every taclet header in the vendored file is a
line `    <name> {`, and its `\heuristics(...)` is the only one in its block.
To re-pin to a newer solkey revision, regenerate with

```bash
F=../solkey/keyext.solidity.core/src/main/resources/\
org/key_project/solidity/proof/rules/solidityProgramRules.key
awk '/^    [A-Za-z0-9_]+ \{$/ { if (nm != "") print nm "\t" h; nm=$1; h=""; next }
     /\\heuristics\(/ { if (nm != "" && h == "") {
       match($0, /\\heuristics\([^)]*\)/)
       h = substr($0, RSTART+12, RLENGTH-13) } }
     END { if (nm != "") print nm "\t" h }' "$F"
```

and rebuild the three tables below in that order.  The `SolKey` reader's
`SolKey.Corpus.keyTaclets_eq_corpus` checks the result *is* the
`.key` file it vendors, in order, so a stale table fails that build rather
than going unnoticed.

`name` is deliberately a `match` and not a lookup in `all`: the corpus check is
a `native_decide` over 252 strings, and a lookup would make it quadratic.

## `\heuristics` is documentary

Three values occur in the corpus — `simplify_prog` (220 taclets),
`simplify_expression` (85) and `concrete_solidity` (5, the literal-condition
`if` rules).  They are KeY's *strategy* annotations: which
automatic rule set may apply the taclet, not what it means.  Lean's rule table
has no automatic strategy (a derivation pins each step by name, and
`Uniqueness.lean` shows at most one rule applies anyway), so nothing here
consumes them.  They are recorded because a `StepEffect` that claims to be a
taclet should carry everything the taclet header says, and because the split is
real information about the calculus: the expression rules are the ones KeY
re-runs eagerly.
-/

namespace Solidity

/-- A KeY `\heuristics(...)` rule set.  The corpus uses exactly these three. -/
inductive Heuristic where
  /-- `simplify_prog`: the program-rewriting rule set (220 taclets). -/
  | simplifyProg
  /-- `simplify_expression`: the eager expression rule set (85 taclets). -/
  | simplifyExpression
  /-- `concrete_solidity`: the five `if` rules on a literal or negated
  condition (`ifTrue`, `ifFalse`, `ifElseTrue`, `ifElseFalse`,
  `ifElseNegated`), which KeY applies as concrete simplifications. -/
  | concreteSolidity
  deriving DecidableEq, Repr

/-- One taclet of `solidityProgramRules.key`, named as the file names it. -/
inductive KeyTaclet where
  | functionBodyExpand
  | emptyModality
  | blockEmpty
  | revertDiamond
  | revertBox
  | storageRootWriteStore
  | storageRootWriteCopySource
  | storageRootReadSelect
  | storageFieldWriteSave
  | storageFieldWriteCopySource
  | storageFieldWriteCaptureSrc
  | storageFieldRead_unfold_rightFst
  | storageIndexRead_unfold_rightFst
  | storageFieldReadFind
  | storageFieldWrite_unfold_leftFst
  | storageFieldWriteStorageRef_unfold_leftFst
  | memoryToStorageField_unfold_leftFst
  | storageIndexWriteMappingSave
  | storageIndexReadMappingFind
  | storageIndexReadMappingBindLocalRoot
  | storageIndexReadMappingStoreRoot
  | storageIndexWriteMappingCopySource
  | storageIndexWriteStorageRefRhsCapture
  | storageIndexWriteArraySave
  | storageIndexReadArrayFind
  | storageIndexReadArrayBindLocalRoot
  | storageIndexReadArrayStoreRoot
  | storageIndexWriteArrayCopySource
  | storagePushValue_unfold_leftFstReceiver
  | storagePush_unfold_leftFstReceiver
  | storagePop_unfold_leftFstReceiver
  | storageLocalRootPush_unfold_leftFstReceiver
  | storagePushValue_unfold_rightSndArgument
  | storagePushValueSave
  | storagePushValueCopySource
  | storagePushLengthSave
  | storageLocalRootPushBind
  | storagePopSave
  | storageLocalRootRebind
  | storageLocalDeclSkip
  | storageLocalDeclInitDrop
  | memoryReferenceDeclFreshAlloc
  | memoryLocalDeclInitDrop
  | memoryRootDeleteFreshRebind
  | memoryRootRebind
  | memoryArrayFreshAlloc
  | memoryStorageCopy
  | memoryStorageCopyUnfold
  | memoryFieldWrite
  | memoryFieldRead
  | memoryFieldRead_unfold_rightFst
  | memoryFieldWriteCaptureSrc
  | memoryFieldWrite_unfold_leftFst
  | memoryFieldWriteMemRef_unfold_leftFst
  | memoryIndexWriteArray
  | memoryIndexReadArrayValue
  | memoryIndexReadArrayMemory
  | memoryIndexRead_unfold_rightFst
  | memoryFieldDeletePrimitive
  | memoryFieldDeleteReference
  | memoryIndexDeletePrimitive
  | memoryIndexDeleteReference
  | memoryFieldDelete_unfold_leftFst
  | memoryIndexDelete_unfold_leftFst
  | memoryToStorageStoreRoot
  | memoryToStorageFieldCopyRoot
  | memoryToStorageFieldCopyField
  | memoryToStorageIndexMappingCopyRoot
  | memoryToStorageIndexArrayCopyRoot
  | localValueDeclInitDrop
  | valueDeclSkip
  | storageFieldReadBindLocalRoot
  | storageFieldReadStoreRoot
  | storageRootAddAssign
  | storageFieldAddAssign_unfold_leftFst
  | storageIndexAddAssign_unfold_leftFst
  | storageFieldAddAssign
  | storageIndexMappingAddAssign
  | storageIndexArrayAddAssign
  | storageRootSubAssign
  | storageFieldSubAssign_unfold_leftFst
  | storageIndexSubAssign_unfold_leftFst
  | storageFieldSubAssign
  | storageIndexMappingSubAssign
  | storageIndexArraySubAssign
  | storageRootMulAssign
  | storageFieldMulAssign_unfold_leftFst
  | storageIndexMulAssign_unfold_leftFst
  | storageFieldMulAssign
  | storageIndexMappingMulAssign
  | storageIndexArrayMulAssign
  | storageRootDivAssign
  | storageFieldDivAssign_unfold_leftFst
  | storageIndexDivAssign_unfold_leftFst
  | storageFieldDivAssign
  | storageIndexMappingDivAssign
  | storageIndexArrayDivAssign
  | storageRootModAssign
  | storageFieldModAssign_unfold_leftFst
  | storageIndexModAssign_unfold_leftFst
  | storageFieldModAssign
  | storageIndexMappingModAssign
  | storageIndexArrayModAssign
  | storageRootDelete
  | storageFieldDelete
  | storageIndexDelete
  | storageFieldDelete_unfold_leftFst
  | storageIndexDelete_unfold_leftFst
  | storageRootPreincrement
  | storageRootPredecrement
  | storageRootPostincrement
  | storageRootPostdecrement
  | storageRootPreincrementAssignment
  | storageRootPredecrementAssignment
  | storageRootPostincrementAssignment
  | storageRootPostdecrementAssignment
  | addition_unfold_left
  | addition_unfold_right
  | localValueAssign
  | additionAssignment
  | subtraction_unfold_left
  | subtraction_unfold_right
  | subtractionAssignment
  | multiplication_unfold_left
  | multiplication_unfold_right
  | multiplicationAssignment
  | power_unfold_left
  | power_unfold_right
  | powerAssignment
  | division_unfold_left
  | division_unfold_right
  | divisionAssignment
  | modulo_unfold_left
  | modulo_unfold_right
  | moduloAssignment
  | storageFieldPreincrement
  | storageFieldPostincrementAssignment
  | storageFieldPostincrement
  | storageFieldPredecrement
  | storageFieldPostdecrement
  | storageFieldPreincrementAssignment
  | storageFieldPredecrementAssignment
  | storageFieldPostdecrementAssignment
  | storageIndexMappingPreincrement
  | storageIndexArrayPreincrement
  | storageIndexMappingPostincrement
  | storageIndexArrayPostincrement
  | storageIndexMappingPredecrement
  | storageIndexArrayPredecrement
  | storageIndexMappingPostdecrement
  | storageIndexArrayPostdecrement
  | storageIndexMappingPreincrementAssignment
  | storageIndexArrayPreincrementAssignment
  | storageIndexMappingPostincrementAssignment
  | storageIndexArrayPostincrementAssignment
  | storageIndexMappingPredecrementAssignment
  | storageIndexArrayPredecrementAssignment
  | storageIndexMappingPostdecrementAssignment
  | storageIndexArrayPostdecrementAssignment
  | storageFieldPreincrement_unfold_leftFst
  | storageFieldPostincrement_unfold_leftFst
  | storageFieldPredecrement_unfold_leftFst
  | storageFieldPostdecrement_unfold_leftFst
  | storageIndexPreincrement_unfold_leftFst
  | storageIndexPostincrement_unfold_leftFst
  | storageIndexPredecrement_unfold_leftFst
  | storageIndexPostdecrement_unfold_leftFst
  | memoryFieldAddAssign
  | memoryFieldSubAssign
  | memoryFieldMulAssign
  | memoryFieldDivAssign
  | memoryFieldModAssign
  | memoryIndexArrayAddAssign
  | memoryIndexArraySubAssign
  | memoryIndexArrayMulAssign
  | memoryIndexArrayDivAssign
  | memoryIndexArrayModAssign
  | memoryFieldAddAssign_unfold_leftFst
  | memoryFieldSubAssign_unfold_leftFst
  | memoryFieldMulAssign_unfold_leftFst
  | memoryFieldDivAssign_unfold_leftFst
  | memoryFieldModAssign_unfold_leftFst
  | memoryIndexAddAssign_unfold_leftFst
  | memoryIndexSubAssign_unfold_leftFst
  | memoryIndexMulAssign_unfold_leftFst
  | memoryIndexDivAssign_unfold_leftFst
  | memoryIndexModAssign_unfold_leftFst
  | memoryFieldPreincrement
  | memoryFieldPostincrement
  | memoryFieldPredecrement
  | memoryFieldPostdecrement
  | memoryFieldPreincrementAssignment
  | memoryFieldPostincrementAssignment
  | memoryFieldPredecrementAssignment
  | memoryFieldPostdecrementAssignment
  | memoryIndexArrayPreincrement
  | memoryIndexArrayPostincrement
  | memoryIndexArrayPredecrement
  | memoryIndexArrayPostdecrement
  | memoryIndexArrayPreincrementAssignment
  | memoryIndexArrayPostincrementAssignment
  | memoryIndexArrayPredecrementAssignment
  | memoryIndexArrayPostdecrementAssignment
  | memoryFieldPreincrement_unfold_leftFst
  | memoryFieldPostincrement_unfold_leftFst
  | memoryFieldPredecrement_unfold_leftFst
  | memoryFieldPostdecrement_unfold_leftFst
  | memoryIndexPreincrement_unfold_leftFst
  | memoryIndexPostincrement_unfold_leftFst
  | memoryIndexPredecrement_unfold_leftFst
  | memoryIndexPostdecrement_unfold_leftFst
  | localDeclPreincrement
  | localAssignPreincrement
  | localDeclPredecrement
  | localAssignPredecrement
  | localDeclPostincrement
  | localAssignPostincrement
  | localDeclPostdecrement
  | localAssignPostdecrement
  | localPreincrement
  | localPostincrement
  | localPredecrement
  | localPostdecrement
  | localAddAssign
  | localSubAssign
  | localMulAssign
  | localDivAssign
  | localModAssign
  | addAssignValueRhsCapture
  | subAssignValueRhsCapture
  | mulAssignValueRhsCapture
  | divAssignValueRhsCapture
  | modAssignValueRhsCapture
  | storageRootWriteValueRhsCapture
  | fieldWriteValueRhsCapture
  | indexWriteValueRhsCapture
  | memoryIndexWriteMemRefRhsCapture
  | storageIndexRead_unfold_rightSndIndex
  | memoryIndexRead_unfold_rightSndIndex
  | storageIndexDeleteNonSimpleIndexCapture
  | memoryIndexDeleteNonSimpleIndexCapture
  | storageFieldRead_unfold_rightSndResult
  | storageIndexRead_unfold_rightSndResult
  | memoryFieldRead_unfold_rightSndResult
  | memoryIndexRead_unfold_rightSndResult
  | assertConditionCapture
  | boolEqualityCaptureLhs
  | boolEqualityCaptureRhs
  | boolEqualityAssignment
  | boolInequalityCaptureLhs
  | boolInequalityCaptureRhs
  | boolInequalityAssignment
  | lessThanCaptureLhs
  | lessThanCaptureRhs
  | lessThanAssignment
  | greaterThanCaptureLhs
  | greaterThanCaptureRhs
  | greaterThanAssignment
  | lessEqualCaptureLhs
  | lessEqualCaptureRhs
  | lessEqualAssignment
  | greaterEqualCaptureLhs
  | greaterEqualCaptureRhs
  | greaterEqualAssignment
  | logicalAndCaptureLhs
  | logicalAndAssignment
  | logicalAndShortCircuitRhs
  | logicalOrCaptureLhs
  | logicalOrAssignment
  | logicalOrShortCircuitRhs
  | logicalNotCapture
  | logicalNotAssignment
  | ternaryCaptureCond
  | ternaryToIf
  | ternaryToIfStorage
  | ifUnfold
  | ifElseUnfold
  | ifTrue
  | ifFalse
  | ifElseTrue
  | ifElseFalse
  | ifElseNegated
  | ifSplit
  | ifElseSplit
  | unaryMinusCapture
  | unaryMinusAssignment
  | assertSimple
  | requireConditionCapture
  | requireSimple
  | transfer_unfold_leftFstReceiver
  | transfer_unfold_rightSndArgument
  | transferNoCallbackBox
  | transferNoCallbackDiamond
  | transferWithCallbackBox
  | transferWithCallbackDiamond
  | storageIndexWrite_unfold_leftFst
  | storageIndexWriteStorageRef_unfold_leftFst
  | memoryToStorageIndex_unfold_leftFst
  | memoryIndexWrite_unfold_leftFst
  | memoryIndexWriteMemRef_unfold_leftFst
  | storageIndexWriteNonSimpleIndexCapture
  | storageIndexWriteStorageRefNonSimpleIndexCapture
  | memoryToStorageIndexNonSimpleIndexCapture
  | memoryIndexWriteNonSimpleIndexCapture
  | memoryIndexWriteMemRefNonSimpleIndexCapture
  | storageIndexWriteCaptureAll
  | storageIndexWriteStorageRefCaptureAll
  | memoryToStorageIndexCaptureAll
  | memoryIndexWriteCaptureAll
  | memoryIndexWriteMemRefCaptureAll
  deriving DecidableEq, Repr

namespace KeyTaclet

/-- The taclet's name, exactly as `solidityProgramRules.key` spells it. -/
def name : KeyTaclet -> String
  | functionBodyExpand => "functionBodyExpand"
  | emptyModality => "emptyModality"
  | blockEmpty => "blockEmpty"
  | revertDiamond => "revertDiamond"
  | revertBox => "revertBox"
  | storageRootWriteStore => "storageRootWriteStore"
  | storageRootWriteCopySource => "storageRootWriteCopySource"
  | storageRootReadSelect => "storageRootReadSelect"
  | storageFieldWriteSave => "storageFieldWriteSave"
  | storageFieldWriteCopySource => "storageFieldWriteCopySource"
  | storageFieldWriteCaptureSrc => "storageFieldWriteCaptureSrc"
  | storageFieldRead_unfold_rightFst => "storageFieldRead_unfold_rightFst"
  | storageIndexRead_unfold_rightFst => "storageIndexRead_unfold_rightFst"
  | storageFieldReadFind => "storageFieldReadFind"
  | storageFieldWrite_unfold_leftFst => "storageFieldWrite_unfold_leftFst"
  | storageFieldWriteStorageRef_unfold_leftFst => "storageFieldWriteStorageRef_unfold_leftFst"
  | memoryToStorageField_unfold_leftFst => "memoryToStorageField_unfold_leftFst"
  | storageIndexWriteMappingSave => "storageIndexWriteMappingSave"
  | storageIndexReadMappingFind => "storageIndexReadMappingFind"
  | storageIndexReadMappingBindLocalRoot => "storageIndexReadMappingBindLocalRoot"
  | storageIndexReadMappingStoreRoot => "storageIndexReadMappingStoreRoot"
  | storageIndexWriteMappingCopySource => "storageIndexWriteMappingCopySource"
  | storageIndexWriteStorageRefRhsCapture => "storageIndexWriteStorageRefRhsCapture"
  | storageIndexWriteArraySave => "storageIndexWriteArraySave"
  | storageIndexReadArrayFind => "storageIndexReadArrayFind"
  | storageIndexReadArrayBindLocalRoot => "storageIndexReadArrayBindLocalRoot"
  | storageIndexReadArrayStoreRoot => "storageIndexReadArrayStoreRoot"
  | storageIndexWriteArrayCopySource => "storageIndexWriteArrayCopySource"
  | storagePushValue_unfold_leftFstReceiver => "storagePushValue_unfold_leftFstReceiver"
  | storagePush_unfold_leftFstReceiver => "storagePush_unfold_leftFstReceiver"
  | storagePop_unfold_leftFstReceiver => "storagePop_unfold_leftFstReceiver"
  | storageLocalRootPush_unfold_leftFstReceiver => "storageLocalRootPush_unfold_leftFstReceiver"
  | storagePushValue_unfold_rightSndArgument => "storagePushValue_unfold_rightSndArgument"
  | storagePushValueSave => "storagePushValueSave"
  | storagePushValueCopySource => "storagePushValueCopySource"
  | storagePushLengthSave => "storagePushLengthSave"
  | storageLocalRootPushBind => "storageLocalRootPushBind"
  | storagePopSave => "storagePopSave"
  | storageLocalRootRebind => "storageLocalRootRebind"
  | storageLocalDeclSkip => "storageLocalDeclSkip"
  | storageLocalDeclInitDrop => "storageLocalDeclInitDrop"
  | memoryReferenceDeclFreshAlloc => "memoryReferenceDeclFreshAlloc"
  | memoryLocalDeclInitDrop => "memoryLocalDeclInitDrop"
  | memoryRootDeleteFreshRebind => "memoryRootDeleteFreshRebind"
  | memoryRootRebind => "memoryRootRebind"
  | memoryArrayFreshAlloc => "memoryArrayFreshAlloc"
  | memoryStorageCopy => "memoryStorageCopy"
  | memoryStorageCopyUnfold => "memoryStorageCopyUnfold"
  | memoryFieldWrite => "memoryFieldWrite"
  | memoryFieldRead => "memoryFieldRead"
  | memoryFieldRead_unfold_rightFst => "memoryFieldRead_unfold_rightFst"
  | memoryFieldWriteCaptureSrc => "memoryFieldWriteCaptureSrc"
  | memoryFieldWrite_unfold_leftFst => "memoryFieldWrite_unfold_leftFst"
  | memoryFieldWriteMemRef_unfold_leftFst => "memoryFieldWriteMemRef_unfold_leftFst"
  | memoryIndexWriteArray => "memoryIndexWriteArray"
  | memoryIndexReadArrayValue => "memoryIndexReadArrayValue"
  | memoryIndexReadArrayMemory => "memoryIndexReadArrayMemory"
  | memoryIndexRead_unfold_rightFst => "memoryIndexRead_unfold_rightFst"
  | memoryFieldDeletePrimitive => "memoryFieldDeletePrimitive"
  | memoryFieldDeleteReference => "memoryFieldDeleteReference"
  | memoryIndexDeletePrimitive => "memoryIndexDeletePrimitive"
  | memoryIndexDeleteReference => "memoryIndexDeleteReference"
  | memoryFieldDelete_unfold_leftFst => "memoryFieldDelete_unfold_leftFst"
  | memoryIndexDelete_unfold_leftFst => "memoryIndexDelete_unfold_leftFst"
  | memoryToStorageStoreRoot => "memoryToStorageStoreRoot"
  | memoryToStorageFieldCopyRoot => "memoryToStorageFieldCopyRoot"
  | memoryToStorageFieldCopyField => "memoryToStorageFieldCopyField"
  | memoryToStorageIndexMappingCopyRoot => "memoryToStorageIndexMappingCopyRoot"
  | memoryToStorageIndexArrayCopyRoot => "memoryToStorageIndexArrayCopyRoot"
  | localValueDeclInitDrop => "localValueDeclInitDrop"
  | valueDeclSkip => "valueDeclSkip"
  | storageFieldReadBindLocalRoot => "storageFieldReadBindLocalRoot"
  | storageFieldReadStoreRoot => "storageFieldReadStoreRoot"
  | storageRootAddAssign => "storageRootAddAssign"
  | storageFieldAddAssign_unfold_leftFst => "storageFieldAddAssign_unfold_leftFst"
  | storageIndexAddAssign_unfold_leftFst => "storageIndexAddAssign_unfold_leftFst"
  | storageFieldAddAssign => "storageFieldAddAssign"
  | storageIndexMappingAddAssign => "storageIndexMappingAddAssign"
  | storageIndexArrayAddAssign => "storageIndexArrayAddAssign"
  | storageRootSubAssign => "storageRootSubAssign"
  | storageFieldSubAssign_unfold_leftFst => "storageFieldSubAssign_unfold_leftFst"
  | storageIndexSubAssign_unfold_leftFst => "storageIndexSubAssign_unfold_leftFst"
  | storageFieldSubAssign => "storageFieldSubAssign"
  | storageIndexMappingSubAssign => "storageIndexMappingSubAssign"
  | storageIndexArraySubAssign => "storageIndexArraySubAssign"
  | storageRootMulAssign => "storageRootMulAssign"
  | storageFieldMulAssign_unfold_leftFst => "storageFieldMulAssign_unfold_leftFst"
  | storageIndexMulAssign_unfold_leftFst => "storageIndexMulAssign_unfold_leftFst"
  | storageFieldMulAssign => "storageFieldMulAssign"
  | storageIndexMappingMulAssign => "storageIndexMappingMulAssign"
  | storageIndexArrayMulAssign => "storageIndexArrayMulAssign"
  | storageRootDivAssign => "storageRootDivAssign"
  | storageFieldDivAssign_unfold_leftFst => "storageFieldDivAssign_unfold_leftFst"
  | storageIndexDivAssign_unfold_leftFst => "storageIndexDivAssign_unfold_leftFst"
  | storageFieldDivAssign => "storageFieldDivAssign"
  | storageIndexMappingDivAssign => "storageIndexMappingDivAssign"
  | storageIndexArrayDivAssign => "storageIndexArrayDivAssign"
  | storageRootModAssign => "storageRootModAssign"
  | storageFieldModAssign_unfold_leftFst => "storageFieldModAssign_unfold_leftFst"
  | storageIndexModAssign_unfold_leftFst => "storageIndexModAssign_unfold_leftFst"
  | storageFieldModAssign => "storageFieldModAssign"
  | storageIndexMappingModAssign => "storageIndexMappingModAssign"
  | storageIndexArrayModAssign => "storageIndexArrayModAssign"
  | storageRootDelete => "storageRootDelete"
  | storageFieldDelete => "storageFieldDelete"
  | storageIndexDelete => "storageIndexDelete"
  | storageFieldDelete_unfold_leftFst => "storageFieldDelete_unfold_leftFst"
  | storageIndexDelete_unfold_leftFst => "storageIndexDelete_unfold_leftFst"
  | storageRootPreincrement => "storageRootPreincrement"
  | storageRootPredecrement => "storageRootPredecrement"
  | storageRootPostincrement => "storageRootPostincrement"
  | storageRootPostdecrement => "storageRootPostdecrement"
  | storageRootPreincrementAssignment => "storageRootPreincrementAssignment"
  | storageRootPredecrementAssignment => "storageRootPredecrementAssignment"
  | storageRootPostincrementAssignment => "storageRootPostincrementAssignment"
  | storageRootPostdecrementAssignment => "storageRootPostdecrementAssignment"
  | addition_unfold_left => "addition_unfold_left"
  | addition_unfold_right => "addition_unfold_right"
  | localValueAssign => "localValueAssign"
  | additionAssignment => "additionAssignment"
  | subtraction_unfold_left => "subtraction_unfold_left"
  | subtraction_unfold_right => "subtraction_unfold_right"
  | subtractionAssignment => "subtractionAssignment"
  | multiplication_unfold_left => "multiplication_unfold_left"
  | multiplication_unfold_right => "multiplication_unfold_right"
  | multiplicationAssignment => "multiplicationAssignment"
  | power_unfold_left => "power_unfold_left"
  | power_unfold_right => "power_unfold_right"
  | powerAssignment => "powerAssignment"
  | division_unfold_left => "division_unfold_left"
  | division_unfold_right => "division_unfold_right"
  | divisionAssignment => "divisionAssignment"
  | modulo_unfold_left => "modulo_unfold_left"
  | modulo_unfold_right => "modulo_unfold_right"
  | moduloAssignment => "moduloAssignment"
  | storageFieldPreincrement => "storageFieldPreincrement"
  | storageFieldPostincrementAssignment => "storageFieldPostincrementAssignment"
  | storageFieldPostincrement => "storageFieldPostincrement"
  | storageFieldPredecrement => "storageFieldPredecrement"
  | storageFieldPostdecrement => "storageFieldPostdecrement"
  | storageFieldPreincrementAssignment => "storageFieldPreincrementAssignment"
  | storageFieldPredecrementAssignment => "storageFieldPredecrementAssignment"
  | storageFieldPostdecrementAssignment => "storageFieldPostdecrementAssignment"
  | storageIndexMappingPreincrement => "storageIndexMappingPreincrement"
  | storageIndexArrayPreincrement => "storageIndexArrayPreincrement"
  | storageIndexMappingPostincrement => "storageIndexMappingPostincrement"
  | storageIndexArrayPostincrement => "storageIndexArrayPostincrement"
  | storageIndexMappingPredecrement => "storageIndexMappingPredecrement"
  | storageIndexArrayPredecrement => "storageIndexArrayPredecrement"
  | storageIndexMappingPostdecrement => "storageIndexMappingPostdecrement"
  | storageIndexArrayPostdecrement => "storageIndexArrayPostdecrement"
  | storageIndexMappingPreincrementAssignment => "storageIndexMappingPreincrementAssignment"
  | storageIndexArrayPreincrementAssignment => "storageIndexArrayPreincrementAssignment"
  | storageIndexMappingPostincrementAssignment => "storageIndexMappingPostincrementAssignment"
  | storageIndexArrayPostincrementAssignment => "storageIndexArrayPostincrementAssignment"
  | storageIndexMappingPredecrementAssignment => "storageIndexMappingPredecrementAssignment"
  | storageIndexArrayPredecrementAssignment => "storageIndexArrayPredecrementAssignment"
  | storageIndexMappingPostdecrementAssignment => "storageIndexMappingPostdecrementAssignment"
  | storageIndexArrayPostdecrementAssignment => "storageIndexArrayPostdecrementAssignment"
  | storageFieldPreincrement_unfold_leftFst => "storageFieldPreincrement_unfold_leftFst"
  | storageFieldPostincrement_unfold_leftFst => "storageFieldPostincrement_unfold_leftFst"
  | storageFieldPredecrement_unfold_leftFst => "storageFieldPredecrement_unfold_leftFst"
  | storageFieldPostdecrement_unfold_leftFst => "storageFieldPostdecrement_unfold_leftFst"
  | storageIndexPreincrement_unfold_leftFst => "storageIndexPreincrement_unfold_leftFst"
  | storageIndexPostincrement_unfold_leftFst => "storageIndexPostincrement_unfold_leftFst"
  | storageIndexPredecrement_unfold_leftFst => "storageIndexPredecrement_unfold_leftFst"
  | storageIndexPostdecrement_unfold_leftFst => "storageIndexPostdecrement_unfold_leftFst"
  | memoryFieldAddAssign => "memoryFieldAddAssign"
  | memoryFieldSubAssign => "memoryFieldSubAssign"
  | memoryFieldMulAssign => "memoryFieldMulAssign"
  | memoryFieldDivAssign => "memoryFieldDivAssign"
  | memoryFieldModAssign => "memoryFieldModAssign"
  | memoryIndexArrayAddAssign => "memoryIndexArrayAddAssign"
  | memoryIndexArraySubAssign => "memoryIndexArraySubAssign"
  | memoryIndexArrayMulAssign => "memoryIndexArrayMulAssign"
  | memoryIndexArrayDivAssign => "memoryIndexArrayDivAssign"
  | memoryIndexArrayModAssign => "memoryIndexArrayModAssign"
  | memoryFieldAddAssign_unfold_leftFst => "memoryFieldAddAssign_unfold_leftFst"
  | memoryFieldSubAssign_unfold_leftFst => "memoryFieldSubAssign_unfold_leftFst"
  | memoryFieldMulAssign_unfold_leftFst => "memoryFieldMulAssign_unfold_leftFst"
  | memoryFieldDivAssign_unfold_leftFst => "memoryFieldDivAssign_unfold_leftFst"
  | memoryFieldModAssign_unfold_leftFst => "memoryFieldModAssign_unfold_leftFst"
  | memoryIndexAddAssign_unfold_leftFst => "memoryIndexAddAssign_unfold_leftFst"
  | memoryIndexSubAssign_unfold_leftFst => "memoryIndexSubAssign_unfold_leftFst"
  | memoryIndexMulAssign_unfold_leftFst => "memoryIndexMulAssign_unfold_leftFst"
  | memoryIndexDivAssign_unfold_leftFst => "memoryIndexDivAssign_unfold_leftFst"
  | memoryIndexModAssign_unfold_leftFst => "memoryIndexModAssign_unfold_leftFst"
  | memoryFieldPreincrement => "memoryFieldPreincrement"
  | memoryFieldPostincrement => "memoryFieldPostincrement"
  | memoryFieldPredecrement => "memoryFieldPredecrement"
  | memoryFieldPostdecrement => "memoryFieldPostdecrement"
  | memoryFieldPreincrementAssignment => "memoryFieldPreincrementAssignment"
  | memoryFieldPostincrementAssignment => "memoryFieldPostincrementAssignment"
  | memoryFieldPredecrementAssignment => "memoryFieldPredecrementAssignment"
  | memoryFieldPostdecrementAssignment => "memoryFieldPostdecrementAssignment"
  | memoryIndexArrayPreincrement => "memoryIndexArrayPreincrement"
  | memoryIndexArrayPostincrement => "memoryIndexArrayPostincrement"
  | memoryIndexArrayPredecrement => "memoryIndexArrayPredecrement"
  | memoryIndexArrayPostdecrement => "memoryIndexArrayPostdecrement"
  | memoryIndexArrayPreincrementAssignment => "memoryIndexArrayPreincrementAssignment"
  | memoryIndexArrayPostincrementAssignment => "memoryIndexArrayPostincrementAssignment"
  | memoryIndexArrayPredecrementAssignment => "memoryIndexArrayPredecrementAssignment"
  | memoryIndexArrayPostdecrementAssignment => "memoryIndexArrayPostdecrementAssignment"
  | memoryFieldPreincrement_unfold_leftFst => "memoryFieldPreincrement_unfold_leftFst"
  | memoryFieldPostincrement_unfold_leftFst => "memoryFieldPostincrement_unfold_leftFst"
  | memoryFieldPredecrement_unfold_leftFst => "memoryFieldPredecrement_unfold_leftFst"
  | memoryFieldPostdecrement_unfold_leftFst => "memoryFieldPostdecrement_unfold_leftFst"
  | memoryIndexPreincrement_unfold_leftFst => "memoryIndexPreincrement_unfold_leftFst"
  | memoryIndexPostincrement_unfold_leftFst => "memoryIndexPostincrement_unfold_leftFst"
  | memoryIndexPredecrement_unfold_leftFst => "memoryIndexPredecrement_unfold_leftFst"
  | memoryIndexPostdecrement_unfold_leftFst => "memoryIndexPostdecrement_unfold_leftFst"
  | localDeclPreincrement => "localDeclPreincrement"
  | localAssignPreincrement => "localAssignPreincrement"
  | localDeclPredecrement => "localDeclPredecrement"
  | localAssignPredecrement => "localAssignPredecrement"
  | localDeclPostincrement => "localDeclPostincrement"
  | localAssignPostincrement => "localAssignPostincrement"
  | localDeclPostdecrement => "localDeclPostdecrement"
  | localAssignPostdecrement => "localAssignPostdecrement"
  | localPreincrement => "localPreincrement"
  | localPostincrement => "localPostincrement"
  | localPredecrement => "localPredecrement"
  | localPostdecrement => "localPostdecrement"
  | localAddAssign => "localAddAssign"
  | localSubAssign => "localSubAssign"
  | localMulAssign => "localMulAssign"
  | localDivAssign => "localDivAssign"
  | localModAssign => "localModAssign"
  | addAssignValueRhsCapture => "addAssignValueRhsCapture"
  | subAssignValueRhsCapture => "subAssignValueRhsCapture"
  | mulAssignValueRhsCapture => "mulAssignValueRhsCapture"
  | divAssignValueRhsCapture => "divAssignValueRhsCapture"
  | modAssignValueRhsCapture => "modAssignValueRhsCapture"
  | storageRootWriteValueRhsCapture => "storageRootWriteValueRhsCapture"
  | fieldWriteValueRhsCapture => "fieldWriteValueRhsCapture"
  | indexWriteValueRhsCapture => "indexWriteValueRhsCapture"
  | memoryIndexWriteMemRefRhsCapture => "memoryIndexWriteMemRefRhsCapture"
  | storageIndexRead_unfold_rightSndIndex => "storageIndexRead_unfold_rightSndIndex"
  | memoryIndexRead_unfold_rightSndIndex => "memoryIndexRead_unfold_rightSndIndex"
  | storageIndexDeleteNonSimpleIndexCapture => "storageIndexDeleteNonSimpleIndexCapture"
  | memoryIndexDeleteNonSimpleIndexCapture => "memoryIndexDeleteNonSimpleIndexCapture"
  | storageFieldRead_unfold_rightSndResult => "storageFieldRead_unfold_rightSndResult"
  | storageIndexRead_unfold_rightSndResult => "storageIndexRead_unfold_rightSndResult"
  | memoryFieldRead_unfold_rightSndResult => "memoryFieldRead_unfold_rightSndResult"
  | memoryIndexRead_unfold_rightSndResult => "memoryIndexRead_unfold_rightSndResult"
  | assertConditionCapture => "assertConditionCapture"
  | boolEqualityCaptureLhs => "boolEqualityCaptureLhs"
  | boolEqualityCaptureRhs => "boolEqualityCaptureRhs"
  | boolEqualityAssignment => "boolEqualityAssignment"
  | boolInequalityCaptureLhs => "boolInequalityCaptureLhs"
  | boolInequalityCaptureRhs => "boolInequalityCaptureRhs"
  | boolInequalityAssignment => "boolInequalityAssignment"
  | lessThanCaptureLhs => "lessThanCaptureLhs"
  | lessThanCaptureRhs => "lessThanCaptureRhs"
  | lessThanAssignment => "lessThanAssignment"
  | greaterThanCaptureLhs => "greaterThanCaptureLhs"
  | greaterThanCaptureRhs => "greaterThanCaptureRhs"
  | greaterThanAssignment => "greaterThanAssignment"
  | lessEqualCaptureLhs => "lessEqualCaptureLhs"
  | lessEqualCaptureRhs => "lessEqualCaptureRhs"
  | lessEqualAssignment => "lessEqualAssignment"
  | greaterEqualCaptureLhs => "greaterEqualCaptureLhs"
  | greaterEqualCaptureRhs => "greaterEqualCaptureRhs"
  | greaterEqualAssignment => "greaterEqualAssignment"
  | logicalAndCaptureLhs => "logicalAndCaptureLhs"
  | logicalAndAssignment => "logicalAndAssignment"
  | logicalAndShortCircuitRhs => "logicalAndShortCircuitRhs"
  | logicalOrCaptureLhs => "logicalOrCaptureLhs"
  | logicalOrAssignment => "logicalOrAssignment"
  | logicalOrShortCircuitRhs => "logicalOrShortCircuitRhs"
  | logicalNotCapture => "logicalNotCapture"
  | logicalNotAssignment => "logicalNotAssignment"
  | ternaryCaptureCond => "ternaryCaptureCond"
  | ternaryToIf => "ternaryToIf"
  | ternaryToIfStorage => "ternaryToIfStorage"
  | ifUnfold => "ifUnfold"
  | ifElseUnfold => "ifElseUnfold"
  | ifTrue => "ifTrue"
  | ifFalse => "ifFalse"
  | ifElseTrue => "ifElseTrue"
  | ifElseFalse => "ifElseFalse"
  | ifElseNegated => "ifElseNegated"
  | ifSplit => "ifSplit"
  | ifElseSplit => "ifElseSplit"
  | unaryMinusCapture => "unaryMinusCapture"
  | unaryMinusAssignment => "unaryMinusAssignment"
  | assertSimple => "assertSimple"
  | requireConditionCapture => "requireConditionCapture"
  | requireSimple => "requireSimple"
  | transfer_unfold_leftFstReceiver => "transfer_unfold_leftFstReceiver"
  | transfer_unfold_rightSndArgument => "transfer_unfold_rightSndArgument"
  | transferNoCallbackBox => "transferNoCallbackBox"
  | transferNoCallbackDiamond => "transferNoCallbackDiamond"
  | transferWithCallbackBox => "transferWithCallbackBox"
  | transferWithCallbackDiamond => "transferWithCallbackDiamond"
  | storageIndexWrite_unfold_leftFst => "storageIndexWrite_unfold_leftFst"
  | storageIndexWriteStorageRef_unfold_leftFst => "storageIndexWriteStorageRef_unfold_leftFst"
  | memoryToStorageIndex_unfold_leftFst => "memoryToStorageIndex_unfold_leftFst"
  | memoryIndexWrite_unfold_leftFst => "memoryIndexWrite_unfold_leftFst"
  | memoryIndexWriteMemRef_unfold_leftFst => "memoryIndexWriteMemRef_unfold_leftFst"
  | storageIndexWriteNonSimpleIndexCapture => "storageIndexWriteNonSimpleIndexCapture"
  | storageIndexWriteStorageRefNonSimpleIndexCapture => "storageIndexWriteStorageRefNonSimpleIndexCapture"
  | memoryToStorageIndexNonSimpleIndexCapture => "memoryToStorageIndexNonSimpleIndexCapture"
  | memoryIndexWriteNonSimpleIndexCapture => "memoryIndexWriteNonSimpleIndexCapture"
  | memoryIndexWriteMemRefNonSimpleIndexCapture => "memoryIndexWriteMemRefNonSimpleIndexCapture"
  | storageIndexWriteCaptureAll => "storageIndexWriteCaptureAll"
  | storageIndexWriteStorageRefCaptureAll => "storageIndexWriteStorageRefCaptureAll"
  | memoryToStorageIndexCaptureAll => "memoryToStorageIndexCaptureAll"
  | memoryIndexWriteCaptureAll => "memoryIndexWriteCaptureAll"
  | memoryIndexWriteMemRefCaptureAll => "memoryIndexWriteMemRefCaptureAll"

/-- The `\heuristics` rule set the taclet is filed under. -/
def heuristic : KeyTaclet -> Heuristic
  | functionBodyExpand => Heuristic.simplifyProg
  | emptyModality => Heuristic.simplifyProg
  | blockEmpty => Heuristic.simplifyProg
  | revertDiamond => Heuristic.simplifyProg
  | revertBox => Heuristic.simplifyProg
  | storageRootWriteStore => Heuristic.simplifyProg
  | storageRootWriteCopySource => Heuristic.simplifyProg
  | storageRootReadSelect => Heuristic.simplifyProg
  | storageFieldWriteSave => Heuristic.simplifyProg
  | storageFieldWriteCopySource => Heuristic.simplifyProg
  | storageFieldWriteCaptureSrc => Heuristic.simplifyProg
  | storageFieldRead_unfold_rightFst => Heuristic.simplifyProg
  | storageIndexRead_unfold_rightFst => Heuristic.simplifyProg
  | storageFieldReadFind => Heuristic.simplifyProg
  | storageFieldWrite_unfold_leftFst => Heuristic.simplifyProg
  | storageFieldWriteStorageRef_unfold_leftFst => Heuristic.simplifyProg
  | memoryToStorageField_unfold_leftFst => Heuristic.simplifyProg
  | storageIndexWriteMappingSave => Heuristic.simplifyProg
  | storageIndexReadMappingFind => Heuristic.simplifyProg
  | storageIndexReadMappingBindLocalRoot => Heuristic.simplifyProg
  | storageIndexReadMappingStoreRoot => Heuristic.simplifyProg
  | storageIndexWriteMappingCopySource => Heuristic.simplifyProg
  | storageIndexWriteStorageRefRhsCapture => Heuristic.simplifyProg
  | storageIndexWriteArraySave => Heuristic.simplifyProg
  | storageIndexReadArrayFind => Heuristic.simplifyProg
  | storageIndexReadArrayBindLocalRoot => Heuristic.simplifyProg
  | storageIndexReadArrayStoreRoot => Heuristic.simplifyProg
  | storageIndexWriteArrayCopySource => Heuristic.simplifyProg
  | storagePushValue_unfold_leftFstReceiver => Heuristic.simplifyProg
  | storagePush_unfold_leftFstReceiver => Heuristic.simplifyProg
  | storagePop_unfold_leftFstReceiver => Heuristic.simplifyProg
  | storageLocalRootPush_unfold_leftFstReceiver => Heuristic.simplifyProg
  | storagePushValue_unfold_rightSndArgument => Heuristic.simplifyProg
  | storagePushValueSave => Heuristic.simplifyExpression
  | storagePushValueCopySource => Heuristic.simplifyExpression
  | storagePushLengthSave => Heuristic.simplifyExpression
  | storageLocalRootPushBind => Heuristic.simplifyExpression
  | storagePopSave => Heuristic.simplifyProg
  | storageLocalRootRebind => Heuristic.simplifyProg
  | storageLocalDeclSkip => Heuristic.simplifyProg
  | storageLocalDeclInitDrop => Heuristic.simplifyProg
  | memoryReferenceDeclFreshAlloc => Heuristic.simplifyProg
  | memoryLocalDeclInitDrop => Heuristic.simplifyProg
  | memoryRootDeleteFreshRebind => Heuristic.simplifyProg
  | memoryRootRebind => Heuristic.simplifyProg
  | memoryArrayFreshAlloc => Heuristic.simplifyProg
  | memoryStorageCopy => Heuristic.simplifyProg
  | memoryStorageCopyUnfold => Heuristic.simplifyProg
  | memoryFieldWrite => Heuristic.simplifyProg
  | memoryFieldRead => Heuristic.simplifyProg
  | memoryFieldRead_unfold_rightFst => Heuristic.simplifyProg
  | memoryFieldWriteCaptureSrc => Heuristic.simplifyProg
  | memoryFieldWrite_unfold_leftFst => Heuristic.simplifyProg
  | memoryFieldWriteMemRef_unfold_leftFst => Heuristic.simplifyProg
  | memoryIndexWriteArray => Heuristic.simplifyProg
  | memoryIndexReadArrayValue => Heuristic.simplifyProg
  | memoryIndexReadArrayMemory => Heuristic.simplifyProg
  | memoryIndexRead_unfold_rightFst => Heuristic.simplifyProg
  | memoryFieldDeletePrimitive => Heuristic.simplifyProg
  | memoryFieldDeleteReference => Heuristic.simplifyProg
  | memoryIndexDeletePrimitive => Heuristic.simplifyProg
  | memoryIndexDeleteReference => Heuristic.simplifyProg
  | memoryFieldDelete_unfold_leftFst => Heuristic.simplifyProg
  | memoryIndexDelete_unfold_leftFst => Heuristic.simplifyProg
  | memoryToStorageStoreRoot => Heuristic.simplifyProg
  | memoryToStorageFieldCopyRoot => Heuristic.simplifyProg
  | memoryToStorageFieldCopyField => Heuristic.simplifyProg
  | memoryToStorageIndexMappingCopyRoot => Heuristic.simplifyProg
  | memoryToStorageIndexArrayCopyRoot => Heuristic.simplifyProg
  | localValueDeclInitDrop => Heuristic.simplifyProg
  | valueDeclSkip => Heuristic.simplifyProg
  | storageFieldReadBindLocalRoot => Heuristic.simplifyProg
  | storageFieldReadStoreRoot => Heuristic.simplifyProg
  | storageRootAddAssign => Heuristic.simplifyExpression
  | storageFieldAddAssign_unfold_leftFst => Heuristic.simplifyProg
  | storageIndexAddAssign_unfold_leftFst => Heuristic.simplifyProg
  | storageFieldAddAssign => Heuristic.simplifyExpression
  | storageIndexMappingAddAssign => Heuristic.simplifyExpression
  | storageIndexArrayAddAssign => Heuristic.simplifyExpression
  | storageRootSubAssign => Heuristic.simplifyExpression
  | storageFieldSubAssign_unfold_leftFst => Heuristic.simplifyProg
  | storageIndexSubAssign_unfold_leftFst => Heuristic.simplifyProg
  | storageFieldSubAssign => Heuristic.simplifyExpression
  | storageIndexMappingSubAssign => Heuristic.simplifyExpression
  | storageIndexArraySubAssign => Heuristic.simplifyExpression
  | storageRootMulAssign => Heuristic.simplifyExpression
  | storageFieldMulAssign_unfold_leftFst => Heuristic.simplifyProg
  | storageIndexMulAssign_unfold_leftFst => Heuristic.simplifyProg
  | storageFieldMulAssign => Heuristic.simplifyExpression
  | storageIndexMappingMulAssign => Heuristic.simplifyExpression
  | storageIndexArrayMulAssign => Heuristic.simplifyExpression
  | storageRootDivAssign => Heuristic.simplifyExpression
  | storageFieldDivAssign_unfold_leftFst => Heuristic.simplifyProg
  | storageIndexDivAssign_unfold_leftFst => Heuristic.simplifyProg
  | storageFieldDivAssign => Heuristic.simplifyExpression
  | storageIndexMappingDivAssign => Heuristic.simplifyExpression
  | storageIndexArrayDivAssign => Heuristic.simplifyExpression
  | storageRootModAssign => Heuristic.simplifyExpression
  | storageFieldModAssign_unfold_leftFst => Heuristic.simplifyProg
  | storageIndexModAssign_unfold_leftFst => Heuristic.simplifyProg
  | storageFieldModAssign => Heuristic.simplifyExpression
  | storageIndexMappingModAssign => Heuristic.simplifyExpression
  | storageIndexArrayModAssign => Heuristic.simplifyExpression
  | storageRootDelete => Heuristic.simplifyExpression
  | storageFieldDelete => Heuristic.simplifyExpression
  | storageIndexDelete => Heuristic.simplifyExpression
  | storageFieldDelete_unfold_leftFst => Heuristic.simplifyProg
  | storageIndexDelete_unfold_leftFst => Heuristic.simplifyProg
  | storageRootPreincrement => Heuristic.simplifyExpression
  | storageRootPredecrement => Heuristic.simplifyExpression
  | storageRootPostincrement => Heuristic.simplifyExpression
  | storageRootPostdecrement => Heuristic.simplifyExpression
  | storageRootPreincrementAssignment => Heuristic.simplifyExpression
  | storageRootPredecrementAssignment => Heuristic.simplifyExpression
  | storageRootPostincrementAssignment => Heuristic.simplifyExpression
  | storageRootPostdecrementAssignment => Heuristic.simplifyExpression
  | addition_unfold_left => Heuristic.simplifyProg
  | addition_unfold_right => Heuristic.simplifyProg
  | localValueAssign => Heuristic.simplifyProg
  | additionAssignment => Heuristic.simplifyProg
  | subtraction_unfold_left => Heuristic.simplifyProg
  | subtraction_unfold_right => Heuristic.simplifyProg
  | subtractionAssignment => Heuristic.simplifyProg
  | multiplication_unfold_left => Heuristic.simplifyProg
  | multiplication_unfold_right => Heuristic.simplifyProg
  | multiplicationAssignment => Heuristic.simplifyProg
  | power_unfold_left => Heuristic.simplifyProg
  | power_unfold_right => Heuristic.simplifyProg
  | powerAssignment => Heuristic.simplifyProg
  | division_unfold_left => Heuristic.simplifyProg
  | division_unfold_right => Heuristic.simplifyProg
  | divisionAssignment => Heuristic.simplifyProg
  | modulo_unfold_left => Heuristic.simplifyProg
  | modulo_unfold_right => Heuristic.simplifyProg
  | moduloAssignment => Heuristic.simplifyProg
  | storageFieldPreincrement => Heuristic.simplifyExpression
  | storageFieldPostincrementAssignment => Heuristic.simplifyExpression
  | storageFieldPostincrement => Heuristic.simplifyExpression
  | storageFieldPredecrement => Heuristic.simplifyExpression
  | storageFieldPostdecrement => Heuristic.simplifyExpression
  | storageFieldPreincrementAssignment => Heuristic.simplifyExpression
  | storageFieldPredecrementAssignment => Heuristic.simplifyExpression
  | storageFieldPostdecrementAssignment => Heuristic.simplifyExpression
  | storageIndexMappingPreincrement => Heuristic.simplifyExpression
  | storageIndexArrayPreincrement => Heuristic.simplifyExpression
  | storageIndexMappingPostincrement => Heuristic.simplifyExpression
  | storageIndexArrayPostincrement => Heuristic.simplifyExpression
  | storageIndexMappingPredecrement => Heuristic.simplifyExpression
  | storageIndexArrayPredecrement => Heuristic.simplifyExpression
  | storageIndexMappingPostdecrement => Heuristic.simplifyExpression
  | storageIndexArrayPostdecrement => Heuristic.simplifyExpression
  | storageIndexMappingPreincrementAssignment => Heuristic.simplifyExpression
  | storageIndexArrayPreincrementAssignment => Heuristic.simplifyExpression
  | storageIndexMappingPostincrementAssignment => Heuristic.simplifyExpression
  | storageIndexArrayPostincrementAssignment => Heuristic.simplifyExpression
  | storageIndexMappingPredecrementAssignment => Heuristic.simplifyExpression
  | storageIndexArrayPredecrementAssignment => Heuristic.simplifyExpression
  | storageIndexMappingPostdecrementAssignment => Heuristic.simplifyExpression
  | storageIndexArrayPostdecrementAssignment => Heuristic.simplifyExpression
  | storageFieldPreincrement_unfold_leftFst => Heuristic.simplifyProg
  | storageFieldPostincrement_unfold_leftFst => Heuristic.simplifyProg
  | storageFieldPredecrement_unfold_leftFst => Heuristic.simplifyProg
  | storageFieldPostdecrement_unfold_leftFst => Heuristic.simplifyProg
  | storageIndexPreincrement_unfold_leftFst => Heuristic.simplifyProg
  | storageIndexPostincrement_unfold_leftFst => Heuristic.simplifyProg
  | storageIndexPredecrement_unfold_leftFst => Heuristic.simplifyProg
  | storageIndexPostdecrement_unfold_leftFst => Heuristic.simplifyProg
  | memoryFieldAddAssign => Heuristic.simplifyExpression
  | memoryFieldSubAssign => Heuristic.simplifyExpression
  | memoryFieldMulAssign => Heuristic.simplifyExpression
  | memoryFieldDivAssign => Heuristic.simplifyExpression
  | memoryFieldModAssign => Heuristic.simplifyExpression
  | memoryIndexArrayAddAssign => Heuristic.simplifyExpression
  | memoryIndexArraySubAssign => Heuristic.simplifyExpression
  | memoryIndexArrayMulAssign => Heuristic.simplifyExpression
  | memoryIndexArrayDivAssign => Heuristic.simplifyExpression
  | memoryIndexArrayModAssign => Heuristic.simplifyExpression
  | memoryFieldAddAssign_unfold_leftFst => Heuristic.simplifyProg
  | memoryFieldSubAssign_unfold_leftFst => Heuristic.simplifyProg
  | memoryFieldMulAssign_unfold_leftFst => Heuristic.simplifyProg
  | memoryFieldDivAssign_unfold_leftFst => Heuristic.simplifyProg
  | memoryFieldModAssign_unfold_leftFst => Heuristic.simplifyProg
  | memoryIndexAddAssign_unfold_leftFst => Heuristic.simplifyProg
  | memoryIndexSubAssign_unfold_leftFst => Heuristic.simplifyProg
  | memoryIndexMulAssign_unfold_leftFst => Heuristic.simplifyProg
  | memoryIndexDivAssign_unfold_leftFst => Heuristic.simplifyProg
  | memoryIndexModAssign_unfold_leftFst => Heuristic.simplifyProg
  | memoryFieldPreincrement => Heuristic.simplifyExpression
  | memoryFieldPostincrement => Heuristic.simplifyExpression
  | memoryFieldPredecrement => Heuristic.simplifyExpression
  | memoryFieldPostdecrement => Heuristic.simplifyExpression
  | memoryFieldPreincrementAssignment => Heuristic.simplifyExpression
  | memoryFieldPostincrementAssignment => Heuristic.simplifyExpression
  | memoryFieldPredecrementAssignment => Heuristic.simplifyExpression
  | memoryFieldPostdecrementAssignment => Heuristic.simplifyExpression
  | memoryIndexArrayPreincrement => Heuristic.simplifyExpression
  | memoryIndexArrayPostincrement => Heuristic.simplifyExpression
  | memoryIndexArrayPredecrement => Heuristic.simplifyExpression
  | memoryIndexArrayPostdecrement => Heuristic.simplifyExpression
  | memoryIndexArrayPreincrementAssignment => Heuristic.simplifyExpression
  | memoryIndexArrayPostincrementAssignment => Heuristic.simplifyExpression
  | memoryIndexArrayPredecrementAssignment => Heuristic.simplifyExpression
  | memoryIndexArrayPostdecrementAssignment => Heuristic.simplifyExpression
  | memoryFieldPreincrement_unfold_leftFst => Heuristic.simplifyProg
  | memoryFieldPostincrement_unfold_leftFst => Heuristic.simplifyProg
  | memoryFieldPredecrement_unfold_leftFst => Heuristic.simplifyProg
  | memoryFieldPostdecrement_unfold_leftFst => Heuristic.simplifyProg
  | memoryIndexPreincrement_unfold_leftFst => Heuristic.simplifyProg
  | memoryIndexPostincrement_unfold_leftFst => Heuristic.simplifyProg
  | memoryIndexPredecrement_unfold_leftFst => Heuristic.simplifyProg
  | memoryIndexPostdecrement_unfold_leftFst => Heuristic.simplifyProg
  | localDeclPreincrement => Heuristic.simplifyProg
  | localAssignPreincrement => Heuristic.simplifyProg
  | localDeclPredecrement => Heuristic.simplifyProg
  | localAssignPredecrement => Heuristic.simplifyProg
  | localDeclPostincrement => Heuristic.simplifyProg
  | localAssignPostincrement => Heuristic.simplifyProg
  | localDeclPostdecrement => Heuristic.simplifyProg
  | localAssignPostdecrement => Heuristic.simplifyProg
  | localPreincrement => Heuristic.simplifyProg
  | localPostincrement => Heuristic.simplifyProg
  | localPredecrement => Heuristic.simplifyProg
  | localPostdecrement => Heuristic.simplifyProg
  | localAddAssign => Heuristic.simplifyProg
  | localSubAssign => Heuristic.simplifyProg
  | localMulAssign => Heuristic.simplifyProg
  | localDivAssign => Heuristic.simplifyProg
  | localModAssign => Heuristic.simplifyProg
  | addAssignValueRhsCapture => Heuristic.simplifyProg
  | subAssignValueRhsCapture => Heuristic.simplifyProg
  | mulAssignValueRhsCapture => Heuristic.simplifyProg
  | divAssignValueRhsCapture => Heuristic.simplifyProg
  | modAssignValueRhsCapture => Heuristic.simplifyProg
  | storageRootWriteValueRhsCapture => Heuristic.simplifyProg
  | fieldWriteValueRhsCapture => Heuristic.simplifyProg
  | indexWriteValueRhsCapture => Heuristic.simplifyProg
  | memoryIndexWriteMemRefRhsCapture => Heuristic.simplifyProg
  | storageIndexRead_unfold_rightSndIndex => Heuristic.simplifyProg
  | memoryIndexRead_unfold_rightSndIndex => Heuristic.simplifyProg
  | storageIndexDeleteNonSimpleIndexCapture => Heuristic.simplifyProg
  | memoryIndexDeleteNonSimpleIndexCapture => Heuristic.simplifyProg
  | storageFieldRead_unfold_rightSndResult => Heuristic.simplifyProg
  | storageIndexRead_unfold_rightSndResult => Heuristic.simplifyProg
  | memoryFieldRead_unfold_rightSndResult => Heuristic.simplifyProg
  | memoryIndexRead_unfold_rightSndResult => Heuristic.simplifyProg
  | assertConditionCapture => Heuristic.simplifyProg
  | boolEqualityCaptureLhs => Heuristic.simplifyProg
  | boolEqualityCaptureRhs => Heuristic.simplifyProg
  | boolEqualityAssignment => Heuristic.simplifyProg
  | boolInequalityCaptureLhs => Heuristic.simplifyProg
  | boolInequalityCaptureRhs => Heuristic.simplifyProg
  | boolInequalityAssignment => Heuristic.simplifyProg
  | lessThanCaptureLhs => Heuristic.simplifyProg
  | lessThanCaptureRhs => Heuristic.simplifyProg
  | lessThanAssignment => Heuristic.simplifyProg
  | greaterThanCaptureLhs => Heuristic.simplifyProg
  | greaterThanCaptureRhs => Heuristic.simplifyProg
  | greaterThanAssignment => Heuristic.simplifyProg
  | lessEqualCaptureLhs => Heuristic.simplifyProg
  | lessEqualCaptureRhs => Heuristic.simplifyProg
  | lessEqualAssignment => Heuristic.simplifyProg
  | greaterEqualCaptureLhs => Heuristic.simplifyProg
  | greaterEqualCaptureRhs => Heuristic.simplifyProg
  | greaterEqualAssignment => Heuristic.simplifyProg
  | logicalAndCaptureLhs => Heuristic.simplifyProg
  | logicalAndAssignment => Heuristic.simplifyProg
  | logicalAndShortCircuitRhs => Heuristic.simplifyProg
  | logicalOrCaptureLhs => Heuristic.simplifyProg
  | logicalOrAssignment => Heuristic.simplifyProg
  | logicalOrShortCircuitRhs => Heuristic.simplifyProg
  | logicalNotCapture => Heuristic.simplifyProg
  | logicalNotAssignment => Heuristic.simplifyProg
  | ternaryCaptureCond => Heuristic.simplifyProg
  | ternaryToIf => Heuristic.simplifyProg
  | ternaryToIfStorage => Heuristic.simplifyProg
  | ifUnfold => Heuristic.simplifyProg
  | ifElseUnfold => Heuristic.simplifyProg
  | ifTrue => Heuristic.concreteSolidity
  | ifFalse => Heuristic.concreteSolidity
  | ifElseTrue => Heuristic.concreteSolidity
  | ifElseFalse => Heuristic.concreteSolidity
  | ifElseNegated => Heuristic.concreteSolidity
  | ifSplit => Heuristic.simplifyProg
  | ifElseSplit => Heuristic.simplifyProg
  | unaryMinusCapture => Heuristic.simplifyProg
  | unaryMinusAssignment => Heuristic.simplifyProg
  | assertSimple => Heuristic.simplifyProg
  | requireConditionCapture => Heuristic.simplifyProg
  | requireSimple => Heuristic.simplifyProg
  | transfer_unfold_leftFstReceiver => Heuristic.simplifyProg
  | transfer_unfold_rightSndArgument => Heuristic.simplifyProg
  | transferNoCallbackBox => Heuristic.simplifyProg
  | transferNoCallbackDiamond => Heuristic.simplifyProg
  | transferWithCallbackBox => Heuristic.simplifyProg
  | transferWithCallbackDiamond => Heuristic.simplifyProg
  | storageIndexWrite_unfold_leftFst => Heuristic.simplifyProg
  | storageIndexWriteStorageRef_unfold_leftFst => Heuristic.simplifyProg
  | memoryToStorageIndex_unfold_leftFst => Heuristic.simplifyProg
  | memoryIndexWrite_unfold_leftFst => Heuristic.simplifyProg
  | memoryIndexWriteMemRef_unfold_leftFst => Heuristic.simplifyProg
  | storageIndexWriteNonSimpleIndexCapture => Heuristic.simplifyProg
  | storageIndexWriteStorageRefNonSimpleIndexCapture => Heuristic.simplifyProg
  | memoryToStorageIndexNonSimpleIndexCapture => Heuristic.simplifyProg
  | memoryIndexWriteNonSimpleIndexCapture => Heuristic.simplifyProg
  | memoryIndexWriteMemRefNonSimpleIndexCapture => Heuristic.simplifyProg
  | storageIndexWriteCaptureAll => Heuristic.simplifyProg
  | storageIndexWriteStorageRefCaptureAll => Heuristic.simplifyProg
  | memoryToStorageIndexCaptureAll => Heuristic.simplifyProg
  | memoryIndexWriteCaptureAll => Heuristic.simplifyProg
  | memoryIndexWriteMemRefCaptureAll => Heuristic.simplifyProg

/-- Every taclet, in the order `solidityProgramRules.key` declares them. -/
def all : List KeyTaclet := [
  KeyTaclet.functionBodyExpand,
  KeyTaclet.emptyModality,
  KeyTaclet.blockEmpty,
  KeyTaclet.revertDiamond,
  KeyTaclet.revertBox,
  KeyTaclet.storageRootWriteStore,
  KeyTaclet.storageRootWriteCopySource,
  KeyTaclet.storageRootReadSelect,
  KeyTaclet.storageFieldWriteSave,
  KeyTaclet.storageFieldWriteCopySource,
  KeyTaclet.storageFieldWriteCaptureSrc,
  KeyTaclet.storageFieldRead_unfold_rightFst,
  KeyTaclet.storageIndexRead_unfold_rightFst,
  KeyTaclet.storageFieldReadFind,
  KeyTaclet.storageFieldWrite_unfold_leftFst,
  KeyTaclet.storageFieldWriteStorageRef_unfold_leftFst,
  KeyTaclet.memoryToStorageField_unfold_leftFst,
  KeyTaclet.storageIndexWriteMappingSave,
  KeyTaclet.storageIndexReadMappingFind,
  KeyTaclet.storageIndexReadMappingBindLocalRoot,
  KeyTaclet.storageIndexReadMappingStoreRoot,
  KeyTaclet.storageIndexWriteMappingCopySource,
  KeyTaclet.storageIndexWriteStorageRefRhsCapture,
  KeyTaclet.storageIndexWriteArraySave,
  KeyTaclet.storageIndexReadArrayFind,
  KeyTaclet.storageIndexReadArrayBindLocalRoot,
  KeyTaclet.storageIndexReadArrayStoreRoot,
  KeyTaclet.storageIndexWriteArrayCopySource,
  KeyTaclet.storagePushValue_unfold_leftFstReceiver,
  KeyTaclet.storagePush_unfold_leftFstReceiver,
  KeyTaclet.storagePop_unfold_leftFstReceiver,
  KeyTaclet.storageLocalRootPush_unfold_leftFstReceiver,
  KeyTaclet.storagePushValue_unfold_rightSndArgument,
  KeyTaclet.storagePushValueSave,
  KeyTaclet.storagePushValueCopySource,
  KeyTaclet.storagePushLengthSave,
  KeyTaclet.storageLocalRootPushBind,
  KeyTaclet.storagePopSave,
  KeyTaclet.storageLocalRootRebind,
  KeyTaclet.storageLocalDeclSkip,
  KeyTaclet.storageLocalDeclInitDrop,
  KeyTaclet.memoryReferenceDeclFreshAlloc,
  KeyTaclet.memoryLocalDeclInitDrop,
  KeyTaclet.memoryRootDeleteFreshRebind,
  KeyTaclet.memoryRootRebind,
  KeyTaclet.memoryArrayFreshAlloc,
  KeyTaclet.memoryStorageCopy,
  KeyTaclet.memoryStorageCopyUnfold,
  KeyTaclet.memoryFieldWrite,
  KeyTaclet.memoryFieldRead,
  KeyTaclet.memoryFieldRead_unfold_rightFst,
  KeyTaclet.memoryFieldWriteCaptureSrc,
  KeyTaclet.memoryFieldWrite_unfold_leftFst,
  KeyTaclet.memoryFieldWriteMemRef_unfold_leftFst,
  KeyTaclet.memoryIndexWriteArray,
  KeyTaclet.memoryIndexReadArrayValue,
  KeyTaclet.memoryIndexReadArrayMemory,
  KeyTaclet.memoryIndexRead_unfold_rightFst,
  KeyTaclet.memoryFieldDeletePrimitive,
  KeyTaclet.memoryFieldDeleteReference,
  KeyTaclet.memoryIndexDeletePrimitive,
  KeyTaclet.memoryIndexDeleteReference,
  KeyTaclet.memoryFieldDelete_unfold_leftFst,
  KeyTaclet.memoryIndexDelete_unfold_leftFst,
  KeyTaclet.memoryToStorageStoreRoot,
  KeyTaclet.memoryToStorageFieldCopyRoot,
  KeyTaclet.memoryToStorageFieldCopyField,
  KeyTaclet.memoryToStorageIndexMappingCopyRoot,
  KeyTaclet.memoryToStorageIndexArrayCopyRoot,
  KeyTaclet.localValueDeclInitDrop,
  KeyTaclet.valueDeclSkip,
  KeyTaclet.storageFieldReadBindLocalRoot,
  KeyTaclet.storageFieldReadStoreRoot,
  KeyTaclet.storageRootAddAssign,
  KeyTaclet.storageFieldAddAssign_unfold_leftFst,
  KeyTaclet.storageIndexAddAssign_unfold_leftFst,
  KeyTaclet.storageFieldAddAssign,
  KeyTaclet.storageIndexMappingAddAssign,
  KeyTaclet.storageIndexArrayAddAssign,
  KeyTaclet.storageRootSubAssign,
  KeyTaclet.storageFieldSubAssign_unfold_leftFst,
  KeyTaclet.storageIndexSubAssign_unfold_leftFst,
  KeyTaclet.storageFieldSubAssign,
  KeyTaclet.storageIndexMappingSubAssign,
  KeyTaclet.storageIndexArraySubAssign,
  KeyTaclet.storageRootMulAssign,
  KeyTaclet.storageFieldMulAssign_unfold_leftFst,
  KeyTaclet.storageIndexMulAssign_unfold_leftFst,
  KeyTaclet.storageFieldMulAssign,
  KeyTaclet.storageIndexMappingMulAssign,
  KeyTaclet.storageIndexArrayMulAssign,
  KeyTaclet.storageRootDivAssign,
  KeyTaclet.storageFieldDivAssign_unfold_leftFst,
  KeyTaclet.storageIndexDivAssign_unfold_leftFst,
  KeyTaclet.storageFieldDivAssign,
  KeyTaclet.storageIndexMappingDivAssign,
  KeyTaclet.storageIndexArrayDivAssign,
  KeyTaclet.storageRootModAssign,
  KeyTaclet.storageFieldModAssign_unfold_leftFst,
  KeyTaclet.storageIndexModAssign_unfold_leftFst,
  KeyTaclet.storageFieldModAssign,
  KeyTaclet.storageIndexMappingModAssign,
  KeyTaclet.storageIndexArrayModAssign,
  KeyTaclet.storageRootDelete,
  KeyTaclet.storageFieldDelete,
  KeyTaclet.storageIndexDelete,
  KeyTaclet.storageFieldDelete_unfold_leftFst,
  KeyTaclet.storageIndexDelete_unfold_leftFst,
  KeyTaclet.storageRootPreincrement,
  KeyTaclet.storageRootPredecrement,
  KeyTaclet.storageRootPostincrement,
  KeyTaclet.storageRootPostdecrement,
  KeyTaclet.storageRootPreincrementAssignment,
  KeyTaclet.storageRootPredecrementAssignment,
  KeyTaclet.storageRootPostincrementAssignment,
  KeyTaclet.storageRootPostdecrementAssignment,
  KeyTaclet.addition_unfold_left,
  KeyTaclet.addition_unfold_right,
  KeyTaclet.localValueAssign,
  KeyTaclet.additionAssignment,
  KeyTaclet.subtraction_unfold_left,
  KeyTaclet.subtraction_unfold_right,
  KeyTaclet.subtractionAssignment,
  KeyTaclet.multiplication_unfold_left,
  KeyTaclet.multiplication_unfold_right,
  KeyTaclet.multiplicationAssignment,
  KeyTaclet.power_unfold_left,
  KeyTaclet.power_unfold_right,
  KeyTaclet.powerAssignment,
  KeyTaclet.division_unfold_left,
  KeyTaclet.division_unfold_right,
  KeyTaclet.divisionAssignment,
  KeyTaclet.modulo_unfold_left,
  KeyTaclet.modulo_unfold_right,
  KeyTaclet.moduloAssignment,
  KeyTaclet.storageFieldPreincrement,
  KeyTaclet.storageFieldPostincrementAssignment,
  KeyTaclet.storageFieldPostincrement,
  KeyTaclet.storageFieldPredecrement,
  KeyTaclet.storageFieldPostdecrement,
  KeyTaclet.storageFieldPreincrementAssignment,
  KeyTaclet.storageFieldPredecrementAssignment,
  KeyTaclet.storageFieldPostdecrementAssignment,
  KeyTaclet.storageIndexMappingPreincrement,
  KeyTaclet.storageIndexArrayPreincrement,
  KeyTaclet.storageIndexMappingPostincrement,
  KeyTaclet.storageIndexArrayPostincrement,
  KeyTaclet.storageIndexMappingPredecrement,
  KeyTaclet.storageIndexArrayPredecrement,
  KeyTaclet.storageIndexMappingPostdecrement,
  KeyTaclet.storageIndexArrayPostdecrement,
  KeyTaclet.storageIndexMappingPreincrementAssignment,
  KeyTaclet.storageIndexArrayPreincrementAssignment,
  KeyTaclet.storageIndexMappingPostincrementAssignment,
  KeyTaclet.storageIndexArrayPostincrementAssignment,
  KeyTaclet.storageIndexMappingPredecrementAssignment,
  KeyTaclet.storageIndexArrayPredecrementAssignment,
  KeyTaclet.storageIndexMappingPostdecrementAssignment,
  KeyTaclet.storageIndexArrayPostdecrementAssignment,
  KeyTaclet.storageFieldPreincrement_unfold_leftFst,
  KeyTaclet.storageFieldPostincrement_unfold_leftFst,
  KeyTaclet.storageFieldPredecrement_unfold_leftFst,
  KeyTaclet.storageFieldPostdecrement_unfold_leftFst,
  KeyTaclet.storageIndexPreincrement_unfold_leftFst,
  KeyTaclet.storageIndexPostincrement_unfold_leftFst,
  KeyTaclet.storageIndexPredecrement_unfold_leftFst,
  KeyTaclet.storageIndexPostdecrement_unfold_leftFst,
  KeyTaclet.memoryFieldAddAssign,
  KeyTaclet.memoryFieldSubAssign,
  KeyTaclet.memoryFieldMulAssign,
  KeyTaclet.memoryFieldDivAssign,
  KeyTaclet.memoryFieldModAssign,
  KeyTaclet.memoryIndexArrayAddAssign,
  KeyTaclet.memoryIndexArraySubAssign,
  KeyTaclet.memoryIndexArrayMulAssign,
  KeyTaclet.memoryIndexArrayDivAssign,
  KeyTaclet.memoryIndexArrayModAssign,
  KeyTaclet.memoryFieldAddAssign_unfold_leftFst,
  KeyTaclet.memoryFieldSubAssign_unfold_leftFst,
  KeyTaclet.memoryFieldMulAssign_unfold_leftFst,
  KeyTaclet.memoryFieldDivAssign_unfold_leftFst,
  KeyTaclet.memoryFieldModAssign_unfold_leftFst,
  KeyTaclet.memoryIndexAddAssign_unfold_leftFst,
  KeyTaclet.memoryIndexSubAssign_unfold_leftFst,
  KeyTaclet.memoryIndexMulAssign_unfold_leftFst,
  KeyTaclet.memoryIndexDivAssign_unfold_leftFst,
  KeyTaclet.memoryIndexModAssign_unfold_leftFst,
  KeyTaclet.memoryFieldPreincrement,
  KeyTaclet.memoryFieldPostincrement,
  KeyTaclet.memoryFieldPredecrement,
  KeyTaclet.memoryFieldPostdecrement,
  KeyTaclet.memoryFieldPreincrementAssignment,
  KeyTaclet.memoryFieldPostincrementAssignment,
  KeyTaclet.memoryFieldPredecrementAssignment,
  KeyTaclet.memoryFieldPostdecrementAssignment,
  KeyTaclet.memoryIndexArrayPreincrement,
  KeyTaclet.memoryIndexArrayPostincrement,
  KeyTaclet.memoryIndexArrayPredecrement,
  KeyTaclet.memoryIndexArrayPostdecrement,
  KeyTaclet.memoryIndexArrayPreincrementAssignment,
  KeyTaclet.memoryIndexArrayPostincrementAssignment,
  KeyTaclet.memoryIndexArrayPredecrementAssignment,
  KeyTaclet.memoryIndexArrayPostdecrementAssignment,
  KeyTaclet.memoryFieldPreincrement_unfold_leftFst,
  KeyTaclet.memoryFieldPostincrement_unfold_leftFst,
  KeyTaclet.memoryFieldPredecrement_unfold_leftFst,
  KeyTaclet.memoryFieldPostdecrement_unfold_leftFst,
  KeyTaclet.memoryIndexPreincrement_unfold_leftFst,
  KeyTaclet.memoryIndexPostincrement_unfold_leftFst,
  KeyTaclet.memoryIndexPredecrement_unfold_leftFst,
  KeyTaclet.memoryIndexPostdecrement_unfold_leftFst,
  KeyTaclet.localDeclPreincrement,
  KeyTaclet.localAssignPreincrement,
  KeyTaclet.localDeclPredecrement,
  KeyTaclet.localAssignPredecrement,
  KeyTaclet.localDeclPostincrement,
  KeyTaclet.localAssignPostincrement,
  KeyTaclet.localDeclPostdecrement,
  KeyTaclet.localAssignPostdecrement,
  KeyTaclet.localPreincrement,
  KeyTaclet.localPostincrement,
  KeyTaclet.localPredecrement,
  KeyTaclet.localPostdecrement,
  KeyTaclet.localAddAssign,
  KeyTaclet.localSubAssign,
  KeyTaclet.localMulAssign,
  KeyTaclet.localDivAssign,
  KeyTaclet.localModAssign,
  KeyTaclet.addAssignValueRhsCapture,
  KeyTaclet.subAssignValueRhsCapture,
  KeyTaclet.mulAssignValueRhsCapture,
  KeyTaclet.divAssignValueRhsCapture,
  KeyTaclet.modAssignValueRhsCapture,
  KeyTaclet.storageRootWriteValueRhsCapture,
  KeyTaclet.fieldWriteValueRhsCapture,
  KeyTaclet.indexWriteValueRhsCapture,
  KeyTaclet.memoryIndexWriteMemRefRhsCapture,
  KeyTaclet.storageIndexRead_unfold_rightSndIndex,
  KeyTaclet.memoryIndexRead_unfold_rightSndIndex,
  KeyTaclet.storageIndexDeleteNonSimpleIndexCapture,
  KeyTaclet.memoryIndexDeleteNonSimpleIndexCapture,
  KeyTaclet.storageFieldRead_unfold_rightSndResult,
  KeyTaclet.storageIndexRead_unfold_rightSndResult,
  KeyTaclet.memoryFieldRead_unfold_rightSndResult,
  KeyTaclet.memoryIndexRead_unfold_rightSndResult,
  KeyTaclet.assertConditionCapture,
  KeyTaclet.boolEqualityCaptureLhs,
  KeyTaclet.boolEqualityCaptureRhs,
  KeyTaclet.boolEqualityAssignment,
  KeyTaclet.boolInequalityCaptureLhs,
  KeyTaclet.boolInequalityCaptureRhs,
  KeyTaclet.boolInequalityAssignment,
  KeyTaclet.lessThanCaptureLhs,
  KeyTaclet.lessThanCaptureRhs,
  KeyTaclet.lessThanAssignment,
  KeyTaclet.greaterThanCaptureLhs,
  KeyTaclet.greaterThanCaptureRhs,
  KeyTaclet.greaterThanAssignment,
  KeyTaclet.lessEqualCaptureLhs,
  KeyTaclet.lessEqualCaptureRhs,
  KeyTaclet.lessEqualAssignment,
  KeyTaclet.greaterEqualCaptureLhs,
  KeyTaclet.greaterEqualCaptureRhs,
  KeyTaclet.greaterEqualAssignment,
  KeyTaclet.logicalAndCaptureLhs,
  KeyTaclet.logicalAndAssignment,
  KeyTaclet.logicalAndShortCircuitRhs,
  KeyTaclet.logicalOrCaptureLhs,
  KeyTaclet.logicalOrAssignment,
  KeyTaclet.logicalOrShortCircuitRhs,
  KeyTaclet.logicalNotCapture,
  KeyTaclet.logicalNotAssignment,
  KeyTaclet.ternaryCaptureCond,
  KeyTaclet.ternaryToIf,
  KeyTaclet.ternaryToIfStorage,
  KeyTaclet.ifUnfold,
  KeyTaclet.ifElseUnfold,
  KeyTaclet.ifTrue,
  KeyTaclet.ifFalse,
  KeyTaclet.ifElseTrue,
  KeyTaclet.ifElseFalse,
  KeyTaclet.ifElseNegated,
  KeyTaclet.ifSplit,
  KeyTaclet.ifElseSplit,
  KeyTaclet.unaryMinusCapture,
  KeyTaclet.unaryMinusAssignment,
  KeyTaclet.assertSimple,
  KeyTaclet.requireConditionCapture,
  KeyTaclet.requireSimple,
  KeyTaclet.transfer_unfold_leftFstReceiver,
  KeyTaclet.transfer_unfold_rightSndArgument,
  KeyTaclet.transferNoCallbackBox,
  KeyTaclet.transferNoCallbackDiamond,
  KeyTaclet.transferWithCallbackBox,
  KeyTaclet.transferWithCallbackDiamond,
  KeyTaclet.storageIndexWrite_unfold_leftFst,
  KeyTaclet.storageIndexWriteStorageRef_unfold_leftFst,
  KeyTaclet.memoryToStorageIndex_unfold_leftFst,
  KeyTaclet.memoryIndexWrite_unfold_leftFst,
  KeyTaclet.memoryIndexWriteMemRef_unfold_leftFst,
  KeyTaclet.storageIndexWriteNonSimpleIndexCapture,
  KeyTaclet.storageIndexWriteStorageRefNonSimpleIndexCapture,
  KeyTaclet.memoryToStorageIndexNonSimpleIndexCapture,
  KeyTaclet.memoryIndexWriteNonSimpleIndexCapture,
  KeyTaclet.memoryIndexWriteMemRefNonSimpleIndexCapture,
  KeyTaclet.storageIndexWriteCaptureAll,
  KeyTaclet.storageIndexWriteStorageRefCaptureAll,
  KeyTaclet.memoryToStorageIndexCaptureAll,
  KeyTaclet.memoryIndexWriteCaptureAll,
  KeyTaclet.memoryIndexWriteMemRefCaptureAll
]

end KeyTaclet

/-- Where a Lean rule comes from: the KeY taclet it transcribes, the several
taclets it merges, or nothing.

`merged` is the common case and it is not a weakness of the port: KeY splits
one rule by a distinction the Lean model does not draw — a root receiver from a
decomposed one (`_root`/`_decompose`), a stack right-hand side from a storage
root (`…RootRhs…`), a value push from a copy-source push — and one Lean rule
covers the family.  `docs/lean-key-rule-map.md` carries the prose for each.

`leanOnly` is the deliberate absence: front-end normalisations, scratch
bindings, the call rules, and operator instances KeY does not have.
`RuleShapes.leanOnlyRules` lists them with a reason each, and checks the list
is exactly the rules whose origin is `leanOnly`. -/
inductive KeyOrigin where
  | taclet (t : KeyTaclet)
  | merged (ts : List KeyTaclet)
  | leanOnly
  deriving DecidableEq, Repr

namespace KeyOrigin

/-- The taclets an origin claims. -/
def taclets : KeyOrigin -> List KeyTaclet
  | taclet t => [t]
  | merged ts => ts
  | leanOnly => []

end KeyOrigin

end Solidity
