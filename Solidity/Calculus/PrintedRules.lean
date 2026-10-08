import Solidity.Calculus.RuleShapes

/-!
# The printed rules, as a Lean type

The printed rule set is the
second port target of the rule table: `KeyTaclets.lean` names what solkey
runs, this module names what is *printed* — one constructor per
`\DeclarePrintedRule` name, with the `tags` reduced to a `PrintedRuleKind` — and
says which `Taclet` constructor is which printed rule.

`printedOrigins` is the map, written from the Lean side and keyed by
constructor name for the reason `RuleShapes.tacletOrigins` is: `Taclet` is a
`Prop`, so there is nothing to match on.  `#check_constructor_table` holds it
to the constructor list, so a constructor added to `Calculus/Core/Rules.lean` does not build
here until it says what it is.  The printed rules are now spelled as
solkey does, so most rows name the constructor's own name; a `merged` row is a
Lean constructor whose `\find` covers several printed rules (a value source and a
reference one, a mapping receiver and an array one, an element type with a
mapping in it and one without).

The other direction is `printed_rules_partitioned`: every printed rule of kind
`rule` is claimed by some row or listed in `unclaimedRules`, and no template,
rejected, unimplemented or first-order name is claimed.

A `leanOnly` row carries its reason.  `keyTier` is the large, uninteresting
one — solkey has the taclet, the printed rules do not include it: the expression
tiers, and the compound and increment families' unfold and assignment steps.
`calculus` is the short list that should be printed: rules with neither a
taclet nor a printed rule, whose theory is only here.

-/

namespace Solidity

/-- What a `\DeclarePrintedRule` block is, read off its `tags`. -/
inductive PrintedRuleKind where
  /-- A rule of the calculus: the default. -/
  | rule
  /-- The six `unfold_*` schemata a family of rules instantiates (tag
  `template` in the storage and memory rules).  Not a rule; nothing claims one. -/
  | template
  /-- Tag `rejected`: printed to be argued against. -/
  | rejected
  /-- Tag `unimplemented` and declared only among the checked arithmetic rules:
  `storageRootIncrement`, the checked `++` on a state variable, whose
  unchecked twin prints as `storageRootPostincrement`. -/
  | unimplemented
  /-- `sizeNotNegative`, the one first-order axiom among the rules. -/
  | firstOrder
  deriving DecidableEq, Repr

/-- One printed rule, under its printed name (`\\_` read as `_`),
grouped by the file that first declares it.  A name declared twice —
the six `unfold_*` templates and the two value-source captures are in both
the storage and memory rules, `memoryFieldRead` is printed for a value and a
reference, and the checked group re-declares six of the arithmetic rules with
checked arithmetic — is one constructor. -/
inductive PrintedRule where
  -- storage
  | unfold_rightFst
  | unfold_rightSnd
  | unfold_rightSndResult
  | unfold_leftFst
  | unfold_leftSnd
  | unfold_source
  | fieldWriteValueRhsCapture
  | indexWriteValueRhsCapture
  | storageFieldRead_unfold_rightFst
  | storageIndexRead_unfold_rightFst
  | storageIndexRead_unfold_rightSndIndex
  | storagePushValue_unfold_rightSndArgument
  | storageFieldRead_unfold_rightSndResult
  | storageIndexRead_unfold_rightSndResult
  | storageFieldWrite_unfold_leftFst
  | storageIndexWriteCaptureAllComplexRecv
  | storageFieldWriteStorageRef_unfold_leftFst
  | storageIndexWriteStorageRefCaptureAllComplexRecv
  | storageFieldDelete_unfold_leftFst
  | storageIndexDelete_unfold_leftFst
  | storagePushValue_unfold_leftFstReceiver
  | storagePush_unfold_leftFstReceiver
  | storagePop_unfold_leftFstReceiver
  | storageLocalRootPush_unfold_leftFstReceiver
  | storageIndexWriteCaptureAllNonSimpleIndex
  | storageIndexWriteStorageRefCaptureAllNonSimpleIndex
  | storageRootWriteValueRhsCapture
  | storageFieldWriteCaptureSrc
  | storageIndexWriteStorageRefRhsCapture
  | storageLocalDeclInitDrop
  | storageLocalDeclSkip
  | storageFieldWriteSave
  | storageFieldWriteCopySource
  | storageRootWriteStore
  | storageRootWriteCopySource
  | storageLocalRootRebind
  | storageFieldReadFind
  | storageRootReadSelect
  | storageFieldReadBindLocalRoot
  | storageFieldReadStoreRoot
  | storageRootDelete
  | storageFieldDelete
  | storageIndexDelete
  | storageIndexArrayDelete
  | storageIndexWriteMappingSave
  | storageIndexWriteMappingCopySource
  | storageIndexReadMappingFind
  | storageIndexReadMappingBindLocalRoot
  | storageIndexReadMappingStoreRoot
  | storageIndexWriteArraySave
  | storageIndexWriteArrayCopySource
  | storageIndexReadArrayFind
  | storageIndexReadArrayBindLocalRoot
  | storageIndexReadArrayBindLocalRootMappingElement
  | storageIndexReadArrayStoreRoot
  | storagePushValueSave
  | storagePushValueCopySource
  | storagePushLengthSave
  | storagePushLengthSaveReferenceElement
  | storageLocalRootPushBind
  | storageLocalRootPushBindMappingElement
  | storagePopSave
  | storagePopSaveMappingElement
  | sizeNotNegative
  | indexWriteInnerNonSimpleIndexCapture
  | indexReadInnerNonSimpleIndexCapture
  -- memory
  | memoryFieldRead_unfold_rightFst
  | memoryIndexRead_unfold_rightFst
  | memoryIndexRead_unfold_rightSndIndex
  | memoryFieldRead_unfold_rightSndResult
  | memoryIndexRead_unfold_rightSndResult
  | memoryFieldWrite_unfold_leftFst
  | memoryIndexWriteCaptureAllComplexRecv
  | memoryFieldWriteMemRef_unfold_leftFst
  | memoryIndexWriteMemRefCaptureAllComplexRecv
  | newArrayCapture
  | memoryFieldDelete_unfold_leftFst
  | memoryIndexDelete_unfold_leftFst
  | memoryIndexWriteCaptureAllNonSimpleIndex
  | memoryIndexWriteMemRefCaptureAllNonSimpleIndex
  | memoryFieldWriteCaptureSrc
  | memoryIndexWriteMemRefRhsCapture
  | memoryLocalDeclInitDrop
  | memoryReferenceDeclFreshAlloc
  | memoryArrayFreshAlloc
  | memoryFieldWrite
  | memoryRootRebind
  | memoryFieldRead
  | memoryRootDeleteFreshRebind
  | memoryFieldDeletePrimitive
  | memoryFieldDeleteReference
  | memoryIndexWriteArray
  | memoryIndexReadArrayValue
  | memoryIndexReadArrayMemory
  | memoryIndexDeletePrimitive
  | memoryIndexDeleteReference
  -- copy
  | memoryStorageCopyUnfold
  | memoryStorageCopy
  | memoryToStorageField_unfold_leftFst
  | memoryToStorageIndexCaptureAllComplexRecv
  | memoryToStorageIndexCaptureAllNonSimpleIndex
  | memoryToStorageFieldCopyRoot
  | memoryToStorageFieldCopyField
  | memoryToStorageIndexMappingCopyRoot
  | memoryToStorageIndexArrayCopyRoot
  | memoryToStorageStoreRoot
  -- control
  | requireConditionCapture
  | assertConditionCapture
  | requireSimple
  | assertSimple
  | revertDiamond
  | revertBox
  | ifElseUnfold
  | ifElseSplit
  | ifElseTrue
  | ifElseFalse
  | ifElseNegated
  -- payment
  | transfer_unfold_leftFstReceiver
  | transfer_unfold_rightSndArgument
  | transferNoCallback
  | transferWithCallbackBox
  | transferWithCallbackDiamond
  -- arithmetic
  | localOpAssign
  | storageRootOpAssign
  | storageFieldOpAssign
  | storageIndexMappingOpAssign
  | localDivAssign
  | unaryMinusAssignment
  | storageIndexArrayOpAssign
  | storageRootPostincrement
  | memoryFieldOpAssign
  | memoryFieldDivAssign
  | memoryIndexArrayOpAssign
  | memoryFieldPostincrement
  -- checked arithmetic
  | storageRootIncrement
  deriving DecidableEq, Repr

-- The printed spelling, `PrintedRule.name`, and every rule, `PrintedRule.all`.
#enum_ctors PrintedRule

namespace PrintedRule

/-- Which kind of declaration the name is, read off its `tags`. -/
def kind : PrintedRule -> PrintedRuleKind
  | .unfold_rightFst | .unfold_rightSnd | .unfold_rightSndResult
  | .unfold_leftFst | .unfold_leftSnd | .unfold_source => .template
  | .indexWriteInnerNonSimpleIndexCapture | .indexReadInnerNonSimpleIndexCapture => .rejected
  | .storageRootIncrement => .unimplemented
  | .sizeNotNegative => .firstOrder
  | _ => .rule

end PrintedRule

/-- Why a `Taclet` constructor has no printed rule. -/
inductive LeanOnlyReason where
  /-- solkey has the taclet and the printed rules do not include it: the expression
  tiers, the operator instances outside `+ - * / %`, the increment and
  compound families' unfold and assignment steps. -/
  | keyTier
  /-- Theory only Lean has.  It should be printed. -/
  | calculus
  deriving DecidableEq, Repr

/-- The printed rule a constructor transcribes, or the reason there is none. -/
inductive PrintedOrigin where
  | printed (p : PrintedRule)
  | merged (ps : List PrintedRule)
  | leanOnly (why : LeanOnlyReason)
  deriving DecidableEq, Repr

namespace PrintedOrigin

/-- The printed rules an origin claims. -/
def rules : PrintedOrigin -> List PrintedRule
  | printed p => [p]
  | merged ps => ps
  | leanOnly _ => []

end PrintedOrigin

namespace PrintedRules

/-- Every `Core.Taclet` constructor, and the printed rule it is.  In `Calculus/Core/Rules.lean`'s
order. -/
def printedOrigins : List (Lean.Name × PrintedOrigin) := [
  -- Step 1: unfold a storage read
  (``Core.Taclet.storageFieldRead_unfold_rightFst, .printed .storageFieldRead_unfold_rightFst),
  (``Core.Taclet.storageIndexRead_unfold_rightFst, .printed .storageIndexRead_unfold_rightFst),
  (``Core.Taclet.storageIndexRead_unfold_rightSndIndex, .printed .storageIndexRead_unfold_rightSndIndex),
  (``Core.Taclet.storageFieldRead_unfold_rightSndResult,
    .merged [.storageFieldRead_unfold_rightSndResult, .storageFieldWriteCaptureSrc]),
  (``Core.Taclet.storageIndexRead_unfold_rightSndResult,
    .merged [.storageIndexRead_unfold_rightSndResult, .storageIndexWriteStorageRefRhsCapture]),
  -- Step 2: decompose a storage write
  (``Core.Taclet.storageFieldWrite_unfold_leftFst, .printed .storageFieldWrite_unfold_leftFst),
  (``Core.Taclet.storageFieldWriteStorageRef_unfold_leftFst,
    .printed .storageFieldWriteStorageRef_unfold_leftFst),
  (``Core.Taclet.storageIndexWriteCaptureAllComplexRecv,
    .printed .storageIndexWriteCaptureAllComplexRecv),
  (``Core.Taclet.storageIndexWriteStorageRefCaptureAllComplexRecv,
    .printed .storageIndexWriteStorageRefCaptureAllComplexRecv),
  (``Core.Taclet.storageIndexWriteCaptureAllNonSimpleIndex,
    .printed .storageIndexWriteCaptureAllNonSimpleIndex),
  (``Core.Taclet.storageIndexWriteStorageRefCaptureAllNonSimpleIndex,
    .printed .storageIndexWriteStorageRefCaptureAllNonSimpleIndex),
  (``Core.Taclet.storageRootWriteValueRhsCapture, .printed .storageRootWriteValueRhsCapture),
  (``Core.Taclet.fieldWriteValueRhsCapture, .printed .fieldWriteValueRhsCapture),
  (``Core.Taclet.indexWriteValueRhsCapture, .printed .indexWriteValueRhsCapture),
  (``Core.Taclet.storageFieldDelete_unfold_leftFst, .printed .storageFieldDelete_unfold_leftFst),
  (``Core.Taclet.storageIndexDelete_unfold_leftFst, .printed .storageIndexDelete_unfold_leftFst),
  (``Core.Taclet.storageIndexDeleteNonSimpleIndexCapture, .leanOnly .keyTier),
  -- Declarations
  (``Core.Taclet.localValueDeclInitDrop, .leanOnly .keyTier),
  (``Core.Taclet.valueDeclSkip, .leanOnly .keyTier),
  (``Core.Taclet.storageLocalDeclInitDrop, .printed .storageLocalDeclInitDrop),
  (``Core.Taclet.storageLocalDeclSkip, .printed .storageLocalDeclSkip),
  (``Core.Taclet.memoryLocalDeclInitDrop, .printed .memoryLocalDeclInitDrop),
  (``Core.Taclet.memoryReferenceDeclFreshAlloc, .printed .memoryReferenceDeclFreshAlloc),
  -- Step 3: storage reads and writes as updates
  (``Core.Taclet.localValueAssign, .leanOnly .keyTier),
  (``Core.Taclet.storageRootReadSelect, .printed .storageRootReadSelect),
  (``Core.Taclet.storageFieldReadFind, .printed .storageFieldReadFind),
  (``Core.Taclet.storageIndexReadMappingFind, .printed .storageIndexReadMappingFind),
  (``Core.Taclet.storageIndexReadArrayFind, .printed .storageIndexReadArrayFind),
  (``Core.Taclet.storageRootWriteStore, .printed .storageRootWriteStore),
  (``Core.Taclet.storageRootWriteCopySource, .printed .storageRootWriteCopySource),
  (``Core.Taclet.storageFieldReadStoreRoot, .printed .storageFieldReadStoreRoot),
  (``Core.Taclet.storageIndexReadMappingStoreRoot, .printed .storageIndexReadMappingStoreRoot),
  (``Core.Taclet.storageIndexReadArrayStoreRoot, .printed .storageIndexReadArrayStoreRoot),
  (``Core.Taclet.storageFieldWriteSave, .printed .storageFieldWriteSave),
  (``Core.Taclet.storageFieldWriteCopySource, .printed .storageFieldWriteCopySource),
  (``Core.Taclet.storageIndexWriteMappingSave, .printed .storageIndexWriteMappingSave),
  (``Core.Taclet.storageIndexWriteArraySave, .printed .storageIndexWriteArraySave),
  (``Core.Taclet.storageIndexWriteMappingCopySource, .printed .storageIndexWriteMappingCopySource),
  (``Core.Taclet.storageIndexWriteArrayCopySource, .printed .storageIndexWriteArrayCopySource),
  (``Core.Taclet.storageLocalRootRebind, .printed .storageLocalRootRebind),
  (``Core.Taclet.storageFieldReadBindLocalRoot, .printed .storageFieldReadBindLocalRoot),
  (``Core.Taclet.storageIndexReadMappingBindLocalRoot, .printed .storageIndexReadMappingBindLocalRoot),
  (``Core.Taclet.storageIndexReadArrayBindLocalRoot, .printed .storageIndexReadArrayBindLocalRoot),
  (``Core.Taclet.storageIndexReadArrayBindLocalRootMappingElement,
    .printed .storageIndexReadArrayBindLocalRootMappingElement),
  (``Core.Taclet.storageRootDelete, .printed .storageRootDelete),
  (``Core.Taclet.storageFieldDelete, .printed .storageFieldDelete),
  (``Core.Taclet.storageIndexDelete, .printed .storageIndexDelete),
  (``Core.Taclet.storageIndexArrayDelete, .printed .storageIndexArrayDelete),
  -- lengths: the printed rules, as KeY, read `.length` as a member
  (``Core.Taclet.storageLengthRead, .printed .storageFieldReadFind),
  (``Core.Taclet.storageLengthRead_unfold_rightFst, .printed .storageFieldRead_unfold_rightFst),
  (``Core.Taclet.memoryLengthRead, .printed .memoryFieldRead),
  (``Core.Taclet.memoryLengthRead_unfold_rightFst, .printed .memoryFieldRead_unfold_rightFst),
  -- Operators: solkey's tiers, below what is printed
  (``Core.Taclet.binopAssignment, .leanOnly .keyTier),
  (``Core.Taclet.binopUnfoldLeft, .leanOnly .keyTier),
  (``Core.Taclet.binopUnfoldRight, .leanOnly .keyTier),
  (``Core.Taclet.logicalAndShortCircuitRhs, .leanOnly .keyTier),
  (``Core.Taclet.logicalOrShortCircuitRhs, .leanOnly .keyTier),
  -- the `-` instance is printed; `!` is a KeY tier
  (``Core.Taclet.unopAssignment, .printed .unaryMinusAssignment),
  (``Core.Taclet.unopCapture, .leanOnly .keyTier),
  -- The conditional
  (``Core.Taclet.ternaryToIf, .leanOnly .keyTier),
  (``Core.Taclet.ternaryCaptureCond, .leanOnly .keyTier),
  -- Compound assignment and `++`/`--`: printed as `op ∈ {+ - * / %}`
  -- once per target, a divisor-guarded rule where the update has to guard,
  -- and the post-increment on two targets
  (``Core.Taclet.localOpAssign, .merged [.localOpAssign, .localDivAssign]),
  (``Core.Taclet.storageRootOpAssign, .printed .storageRootOpAssign),
  (``Core.Taclet.storageFieldOpAssign, .printed .storageFieldOpAssign),
  (``Core.Taclet.storageIndexMappingOpAssign, .printed .storageIndexMappingOpAssign),
  (``Core.Taclet.storageIndexArrayOpAssign, .printed .storageIndexArrayOpAssign),
  (``Core.Taclet.memoryFieldOpAssign, .merged [.memoryFieldOpAssign, .memoryFieldDivAssign]),
  (``Core.Taclet.memoryIndexArrayOpAssign, .printed .memoryIndexArrayOpAssign),
  (``Core.Taclet.storageFieldOpAssignUnfoldLeftFst, .leanOnly .keyTier),
  (``Core.Taclet.storageIndexOpAssignUnfoldLeftFst, .leanOnly .keyTier),
  (``Core.Taclet.memoryFieldOpAssignUnfoldLeftFst, .leanOnly .keyTier),
  (``Core.Taclet.memoryIndexOpAssignUnfoldLeftFst, .leanOnly .keyTier),
  (``Core.Taclet.compoundAssignValueRhsCapture, .leanOnly .keyTier),
  (``Core.Taclet.localIncrement, .leanOnly .keyTier),
  (``Core.Taclet.storageRootIncrement, .printed .storageRootPostincrement),
  (``Core.Taclet.storageFieldIncrement, .leanOnly .keyTier),
  (``Core.Taclet.storageIndexIncrement, .leanOnly .keyTier),
  (``Core.Taclet.memoryFieldIncrement, .printed .memoryFieldPostincrement),
  (``Core.Taclet.memoryIndexArrayIncrement, .leanOnly .keyTier),
  (``Core.Taclet.storageFieldIncrementUnfoldLeftFst, .leanOnly .keyTier),
  (``Core.Taclet.storageIndexIncrementUnfoldLeftFst, .leanOnly .keyTier),
  (``Core.Taclet.memoryFieldIncrementUnfoldLeftFst, .leanOnly .keyTier),
  (``Core.Taclet.memoryIndexIncrementUnfoldLeftFst, .leanOnly .keyTier),
  (``Core.Taclet.localAssignIncrement, .leanOnly .keyTier),
  (``Core.Taclet.storageRootIncrementAssignment, .leanOnly .keyTier),
  (``Core.Taclet.storageFieldIncrementAssignment, .leanOnly .keyTier),
  (``Core.Taclet.storageIndexIncrementAssignment, .leanOnly .keyTier),
  (``Core.Taclet.memoryFieldIncrementAssignment, .leanOnly .keyTier),
  (``Core.Taclet.memoryIndexArrayIncrementAssignment, .leanOnly .keyTier),
  -- Arrays: the printed rules, as solkey, split by the element type
  (``Core.Taclet.storagePushValueSave, .printed .storagePushValueSave),
  (``Core.Taclet.storagePushValueCopySource, .printed .storagePushValueCopySource),
  (``Core.Taclet.storagePushLengthSave, .printed .storagePushLengthSave),
  (``Core.Taclet.storagePushLengthSaveReferenceElement,
    .printed .storagePushLengthSaveReferenceElement),
  (``Core.Taclet.storagePushValue_unfold_rightSndArgument,
    .printed .storagePushValue_unfold_rightSndArgument),
  (``Core.Taclet.storagePushValue_unfold_leftFstReceiver,
    .printed .storagePushValue_unfold_leftFstReceiver),
  (``Core.Taclet.storagePush_unfold_leftFstReceiver, .printed .storagePush_unfold_leftFstReceiver),
  (``Core.Taclet.storagePop_unfold_leftFstReceiver, .printed .storagePop_unfold_leftFstReceiver),
  (``Core.Taclet.storagePopSave, .printed .storagePopSave),
  (``Core.Taclet.storagePopSaveMappingElement, .printed .storagePopSaveMappingElement),
  (``Core.Taclet.storageLocalRootPush_unfold_leftFstReceiver,
    .printed .storageLocalRootPush_unfold_leftFstReceiver),
  (``Core.Taclet.storageLocalRootPushBind, .printed .storageLocalRootPushBind),
  (``Core.Taclet.storageLocalRootPushBindMappingElement,
    .printed .storageLocalRootPushBindMappingElement),
  -- Transfer
  (``Core.Taclet.transfer_unfold_leftFstReceiver, .printed .transfer_unfold_leftFstReceiver),
  (``Core.Taclet.transfer_unfold_rightSndArgument, .printed .transfer_unfold_rightSndArgument),
  (``Core.Taclet.transferNoCallbackBox, .printed .transferNoCallback),
  -- `send`: solkey's taclets, not printed
  (``Core.Taclet.send_unfold_leftFstReceiver, .leanOnly .keyTier),
  (``Core.Taclet.send_unfold_rightSndArgument, .leanOnly .keyTier),
  (``Core.Taclet.sendNoCallbackBox, .leanOnly .keyTier),
  (``Core.Taclet.sendNoCallbackDiamond, .leanOnly .keyTier),
  -- Memory
  (``Core.Taclet.memoryFieldRead_unfold_rightFst, .printed .memoryFieldRead_unfold_rightFst),
  (``Core.Taclet.memoryIndexRead_unfold_rightFst, .printed .memoryIndexRead_unfold_rightFst),
  (``Core.Taclet.memoryIndexRead_unfold_rightSndIndex, .printed .memoryIndexRead_unfold_rightSndIndex),
  (``Core.Taclet.memoryFieldRead, .printed .memoryFieldRead),
  (``Core.Taclet.memoryIndexReadArrayValue, .printed .memoryIndexReadArrayValue),
  (``Core.Taclet.memoryRootRebind, .printed .memoryRootRebind),
  (``Core.Taclet.memoryFieldReadAliasRoot, .printed .memoryFieldRead),
  (``Core.Taclet.memoryIndexReadArrayMemory, .printed .memoryIndexReadArrayMemory),
  (``Core.Taclet.memoryFieldWrite, .printed .memoryFieldWrite),
  (``Core.Taclet.memoryIndexWriteArray, .printed .memoryIndexWriteArray),
  (``Core.Taclet.memoryFieldWriteCopy, .printed .memoryFieldWrite),
  (``Core.Taclet.memoryIndexWriteCopy, .printed .memoryIndexWriteArray),
  (``Core.Taclet.memoryFieldWrite_unfold_leftFst,
    .merged [.memoryFieldWrite_unfold_leftFst, .memoryFieldWriteMemRef_unfold_leftFst]),
  (``Core.Taclet.memoryIndexWriteCaptureAllComplexRecv,
    .printed .memoryIndexWriteCaptureAllComplexRecv),
  (``Core.Taclet.memoryIndexWriteMemRefCaptureAllComplexRecv,
    .printed .memoryIndexWriteMemRefCaptureAllComplexRecv),
  (``Core.Taclet.memoryIndexWriteCaptureAllNonSimpleIndex,
    .printed .memoryIndexWriteCaptureAllNonSimpleIndex),
  (``Core.Taclet.memoryIndexWriteMemRefCaptureAllNonSimpleIndex,
    .printed .memoryIndexWriteMemRefCaptureAllNonSimpleIndex),
  (``Core.Taclet.memoryFieldWriteUnfoldSource, .printed .fieldWriteValueRhsCapture),
  (``Core.Taclet.memoryIndexWriteUnfoldSource, .printed .indexWriteValueRhsCapture),
  (``Core.Taclet.memoryRootDeleteFreshRebind, .printed .memoryRootDeleteFreshRebind),
  (``Core.Taclet.memoryFieldDeletePrimitive, .printed .memoryFieldDeletePrimitive),
  (``Core.Taclet.memoryFieldDeleteReference, .printed .memoryFieldDeleteReference),
  (``Core.Taclet.memoryIndexDeletePrimitive, .printed .memoryIndexDeletePrimitive),
  (``Core.Taclet.memoryIndexDeleteReference, .printed .memoryIndexDeleteReference),
  (``Core.Taclet.memoryFieldDelete_unfold_leftFst, .printed .memoryFieldDelete_unfold_leftFst),
  (``Core.Taclet.memoryIndexDelete_unfold_leftFst, .printed .memoryIndexDelete_unfold_leftFst),
  (``Core.Taclet.memoryIndexDeleteNonSimpleIndexCapture, .leanOnly .keyTier),
  (``Core.Taclet.memoryArrayFreshAlloc, .printed .memoryArrayFreshAlloc),
  (``Core.Taclet.newArrayCapture, .printed .newArrayCapture),
  -- Storage and memory
  (``Core.Taclet.memoryStorageCopy, .printed .memoryStorageCopy),
  (``Core.Taclet.memoryStorageCopyUnfold, .printed .memoryStorageCopyUnfold),
  (``Core.Taclet.memoryToStorageStoreRoot, .printed .memoryToStorageStoreRoot),
  (``Core.Taclet.memoryToStorageFieldCopyRoot,
    .merged [.memoryToStorageFieldCopyRoot, .memoryToStorageFieldCopyField]),
  (``Core.Taclet.memoryToStorageIndexMappingCopyRoot, .printed .memoryToStorageIndexMappingCopyRoot),
  (``Core.Taclet.memoryToStorageIndexArrayCopyRoot, .printed .memoryToStorageIndexArrayCopyRoot),
  (``Core.Taclet.memoryToStorageField_unfold_leftFst, .printed .memoryToStorageField_unfold_leftFst),
  (``Core.Taclet.memoryToStorageIndexCaptureAllComplexRecv,
    .printed .memoryToStorageIndexCaptureAllComplexRecv),
  (``Core.Taclet.memoryToStorageIndexCaptureAllNonSimpleIndex,
    .printed .memoryToStorageIndexCaptureAllNonSimpleIndex),
  -- Control flow
  (``Core.Taclet.ifElseUnfold, .printed .ifElseUnfold),
  (``Core.Taclet.ifElseSplit, .printed .ifElseSplit),
  (``Core.Taclet.requireConditionCapture, .printed .requireConditionCapture),
  (``Core.Taclet.requireSimple, .printed .requireSimple),
  (``Core.Taclet.assertConditionCapture, .printed .assertConditionCapture),
  (``Core.Taclet.assertSimple, .printed .assertSimple),
  (``Core.Taclet.revertBox, .printed .revertBox),
  (``Core.Taclet.revertDiamond, .printed .revertDiamond),
  -- Calls: none printed; solkey has `functionBodyExpand`, `internalCallExpand`
  (``Core.Taclet.functionBodyExpand, .leanOnly .keyTier),
  (``Core.Taclet.internalCallExpand, .leanOnly .keyTier),
  -- External calls: none printed; solkey has `tryCallNoCallbackBox`
  (``Core.Taclet.tryCallNoCallbackBox, .leanOnly .keyTier),
  -- Blocks: none printed; solkey has `blockEmpty`
  (``Core.Taclet.blockEmpty, .leanOnly .keyTier) ]

#check_constructor_table Core.Taclet, printedOrigins.map Prod.fst

/-- The rules solkey does not have (`LeanTaclet`), and the printed rule each is.
The capture of an argument (`unfoldArgument`), a `try` and a payment under
the diamond, a loop at its bound and one with an invariant, have no taclet
and no printed rule; `whileUnwind`, `whileInvariantBox` and
`whileInvariantDiamond` are solkey's, past the pinned checkout, and not
printed. -/
def leanPrintedOrigins : List (Lean.Name × PrintedOrigin) := [
  (``Core.LeanTaclet.functionCallArgCapture, .leanOnly .calculus),
  (``Core.LeanTaclet.tryCallDiamond, .leanOnly .calculus),
  (``Core.LeanTaclet.transferDiamond, .leanOnly .calculus),
  (``Core.LeanTaclet.whileUnwind, .leanOnly .keyTier),
  (``Core.LeanTaclet.loopExit, .leanOnly .calculus),
  (``Core.LeanTaclet.whileInvariantBox, .leanOnly .keyTier),
  (``Core.LeanTaclet.whileInvariantDiamond, .leanOnly .keyTier),
  (``Core.LeanTaclet.whileClose, .leanOnly .calculus),
  (``Core.LeanTaclet.whileNoVariantDiamond, .leanOnly .calculus) ]

#check_constructor_table Core.LeanTaclet, leanPrintedOrigins.map Prod.fst

/-- The callback taclets and the printed `transferWithCallbackBox` rule;
solkey's `tryCallWithCallbackBox` and `sendWithCallbackBox` are not printed. -/
def callbackPrintedOrigins : List (Lean.Name × PrintedOrigin) := [
  (``Core.CallbackTaclet.transferWithCallbackBox, .printed .transferWithCallbackBox),
  (``Core.CallbackTaclet.sendWithCallbackBox, .leanOnly .keyTier),
  (``Core.CallbackTaclet.tryCallWithCallbackBox, .leanOnly .keyTier) ]

#check_constructor_table Core.CallbackTaclet, callbackPrintedOrigins.map Prod.fst

/-! ## Which printed rules the table claims -/

/-- Whether some row names the printed rule. -/
def claims (p : PrintedRule) : Bool :=
  (printedOrigins ++ leanPrintedOrigins ++ callbackPrintedOrigins).any fun r => r.2.rules.contains p

/-- Every printed rule some row names, in `PrintedRule.all`'s order. -/
def claimedPrintedRules : List PrintedRule := PrintedRule.all.filter claims

/-- The printed rules of kind `rule` that **no** constructor claims.  The
reasons are `RuleShapes.unclaimedTaclets`', rule for rule: the printed rules are
what solkey runs, and the typed syntax takes a memory path
as a source in place, so nothing captures one (four); has no strategy for the
literal-condition `if` shortcuts (three); and books a payment under the box
only, the diamond closing to `false` (`transferWithCallbackDiamond`).  The
callback `transfer` rule is `callbackPrintedOrigins`'. -/
def unclaimedRules : List PrintedRule :=
  [ .memoryFieldRead_unfold_rightSndResult, .memoryIndexRead_unfold_rightSndResult,
    .memoryFieldWriteCaptureSrc, .memoryIndexWriteMemRefRhsCapture,
    .ifElseTrue, .ifElseFalse, .ifElseNegated, .transferWithCallbackDiamond ]

/-- **The coverage fact**: a printed rule is claimed exactly when it is of kind
`rule` and not excused above.  A printed rule Lean never ports
fails this; so does a row that names a template, a rejected or unimplemented
rule, or the first-order axiom. -/
theorem printed_rules_partitioned :
    PrintedRule.all.all
      (fun p => claims p != (p.kind != .rule || unclaimedRules.contains p)) = true := by
  decide +kernel

theorem printedRules_count : PrintedRule.all.length = 135 := by decide +kernel

theorem claimedPrintedRules_count : claimedPrintedRules.length = 117 := by decide +kernel

theorem unclaimedRules_count : unclaimedRules.length = 8 := by decide +kernel

/-! ## The constructors with no printed rule -/

/-- The constructors whose origin is `leanOnly why`. -/
def leanOnlyRows (why : LeanOnlyReason) : List Lean.Name :=
  ((printedOrigins ++ leanPrintedOrigins).filter fun r => r.2 == .leanOnly why).map Prod.fst

theorem leanOnly_keyTier_count : (leanOnlyRows .keyTier).length = 43 := by decide +kernel

theorem leanOnly_calculus_count : (leanOnlyRows .calculus).length = 6 := by decide +kernel

end PrintedRules
end Solidity
