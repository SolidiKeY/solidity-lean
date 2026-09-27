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
to the constructor list, so a constructor added to `Rules.lean` does not build
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
  | transferNoCallbackBox
  | transferNoCallbackDiamond
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

namespace PrintedRule

/-- The printed spelling. -/
def name : PrintedRule -> String
  | .unfold_rightFst => "unfold_rightFst"
  | .unfold_rightSnd => "unfold_rightSnd"
  | .unfold_rightSndResult => "unfold_rightSndResult"
  | .unfold_leftFst => "unfold_leftFst"
  | .unfold_leftSnd => "unfold_leftSnd"
  | .unfold_source => "unfold_source"
  | .fieldWriteValueRhsCapture => "fieldWriteValueRhsCapture"
  | .indexWriteValueRhsCapture => "indexWriteValueRhsCapture"
  | .storageFieldRead_unfold_rightFst => "storageFieldRead_unfold_rightFst"
  | .storageIndexRead_unfold_rightFst => "storageIndexRead_unfold_rightFst"
  | .storageIndexRead_unfold_rightSndIndex => "storageIndexRead_unfold_rightSndIndex"
  | .storagePushValue_unfold_rightSndArgument => "storagePushValue_unfold_rightSndArgument"
  | .storageFieldRead_unfold_rightSndResult => "storageFieldRead_unfold_rightSndResult"
  | .storageIndexRead_unfold_rightSndResult => "storageIndexRead_unfold_rightSndResult"
  | .storageFieldWrite_unfold_leftFst => "storageFieldWrite_unfold_leftFst"
  | .storageIndexWriteCaptureAllComplexRecv => "storageIndexWriteCaptureAllComplexRecv"
  | .storageFieldWriteStorageRef_unfold_leftFst => "storageFieldWriteStorageRef_unfold_leftFst"
  | .storageIndexWriteStorageRefCaptureAllComplexRecv => "storageIndexWriteStorageRefCaptureAllComplexRecv"
  | .storageFieldDelete_unfold_leftFst => "storageFieldDelete_unfold_leftFst"
  | .storageIndexDelete_unfold_leftFst => "storageIndexDelete_unfold_leftFst"
  | .storagePushValue_unfold_leftFstReceiver => "storagePushValue_unfold_leftFstReceiver"
  | .storagePush_unfold_leftFstReceiver => "storagePush_unfold_leftFstReceiver"
  | .storagePop_unfold_leftFstReceiver => "storagePop_unfold_leftFstReceiver"
  | .storageLocalRootPush_unfold_leftFstReceiver => "storageLocalRootPush_unfold_leftFstReceiver"
  | .storageIndexWriteCaptureAllNonSimpleIndex => "storageIndexWriteCaptureAllNonSimpleIndex"
  | .storageIndexWriteStorageRefCaptureAllNonSimpleIndex => "storageIndexWriteStorageRefCaptureAllNonSimpleIndex"
  | .storageRootWriteValueRhsCapture => "storageRootWriteValueRhsCapture"
  | .storageFieldWriteCaptureSrc => "storageFieldWriteCaptureSrc"
  | .storageIndexWriteStorageRefRhsCapture => "storageIndexWriteStorageRefRhsCapture"
  | .storageLocalDeclInitDrop => "storageLocalDeclInitDrop"
  | .storageLocalDeclSkip => "storageLocalDeclSkip"
  | .storageFieldWriteSave => "storageFieldWriteSave"
  | .storageFieldWriteCopySource => "storageFieldWriteCopySource"
  | .storageRootWriteStore => "storageRootWriteStore"
  | .storageRootWriteCopySource => "storageRootWriteCopySource"
  | .storageLocalRootRebind => "storageLocalRootRebind"
  | .storageFieldReadFind => "storageFieldReadFind"
  | .storageRootReadSelect => "storageRootReadSelect"
  | .storageFieldReadBindLocalRoot => "storageFieldReadBindLocalRoot"
  | .storageFieldReadStoreRoot => "storageFieldReadStoreRoot"
  | .storageRootDelete => "storageRootDelete"
  | .storageFieldDelete => "storageFieldDelete"
  | .storageIndexDelete => "storageIndexDelete"
  | .storageIndexArrayDelete => "storageIndexArrayDelete"
  | .storageIndexWriteMappingSave => "storageIndexWriteMappingSave"
  | .storageIndexWriteMappingCopySource => "storageIndexWriteMappingCopySource"
  | .storageIndexReadMappingFind => "storageIndexReadMappingFind"
  | .storageIndexReadMappingBindLocalRoot => "storageIndexReadMappingBindLocalRoot"
  | .storageIndexReadMappingStoreRoot => "storageIndexReadMappingStoreRoot"
  | .storageIndexWriteArraySave => "storageIndexWriteArraySave"
  | .storageIndexWriteArrayCopySource => "storageIndexWriteArrayCopySource"
  | .storageIndexReadArrayFind => "storageIndexReadArrayFind"
  | .storageIndexReadArrayBindLocalRoot => "storageIndexReadArrayBindLocalRoot"
  | .storageIndexReadArrayBindLocalRootMappingElement => "storageIndexReadArrayBindLocalRootMappingElement"
  | .storageIndexReadArrayStoreRoot => "storageIndexReadArrayStoreRoot"
  | .storagePushValueSave => "storagePushValueSave"
  | .storagePushValueCopySource => "storagePushValueCopySource"
  | .storagePushLengthSave => "storagePushLengthSave"
  | .storagePushLengthSaveReferenceElement => "storagePushLengthSaveReferenceElement"
  | .storageLocalRootPushBind => "storageLocalRootPushBind"
  | .storageLocalRootPushBindMappingElement => "storageLocalRootPushBindMappingElement"
  | .storagePopSave => "storagePopSave"
  | .storagePopSaveMappingElement => "storagePopSaveMappingElement"
  | .sizeNotNegative => "sizeNotNegative"
  | .indexWriteInnerNonSimpleIndexCapture => "indexWriteInnerNonSimpleIndexCapture"
  | .indexReadInnerNonSimpleIndexCapture => "indexReadInnerNonSimpleIndexCapture"
  | .memoryFieldRead_unfold_rightFst => "memoryFieldRead_unfold_rightFst"
  | .memoryIndexRead_unfold_rightFst => "memoryIndexRead_unfold_rightFst"
  | .memoryIndexRead_unfold_rightSndIndex => "memoryIndexRead_unfold_rightSndIndex"
  | .memoryFieldRead_unfold_rightSndResult => "memoryFieldRead_unfold_rightSndResult"
  | .memoryIndexRead_unfold_rightSndResult => "memoryIndexRead_unfold_rightSndResult"
  | .memoryFieldWrite_unfold_leftFst => "memoryFieldWrite_unfold_leftFst"
  | .memoryIndexWriteCaptureAllComplexRecv => "memoryIndexWriteCaptureAllComplexRecv"
  | .memoryFieldWriteMemRef_unfold_leftFst => "memoryFieldWriteMemRef_unfold_leftFst"
  | .memoryIndexWriteMemRefCaptureAllComplexRecv => "memoryIndexWriteMemRefCaptureAllComplexRecv"
  | .newArrayCapture => "newArrayCapture"
  | .memoryFieldDelete_unfold_leftFst => "memoryFieldDelete_unfold_leftFst"
  | .memoryIndexDelete_unfold_leftFst => "memoryIndexDelete_unfold_leftFst"
  | .memoryIndexWriteCaptureAllNonSimpleIndex => "memoryIndexWriteCaptureAllNonSimpleIndex"
  | .memoryIndexWriteMemRefCaptureAllNonSimpleIndex => "memoryIndexWriteMemRefCaptureAllNonSimpleIndex"
  | .memoryFieldWriteCaptureSrc => "memoryFieldWriteCaptureSrc"
  | .memoryIndexWriteMemRefRhsCapture => "memoryIndexWriteMemRefRhsCapture"
  | .memoryLocalDeclInitDrop => "memoryLocalDeclInitDrop"
  | .memoryReferenceDeclFreshAlloc => "memoryReferenceDeclFreshAlloc"
  | .memoryArrayFreshAlloc => "memoryArrayFreshAlloc"
  | .memoryFieldWrite => "memoryFieldWrite"
  | .memoryRootRebind => "memoryRootRebind"
  | .memoryFieldRead => "memoryFieldRead"
  | .memoryRootDeleteFreshRebind => "memoryRootDeleteFreshRebind"
  | .memoryFieldDeletePrimitive => "memoryFieldDeletePrimitive"
  | .memoryFieldDeleteReference => "memoryFieldDeleteReference"
  | .memoryIndexWriteArray => "memoryIndexWriteArray"
  | .memoryIndexReadArrayValue => "memoryIndexReadArrayValue"
  | .memoryIndexReadArrayMemory => "memoryIndexReadArrayMemory"
  | .memoryIndexDeletePrimitive => "memoryIndexDeletePrimitive"
  | .memoryIndexDeleteReference => "memoryIndexDeleteReference"
  | .memoryStorageCopyUnfold => "memoryStorageCopyUnfold"
  | .memoryStorageCopy => "memoryStorageCopy"
  | .memoryToStorageField_unfold_leftFst => "memoryToStorageField_unfold_leftFst"
  | .memoryToStorageIndexCaptureAllComplexRecv => "memoryToStorageIndexCaptureAllComplexRecv"
  | .memoryToStorageIndexCaptureAllNonSimpleIndex => "memoryToStorageIndexCaptureAllNonSimpleIndex"
  | .memoryToStorageFieldCopyRoot => "memoryToStorageFieldCopyRoot"
  | .memoryToStorageFieldCopyField => "memoryToStorageFieldCopyField"
  | .memoryToStorageIndexMappingCopyRoot => "memoryToStorageIndexMappingCopyRoot"
  | .memoryToStorageIndexArrayCopyRoot => "memoryToStorageIndexArrayCopyRoot"
  | .memoryToStorageStoreRoot => "memoryToStorageStoreRoot"
  | .requireConditionCapture => "requireConditionCapture"
  | .assertConditionCapture => "assertConditionCapture"
  | .requireSimple => "requireSimple"
  | .assertSimple => "assertSimple"
  | .revertDiamond => "revertDiamond"
  | .revertBox => "revertBox"
  | .ifElseUnfold => "ifElseUnfold"
  | .ifElseSplit => "ifElseSplit"
  | .ifElseTrue => "ifElseTrue"
  | .ifElseFalse => "ifElseFalse"
  | .ifElseNegated => "ifElseNegated"
  | .transfer_unfold_leftFstReceiver => "transfer_unfold_leftFstReceiver"
  | .transfer_unfold_rightSndArgument => "transfer_unfold_rightSndArgument"
  | .transferNoCallbackBox => "transferNoCallbackBox"
  | .transferNoCallbackDiamond => "transferNoCallbackDiamond"
  | .transferWithCallbackBox => "transferWithCallbackBox"
  | .transferWithCallbackDiamond => "transferWithCallbackDiamond"
  | .localOpAssign => "localOpAssign"
  | .storageRootOpAssign => "storageRootOpAssign"
  | .storageFieldOpAssign => "storageFieldOpAssign"
  | .storageIndexMappingOpAssign => "storageIndexMappingOpAssign"
  | .localDivAssign => "localDivAssign"
  | .unaryMinusAssignment => "unaryMinusAssignment"
  | .storageIndexArrayOpAssign => "storageIndexArrayOpAssign"
  | .storageRootPostincrement => "storageRootPostincrement"
  | .memoryFieldOpAssign => "memoryFieldOpAssign"
  | .memoryFieldDivAssign => "memoryFieldDivAssign"
  | .memoryIndexArrayOpAssign => "memoryIndexArrayOpAssign"
  | .memoryFieldPostincrement => "memoryFieldPostincrement"
  | .storageRootIncrement => "storageRootIncrement"

/-- Which kind of declaration the name is, read off its `tags`. -/
def kind : PrintedRule -> PrintedRuleKind
  | .unfold_rightFst | .unfold_rightSnd | .unfold_rightSndResult
  | .unfold_leftFst | .unfold_leftSnd | .unfold_source => .template
  | .indexWriteInnerNonSimpleIndexCapture | .indexReadInnerNonSimpleIndexCapture => .rejected
  | .storageRootIncrement => .unimplemented
  | .sizeNotNegative => .firstOrder
  | _ => .rule

/-- Every constructor, in declaration order. -/
def all : List PrintedRule :=
  [ .unfold_rightFst,
    .unfold_rightSnd,
    .unfold_rightSndResult,
    .unfold_leftFst,
    .unfold_leftSnd,
    .unfold_source,
    .fieldWriteValueRhsCapture,
    .indexWriteValueRhsCapture,
    .storageFieldRead_unfold_rightFst,
    .storageIndexRead_unfold_rightFst,
    .storageIndexRead_unfold_rightSndIndex,
    .storagePushValue_unfold_rightSndArgument,
    .storageFieldRead_unfold_rightSndResult,
    .storageIndexRead_unfold_rightSndResult,
    .storageFieldWrite_unfold_leftFst,
    .storageIndexWriteCaptureAllComplexRecv,
    .storageFieldWriteStorageRef_unfold_leftFst,
    .storageIndexWriteStorageRefCaptureAllComplexRecv,
    .storageFieldDelete_unfold_leftFst,
    .storageIndexDelete_unfold_leftFst,
    .storagePushValue_unfold_leftFstReceiver,
    .storagePush_unfold_leftFstReceiver,
    .storagePop_unfold_leftFstReceiver,
    .storageLocalRootPush_unfold_leftFstReceiver,
    .storageIndexWriteCaptureAllNonSimpleIndex,
    .storageIndexWriteStorageRefCaptureAllNonSimpleIndex,
    .storageRootWriteValueRhsCapture,
    .storageFieldWriteCaptureSrc,
    .storageIndexWriteStorageRefRhsCapture,
    .storageLocalDeclInitDrop,
    .storageLocalDeclSkip,
    .storageFieldWriteSave,
    .storageFieldWriteCopySource,
    .storageRootWriteStore,
    .storageRootWriteCopySource,
    .storageLocalRootRebind,
    .storageFieldReadFind,
    .storageRootReadSelect,
    .storageFieldReadBindLocalRoot,
    .storageFieldReadStoreRoot,
    .storageRootDelete,
    .storageFieldDelete,
    .storageIndexDelete,
    .storageIndexArrayDelete,
    .storageIndexWriteMappingSave,
    .storageIndexWriteMappingCopySource,
    .storageIndexReadMappingFind,
    .storageIndexReadMappingBindLocalRoot,
    .storageIndexReadMappingStoreRoot,
    .storageIndexWriteArraySave,
    .storageIndexWriteArrayCopySource,
    .storageIndexReadArrayFind,
    .storageIndexReadArrayBindLocalRoot,
    .storageIndexReadArrayBindLocalRootMappingElement,
    .storageIndexReadArrayStoreRoot,
    .storagePushValueSave,
    .storagePushValueCopySource,
    .storagePushLengthSave,
    .storagePushLengthSaveReferenceElement,
    .storageLocalRootPushBind,
    .storageLocalRootPushBindMappingElement,
    .storagePopSave,
    .storagePopSaveMappingElement,
    .sizeNotNegative,
    .indexWriteInnerNonSimpleIndexCapture,
    .indexReadInnerNonSimpleIndexCapture,
    .memoryFieldRead_unfold_rightFst,
    .memoryIndexRead_unfold_rightFst,
    .memoryIndexRead_unfold_rightSndIndex,
    .memoryFieldRead_unfold_rightSndResult,
    .memoryIndexRead_unfold_rightSndResult,
    .memoryFieldWrite_unfold_leftFst,
    .memoryIndexWriteCaptureAllComplexRecv,
    .memoryFieldWriteMemRef_unfold_leftFst,
    .memoryIndexWriteMemRefCaptureAllComplexRecv,
    .newArrayCapture,
    .memoryFieldDelete_unfold_leftFst,
    .memoryIndexDelete_unfold_leftFst,
    .memoryIndexWriteCaptureAllNonSimpleIndex,
    .memoryIndexWriteMemRefCaptureAllNonSimpleIndex,
    .memoryFieldWriteCaptureSrc,
    .memoryIndexWriteMemRefRhsCapture,
    .memoryLocalDeclInitDrop,
    .memoryReferenceDeclFreshAlloc,
    .memoryArrayFreshAlloc,
    .memoryFieldWrite,
    .memoryRootRebind,
    .memoryFieldRead,
    .memoryRootDeleteFreshRebind,
    .memoryFieldDeletePrimitive,
    .memoryFieldDeleteReference,
    .memoryIndexWriteArray,
    .memoryIndexReadArrayValue,
    .memoryIndexReadArrayMemory,
    .memoryIndexDeletePrimitive,
    .memoryIndexDeleteReference,
    .memoryStorageCopyUnfold,
    .memoryStorageCopy,
    .memoryToStorageField_unfold_leftFst,
    .memoryToStorageIndexCaptureAllComplexRecv,
    .memoryToStorageIndexCaptureAllNonSimpleIndex,
    .memoryToStorageFieldCopyRoot,
    .memoryToStorageFieldCopyField,
    .memoryToStorageIndexMappingCopyRoot,
    .memoryToStorageIndexArrayCopyRoot,
    .memoryToStorageStoreRoot,
    .requireConditionCapture,
    .assertConditionCapture,
    .requireSimple,
    .assertSimple,
    .revertDiamond,
    .revertBox,
    .ifElseUnfold,
    .ifElseSplit,
    .ifElseTrue,
    .ifElseFalse,
    .ifElseNegated,
    .transfer_unfold_leftFstReceiver,
    .transfer_unfold_rightSndArgument,
    .transferNoCallbackBox,
    .transferNoCallbackDiamond,
    .transferWithCallbackBox,
    .transferWithCallbackDiamond,
    .localOpAssign,
    .storageRootOpAssign,
    .storageFieldOpAssign,
    .storageIndexMappingOpAssign,
    .localDivAssign,
    .unaryMinusAssignment,
    .storageIndexArrayOpAssign,
    .storageRootPostincrement,
    .memoryFieldOpAssign,
    .memoryFieldDivAssign,
    .memoryIndexArrayOpAssign,
    .memoryFieldPostincrement,
    .storageRootIncrement ]

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

/-- Every `Taclet` constructor, and the printed rule it is.  In `Rules.lean`'s
order. -/
def printedOrigins : List (Lean.Name × PrintedOrigin) := [
  -- Step 1: unfold a storage read
  (``Taclet.storageFieldRead_unfold_rightFst, .printed .storageFieldRead_unfold_rightFst),
  (``Taclet.storageIndexRead_unfold_rightFst, .printed .storageIndexRead_unfold_rightFst),
  (``Taclet.storageIndexRead_unfold_rightSndIndex, .printed .storageIndexRead_unfold_rightSndIndex),
  (``Taclet.storageFieldRead_unfold_rightSndResult,
    .merged [.storageFieldRead_unfold_rightSndResult, .storageFieldWriteCaptureSrc]),
  (``Taclet.storageIndexRead_unfold_rightSndResult,
    .merged [.storageIndexRead_unfold_rightSndResult, .storageIndexWriteStorageRefRhsCapture]),
  -- Step 2: decompose a storage write
  (``Taclet.storageFieldWrite_unfold_leftFst, .printed .storageFieldWrite_unfold_leftFst),
  (``Taclet.storageFieldWriteStorageRef_unfold_leftFst,
    .printed .storageFieldWriteStorageRef_unfold_leftFst),
  (``Taclet.storageIndexWriteCaptureAllComplexRecv,
    .printed .storageIndexWriteCaptureAllComplexRecv),
  (``Taclet.storageIndexWriteStorageRefCaptureAllComplexRecv,
    .printed .storageIndexWriteStorageRefCaptureAllComplexRecv),
  (``Taclet.storageIndexWriteCaptureAllNonSimpleIndex,
    .printed .storageIndexWriteCaptureAllNonSimpleIndex),
  (``Taclet.storageIndexWriteStorageRefCaptureAllNonSimpleIndex,
    .printed .storageIndexWriteStorageRefCaptureAllNonSimpleIndex),
  (``Taclet.storageRootWriteValueRhsCapture, .printed .storageRootWriteValueRhsCapture),
  (``Taclet.fieldWriteValueRhsCapture, .printed .fieldWriteValueRhsCapture),
  (``Taclet.indexWriteValueRhsCapture, .printed .indexWriteValueRhsCapture),
  (``Taclet.storageFieldDelete_unfold_leftFst, .printed .storageFieldDelete_unfold_leftFst),
  (``Taclet.storageIndexDelete_unfold_leftFst, .printed .storageIndexDelete_unfold_leftFst),
  (``Taclet.storageIndexDeleteNonSimpleIndexCapture, .leanOnly .keyTier),
  -- Declarations
  (``Taclet.localValueDeclInitDrop, .leanOnly .keyTier),
  (``Taclet.valueDeclSkip, .leanOnly .keyTier),
  (``Taclet.storageLocalDeclInitDrop, .printed .storageLocalDeclInitDrop),
  (``Taclet.storageLocalDeclSkip, .printed .storageLocalDeclSkip),
  (``Taclet.memoryLocalDeclInitDrop, .printed .memoryLocalDeclInitDrop),
  (``Taclet.memoryReferenceDeclFreshAlloc, .printed .memoryReferenceDeclFreshAlloc),
  -- Step 3: storage reads and writes as updates
  (``Taclet.localValueAssign, .leanOnly .keyTier),
  (``Taclet.storageRootReadSelect, .printed .storageRootReadSelect),
  (``Taclet.storageFieldReadFind, .printed .storageFieldReadFind),
  (``Taclet.storageIndexReadMappingFind, .printed .storageIndexReadMappingFind),
  (``Taclet.storageIndexReadArrayFind, .printed .storageIndexReadArrayFind),
  (``Taclet.storageRootWriteStore, .printed .storageRootWriteStore),
  (``Taclet.storageRootWriteCopySource, .printed .storageRootWriteCopySource),
  (``Taclet.storageFieldReadStoreRoot, .printed .storageFieldReadStoreRoot),
  (``Taclet.storageIndexReadMappingStoreRoot, .printed .storageIndexReadMappingStoreRoot),
  (``Taclet.storageIndexReadArrayStoreRoot, .printed .storageIndexReadArrayStoreRoot),
  (``Taclet.storageFieldWriteSave, .printed .storageFieldWriteSave),
  (``Taclet.storageFieldWriteCopySource, .printed .storageFieldWriteCopySource),
  (``Taclet.storageIndexWriteMappingSave, .printed .storageIndexWriteMappingSave),
  (``Taclet.storageIndexWriteArraySave, .printed .storageIndexWriteArraySave),
  (``Taclet.storageIndexWriteMappingCopySource, .printed .storageIndexWriteMappingCopySource),
  (``Taclet.storageIndexWriteArrayCopySource, .printed .storageIndexWriteArrayCopySource),
  (``Taclet.storageLocalRootRebind, .printed .storageLocalRootRebind),
  (``Taclet.storageFieldReadBindLocalRoot, .printed .storageFieldReadBindLocalRoot),
  (``Taclet.storageIndexReadMappingBindLocalRoot, .printed .storageIndexReadMappingBindLocalRoot),
  (``Taclet.storageIndexReadArrayBindLocalRoot, .printed .storageIndexReadArrayBindLocalRoot),
  (``Taclet.storageIndexReadArrayBindLocalRootMappingElement,
    .printed .storageIndexReadArrayBindLocalRootMappingElement),
  (``Taclet.storageRootDelete, .printed .storageRootDelete),
  (``Taclet.storageFieldDelete, .printed .storageFieldDelete),
  (``Taclet.storageIndexDelete, .printed .storageIndexDelete),
  (``Taclet.storageIndexArrayDelete, .printed .storageIndexArrayDelete),
  -- lengths: the printed rules, as KeY, read `.length` as a member
  (``Taclet.storageLengthRead, .printed .storageFieldReadFind),
  (``Taclet.storageLengthRead_unfold_rightFst, .printed .storageFieldRead_unfold_rightFst),
  (``Taclet.memoryLengthRead, .printed .memoryFieldRead),
  (``Taclet.memoryLengthRead_unfold_rightFst, .printed .memoryFieldRead_unfold_rightFst),
  -- Operators: solkey's tiers, below what is printed
  (``Taclet.binopAssignment, .leanOnly .keyTier),
  (``Taclet.binopUnfoldLeft, .leanOnly .keyTier),
  (``Taclet.binopUnfoldRight, .leanOnly .keyTier),
  (``Taclet.logicalAndShortCircuitRhs, .leanOnly .keyTier),
  (``Taclet.logicalOrShortCircuitRhs, .leanOnly .keyTier),
  -- the `-` instance is printed; `!` is a KeY tier
  (``Taclet.unopAssignment, .printed .unaryMinusAssignment),
  (``Taclet.unopCapture, .leanOnly .keyTier),
  -- The conditional
  (``Taclet.ternaryToIf, .leanOnly .keyTier),
  (``Taclet.ternaryCaptureCond, .leanOnly .keyTier),
  -- Compound assignment and `++`/`--`: printed as `op ∈ {+ - * / %}`
  -- once per target, a divisor-guarded rule where the update has to guard,
  -- and the post-increment on two targets
  (``Taclet.localOpAssign, .merged [.localOpAssign, .localDivAssign]),
  (``Taclet.storageRootOpAssign, .printed .storageRootOpAssign),
  (``Taclet.storageFieldOpAssign, .printed .storageFieldOpAssign),
  (``Taclet.storageIndexMappingOpAssign, .printed .storageIndexMappingOpAssign),
  (``Taclet.storageIndexArrayOpAssign, .printed .storageIndexArrayOpAssign),
  (``Taclet.memoryFieldOpAssign, .merged [.memoryFieldOpAssign, .memoryFieldDivAssign]),
  (``Taclet.memoryIndexArrayOpAssign, .printed .memoryIndexArrayOpAssign),
  (``Taclet.storageFieldOpAssignUnfoldLeftFst, .leanOnly .keyTier),
  (``Taclet.storageIndexOpAssignUnfoldLeftFst, .leanOnly .keyTier),
  (``Taclet.memoryFieldOpAssignUnfoldLeftFst, .leanOnly .keyTier),
  (``Taclet.memoryIndexOpAssignUnfoldLeftFst, .leanOnly .keyTier),
  (``Taclet.compoundAssignValueRhsCapture, .leanOnly .keyTier),
  (``Taclet.localIncrement, .leanOnly .keyTier),
  (``Taclet.storageRootIncrement, .printed .storageRootPostincrement),
  (``Taclet.storageFieldIncrement, .leanOnly .keyTier),
  (``Taclet.storageIndexIncrement, .leanOnly .keyTier),
  (``Taclet.memoryFieldIncrement, .printed .memoryFieldPostincrement),
  (``Taclet.memoryIndexArrayIncrement, .leanOnly .keyTier),
  (``Taclet.storageFieldIncrementUnfoldLeftFst, .leanOnly .keyTier),
  (``Taclet.storageIndexIncrementUnfoldLeftFst, .leanOnly .keyTier),
  (``Taclet.memoryFieldIncrementUnfoldLeftFst, .leanOnly .keyTier),
  (``Taclet.memoryIndexIncrementUnfoldLeftFst, .leanOnly .keyTier),
  (``Taclet.localAssignIncrement, .leanOnly .keyTier),
  (``Taclet.storageRootIncrementAssignment, .leanOnly .keyTier),
  (``Taclet.storageFieldIncrementAssignment, .leanOnly .keyTier),
  (``Taclet.storageIndexIncrementAssignment, .leanOnly .keyTier),
  (``Taclet.memoryFieldIncrementAssignment, .leanOnly .keyTier),
  (``Taclet.memoryIndexArrayIncrementAssignment, .leanOnly .keyTier),
  -- Arrays: the printed rules, as solkey, split by the element type
  (``Taclet.storagePushValueSave, .printed .storagePushValueSave),
  (``Taclet.storagePushValueCopySource, .printed .storagePushValueCopySource),
  (``Taclet.storagePushLengthSave, .printed .storagePushLengthSave),
  (``Taclet.storagePushLengthSaveReferenceElement,
    .printed .storagePushLengthSaveReferenceElement),
  (``Taclet.storagePushValue_unfold_rightSndArgument,
    .printed .storagePushValue_unfold_rightSndArgument),
  (``Taclet.storagePushValue_unfold_leftFstReceiver,
    .printed .storagePushValue_unfold_leftFstReceiver),
  (``Taclet.storagePush_unfold_leftFstReceiver, .printed .storagePush_unfold_leftFstReceiver),
  (``Taclet.storagePop_unfold_leftFstReceiver, .printed .storagePop_unfold_leftFstReceiver),
  (``Taclet.storagePopSave, .printed .storagePopSave),
  (``Taclet.storagePopSaveMappingElement, .printed .storagePopSaveMappingElement),
  (``Taclet.storageLocalRootPush_unfold_leftFstReceiver,
    .printed .storageLocalRootPush_unfold_leftFstReceiver),
  (``Taclet.storageLocalRootPushBind, .printed .storageLocalRootPushBind),
  (``Taclet.storageLocalRootPushBindMappingElement,
    .printed .storageLocalRootPushBindMappingElement),
  -- Transfer
  (``Taclet.transfer_unfold_leftFstReceiver, .printed .transfer_unfold_leftFstReceiver),
  (``Taclet.transfer_unfold_rightSndArgument, .printed .transfer_unfold_rightSndArgument),
  (``Taclet.transferNoCallback, .merged [.transferNoCallbackBox, .transferNoCallbackDiamond]),
  -- Memory
  (``Taclet.memoryFieldRead_unfold_rightFst, .printed .memoryFieldRead_unfold_rightFst),
  (``Taclet.memoryIndexRead_unfold_rightFst, .printed .memoryIndexRead_unfold_rightFst),
  (``Taclet.memoryIndexRead_unfold_rightSndIndex, .printed .memoryIndexRead_unfold_rightSndIndex),
  (``Taclet.memoryFieldReadHeap, .printed .memoryFieldRead),
  (``Taclet.memoryIndexReadHeap, .printed .memoryIndexReadArrayValue),
  (``Taclet.memoryRootAlias, .printed .memoryRootRebind),
  (``Taclet.memoryFieldReadAliasRoot, .printed .memoryFieldRead),
  (``Taclet.memoryIndexReadAliasRoot, .printed .memoryIndexReadArrayMemory),
  (``Taclet.memoryFieldWriteStore, .printed .memoryFieldWrite),
  (``Taclet.memoryIndexWriteStore, .printed .memoryIndexWriteArray),
  (``Taclet.memoryFieldWriteCopy, .printed .memoryFieldWrite),
  (``Taclet.memoryIndexWriteCopy, .printed .memoryIndexWriteArray),
  (``Taclet.memoryFieldWrite_unfold_leftFst,
    .merged [.memoryFieldWrite_unfold_leftFst, .memoryFieldWriteMemRef_unfold_leftFst]),
  (``Taclet.memoryIndexWriteCaptureAllComplexRecv,
    .printed .memoryIndexWriteCaptureAllComplexRecv),
  (``Taclet.memoryIndexWriteMemRefCaptureAllComplexRecv,
    .printed .memoryIndexWriteMemRefCaptureAllComplexRecv),
  (``Taclet.memoryIndexWriteCaptureAllNonSimpleIndex,
    .printed .memoryIndexWriteCaptureAllNonSimpleIndex),
  (``Taclet.memoryIndexWriteMemRefCaptureAllNonSimpleIndex,
    .printed .memoryIndexWriteMemRefCaptureAllNonSimpleIndex),
  (``Taclet.memoryFieldWriteUnfoldSource, .printed .fieldWriteValueRhsCapture),
  (``Taclet.memoryIndexWriteUnfoldSource, .printed .indexWriteValueRhsCapture),
  (``Taclet.memoryRootDeleteFreshRebind, .printed .memoryRootDeleteFreshRebind),
  (``Taclet.memoryFieldDeletePrimitive, .printed .memoryFieldDeletePrimitive),
  (``Taclet.memoryFieldDeleteReference, .printed .memoryFieldDeleteReference),
  (``Taclet.memoryIndexDeletePrimitive, .printed .memoryIndexDeletePrimitive),
  (``Taclet.memoryIndexDeleteReference, .printed .memoryIndexDeleteReference),
  (``Taclet.memoryFieldDelete_unfold_leftFst, .printed .memoryFieldDelete_unfold_leftFst),
  (``Taclet.memoryIndexDelete_unfold_leftFst, .printed .memoryIndexDelete_unfold_leftFst),
  (``Taclet.memoryIndexDeleteNonSimpleIndexCapture, .leanOnly .keyTier),
  (``Taclet.memoryArrayFreshAlloc, .printed .memoryArrayFreshAlloc),
  (``Taclet.newArrayCapture, .printed .newArrayCapture),
  -- Storage and memory
  (``Taclet.memoryStorageCopy, .printed .memoryStorageCopy),
  (``Taclet.memoryStorageCopyUnfold, .printed .memoryStorageCopyUnfold),
  (``Taclet.memoryToStorageStoreRoot, .printed .memoryToStorageStoreRoot),
  (``Taclet.memoryToStorageFieldCopyRoot,
    .merged [.memoryToStorageFieldCopyRoot, .memoryToStorageFieldCopyField]),
  (``Taclet.memoryToStorageIndexMappingCopyRoot, .printed .memoryToStorageIndexMappingCopyRoot),
  (``Taclet.memoryToStorageIndexArrayCopyRoot, .printed .memoryToStorageIndexArrayCopyRoot),
  (``Taclet.memoryToStorageField_unfold_leftFst, .printed .memoryToStorageField_unfold_leftFst),
  (``Taclet.memoryToStorageIndexCaptureAllComplexRecv,
    .printed .memoryToStorageIndexCaptureAllComplexRecv),
  (``Taclet.memoryToStorageIndexCaptureAllNonSimpleIndex,
    .printed .memoryToStorageIndexCaptureAllNonSimpleIndex),
  -- Control flow
  (``Taclet.ifElseUnfold, .printed .ifElseUnfold),
  (``Taclet.ifElseSplit, .printed .ifElseSplit),
  (``Taclet.requireConditionCapture, .printed .requireConditionCapture),
  (``Taclet.requireSimple, .printed .requireSimple),
  (``Taclet.assertConditionCapture, .printed .assertConditionCapture),
  (``Taclet.assertSimple, .printed .assertSimple),
  (``Taclet.revertBox, .printed .revertBox),
  (``Taclet.revertDiamond, .printed .revertDiamond) ]

#check_constructor_table Taclet, printedOrigins.map Prod.fst

/-! ## Which printed rules the table claims -/

/-- Whether some row names the printed rule. -/
def claims (p : PrintedRule) : Bool :=
  printedOrigins.any fun r => r.2.rules.contains p

/-- Every printed rule some row names, in `PrintedRule.all`'s order. -/
def claimedPrintedRules : List PrintedRule := PrintedRule.all.filter claims

/-- The printed rules of kind `rule` that **no** constructor claims.  The
reasons are `RuleShapes.unclaimedTaclets`', rule for rule: the printed rules are
what solkey runs, and the typed syntax takes a memory path
as a source in place, so nothing captures one (four); has no strategy for the
literal-condition `if` shortcuts (three); and transcribes only the
no-callback `transfer` (two). -/
def unclaimedRules : List PrintedRule :=
  [ .memoryFieldRead_unfold_rightSndResult, .memoryIndexRead_unfold_rightSndResult,
    .memoryFieldWriteCaptureSrc, .memoryIndexWriteMemRefRhsCapture,
    .ifElseTrue, .ifElseFalse, .ifElseNegated,
    .transferWithCallbackBox, .transferWithCallbackDiamond ]

/-- **The coverage fact**: a printed rule is claimed exactly when it is of kind
`rule` and not excused above.  A printed rule Lean never ports
fails this; so does a row that names a template, a rejected or unimplemented
rule, or the first-order axiom. -/
theorem printed_rules_partitioned :
    PrintedRule.all.all
      (fun p => claims p != (p.kind != .rule || unclaimedRules.contains p)) = true := by
  decide +kernel

theorem printedRules_count : PrintedRule.all.length = 136 := by decide +kernel

theorem claimedPrintedRules_count : claimedPrintedRules.length = 117 := by decide +kernel

theorem unclaimedRules_count : unclaimedRules.length = 9 := by decide +kernel

/-! ## The constructors with no printed rule -/

/-- The constructors whose origin is `leanOnly why`. -/
def leanOnlyRows (why : LeanOnlyReason) : List Lean.Name :=
  (printedOrigins.filter fun r => r.2 == .leanOnly why).map Prod.fst

theorem leanOnly_keyTier_count : (leanOnlyRows .keyTier).length = 32 := by decide +kernel

theorem leanOnly_calculus_count : (leanOnlyRows .calculus).length = 0 := by decide +kernel

end PrintedRules
end Solidity
