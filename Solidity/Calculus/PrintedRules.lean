import Solidity.Calculus.Rules

/-!
# The printed rules, as a Lean type

The printed rule set is the
second port target of this table: `KeyTaclets.lean` names what solkey runs,
this module names what is *printed* — one constructor per
`\DeclarePrintedRule` name, with the `tags` reduced to a `PrintedRuleKind`.  It
exists for the same reason: "which printed rule is this Lean rule?" is then a
total `match` the compiler checks, and "which printed rules does Lean not have,
and which Lean rules are not printed?" is a `native_decide` rather
than a grep across two repositories.

`printedOrigin` is the map.  It is written from the Lean side, one arm per
`RuleName`, because the Lean table is the finer one: a parameterized family
lists every operator instance where the printed table has one schematic rule, box and
diamond twins are two names here and one there, and a few printed rules are one
Lean rule (`merged`) because Lean's condition already covers both.  The other
direction is `printed_rules_partitioned`: every printed rule of kind `rule` is
claimed by some arm except `ifElseSplit`, which is `JudgmentSplit.ite_split`
and not a rule, and no template, rejected, or first-order name is claimed.

A `leanOnly` arm carries its reason, and the three reasons are three
different to-do lists.  `keyTier` is the largest and the least interesting:
solkey has a taclet, the printed rules do not include it, and the Lean rule exists
to transcribe the taclet — the finer expression tiers, `**=`, the
comparison instances of the compound families.  `plumbing` is the front-end
normalisation only this syntax needs (`docs/lean-key-rule-map.md`).
`calculus` is the short list that should be printed: rules with neither
a taclet nor a printed rule, whose theory is only here.

printed rules in both directions; `PrintedRule.name` is the spelling it reads.
-/

namespace Solidity

/-- What a `\DeclarePrintedRule` block is, read off its `tags`. -/
inductive PrintedRuleKind where
  /-- A rule of the calculus: the default. -/
  | rule
  /-- Tag `template`: the six `unfold_*` schemata a family of rules
  instantiates.  Not a rule; nothing claims one. -/
  | template
  /-- Tag `rejected`: printed to be argued against. -/
  | rejected
  /-- Tag `unimplemented` and declared only among the checked arithmetic rules.  Today
  every checked twin re-declares an arithmetic rule name, so nothing is of
  this kind. -/
  | unimplemented
  /-- `sizeNotNegative`, the one first-order axiom among the rules
  (`Typing/WellFormedConsumers.lean`). -/
  | firstOrder
  deriving DecidableEq, Repr

/-- One printed rule, under its printed name (`\\_` read as `_`).
A name declared twice — the six `unfold_*` templates are in both
the storage and memory rules, and the checked group re-declares seven of
the arithmetic rules with checked arithmetic — is one constructor. -/
inductive PrintedRule where
  | unfold_rightFst
  | storageFieldRead_unfold_rightFst
  | storageIndexRead_unfold_rightFst
  | unfold_rightSnd
  | storageIndexRead_unfold_rightSndIndex
  | storagePushValue_unfold_rightSndArgument
  | unfold_rightSndResult
  | storageFieldRead_unfold_rightSndResult
  | storageIndexRead_unfold_rightSndResult
  | unfold_leftFst
  | storageFieldWrite_unfold_leftFst
  | storageIndexWrite_unfold_leftFst
  | storageFieldWriteRef_unfold_leftFst
  | storageIndexWriteRef_unfold_leftFst
  | storageFieldDelete_unfold_leftFst
  | storageIndexDelete_unfold_leftFst
  | storagePushValue_unfold_leftFstReceiver
  | storagePush_unfold_leftFstReceiver
  | storagePop_unfold_leftFstReceiver
  | storageLocalRootPush_unfold_leftFstReceiver
  | unfold_leftSnd
  | storageIndexWrite_unfold_leftSndIndex
  | storageIndexWriteRef_unfold_leftSndIndex
  | unfold_source
  | storageFieldWrite_unfold_source
  | storageIndexWrite_unfold_source
  | storageRootWrite_unfold_source
  | storageFieldWriteRef_unfold_source
  | storageIndexWriteRef_unfold_source
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
  | storageIndexWriteMappingSave
  | storageIndexWriteMappingCopySource
  | storageIndexReadMappingFind
  | storageIndexReadMappingBindLocalRoot
  | storageIndexReadMappingStoreRoot
  | storageIndexWriteArraySave
  | storageIndexWriteArrayCopySource
  | storageIndexReadArrayFind
  | storageIndexReadArrayBindLocalRoot
  | storageIndexReadArrayStoreRoot
  | storagePushValueSave
  | storagePushValueCopySource
  | storagePushLengthSave
  | storageLocalRootPushBind
  | storagePopSave
  | sizeNotNegative
  | indexWriteInnerNonSimpleIndexCapture
  | indexReadInnerNonSimpleIndexCapture
  | memoryFieldRead_unfold_rightFst
  | memoryIndexRead_unfold_rightFst
  | memoryIndexRead_unfold_rightSndIndex
  | memoryFieldRead_unfold_rightSndResult
  | memoryIndexRead_unfold_rightSndResult
  | memoryFieldWrite_unfold_leftFst
  | memoryIndexWrite_unfold_leftFst
  | memoryFieldWriteRef_unfold_leftFst
  | memoryIndexWriteRef_unfold_leftFst
  | memoryFieldDelete_unfold_leftFst
  | memoryIndexDelete_unfold_leftFst
  | memoryIndexWrite_unfold_leftSndIndex
  | memoryIndexWriteRef_unfold_leftSndIndex
  | memoryFieldWrite_unfold_source
  | memoryIndexWrite_unfold_source
  | memoryFieldWriteRef_unfold_source
  | memoryIndexWriteRef_unfold_source
  | memoryLocalDeclInitDrop
  | memoryDeclFreshAlloc
  | memoryArrayFreshAlloc
  | memoryFieldWriteStore
  | memoryRootAlias
  | memoryFieldReadHeap
  | memoryFieldReadAliasRoot
  | memoryRootDeleteFreshRebind
  | memoryFieldDeletePrimitive
  | memoryFieldDeleteReference
  | memoryIndexWriteStore
  | memoryIndexReadHeap
  | memoryIndexReadAliasRoot
  | memoryIndexDeletePrimitive
  | memoryIndexDeleteReference
  | memoryStorageCopyUnfold
  | memoryStorageCopy
  | memoryToStorageField_unfold_leftFst
  | memoryToStorageIndex_unfold_leftFst
  | memoryToStorageIndex_unfold_leftSndIndex
  | memoryToStorageFieldCopyRoot
  | memoryToStorageFieldCopyField
  | memoryToStorageIndexMappingCopyRoot
  | memoryToStorageIndexArrayCopyRoot
  | memoryToStorageStoreRoot
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
  | transfer_unfold_leftFstReceiver
  | transfer_unfold_rightSndArgument
  | transferNoCallbackBox
  | transferNoCallbackDiamond
  | transferWithCallbackBox
  | transferWithCallbackDiamond
  | localOpAssign
  | storageRootOpAssign
  | storageFieldOpAssign
  | storageIndexMappingOpAssign
  | storageIndexArrayOpAssign
  | storageRootIncrement
  | localDivAssign
  | unaryMinusAssignment
  | memoryFieldOpAssign
  | memoryFieldDivAssign
  | memoryIndexArrayOpAssign
  | memoryFieldIncrement
  deriving DecidableEq, Repr

namespace PrintedRule

/-- The printed spelling, for the script that checks the enumeration against
the rule sources. -/
def name : PrintedRule -> String
  | .unfold_rightFst => "unfold_rightFst"
  | .storageFieldRead_unfold_rightFst => "storageFieldRead_unfold_rightFst"
  | .storageIndexRead_unfold_rightFst => "storageIndexRead_unfold_rightFst"
  | .unfold_rightSnd => "unfold_rightSnd"
  | .storageIndexRead_unfold_rightSndIndex => "storageIndexRead_unfold_rightSndIndex"
  | .storagePushValue_unfold_rightSndArgument => "storagePushValue_unfold_rightSndArgument"
  | .unfold_rightSndResult => "unfold_rightSndResult"
  | .storageFieldRead_unfold_rightSndResult => "storageFieldRead_unfold_rightSndResult"
  | .storageIndexRead_unfold_rightSndResult => "storageIndexRead_unfold_rightSndResult"
  | .unfold_leftFst => "unfold_leftFst"
  | .storageFieldWrite_unfold_leftFst => "storageFieldWrite_unfold_leftFst"
  | .storageIndexWrite_unfold_leftFst => "storageIndexWrite_unfold_leftFst"
  | .storageFieldWriteRef_unfold_leftFst => "storageFieldWriteRef_unfold_leftFst"
  | .storageIndexWriteRef_unfold_leftFst => "storageIndexWriteRef_unfold_leftFst"
  | .storageFieldDelete_unfold_leftFst => "storageFieldDelete_unfold_leftFst"
  | .storageIndexDelete_unfold_leftFst => "storageIndexDelete_unfold_leftFst"
  | .storagePushValue_unfold_leftFstReceiver => "storagePushValue_unfold_leftFstReceiver"
  | .storagePush_unfold_leftFstReceiver => "storagePush_unfold_leftFstReceiver"
  | .storagePop_unfold_leftFstReceiver => "storagePop_unfold_leftFstReceiver"
  | .storageLocalRootPush_unfold_leftFstReceiver => "storageLocalRootPush_unfold_leftFstReceiver"
  | .unfold_leftSnd => "unfold_leftSnd"
  | .storageIndexWrite_unfold_leftSndIndex => "storageIndexWrite_unfold_leftSndIndex"
  | .storageIndexWriteRef_unfold_leftSndIndex => "storageIndexWriteRef_unfold_leftSndIndex"
  | .unfold_source => "unfold_source"
  | .storageFieldWrite_unfold_source => "storageFieldWrite_unfold_source"
  | .storageIndexWrite_unfold_source => "storageIndexWrite_unfold_source"
  | .storageRootWrite_unfold_source => "storageRootWrite_unfold_source"
  | .storageFieldWriteRef_unfold_source => "storageFieldWriteRef_unfold_source"
  | .storageIndexWriteRef_unfold_source => "storageIndexWriteRef_unfold_source"
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
  | .storageIndexWriteMappingSave => "storageIndexWriteMappingSave"
  | .storageIndexWriteMappingCopySource => "storageIndexWriteMappingCopySource"
  | .storageIndexReadMappingFind => "storageIndexReadMappingFind"
  | .storageIndexReadMappingBindLocalRoot => "storageIndexReadMappingBindLocalRoot"
  | .storageIndexReadMappingStoreRoot => "storageIndexReadMappingStoreRoot"
  | .storageIndexWriteArraySave => "storageIndexWriteArraySave"
  | .storageIndexWriteArrayCopySource => "storageIndexWriteArrayCopySource"
  | .storageIndexReadArrayFind => "storageIndexReadArrayFind"
  | .storageIndexReadArrayBindLocalRoot => "storageIndexReadArrayBindLocalRoot"
  | .storageIndexReadArrayStoreRoot => "storageIndexReadArrayStoreRoot"
  | .storagePushValueSave => "storagePushValueSave"
  | .storagePushValueCopySource => "storagePushValueCopySource"
  | .storagePushLengthSave => "storagePushLengthSave"
  | .storageLocalRootPushBind => "storageLocalRootPushBind"
  | .storagePopSave => "storagePopSave"
  | .sizeNotNegative => "sizeNotNegative"
  | .indexWriteInnerNonSimpleIndexCapture => "indexWriteInnerNonSimpleIndexCapture"
  | .indexReadInnerNonSimpleIndexCapture => "indexReadInnerNonSimpleIndexCapture"
  | .memoryFieldRead_unfold_rightFst => "memoryFieldRead_unfold_rightFst"
  | .memoryIndexRead_unfold_rightFst => "memoryIndexRead_unfold_rightFst"
  | .memoryIndexRead_unfold_rightSndIndex => "memoryIndexRead_unfold_rightSndIndex"
  | .memoryFieldRead_unfold_rightSndResult => "memoryFieldRead_unfold_rightSndResult"
  | .memoryIndexRead_unfold_rightSndResult => "memoryIndexRead_unfold_rightSndResult"
  | .memoryFieldWrite_unfold_leftFst => "memoryFieldWrite_unfold_leftFst"
  | .memoryIndexWrite_unfold_leftFst => "memoryIndexWrite_unfold_leftFst"
  | .memoryFieldWriteRef_unfold_leftFst => "memoryFieldWriteRef_unfold_leftFst"
  | .memoryIndexWriteRef_unfold_leftFst => "memoryIndexWriteRef_unfold_leftFst"
  | .memoryFieldDelete_unfold_leftFst => "memoryFieldDelete_unfold_leftFst"
  | .memoryIndexDelete_unfold_leftFst => "memoryIndexDelete_unfold_leftFst"
  | .memoryIndexWrite_unfold_leftSndIndex => "memoryIndexWrite_unfold_leftSndIndex"
  | .memoryIndexWriteRef_unfold_leftSndIndex => "memoryIndexWriteRef_unfold_leftSndIndex"
  | .memoryFieldWrite_unfold_source => "memoryFieldWrite_unfold_source"
  | .memoryIndexWrite_unfold_source => "memoryIndexWrite_unfold_source"
  | .memoryFieldWriteRef_unfold_source => "memoryFieldWriteRef_unfold_source"
  | .memoryIndexWriteRef_unfold_source => "memoryIndexWriteRef_unfold_source"
  | .memoryLocalDeclInitDrop => "memoryLocalDeclInitDrop"
  | .memoryDeclFreshAlloc => "memoryDeclFreshAlloc"
  | .memoryArrayFreshAlloc => "memoryArrayFreshAlloc"
  | .memoryFieldWriteStore => "memoryFieldWriteStore"
  | .memoryRootAlias => "memoryRootAlias"
  | .memoryFieldReadHeap => "memoryFieldReadHeap"
  | .memoryFieldReadAliasRoot => "memoryFieldReadAliasRoot"
  | .memoryRootDeleteFreshRebind => "memoryRootDeleteFreshRebind"
  | .memoryFieldDeletePrimitive => "memoryFieldDeletePrimitive"
  | .memoryFieldDeleteReference => "memoryFieldDeleteReference"
  | .memoryIndexWriteStore => "memoryIndexWriteStore"
  | .memoryIndexReadHeap => "memoryIndexReadHeap"
  | .memoryIndexReadAliasRoot => "memoryIndexReadAliasRoot"
  | .memoryIndexDeletePrimitive => "memoryIndexDeletePrimitive"
  | .memoryIndexDeleteReference => "memoryIndexDeleteReference"
  | .memoryStorageCopyUnfold => "memoryStorageCopyUnfold"
  | .memoryStorageCopy => "memoryStorageCopy"
  | .memoryToStorageField_unfold_leftFst => "memoryToStorageField_unfold_leftFst"
  | .memoryToStorageIndex_unfold_leftFst => "memoryToStorageIndex_unfold_leftFst"
  | .memoryToStorageIndex_unfold_leftSndIndex => "memoryToStorageIndex_unfold_leftSndIndex"
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
  | .storageIndexArrayOpAssign => "storageIndexArrayOpAssign"
  | .storageRootIncrement => "storageRootIncrement"
  | .localDivAssign => "localDivAssign"
  | .unaryMinusAssignment => "unaryMinusAssignment"
  | .memoryFieldOpAssign => "memoryFieldOpAssign"
  | .memoryFieldDivAssign => "memoryFieldDivAssign"
  | .memoryIndexArrayOpAssign => "memoryIndexArrayOpAssign"
  | .memoryFieldIncrement => "memoryFieldIncrement"

/-- Which kind of declaration the name is, read off its `tags`. -/
def kind : PrintedRule -> PrintedRuleKind
  | .unfold_rightFst => .template
  | .unfold_rightSnd => .template
  | .unfold_rightSndResult => .template
  | .unfold_leftFst => .template
  | .unfold_leftSnd => .template
  | .unfold_source => .template
  | .indexWriteInnerNonSimpleIndexCapture => .rejected
  | .indexReadInnerNonSimpleIndexCapture => .rejected
  | .sizeNotNegative => .firstOrder
  | _ => .rule

/-- Every constructor, in declaration order. -/
def all : List PrintedRule :=
  [ .unfold_rightFst,
    .storageFieldRead_unfold_rightFst,
    .storageIndexRead_unfold_rightFst,
    .unfold_rightSnd,
    .storageIndexRead_unfold_rightSndIndex,
    .storagePushValue_unfold_rightSndArgument,
    .unfold_rightSndResult,
    .storageFieldRead_unfold_rightSndResult,
    .storageIndexRead_unfold_rightSndResult,
    .unfold_leftFst,
    .storageFieldWrite_unfold_leftFst,
    .storageIndexWrite_unfold_leftFst,
    .storageFieldWriteRef_unfold_leftFst,
    .storageIndexWriteRef_unfold_leftFst,
    .storageFieldDelete_unfold_leftFst,
    .storageIndexDelete_unfold_leftFst,
    .storagePushValue_unfold_leftFstReceiver,
    .storagePush_unfold_leftFstReceiver,
    .storagePop_unfold_leftFstReceiver,
    .storageLocalRootPush_unfold_leftFstReceiver,
    .unfold_leftSnd,
    .storageIndexWrite_unfold_leftSndIndex,
    .storageIndexWriteRef_unfold_leftSndIndex,
    .unfold_source,
    .storageFieldWrite_unfold_source,
    .storageIndexWrite_unfold_source,
    .storageRootWrite_unfold_source,
    .storageFieldWriteRef_unfold_source,
    .storageIndexWriteRef_unfold_source,
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
    .storageIndexWriteMappingSave,
    .storageIndexWriteMappingCopySource,
    .storageIndexReadMappingFind,
    .storageIndexReadMappingBindLocalRoot,
    .storageIndexReadMappingStoreRoot,
    .storageIndexWriteArraySave,
    .storageIndexWriteArrayCopySource,
    .storageIndexReadArrayFind,
    .storageIndexReadArrayBindLocalRoot,
    .storageIndexReadArrayStoreRoot,
    .storagePushValueSave,
    .storagePushValueCopySource,
    .storagePushLengthSave,
    .storageLocalRootPushBind,
    .storagePopSave,
    .sizeNotNegative,
    .indexWriteInnerNonSimpleIndexCapture,
    .indexReadInnerNonSimpleIndexCapture,
    .memoryFieldRead_unfold_rightFst,
    .memoryIndexRead_unfold_rightFst,
    .memoryIndexRead_unfold_rightSndIndex,
    .memoryFieldRead_unfold_rightSndResult,
    .memoryIndexRead_unfold_rightSndResult,
    .memoryFieldWrite_unfold_leftFst,
    .memoryIndexWrite_unfold_leftFst,
    .memoryFieldWriteRef_unfold_leftFst,
    .memoryIndexWriteRef_unfold_leftFst,
    .memoryFieldDelete_unfold_leftFst,
    .memoryIndexDelete_unfold_leftFst,
    .memoryIndexWrite_unfold_leftSndIndex,
    .memoryIndexWriteRef_unfold_leftSndIndex,
    .memoryFieldWrite_unfold_source,
    .memoryIndexWrite_unfold_source,
    .memoryFieldWriteRef_unfold_source,
    .memoryIndexWriteRef_unfold_source,
    .memoryLocalDeclInitDrop,
    .memoryDeclFreshAlloc,
    .memoryArrayFreshAlloc,
    .memoryFieldWriteStore,
    .memoryRootAlias,
    .memoryFieldReadHeap,
    .memoryFieldReadAliasRoot,
    .memoryRootDeleteFreshRebind,
    .memoryFieldDeletePrimitive,
    .memoryFieldDeleteReference,
    .memoryIndexWriteStore,
    .memoryIndexReadHeap,
    .memoryIndexReadAliasRoot,
    .memoryIndexDeletePrimitive,
    .memoryIndexDeleteReference,
    .memoryStorageCopyUnfold,
    .memoryStorageCopy,
    .memoryToStorageField_unfold_leftFst,
    .memoryToStorageIndex_unfold_leftFst,
    .memoryToStorageIndex_unfold_leftSndIndex,
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
    .storageIndexArrayOpAssign,
    .storageRootIncrement,
    .localDivAssign,
    .unaryMinusAssignment,
    .memoryFieldOpAssign,
    .memoryFieldDivAssign,
    .memoryIndexArrayOpAssign,
    .memoryFieldIncrement ]

end PrintedRule

/-- Why a Lean rule has no printed rule. -/
inductive LeanOnlyReason where
  /-- solkey has the taclet and the printed rules do not include it: the expression
  tiers, the operator instances outside `+ - * / %`, the increment and
  compound families' unfold and assignment steps. -/
  | keyTier
  /-- Front-end normalisation of this syntax: the push sugar, the scratch
  alias, the expression statement. -/
  | plumbing
  /-- Theory only Lean has.  It should be printed. -/
  | calculus
  deriving DecidableEq, Repr

/-- The printed rule a Lean rule transcribes, or the reason there is none. -/
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

open Rules

/-- The printed compound-assignment operators: `+= -= *= /= %=`. -/
private def printedCompound (op : BinOp) (p : PrintedRule) : PrintedOrigin :=
  if op.hasCompoundAssign then .printed p else .leanOnly .keyTier

/-- The map.  Total over `RuleName`, so a new rule does not compile until it
says which printed rule it is, or why there is none. -/
def printedOrigin : RuleName -> PrintedOrigin
  -- storage: unfold
  | .storageFieldReadUnfoldRightFst => .printed .storageFieldRead_unfold_rightFst
  | .storageIndexReadUnfoldRightFst => .printed .storageIndexRead_unfold_rightFst
  | .storageIndexReadUnfoldRightSndIndex => .printed .storageIndexRead_unfold_rightSndIndex
  | .storagePushValueUnfoldRightSndArgument => .printed .storagePushValue_unfold_rightSndArgument
  | .storageFieldReadUnfoldRightSndResult =>
      .merged [.storageFieldRead_unfold_rightSndResult, .storageFieldWriteRef_unfold_source]
  | .storageIndexReadUnfoldRightSndResult =>
      .merged [.storageIndexRead_unfold_rightSndResult, .storageIndexWriteRef_unfold_source]
  | .storageFieldWriteUnfoldLeftFst => .printed .storageFieldWrite_unfold_leftFst
  | .storageIndexWriteUnfoldLeftFst => .printed .storageIndexWrite_unfold_leftFst
  | .storageFieldWriteRefUnfoldLeftFst => .printed .storageFieldWriteRef_unfold_leftFst
  | .storageIndexWriteRefUnfoldLeftFst => .printed .storageIndexWriteRef_unfold_leftFst
  | .storageFieldDeleteUnfoldLeftFst => .printed .storageFieldDelete_unfold_leftFst
  | .storageIndexDeleteUnfoldLeftFst => .printed .storageIndexDelete_unfold_leftFst
  | .storagePushPlaceDeleteUnfoldLeftFst => .leanOnly .plumbing
  | .storagePushValueUnfoldLeftFstReceiver => .printed .storagePushValue_unfold_leftFstReceiver
  | .storagePushUnfoldLeftFstReceiver => .printed .storagePush_unfold_leftFstReceiver
  | .storagePopUnfoldLeftFstReceiver => .printed .storagePop_unfold_leftFstReceiver
  | .storageLocalRootPushUnfoldLeftFstReceiver => .printed .storageLocalRootPush_unfold_leftFstReceiver
  | .storageIndexWriteUnfoldLeftSndIndex => .printed .storageIndexWrite_unfold_leftSndIndex
  | .storageIndexWriteRefUnfoldLeftSndIndex => .printed .storageIndexWriteRef_unfold_leftSndIndex
  | .storageIndexDeleteNonSimpleIndexCapture => .leanOnly .keyTier
  | .storageRootWriteUnfoldSource => .printed .storageRootWrite_unfold_source
  | .storageFieldWriteUnfoldSource => .printed .storageFieldWrite_unfold_source
  | .storageIndexWriteUnfoldSource => .printed .storageIndexWrite_unfold_source
  -- declarations
  | .storageLocalDeclInitDrop => .printed .storageLocalDeclInitDrop
  | .storageLocalDeclSkip => .printed .storageLocalDeclSkip
  | .localValueDeclInitDrop => .leanOnly .keyTier
  | .valueDeclSkip => .leanOnly .keyTier
  -- storage: terminal
  | .storageFieldWriteSave => .printed .storageFieldWriteSave
  | .storageFieldWriteCopySource => .printed .storageFieldWriteCopySource
  | .storageRootWriteStore => .printed .storageRootWriteStore
  | .storageRootWriteCopySource => .printed .storageRootWriteCopySource
  | .storageLocalRootRebind => .printed .storageLocalRootRebind
  | .storageFieldReadFind => .printed .storageFieldReadFind
  | .storageRootReadSelect => .printed .storageRootReadSelect
  | .storageFieldReadBindLocalRoot => .printed .storageFieldReadBindLocalRoot
  | .storageFieldReadStoreRoot => .printed .storageFieldReadStoreRoot
  | .storageRootDelete => .printed .storageRootDelete
  | .storageFieldDelete => .printed .storageFieldDelete
  | .storageIndexDelete => .printed .storageIndexDelete
  | .storagePushPlaceDelete => .leanOnly .plumbing
  | .storageIndexWriteMappingSave => .printed .storageIndexWriteMappingSave
  | .storageIndexWriteMappingCopySource => .printed .storageIndexWriteMappingCopySource
  | .storageIndexReadMappingFind => .printed .storageIndexReadMappingFind
  | .storageIndexReadMappingBindLocalRoot => .printed .storageIndexReadMappingBindLocalRoot
  | .storageIndexReadMappingStoreRoot => .printed .storageIndexReadMappingStoreRoot
  | .storageIndexWriteArraySaveBox => .printed .storageIndexWriteArraySave
  | .storageIndexWriteArraySaveDiamond => .printed .storageIndexWriteArraySave
  | .storageIndexWriteArrayCopySourceBox => .printed .storageIndexWriteArrayCopySource
  | .storageIndexWriteArrayCopySourceDiamond => .printed .storageIndexWriteArrayCopySource
  | .storageIndexReadArrayFindBox => .printed .storageIndexReadArrayFind
  | .storageIndexReadArrayFindDiamond => .printed .storageIndexReadArrayFind
  | .storageIndexReadArrayBindLocalRootBox => .printed .storageIndexReadArrayBindLocalRoot
  | .storageIndexReadArrayBindLocalRootDiamond => .printed .storageIndexReadArrayBindLocalRoot
  | .storageIndexReadArrayStoreRootBox => .printed .storageIndexReadArrayStoreRoot
  | .storageIndexReadArrayStoreRootDiamond => .printed .storageIndexReadArrayStoreRoot
  | .storagePushValueSave => .printed .storagePushValueSave
  | .storagePushValueCopySource => .printed .storagePushValueCopySource
  | .storagePushLengthSave => .printed .storagePushLengthSave
  | .storageLocalRootPushBind => .printed .storageLocalRootPushBind
  | .storagePopSaveBox => .printed .storagePopSave
  | .storagePopSaveDiamond => .printed .storagePopSave
  -- control
  | .requireConditionCapture => .printed .requireConditionCapture
  | .assertConditionCapture => .printed .assertConditionCapture
  | .requireSimple => .printed .requireSimple
  | .assertSimple => .printed .assertSimple
  | .ifElseUnfold => .printed .ifElseUnfold
  | .ifElseTrue => .printed .ifElseTrue
  | .ifElseFalse => .printed .ifElseFalse
  | .ifElseNegated => .printed .ifElseNegated
  | .revertBox => .printed .revertBox
  | .revertDiamond => .printed .revertDiamond
  -- payment
  | .transferUnfoldLeftFstReceiver => .printed .transfer_unfold_leftFstReceiver
  | .transferUnfoldRightSndArgument => .printed .transfer_unfold_rightSndArgument
  | .transferNoCallbackBox => .printed .transferNoCallbackBox
  | .transferNoCallbackDiamond => .printed .transferNoCallbackDiamond
  | .transferWithCallback => .merged [.transferWithCallbackBox, .transferWithCallbackDiamond]
  -- memory: unfold
  | .memoryFieldReadUnfoldRightFst => .printed .memoryFieldRead_unfold_rightFst
  | .memoryIndexReadUnfoldRightFst => .printed .memoryIndexRead_unfold_rightFst
  | .memoryIndexReadUnfoldRightSndIndex => .printed .memoryIndexRead_unfold_rightSndIndex
  | .memoryFieldReadUnfoldRightSndResult =>
      .merged [.memoryFieldRead_unfold_rightSndResult, .memoryFieldWriteRef_unfold_source]
  | .memoryIndexReadUnfoldRightSndResult =>
      .merged [.memoryIndexRead_unfold_rightSndResult, .memoryIndexWriteRef_unfold_source]
  | .memoryFieldWriteUnfoldLeftFst => .printed .memoryFieldWrite_unfold_leftFst
  | .memoryIndexWriteUnfoldLeftFst => .printed .memoryIndexWrite_unfold_leftFst
  | .memoryFieldWriteRefUnfoldLeftFst => .printed .memoryFieldWriteRef_unfold_leftFst
  | .memoryIndexWriteRefUnfoldLeftFst => .printed .memoryIndexWriteRef_unfold_leftFst
  | .memoryFieldDeleteUnfoldLeftFst => .printed .memoryFieldDelete_unfold_leftFst
  | .memoryIndexDeleteUnfoldLeftFst => .printed .memoryIndexDelete_unfold_leftFst
  | .memoryIndexWriteUnfoldLeftSndIndex => .printed .memoryIndexWrite_unfold_leftSndIndex
  | .memoryIndexWriteRefUnfoldLeftSndIndex => .printed .memoryIndexWriteRef_unfold_leftSndIndex
  | .memoryIndexDeleteNonSimpleIndexCapture => .leanOnly .keyTier
  | .memoryFieldWriteUnfoldSource => .printed .memoryFieldWrite_unfold_source
  | .memoryIndexWriteUnfoldSource => .printed .memoryIndexWrite_unfold_source
  -- memory: terminal
  | .memoryLocalDeclInitDrop => .printed .memoryLocalDeclInitDrop
  | .memoryDeclFreshAlloc => .merged [.memoryDeclFreshAlloc, .memoryArrayFreshAlloc]
  | .memoryFieldWriteStore => .printed .memoryFieldWriteStore
  | .memoryRootAlias => .printed .memoryRootAlias
  | .memoryFieldReadHeap => .printed .memoryFieldReadHeap
  | .memoryFieldReadAliasRoot => .printed .memoryFieldReadAliasRoot
  | .memoryRootDeleteFreshRebind => .printed .memoryRootDeleteFreshRebind
  | .memoryFieldDeletePrimitive => .printed .memoryFieldDeletePrimitive
  | .memoryFieldDeleteReference => .printed .memoryFieldDeleteReference
  | .memoryIndexWriteStoreBox => .printed .memoryIndexWriteStore
  | .memoryIndexWriteStoreDiamond => .printed .memoryIndexWriteStore
  | .memoryIndexReadHeapBox => .printed .memoryIndexReadHeap
  | .memoryIndexReadHeapDiamond => .printed .memoryIndexReadHeap
  | .memoryIndexReadAliasRootBox => .printed .memoryIndexReadAliasRoot
  | .memoryIndexReadAliasRootDiamond => .printed .memoryIndexReadAliasRoot
  | .memoryIndexDeletePrimitiveBox => .printed .memoryIndexDeletePrimitive
  | .memoryIndexDeletePrimitiveDiamond => .printed .memoryIndexDeletePrimitive
  | .memoryIndexDeleteReferenceBox => .printed .memoryIndexDeleteReference
  | .memoryIndexDeleteReferenceDiamond => .printed .memoryIndexDeleteReference
  -- copy
  | .memoryStorageCopyUnfold => .printed .memoryStorageCopyUnfold
  | .memoryStorageCopy => .printed .memoryStorageCopy
  | .memoryToStorageFieldUnfoldLeftFst => .printed .memoryToStorageField_unfold_leftFst
  | .memoryToStorageIndexUnfoldLeftFst => .printed .memoryToStorageIndex_unfold_leftFst
  | .memoryToStorageIndexUnfoldLeftSndIndex => .printed .memoryToStorageIndex_unfold_leftSndIndex
  | .memoryToStorageFieldCopyRoot => .printed .memoryToStorageFieldCopyRoot
  | .memoryToStorageFieldCopyField => .printed .memoryToStorageFieldCopyField
  | .memoryToStorageIndexMappingCopyRoot => .printed .memoryToStorageIndexMappingCopyRoot
  | .memoryToStorageIndexArrayCopyRootBox => .printed .memoryToStorageIndexArrayCopyRoot
  | .memoryToStorageIndexArrayCopyRootDiamond => .printed .memoryToStorageIndexArrayCopyRoot
  | .memoryToStorageStoreRoot => .printed .memoryToStorageStoreRoot
  -- arithmetic: `op ∈ {+ - * / %}` is printed once per target, and
  -- a separate divisor-guarded rule where the update has to guard
  | .localOpAssign .div | .localOpAssign .mod => .merged [.localOpAssign, .localDivAssign]
  | .localOpAssign op => printedCompound op .localOpAssign
  | .storageRootOpAssign op => printedCompound op .storageRootOpAssign
  | .storageFieldOpAssign op => printedCompound op .storageFieldOpAssign
  | .storageIndexMappingOpAssign op => printedCompound op .storageIndexMappingOpAssign
  | .storageIndexArrayOpAssign op => printedCompound op .storageIndexArrayOpAssign
  | .storageFieldOpAssignUnfoldLeftFst _ => .leanOnly .keyTier
  | .storageIndexOpAssignUnfoldLeftFst _ => .leanOnly .keyTier
  | .storageRootIncrement _ => .printed .storageRootIncrement
  | .storageFieldIncrement _ => .leanOnly .keyTier
  | .storageIndexIncrement _ => .leanOnly .keyTier
  | .storageFieldIncrementUnfoldLeftFst _ => .leanOnly .keyTier
  | .storageIndexIncrementUnfoldLeftFst _ => .leanOnly .keyTier
  | .storageRootIncrementAssignment _ => .leanOnly .keyTier
  | .storageFieldIncrementAssignment _ => .leanOnly .keyTier
  | .storageIndexIncrementAssignment _ => .leanOnly .keyTier
  | .memoryFieldOpAssign .div | .memoryFieldOpAssign .mod =>
      .merged [.memoryFieldOpAssign, .memoryFieldDivAssign]
  | .memoryFieldOpAssign op => printedCompound op .memoryFieldOpAssign
  | .memoryIndexArrayOpAssign op => printedCompound op .memoryIndexArrayOpAssign
  | .memoryFieldOpAssignUnfoldLeftFst _ => .leanOnly .keyTier
  | .memoryIndexOpAssignUnfoldLeftFst _ => .leanOnly .keyTier
  | .memoryFieldIncrement _ => .printed .memoryFieldIncrement
  | .memoryIndexArrayIncrement _ => .leanOnly .keyTier
  | .memoryFieldIncrementUnfoldLeftFst _ => .leanOnly .keyTier
  | .memoryIndexIncrementUnfoldLeftFst _ => .leanOnly .keyTier
  | .memoryFieldIncrementAssignment _ => .leanOnly .keyTier
  | .memoryIndexArrayIncrementAssignment _ => .leanOnly .keyTier
  -- expressions: solkey's tiers, below what is printed
  | .binopUnfoldLeft _ => .leanOnly .keyTier
  | .binopUnfoldRight _ => .leanOnly .keyTier
  | .binopAssignment _ => .leanOnly .keyTier
  | .logicalAndShortCircuitRhs => .leanOnly .keyTier
  | .logicalOrShortCircuitRhs => .leanOnly .keyTier
  | .ternaryCaptureCond => .leanOnly .keyTier
  | .ternaryToIf => .leanOnly .keyTier
  | .ternaryToIfStorage => .leanOnly .keyTier
  | .ternaryToIfMemory => .leanOnly .plumbing
  | .unopCapture _ => .leanOnly .keyTier
  | .unopAssignment .neg => .printed .unaryMinusAssignment
  | .unopAssignment .not => .leanOnly .keyTier
  | .compoundAssignValueRhsCapture _ => .leanOnly .keyTier
  | .localValueAssign => .leanOnly .keyTier
  | .localAssignIncrement _ => .leanOnly .keyTier
  | .localIncrement _ => .leanOnly .keyTier
  -- calls
  | .functionCallArgCapture => .leanOnly .calculus
  | .functionBodyExpand => .leanOnly .keyTier
  -- front end
  | .storagePlaceAlias => .leanOnly .plumbing
  | .exprStmtCapture => .leanOnly .plumbing
  | .pushAssignLower => .leanOnly .plumbing
  | .pushFieldAssignLower => .leanOnly .plumbing
  | .storagePushLhsToPushValue => .leanOnly .plumbing
  -- cross-domain scratch steps
  | .storageToMemoryDeclUnfoldRightFst => .leanOnly .calculus
  | .storageToMemoryDeclCopyField => .leanOnly .calculus
  | .storageToMemoryDeclCopyRoot => .leanOnly .calculus
  | .memoryToStorageUnfoldRightFstSource => .leanOnly .calculus
  -- memory copies: `memoryFieldWrite` on a reference-typed field
  | .memoryFieldWriteCopy => .leanOnly .keyTier
  | .memoryIndexWriteCopyBox => .leanOnly .keyTier
  | .memoryIndexWriteCopyDiamond => .leanOnly .keyTier

/-! ## Which printed rules the table claims -/

/-- Every printed rule some arm of `printedOrigin` names, `transferWithCallback`'s
two included (it is the `transferSemantics` alternative, so it is not in
`ruleNames`). -/
def claimedPrintedRules : List PrintedRule :=
  ((ruleNames ++ [RuleName.transferWithCallback]).flatMap
    fun r => (printedOrigin r).rules).eraseDups

/-- The printed rules of kind `rule` that **no** Lean rule claims, and why.
One: `ifElseSplit` is a sequent-level two-goal split on a simple condition,
which a single-successor `BlockStep` cannot produce; it is
`SolidityJudgment.ite_split` (`JudgmentSplit.lean`), the same way KeY's
`ifSplit`/`ifElseSplit` are excused in `RuleShapes.unclaimedTaclets`. -/
def unclaimedRules : List PrintedRule := [.ifElseSplit]

/-- **The coverage fact**: a printed rule is claimed exactly when it is of kind
`rule` and not excused above.  A printed rule Lean never ports
fails this; so does an arm that names a template, a rejected rule, or the
first-order axiom. -/
theorem printed_rules_partitioned :
    PrintedRule.all.all
      (fun p => claimedPrintedRules.contains p
        != (p.kind != .rule || unclaimedRules.contains p)) = true := by
  native_decide

/-! ## The rules with no printed rule -/

/-- The rule instances whose origin is `leanOnly why`, out of `ruleNames`.
Every instance of a parameterized family counts, as in
`RuleShapes.leanOnlyRules`: `localOpAssign .lt` is a listed rule, and the
printed rules of course have no `<=` compound assignment. -/
def leanOnlyRules (why : LeanOnlyReason) : List RuleName :=
  ruleNames.filter fun r => printedOrigin r == .leanOnly why

theorem leanOnlyRules_keyTier_count : (leanOnlyRules .keyTier).length = 248 := by
  native_decide

theorem leanOnlyRules_plumbing_count : (leanOnlyRules .plumbing).length = 8 := by
  native_decide

theorem leanOnlyRules_calculus_count : (leanOnlyRules .calculus).length = 5 := by
  native_decide

/-- And the complement: 159 of the 420 instances name a printed rule, claiming
122 of the 123 printed rules of kind `rule` between them. -/
theorem rules_with_printed_origin_count :
    (ruleNames.filter fun r => (printedOrigin r).rules != []).length = 159 := by
  native_decide

theorem claimedPrintedRules_count : claimedPrintedRules.length = 122 := by native_decide

end PrintedRules
end Solidity
