import Solidity.Calculus.Rules

/-!
# The paper's rules, as a Lean type

The pre-licentiate paper (`../Pre-licenciate-paper`, `rules/*.tex`) is the
second port target of this table: `KeyTaclets.lean` names what solkey runs,
this module names what the paper *prints* — one constructor per
`\DeclarePaperRule` name, with the `tags` reduced to a `PaperRuleKind`.  It
exists for the same reason: "which paper rule is this Lean rule?" is then a
total `match` the compiler checks, and "which paper rules does Lean not have,
and which Lean rules does the paper not have?" is a `native_decide` rather
than a grep across two repositories.

`paperOrigin` is the map.  It is written from the Lean side, one arm per
`RuleName`, because the Lean table is the finer one: a parameterized family
lists every operator instance and the paper prints one schematic rule, box and
diamond twins are two names here and one there, and a few paper rules are one
Lean rule (`merged`) because Lean's condition already covers both.  The other
direction is `paper_rules_partitioned`: every paper rule of kind `rule` is
claimed by some arm except `ifElseSplit`, which is `JudgmentSplit.ite_split`
and not a rule, and no template, rejected, or first-order name is claimed.

A `leanOnly` arm carries its reason, and the three reasons are three
different to-do lists.  `keyTier` is the largest and the least interesting:
solkey has a taclet, the paper does not print it, and the Lean rule exists
to transcribe the taclet — the finer expression tiers, `**=`, the
comparison instances of the compound families.  `plumbing` is the front-end
normalisation only this syntax needs (`docs/lean-key-rule-map.md`).
`calculus` is the short list that should reach the paper: rules with neither
a taclet nor a paper rule, whose theory is only here.

The script `scripts/check-paper-rules.mjs` holds the enumeration to the
`.tex` files in both directions; `PaperRule.name` is the spelling it reads.
-/

namespace Solidity

/-- What a `\DeclarePaperRule` block is, read off its `tags`. -/
inductive PaperRuleKind where
  /-- A rule of the calculus: the default. -/
  | rule
  /-- Tag `template`: the six `unfold_*` schemata a family of rules
  instantiates.  Not a rule; nothing claims one. -/
  | template
  /-- Tag `rejected`: printed to be argued against. -/
  | rejected
  /-- Tag `unimplemented` and declared only in `arith-checked.tex`.  Today
  every checked twin re-declares an `arith.tex` name, so nothing is of
  this kind. -/
  | unimplemented
  /-- `sizeNotNegative`, the one first-order axiom among the rules
  (`Typing/WellFormedConsumers.lean`). -/
  | firstOrder
  deriving DecidableEq, Repr

/-- One rule of the paper, named as `rules/*.tex` names it (`\\_` read as `_`).
A name the paper declares twice — the six `unfold_*` templates are in both
`storage.tex` and `memory.tex`, and `arith-checked.tex` re-declares seven of
`arith.tex`'s rules with checked arithmetic — is one constructor. -/
inductive PaperRule where
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

namespace PaperRule

/-- The paper's spelling, for the script that checks the enumeration against
`rules/*.tex`. -/
def name : PaperRule -> String
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
def kind : PaperRule -> PaperRuleKind
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
def all : List PaperRule :=
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

end PaperRule

/-- Why a Lean rule has no paper rule. -/
inductive LeanOnlyReason where
  /-- solkey has the taclet and the paper does not print it: the expression
  tiers, the operator instances outside `+ - * / %`, the increment and
  compound families' unfold and assignment steps. -/
  | keyTier
  /-- Front-end normalisation of this syntax: the push sugar, the scratch
  alias, the expression statement. -/
  | plumbing
  /-- Theory only Lean has.  The paper should gain it. -/
  | calculus
  deriving DecidableEq, Repr

/-- The paper rule a Lean rule transcribes, or the reason there is none. -/
inductive PaperOrigin where
  | paper (p : PaperRule)
  | merged (ps : List PaperRule)
  | leanOnly (why : LeanOnlyReason)
  deriving DecidableEq, Repr

namespace PaperOrigin

/-- The paper rules an origin claims. -/
def rules : PaperOrigin -> List PaperRule
  | paper p => [p]
  | merged ps => ps
  | leanOnly _ => []

end PaperOrigin

namespace PaperRules

open Rules

/-- The compound-assignment operators the paper prints: `+= -= *= /= %=`. -/
private def paperCompound (op : BinOp) (p : PaperRule) : PaperOrigin :=
  if op.hasCompoundAssign then .paper p else .leanOnly .keyTier

/-- The map.  Total over `RuleName`, so a new rule does not compile until it
says what it is to the paper. -/
def paperOrigin : RuleName -> PaperOrigin
  -- storage: unfold
  | .storageFieldReadUnfoldRightFst => .paper .storageFieldRead_unfold_rightFst
  | .storageIndexReadUnfoldRightFst => .paper .storageIndexRead_unfold_rightFst
  | .storageIndexReadUnfoldRightSndIndex => .paper .storageIndexRead_unfold_rightSndIndex
  | .storagePushValueUnfoldRightSndArgument => .paper .storagePushValue_unfold_rightSndArgument
  | .storageFieldReadUnfoldRightSndResult =>
      .merged [.storageFieldRead_unfold_rightSndResult, .storageFieldWriteRef_unfold_source]
  | .storageIndexReadUnfoldRightSndResult =>
      .merged [.storageIndexRead_unfold_rightSndResult, .storageIndexWriteRef_unfold_source]
  | .storageFieldWriteUnfoldLeftFst => .paper .storageFieldWrite_unfold_leftFst
  | .storageIndexWriteUnfoldLeftFst => .paper .storageIndexWrite_unfold_leftFst
  | .storageFieldWriteRefUnfoldLeftFst => .paper .storageFieldWriteRef_unfold_leftFst
  | .storageIndexWriteRefUnfoldLeftFst => .paper .storageIndexWriteRef_unfold_leftFst
  | .storageFieldDeleteUnfoldLeftFst => .paper .storageFieldDelete_unfold_leftFst
  | .storageIndexDeleteUnfoldLeftFst => .paper .storageIndexDelete_unfold_leftFst
  | .storagePushPlaceDeleteUnfoldLeftFst => .leanOnly .plumbing
  | .storagePushValueUnfoldLeftFstReceiver => .paper .storagePushValue_unfold_leftFstReceiver
  | .storagePushUnfoldLeftFstReceiver => .paper .storagePush_unfold_leftFstReceiver
  | .storagePopUnfoldLeftFstReceiver => .paper .storagePop_unfold_leftFstReceiver
  | .storageLocalRootPushUnfoldLeftFstReceiver => .paper .storageLocalRootPush_unfold_leftFstReceiver
  | .storageIndexWriteUnfoldLeftSndIndex => .paper .storageIndexWrite_unfold_leftSndIndex
  | .storageIndexWriteRefUnfoldLeftSndIndex => .paper .storageIndexWriteRef_unfold_leftSndIndex
  | .storageIndexDeleteNonSimpleIndexCapture => .leanOnly .keyTier
  | .storageRootWriteUnfoldSource => .paper .storageRootWrite_unfold_source
  | .storageFieldWriteUnfoldSource => .paper .storageFieldWrite_unfold_source
  | .storageIndexWriteUnfoldSource => .paper .storageIndexWrite_unfold_source
  -- declarations
  | .storageLocalDeclInitDrop => .paper .storageLocalDeclInitDrop
  | .storageLocalDeclSkip => .paper .storageLocalDeclSkip
  | .localValueDeclInitDrop => .leanOnly .keyTier
  | .valueDeclSkip => .leanOnly .keyTier
  -- storage: terminal
  | .storageFieldWriteSave => .paper .storageFieldWriteSave
  | .storageFieldWriteCopySource => .paper .storageFieldWriteCopySource
  | .storageRootWriteStore => .paper .storageRootWriteStore
  | .storageRootWriteCopySource => .paper .storageRootWriteCopySource
  | .storageLocalRootRebind => .paper .storageLocalRootRebind
  | .storageFieldReadFind => .paper .storageFieldReadFind
  | .storageRootReadSelect => .paper .storageRootReadSelect
  | .storageFieldReadBindLocalRoot => .paper .storageFieldReadBindLocalRoot
  | .storageFieldReadStoreRoot => .paper .storageFieldReadStoreRoot
  | .storageRootDelete => .paper .storageRootDelete
  | .storageFieldDelete => .paper .storageFieldDelete
  | .storageIndexDelete => .paper .storageIndexDelete
  | .storagePushPlaceDelete => .leanOnly .plumbing
  | .storageIndexWriteMappingSave => .paper .storageIndexWriteMappingSave
  | .storageIndexWriteMappingCopySource => .paper .storageIndexWriteMappingCopySource
  | .storageIndexReadMappingFind => .paper .storageIndexReadMappingFind
  | .storageIndexReadMappingBindLocalRoot => .paper .storageIndexReadMappingBindLocalRoot
  | .storageIndexReadMappingStoreRoot => .paper .storageIndexReadMappingStoreRoot
  | .storageIndexWriteArraySaveBox => .paper .storageIndexWriteArraySave
  | .storageIndexWriteArraySaveDiamond => .paper .storageIndexWriteArraySave
  | .storageIndexWriteArrayCopySourceBox => .paper .storageIndexWriteArrayCopySource
  | .storageIndexWriteArrayCopySourceDiamond => .paper .storageIndexWriteArrayCopySource
  | .storageIndexReadArrayFindBox => .paper .storageIndexReadArrayFind
  | .storageIndexReadArrayFindDiamond => .paper .storageIndexReadArrayFind
  | .storageIndexReadArrayBindLocalRootBox => .paper .storageIndexReadArrayBindLocalRoot
  | .storageIndexReadArrayBindLocalRootDiamond => .paper .storageIndexReadArrayBindLocalRoot
  | .storageIndexReadArrayStoreRootBox => .paper .storageIndexReadArrayStoreRoot
  | .storageIndexReadArrayStoreRootDiamond => .paper .storageIndexReadArrayStoreRoot
  | .storagePushValueSave => .paper .storagePushValueSave
  | .storagePushValueCopySource => .paper .storagePushValueCopySource
  | .storagePushLengthSave => .paper .storagePushLengthSave
  | .storageLocalRootPushBind => .paper .storageLocalRootPushBind
  | .storagePopSaveBox => .paper .storagePopSave
  | .storagePopSaveDiamond => .paper .storagePopSave
  -- control
  | .requireConditionCapture => .paper .requireConditionCapture
  | .assertConditionCapture => .paper .assertConditionCapture
  | .requireSimple => .paper .requireSimple
  | .assertSimple => .paper .assertSimple
  | .ifElseUnfold => .paper .ifElseUnfold
  | .ifElseTrue => .paper .ifElseTrue
  | .ifElseFalse => .paper .ifElseFalse
  | .ifElseNegated => .paper .ifElseNegated
  | .revertBox => .paper .revertBox
  | .revertDiamond => .paper .revertDiamond
  -- payment
  | .transferUnfoldLeftFstReceiver => .paper .transfer_unfold_leftFstReceiver
  | .transferUnfoldRightSndArgument => .paper .transfer_unfold_rightSndArgument
  | .transferNoCallbackBox => .paper .transferNoCallbackBox
  | .transferNoCallbackDiamond => .paper .transferNoCallbackDiamond
  | .transferWithCallback => .merged [.transferWithCallbackBox, .transferWithCallbackDiamond]
  -- memory: unfold
  | .memoryFieldReadUnfoldRightFst => .paper .memoryFieldRead_unfold_rightFst
  | .memoryIndexReadUnfoldRightFst => .paper .memoryIndexRead_unfold_rightFst
  | .memoryIndexReadUnfoldRightSndIndex => .paper .memoryIndexRead_unfold_rightSndIndex
  | .memoryFieldReadUnfoldRightSndResult =>
      .merged [.memoryFieldRead_unfold_rightSndResult, .memoryFieldWriteRef_unfold_source]
  | .memoryIndexReadUnfoldRightSndResult =>
      .merged [.memoryIndexRead_unfold_rightSndResult, .memoryIndexWriteRef_unfold_source]
  | .memoryFieldWriteUnfoldLeftFst => .paper .memoryFieldWrite_unfold_leftFst
  | .memoryIndexWriteUnfoldLeftFst => .paper .memoryIndexWrite_unfold_leftFst
  | .memoryFieldWriteRefUnfoldLeftFst => .paper .memoryFieldWriteRef_unfold_leftFst
  | .memoryIndexWriteRefUnfoldLeftFst => .paper .memoryIndexWriteRef_unfold_leftFst
  | .memoryFieldDeleteUnfoldLeftFst => .paper .memoryFieldDelete_unfold_leftFst
  | .memoryIndexDeleteUnfoldLeftFst => .paper .memoryIndexDelete_unfold_leftFst
  | .memoryIndexWriteUnfoldLeftSndIndex => .paper .memoryIndexWrite_unfold_leftSndIndex
  | .memoryIndexWriteRefUnfoldLeftSndIndex => .paper .memoryIndexWriteRef_unfold_leftSndIndex
  | .memoryIndexDeleteNonSimpleIndexCapture => .leanOnly .keyTier
  | .memoryFieldWriteUnfoldSource => .paper .memoryFieldWrite_unfold_source
  | .memoryIndexWriteUnfoldSource => .paper .memoryIndexWrite_unfold_source
  -- memory: terminal
  | .memoryLocalDeclInitDrop => .paper .memoryLocalDeclInitDrop
  | .memoryDeclFreshAlloc => .merged [.memoryDeclFreshAlloc, .memoryArrayFreshAlloc]
  | .memoryFieldWriteStore => .paper .memoryFieldWriteStore
  | .memoryRootAlias => .paper .memoryRootAlias
  | .memoryFieldReadHeap => .paper .memoryFieldReadHeap
  | .memoryFieldReadAliasRoot => .paper .memoryFieldReadAliasRoot
  | .memoryRootDeleteFreshRebind => .paper .memoryRootDeleteFreshRebind
  | .memoryFieldDeletePrimitive => .paper .memoryFieldDeletePrimitive
  | .memoryFieldDeleteReference => .paper .memoryFieldDeleteReference
  | .memoryIndexWriteStoreBox => .paper .memoryIndexWriteStore
  | .memoryIndexWriteStoreDiamond => .paper .memoryIndexWriteStore
  | .memoryIndexReadHeapBox => .paper .memoryIndexReadHeap
  | .memoryIndexReadHeapDiamond => .paper .memoryIndexReadHeap
  | .memoryIndexReadAliasRootBox => .paper .memoryIndexReadAliasRoot
  | .memoryIndexReadAliasRootDiamond => .paper .memoryIndexReadAliasRoot
  | .memoryIndexDeletePrimitiveBox => .paper .memoryIndexDeletePrimitive
  | .memoryIndexDeletePrimitiveDiamond => .paper .memoryIndexDeletePrimitive
  | .memoryIndexDeleteReferenceBox => .paper .memoryIndexDeleteReference
  | .memoryIndexDeleteReferenceDiamond => .paper .memoryIndexDeleteReference
  -- copy
  | .memoryStorageCopyUnfold => .paper .memoryStorageCopyUnfold
  | .memoryStorageCopy => .paper .memoryStorageCopy
  | .memoryToStorageFieldUnfoldLeftFst => .paper .memoryToStorageField_unfold_leftFst
  | .memoryToStorageIndexUnfoldLeftFst => .paper .memoryToStorageIndex_unfold_leftFst
  | .memoryToStorageIndexUnfoldLeftSndIndex => .paper .memoryToStorageIndex_unfold_leftSndIndex
  | .memoryToStorageFieldCopyRoot => .paper .memoryToStorageFieldCopyRoot
  | .memoryToStorageFieldCopyField => .paper .memoryToStorageFieldCopyField
  | .memoryToStorageIndexMappingCopyRoot => .paper .memoryToStorageIndexMappingCopyRoot
  | .memoryToStorageIndexArrayCopyRootBox => .paper .memoryToStorageIndexArrayCopyRoot
  | .memoryToStorageIndexArrayCopyRootDiamond => .paper .memoryToStorageIndexArrayCopyRoot
  | .memoryToStorageStoreRoot => .paper .memoryToStorageStoreRoot
  -- arithmetic: the paper prints `op ∈ {+ - * / %}` once per target, and
  -- a separate divisor-guarded rule where the update has to guard
  | .localOpAssign .div | .localOpAssign .mod => .merged [.localOpAssign, .localDivAssign]
  | .localOpAssign op => paperCompound op .localOpAssign
  | .storageRootOpAssign op => paperCompound op .storageRootOpAssign
  | .storageFieldOpAssign op => paperCompound op .storageFieldOpAssign
  | .storageIndexMappingOpAssign op => paperCompound op .storageIndexMappingOpAssign
  | .storageIndexArrayOpAssign op => paperCompound op .storageIndexArrayOpAssign
  | .storageFieldOpAssignUnfoldLeftFst _ => .leanOnly .keyTier
  | .storageIndexOpAssignUnfoldLeftFst _ => .leanOnly .keyTier
  | .storageRootIncrement _ => .paper .storageRootIncrement
  | .storageFieldIncrement _ => .leanOnly .keyTier
  | .storageIndexIncrement _ => .leanOnly .keyTier
  | .storageFieldIncrementUnfoldLeftFst _ => .leanOnly .keyTier
  | .storageIndexIncrementUnfoldLeftFst _ => .leanOnly .keyTier
  | .storageRootIncrementAssignment _ => .leanOnly .keyTier
  | .storageFieldIncrementAssignment _ => .leanOnly .keyTier
  | .storageIndexIncrementAssignment _ => .leanOnly .keyTier
  | .memoryFieldOpAssign .div | .memoryFieldOpAssign .mod =>
      .merged [.memoryFieldOpAssign, .memoryFieldDivAssign]
  | .memoryFieldOpAssign op => paperCompound op .memoryFieldOpAssign
  | .memoryIndexArrayOpAssign op => paperCompound op .memoryIndexArrayOpAssign
  | .memoryFieldOpAssignUnfoldLeftFst _ => .leanOnly .keyTier
  | .memoryIndexOpAssignUnfoldLeftFst _ => .leanOnly .keyTier
  | .memoryFieldIncrement _ => .paper .memoryFieldIncrement
  | .memoryIndexArrayIncrement _ => .leanOnly .keyTier
  | .memoryFieldIncrementUnfoldLeftFst _ => .leanOnly .keyTier
  | .memoryIndexIncrementUnfoldLeftFst _ => .leanOnly .keyTier
  | .memoryFieldIncrementAssignment _ => .leanOnly .keyTier
  | .memoryIndexArrayIncrementAssignment _ => .leanOnly .keyTier
  -- expressions: solkey's tiers, below what the paper prints
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
  | .unopAssignment .neg => .paper .unaryMinusAssignment
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

/-! ## Which paper rules the table claims -/

/-- Every paper rule some arm of `paperOrigin` names, `transferWithCallback`'s
two included (it is the `transferSemantics` alternative, so it is not in
`ruleNames`). -/
def claimedPaperRules : List PaperRule :=
  ((ruleNames ++ [RuleName.transferWithCallback]).flatMap
    fun r => (paperOrigin r).rules).eraseDups

/-- The paper rules of kind `rule` that **no** Lean rule claims, and why.
One: `ifElseSplit` is a sequent-level two-goal split on a simple condition,
which a single-successor `BlockStep` cannot produce; it is
`SolidityJudgment.ite_split` (`JudgmentSplit.lean`), the same way KeY's
`ifSplit`/`ifElseSplit` are excused in `RuleShapes.unclaimedTaclets`. -/
def unclaimedRules : List PaperRule := [.ifElseSplit]

/-- **The coverage fact**: a paper rule is claimed exactly when it is of kind
`rule` and not excused above.  A rule the paper adds and Lean never ports
fails this; so does an arm that names a template, a rejected rule, or the
first-order axiom. -/
theorem paper_rules_partitioned :
    PaperRule.all.all
      (fun p => claimedPaperRules.contains p
        != (p.kind != .rule || unclaimedRules.contains p)) = true := by
  native_decide

/-! ## The rules with no paper rule -/

/-- The rule instances whose origin is `leanOnly why`, out of `ruleNames`.
Every instance of a parameterized family counts, as in
`RuleShapes.leanOnlyRules`: `localOpAssign .lt` is a listed rule, and the
paper of course prints no `<=` compound assignment. -/
def leanOnlyRules (why : LeanOnlyReason) : List RuleName :=
  ruleNames.filter fun r => paperOrigin r == .leanOnly why

theorem leanOnlyRules_keyTier_count : (leanOnlyRules .keyTier).length = 248 := by
  native_decide

theorem leanOnlyRules_plumbing_count : (leanOnlyRules .plumbing).length = 8 := by
  native_decide

theorem leanOnlyRules_calculus_count : (leanOnlyRules .calculus).length = 5 := by
  native_decide

/-- And the complement: 159 of the 420 instances name a paper rule, claiming
122 of the paper's 123 rules of kind `rule` between them. -/
theorem rules_with_paper_origin_count :
    (ruleNames.filter fun r => (paperOrigin r).rules != []).length = 159 := by
  native_decide

theorem claimedPaperRules_count : claimedPaperRules.length = 122 := by native_decide

end PaperRules
end Solidity
