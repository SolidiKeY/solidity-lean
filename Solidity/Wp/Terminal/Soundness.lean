import Solidity.Completeness
import Solidity.Wp.Terminal.UpdateControl
import Solidity.Wp.Terminal.UpdateStack
import Solidity.Wp.Terminal.UpdateCompound
import Solidity.Wp.Terminal.UpdateStorage
import Solidity.Wp.Terminal.UpdateMemory
import Solidity.Wp.Terminal.UpdateDecl
import Solidity.Wp.Terminal.UpdatePushPop

/-!
# Terminal rules: the state-carrying bridge

Every *terminal* rule of the calculus (empty residual block in `Rules.ruleEffect`)
has a state update in `Wp/Terminal/Table.lean` (`terminalUpdate?`), and
a theorem `<rule>_update` in `Wp/Terminal/Update*.lean` proving, under
the rule's guard,

    execStmt s stmt = terminalUpdate r stmt s.

This module assembles them:

* `terminalUpdate_sound` — the dispatch: for every rule in the table, on
  every statement its guard accepts, the interpreter computes the update.
* `TerminalRuleStep` / `terminal_step_sound` — a first step of a named
  terminal rule (the rule name is an index, so the bridge needs no
  existential) yields the update at every state: the "taclet ⇒ update"
  statement the port set out to prove.
* `IsTerminal` / `isTerminal_of_hasUpdate` — every rule in the table has an
  empty residual, checked against `ruleEffect` itself.

What is *not* here: the converse `IsTerminal r → hasUpdate r` on
`ruleNames` (that no unfold rule is accidentally terminal) needs a
non-terminality witness per unfold rule; it is not proved.  The only update
that keeps an interpreter call is `storagePlaceAliasUpd` (an impure captured
path), with the pure form `storagePlaceAliasUpd_pure`.

Coverage by family (rule names as in `RuleName`):

* `Terminal/UpdateControl.lean` — revert{Box,Diamond}, assertSimple,
  requireSimple, transferNoCallback.
* `Terminal/UpdateStack.lean` — storageRootReadSelect, storageFieldReadFind,
  storageIndexRead{ArrayFind{Box,Diamond},MappingFind}, memoryFieldReadHeap,
  memoryIndexReadHeap{Box,Diamond}, localValueAssign, binopAssignment op,
  unopAssignment op, localAssignIncDec op,
  storage{Root,Field,Index}IncDecAssignment op,
  memory{Field,Index}IncDecAssignment op.
* `Terminal/UpdateCompound.lean` — localCompoundAssign op,
  storage{Root,Field,Index}CompoundAssign op, localIncDec op,
  storage{Root,Field,Index}IncDec op, and the memory-target arithmetic
  twins memory{Field,Index}CompoundAssign op, memory{Field,Index}IncDec op
  (no root form: a memory root binds an identity, not a value cell).
* `Terminal/UpdateStorage.lean` — storageRootWrite{Store,CopySource},
  memoryToStorageStoreRoot, storageLocalRootRebind,
  storageFieldWrite{Save,CopySource}, memoryToStorageFieldCopyRoot,
  storageIndexWrite{Array{Save,CopySource}{Box,Diamond},Mapping{Save,CopySource}},
  memoryToStorageIndex{Mapping,ArrayBox,ArrayDiamond}CopyRoot,
  storage{Field,IndexBox,IndexDiamond,IndexMapping}Read{BindLocalRoot,StoreRoot}.
* `Terminal/UpdateMemory.lean` — memoryRootAlias, memoryStorageCopy,
  memoryFieldWrite{Store,Copy}, memoryIndexWrite{Store,Copy}{Box,Diamond},
  memoryFieldReadAliasRoot, memoryIndexReadAliasRoot{Box,Diamond}.
* `Terminal/UpdateDecl.lean` — valueDeclSkip, storageLocalDeclSkip,
  storagePlaceAlias, memoryDeclFreshAlloc, storageToMemoryDeclCopy{Field,Root},
  storageDeleteSimpleTarget, memoryDeleteSimpleTarget (all sub-shapes).
* `Terminal/UpdatePushPop.lean` — storagePushValue{Save,CopySource},
  storagePushLengthSave, storagePopSave{Box,Diamond}, storageLocalRootPushBind.

`transferWithCallback` is not in `ruleNames`; its meaning is
`CallbackSemantics.ExecC`, not a state update, so it has no table entry.
-/

namespace Solidity
namespace Wp

open Semantics Rules

set_option maxHeartbeats 4000000 in
/-- **The dispatch**: on every statement a table rule's guard accepts, the
interpreter computes that rule's update. -/
theorem terminalUpdate_sound (r : RuleName) (hr : hasUpdate r = true)
    (stmt : Stmt) (s : State) (hcond : (ruleEffect r).cond stmt) :
    execStmt s stmt = terminalUpdate r stmt s := by
  cases r
  case storageRootReadSelect =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageRootReadSelect_update s _ _ hcond
  case storageFieldReadFind =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageFieldReadFind_update s _ _ hcond
  case storageIndexReadArrayFindBox =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageIndexReadArrayFindBox_update s _ _ hcond
  case storageIndexReadArrayFindDiamond =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageIndexReadArrayFindDiamond_update s _ _ hcond
  case storageIndexReadMappingFind =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageIndexReadMappingFind_update s _ _ hcond
  case memoryFieldReadHeap =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryFieldReadHeap_update s _ _ hcond
  case memoryIndexReadHeapBox =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryIndexReadHeapBox_update s _ _ hcond
  case memoryIndexReadHeapDiamond =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryIndexReadHeapDiamond_update s _ _ hcond
  case localValueAssign =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact localValueAssign_update s _ _ hcond
  case storageFieldReadBindLocalRoot =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageFieldReadBindLocalRoot_update s _ _ hcond
  case storageIndexReadArrayBindLocalRootBox =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageIndexReadArrayBindLocalRootBox_update s _ _ hcond
  case storageIndexReadArrayBindLocalRootDiamond =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageIndexReadArrayBindLocalRootDiamond_update s _ _ hcond
  case storageIndexReadMappingBindLocalRoot =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageIndexReadMappingBindLocalRoot_update s _ _ hcond
  case storageLocalRootRebind =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageLocalRootRebind_update s _ _ hcond
  case storageFieldReadStoreRoot =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageFieldReadStoreRoot_update s _ _ hcond
  case storageIndexReadArrayStoreRootBox =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageIndexReadArrayStoreRootBox_update s _ _ hcond
  case storageIndexReadArrayStoreRootDiamond =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageIndexReadArrayStoreRootDiamond_update s _ _ hcond
  case storageIndexReadMappingStoreRoot =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageIndexReadMappingStoreRoot_update s _ _ hcond
  case storageRootWriteStore =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageRootWriteStore_update s _ _ hcond
  case storageRootWriteCopySource =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageRootWriteCopySource_update s _ _ hcond
  case memoryToStorageStoreRoot =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryToStorageStoreRoot_update s _ _ hcond
  case storageFieldWriteSave =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageFieldWriteSave_update s _ _ hcond
  case storageFieldWriteCopySource =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageFieldWriteCopySource_update s _ _ hcond
  case memoryToStorageFieldCopyRoot =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryToStorageFieldCopyRoot_update s _ _ hcond
  case storageIndexWriteArraySaveBox =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageIndexWriteArraySaveBox_update s _ _ hcond
  case storageIndexWriteArraySaveDiamond =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageIndexWriteArraySaveDiamond_update s _ _ hcond
  case storageIndexWriteMappingSave =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageIndexWriteMappingSave_update s _ _ hcond
  case storageIndexWriteArrayCopySourceBox =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageIndexWriteArrayCopySourceBox_update s _ _ hcond
  case storageIndexWriteArrayCopySourceDiamond =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageIndexWriteArrayCopySourceDiamond_update s _ _ hcond
  case storageIndexWriteMappingCopySource =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageIndexWriteMappingCopySource_update s _ _ hcond
  case memoryToStorageIndexMappingCopyRoot =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryToStorageIndexMappingCopyRoot_update s _ _ hcond
  case memoryToStorageIndexArrayCopyRootBox =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryToStorageIndexArrayCopyRootBox_update s _ _ hcond
  case memoryToStorageIndexArrayCopyRootDiamond =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryToStorageIndexArrayCopyRootDiamond_update s _ _ hcond
  case storageLocalRootPushBind =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageLocalRootPushBind_update s _ _ hcond
  case memoryRootAlias =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryRootAlias_update s _ _ hcond
  case memoryStorageCopy =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryStorageCopy_update s _ _ hcond
  case memoryFieldWriteStore =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryFieldWriteStore_update s _ _ hcond
  case memoryFieldWriteCopy =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryFieldWriteCopy_update s _ _ hcond
  case memoryIndexWriteStoreBox =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryIndexWriteStoreBox_update s _ _ hcond
  case memoryIndexWriteStoreDiamond =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryIndexWriteStoreDiamond_update s _ _ hcond
  case memoryIndexWriteCopyBox =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryIndexWriteCopyBox_update s _ _ hcond
  case memoryIndexWriteCopyDiamond =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryIndexWriteCopyDiamond_update s _ _ hcond
  case memoryFieldReadAliasRoot =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryFieldReadAliasRoot_update s _ _ hcond
  case memoryIndexReadAliasRootBox =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryIndexReadAliasRootBox_update s _ _ hcond
  case memoryIndexReadAliasRootDiamond =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryIndexReadAliasRootDiamond_update s _ _ hcond
  case binopAssignment op =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact binopAssignment_update op s _ _ hcond
  case unopAssignment op =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact unopAssignment_update op s _ _ hcond
  case localAssignIncDec op =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact localAssignIncDec_update op s _ _ hcond
  case storageRootIncDecAssignment op =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageRootIncDecAssignment_update op s _ _ hcond
  case storageFieldIncDecAssignment op =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageFieldIncDecAssignment_update op s _ _ hcond
  case storageIndexIncDecAssignment op =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageIndexIncDecAssignment_update op s _ _ hcond
  case memoryFieldIncDecAssignment op =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryFieldIncDecAssignment_update op s _ _ hcond
  case memoryIndexIncDecAssignment op =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryIndexIncDecAssignment_update op s _ _ hcond
  case localCompoundAssign op =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact localCompoundAssign_update op _ s _ _ hcond
  case storageRootCompoundAssign op =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageRootCompoundAssign_update op _ s _ _ hcond
  case storageFieldCompoundAssign op =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageFieldCompoundAssign_update op _ s _ _ hcond
  case storageIndexCompoundAssign op =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageIndexCompoundAssign_update op _ s _ _ hcond
  case memoryFieldCompoundAssign op =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryFieldCompoundAssign_update op _ s _ _ hcond
  case memoryIndexCompoundAssign op =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryIndexCompoundAssign_update op _ s _ _ hcond
  case localIncDec op =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact localIncDec_update op s _ hcond
  case storageRootIncDec op =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageRootIncDec_update op s _ hcond
  case storageFieldIncDec op =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageFieldIncDec_update op s _ hcond
  case storageIndexIncDec op =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageIndexIncDec_update op s _ hcond
  case memoryFieldIncDec op =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryFieldIncDec_update op s _ hcond
  case memoryIndexIncDec op =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryIndexIncDec_update op s _ hcond
  case valueDeclSkip =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact valueDeclSkip_update s _ _ _ hcond
  case storageLocalDeclSkip =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageLocalDeclSkip_update s _ _ _ hcond
  case storagePlaceAlias =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storagePlaceAlias_update s _ _ _ hcond
  case memoryDeclFreshAlloc =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryDeclFreshAlloc_update s _ _ _ hcond
  case storageToMemoryDeclCopyField =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageToMemoryDeclCopyField_update s _ _ _ hcond
  case storageToMemoryDeclCopyRoot =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageToMemoryDeclCopyRoot_update s _ _ _ hcond
  case storageDeleteSimpleTarget =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storageDeleteSimpleTarget_update s _ hcond
  case memoryDeleteSimpleTarget =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact memoryDeleteSimpleTarget_update s _ hcond
  case storagePushValueSave =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storagePushValueSave_update s _ _ hcond
  case storagePushValueCopySource =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storagePushValueCopySource_update s _ _ hcond
  case storagePushLengthSave =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storagePushLengthSave_update s _ _ hcond
  case storagePopSaveBox =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storagePopSaveBox_update s _ hcond
  case storagePopSaveDiamond =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact storagePopSaveDiamond_update s _ hcond
  case revertBox =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact revertBox_update s _ hcond
  case revertDiamond =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact revertDiamond_update s _ hcond
  case assertSimple =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact assertSimple_update s _ hcond
  case requireSimple =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact requireSimple_update s _ hcond
  case transferNoCallback =>
      cases stmt <;> first
        | exact (hcond : False).elim
        | exact transferNoCallback_update s _ _ hcond
  all_goals exact Bool.noConfusion hr

/-- A first step of a *named* terminal rule.  `FirstStepCase` carries the
step case, so the rule name is an index rather than an existential. -/
abbrev TerminalRuleStep (sm : SolidityModality) (lhs : Stmt) (r : RuleName)
    (cond : Prop) : Prop :=
  FirstStepCase sm lhs Rules.stepCases (Rules.stepCase r) cond []

theorem TerminalRuleStep.toRuleStep {sm : SolidityModality} {lhs : Stmt}
    {r : RuleName} {cond : Prop} (h : TerminalRuleStep sm lhs r cond) :
    RuleStep sm lhs cond [] :=
  RuleStep.ofStepCase h

/-- **Taclet ⇒ update**: a terminal step of rule `r` computes `r`'s update
at every state. -/
theorem terminal_step_sound {sm : SolidityModality} {lhs : Stmt} {r : RuleName}
    {cond : Prop} (s : State) (hr : hasUpdate r = true)
    (hstep : TerminalRuleStep sm lhs r cond) :
    execStmt s lhs = terminalUpdate r lhs s :=
  terminalUpdate_sound r hr lhs s (FirstStepCase.effect_cond_holds hstep)

/-! ## The table is a table of terminal rules -/

/-- A rule is terminal when its residual is empty on every statement its
guard accepts. -/
def IsTerminal (r : RuleName) : Prop :=
  ∀ (stmt : Stmt) (h : (ruleEffect r).cond stmt),
    (ruleEffect r).block stmt h = []

set_option maxHeartbeats 4000000 in
/-- Every rule in the update table has an empty residual — checked against
`ruleEffect`, not against a second hand-written table. -/
theorem isTerminal_of_hasUpdate (r : RuleName) (hr : hasUpdate r = true) :
    IsTerminal r := by
  intro stmt h
  cases r <;> first
    | exact Bool.noConfusion hr
    | (cases stmt <;> first | exact (h : False).elim | rfl)

end Wp
end Solidity
