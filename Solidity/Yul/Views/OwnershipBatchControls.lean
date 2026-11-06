import Solidity.Yul.Views.OwnershipElement
import Solidity.Yul.Views.OwnershipTailControls

namespace Solidity.Yul.Views.Controls

theorem ot_actual_batch : runOwnership? packedStepFrame dynComputed dynTestFixed
    [(43,0),(45,0),(43,3),(45,1)] dynSnapshotRun.2 otResidual =
      (some (.ok ()),otGrowY.step.1.2,otGrowY.step.2) := by
  rw [otShrinkX.batch_nonstatic _ rfl,otShrinkY.batch_nonstatic _ rfl,
      otGrowX.batch_nonstatic _ rfl,otGrowY.batch_nonstatic _ rfl]
  rfl

theorem ot_static_no_residual_update : otShrinkX.asStatic.step =
    ((.error (.revert []),dynSnapshotRun.2),otResidual) := otShrinkX.static_preserves_both

theorem ot_static_batch_stops : runOwnership? {packedStepFrame with static := true} dynComputed dynTestFixed
    [(43,0),(45,0),(43,3),(45,1)] dynSnapshotRun.2 otResidual =
      (some (.error (.revert [])),dynSnapshotRun.2,otResidual) :=
  otShrinkX.asStatic.batch_static _ rfl

theorem ot_transaction_whole_persistent : finiteEncode otGrowY.next
    ((companionEndTx otGrowY.after).source.world.accounts account).storage
    (fun q => (companionEndTx otGrowY.after).residual.cells (complementKey false account q)) = some otRaw31 :=
  (otGrowY.endTx_reencode rfl).trans (congrArg some ot_grow_y_next)

def otAliases : Source.EMState dynEnv [dynArray,dynArray] :=
  ⟨.cons dynX.reference (.cons dynX.reference .nil),otGrowY.step.1.2.2⟩

theorem ot_alias_readLen : (Source.readLen (E := dynEnv) packedStepFrame (dynPath "xs")).run otAliases = (.ok 3,otAliases) := by
  have member := dynComputed.snapshot_root_member dynTestFixed otGrowY.nextRaw (dynX.registration account) dyn_header_member.1
  have view := otGrowY.view rfl (dynX.registration account) member
  have cell := dynX.view_length_cell account _ otGrowY.nextRaw view
  have read := dynX.readLen packedStepFrame otAliases (otGrowY.nextRaw 43) rfl cell
  rw [ot_grow_y_next] at read
  exact read

theorem ot_two_actual_local_aliases :
    (Source.lengthOf (E := dynEnv) packedStepFrame (otAliases.1.get .here)).run otAliases = (.ok 3,otAliases) ∧
    (Source.lengthOf (E := dynEnv) packedStepFrame (otAliases.1.get (.there .here))).run otAliases = (.ok 3,otAliases) :=
  ⟨ot_alias_readLen,ot_alias_readLen⟩

theorem ot_alias_index_tail :
    (Source.indexLoc (E := dynEnv) packedStepFrame (otAliases.1.get (.there .here)) 2).run otAliases =
      (.ok (.stor ⟨dynName "xs",[.index 2]⟩),otAliases) :=
  dynX.indexLoc packedStepFrame otAliases 3 ot_alias_readLen 2

theorem ot_late_static_preserves_prefix : otShrinkY.asStatic.step =
    ((.error (.revert []),otShrinkX.step.1.2),otShrinkX.step.2) := otShrinkY.static_preserves_both

theorem ot_other_account : otGrowY.after.source.world.accounts (⟨2,by decide⟩) =
    dynSnapshotRun.2.2.ex.world.accounts (⟨2,by decide⟩) :=
  (otGrowY.account_other _ (by decide)).trans ((otGrowX.account_other _ (by decide)).trans
    ((otShrinkY.account_other _ (by decide)).trans (otShrinkX.account_other _ (by decide))))

theorem ot_other_transient_bank : otGrowY.after.source.transient = dynSnapshotRun.2.2.ex.transient :=
  otGrowY.transient_unchanged.trans (otGrowX.transient_unchanged.trans
    (otShrinkY.transient_unchanged.trans otShrinkX.transient_unchanged))

theorem ot_other_residual_bank (q : Roadmap.Word) :
    otGrowY.step.2.cells (complementKey true account q) = otResidual.cells (complementKey true account q) :=
  (otGrowY.other_key _ (Or.inl (by change true ≠ false; decide))).trans ((otGrowX.other_key _ (Or.inl (by change true ≠ false; decide))).trans
    ((otShrinkY.other_key _ (Or.inl (by change true ≠ false; decide))).trans (otShrinkX.other_key _ (Or.inl (by change true ≠ false; decide)))))

theorem ot_alias_tail_payload :
    (Source.readLoc (E := dynEnv) packedStepFrame (Source.Loc.stor (τ := .int .u256) ⟨dynName "xs",[.index 2]⟩)).run otAliases =
      (.ok (uintValueOfWord dynEnv.layout 77),otAliases) := by
  have member : dynX.element dynTestFixed account 2 ∈ otGrowY.next := by
    rw [ot_grow_y_inventory]
    have member := dynComputed.snapshot_element_member dynTestFixed otRaw31 dynXTrace 2 (by decide)
    rw [(dynComputed.traceHeader dynXTrace).proof_irrel dynX] at member
    exact member
  have bank := dynComputed.snapshot_bank_agreement dynTestFixed otGrowY.nextRaw (dynX.element dynTestFixed account 2) member
  have view := otGrowY.view rfl (dynX.element dynTestFixed account 2) member
  have read := dynX.read_element packedStepFrame otAliases dynTestFixed 2 otGrowY.nextRaw bank view
  rw [ot_grow_y_next] at read
  exact read

theorem ot_alias_index_then_read :
    (do
      let loc ← Source.indexLoc (E := dynEnv) packedStepFrame (otAliases.1.get (.there .here)) 2
      Source.readLoc packedStepFrame loc).run otAliases = (.ok (uintValueOfWord dynEnv.layout 77),otAliases) := by
  rw [Source.Hoare.run_bind,ot_alias_index_tail]
  exact ot_alias_tail_payload

end Solidity.Yul.Views.Controls
