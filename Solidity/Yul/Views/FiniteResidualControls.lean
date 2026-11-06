import Solidity.Yul.Views.FiniteControls
import Solidity.Yul.Views.FiniteResidual

/-! Finite registered paths, actual typed source batches and residual journaling.
Registration is not completeness for all source paths; transient snapshots here
are within a transaction, not initialization or admission claims. -/
namespace Solidity.Yul.Views.Controls

def finiteTxRegistration : ScalarPath layout allBool := ⟨txPath, 0, boolField, txCodec, .bool⟩
def finiteRegistered : ResidualOwnership := registeredOwnership
  (L := finitePerAccount) (T := perAccount) (fun _ => finitePaths) (fun _ => [finiteTxRegistration])

def finitePersistentKey : ResidualKey finiteRegistered := ⟨false, account, 99, by
  intro h
  change ∃ c ∈ finitePaths, c.slot = 99 at h
  obtain ⟨c, hc, hs⟩ := h
  simp only [finitePaths, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact (by decide : flagPathCodec.slot ≠ 99) hs
  · exact (by decide : smallPathCodec.slot ≠ 99) hs
  · exact (by decide : widePathCodec.slot ≠ 99) hs⟩
def finiteTransientKey : ResidualKey finiteRegistered := ⟨true, account, 99, by
  intro h
  change ∃ c ∈ [finiteTxRegistration], c.slot = 99 at h
  obtain ⟨c, hc, hs⟩ := h
  have he := List.mem_singleton.mp hc
  subst c
  exact (by decide : finiteTxRegistration.slot ≠ 99) hs⟩

def finiteResidualBase := saveSlot nonzeroSlots 99 42
def finiteResidualTarget : SlotView := (finiteEncode finitePaths finiteTarget finiteResidualBase).getD nonzeroSlots

theorem finite_registered_slot_preserved : finiteResidualTarget 99 = 42 := by
  have he : finiteEncode finitePaths finiteTarget finiteResidualBase = some finiteResidualTarget := rfl
  have hp := finiteEncode_registered_residual
    (L := finitePerAccount) (T := perAccount) (fun _ => finitePaths) (fun _ => [finiteTxRegistration])
    finitePersistentKey rfl finiteTarget finiteResidualBase finiteResidualTarget he
  exact hp.trans (find_saveSlot nonzeroSlots 99 42)

def finiteCompanionInitial : ResidualCompanion layout finitePerAccount perAccount finiteRegistered :=
  ⟨finiteInitial, ⟨fun _ => 165, []⟩⟩
def finiteResidualPrefix : List (ResidualKey finiteRegistered × Roadmap.Word) := [(finitePersistentKey, 42)]
def finiteResidualChild : List (ResidualKey finiteRegistered × Roadmap.Word) :=
  [(finitePersistentKey, 43), (finiteTransientKey, 7)]
def finiteCompanionCaller := companionRunResidual (companionRunSource finiteCompanionInitial [finitePrefixOp]) finiteResidualPrefix
def finiteCompanionChild := companionRunResidual (companionRunSource finiteCompanionCaller finiteChildren) finiteResidualChild

theorem finite_combined_changed :
    (finiteCompanionChild.source.world.accounts account).storage = finiteTarget ∧
    finiteCompanionChild.residual.cells finitePersistentKey = 43 ∧
    finiteCompanionChild.residual.cells finiteTransientKey = 7 := ⟨rfl, rfl, rfl⟩

theorem finite_combined_inner_rollback :
    companionRollback (companionEnter finiteCompanionCaller account account 0 [] false) finiteCompanionChild = finiteCompanionCaller :=
  companionRollback_run finiteCompanionCaller finiteChildren finiteResidualChild account account 0 [] false

theorem finite_combined_outer_commit_revert :
    companionRollback (companionEnter finiteCompanionInitial account account 0 [] false)
      (companionCommit (companionEnter finiteCompanionCaller account account 0 [] false) finiteCompanionChild) = finiteCompanionInitial :=
  companionRollback_outer_commit finiteCompanionInitial [finitePrefixOp] finiteChildren finiteResidualPrefix finiteResidualChild account account 0 [] false

theorem finite_combined_reset :
    ((companionEndTx finiteCompanionChild).source.world.accounts account).storage = finiteTarget ∧
    ((companionEndTx finiteCompanionChild).source.transient.cells account).cell txPath = none ∧
    (companionEndTx finiteCompanionChild).residual.cells finitePersistentKey = 43 ∧
    (companionEndTx finiteCompanionChild).residual.cells finiteTransientKey = 0 ∧
    (companionEndTx finiteCompanionChild).source.journal = [] ∧
    (companionEndTx finiteCompanionChild).residual.journal = [] := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

#print axioms finite_registered_slot_preserved
#print axioms finite_combined_outer_commit_revert
end Solidity.Yul.Views.Controls
