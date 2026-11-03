import Solidity.Yul.Views.ResidualJournal
import Solidity.Yul.Views.ScalarWritebackControls

/-! Fixed registered ownership is deliberately scoped to the canonical bool
components, not all paths of the source store. Actual typed source updates and
nonzero complete unowned slots share frame rollback/reset controls. -/
namespace Solidity.Yul.Views.Controls

def boolOwnership (transient : Bool) (_ : Roadmap.Address) (slot : Roadmap.Word) : Prop :=
  if transient then slot.val = 0 else slot.val = 7

def persistentResidual : ResidualKey boolOwnership := ⟨false, account, ⟨99, by decide⟩, by change ¬(99 = 7); decide⟩
def transientResidual : ResidualKey boolOwnership := ⟨true, account, ⟨99, by decide⟩, by change ¬(99 = 0); decide⟩
def untouchedResidual : ResidualKey boolOwnership := ⟨false, account, ⟨100, by decide⟩, by change ¬(100 = 7); decide⟩

def residualInitial : ResidualJournal boolOwnership := ⟨fun _ => ⟨165, by decide⟩, []⟩
def companionInitial : ResidualCompanion layout perAccount perAccount boolOwnership :=
  ⟨initial, residualInitial⟩
def residualCallerWrites : List (ResidualKey boolOwnership × Roadmap.Word) := [(persistentResidual, ⟨42, by decide⟩)]
def residualChildWrites : List (ResidualKey boolOwnership × Roadmap.Word) :=
  [(persistentResidual, ⟨43, by decide⟩), (transientResidual, ⟨7, by decide⟩)]
def companionCaller := companionRunResidual (companionRunSource companionInitial [firstSourceOp]) residualCallerWrites
def companionChild := companionRunResidual (companionRunSource companionCaller childChanges) residualChildWrites

theorem actual_residual_source_writes :
    ((companionChild.source.world.accounts account).storage.cell firstPath = some (.bool true)) ∧
    ((companionChild.source.world.accounts account).storage.cell secondPath = some (.bool true)) ∧
    ((companionChild.source.transient.cells account).cell txPath = some (.bool true)) ∧
    companionChild.residual.cells persistentResidual = ⟨43, by decide⟩ ∧
    companionChild.residual.cells transientResidual = ⟨7, by decide⟩ ∧
    companionChild.residual.cells untouchedResidual = ⟨165, by decide⟩ ∧
    companionChild.source.journal.length = 3 ∧ companionChild.residual.journal.length = 3 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem residual_inner_revert_prefix :
    companionRollback (companionEnter companionCaller account account 0 [] false) companionChild = companionCaller ∧
    companionCaller.residual.cells persistentResidual = ⟨42, by decide⟩ ∧
    companionCaller.residual.cells transientResidual = ⟨165, by decide⟩ ∧
    (companionCaller.source.world.accounts account).storage.cell firstPath = some (.bool true) := by
  exact ⟨companionRollback_run companionCaller childChanges residualChildWrites account account 0 [] false,
    rfl, rfl, rfl⟩

theorem residual_outer_revert_after_child_commit :
    companionRollback (companionEnter companionInitial account account 0 [] false)
      (companionCommit (companionEnter companionCaller account account 0 [] false) companionChild) = companionInitial :=
  companionRollback_outer_commit companionInitial [firstSourceOp] childChanges
    residualCallerWrites residualChildWrites account account 0 [] false

theorem residual_repeated_write_restored :
    residualUndoN 2 (residualRun residualInitial
      [(persistentResidual, ⟨42, by decide⟩), (persistentResidual, ⟨43, by decide⟩)]) = residualInitial :=
  residualUndoN_run residualInitial [(persistentResidual, ⟨42, by decide⟩), (persistentResidual, ⟨43, by decide⟩)]

theorem residual_unrelated_slot : companionChild.residual.cells untouchedResidual = residualInitial.cells untouchedResidual :=
  residualRun_other _ (residualCallerWrites ++ residualChildWrites) _ (by
    intro w hw
    simp only [residualCallerWrites, residualChildWrites, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hw
    rcases hw with (rfl | rfl | rfl) <;> decide)

theorem residual_transaction_reset :
    ((companionEndTx companionChild).source.world.accounts account).storage.cell secondPath = some (.bool true) ∧
    ((companionEndTx companionChild).source.transient.cells account).cell txPath = none ∧
    (companionEndTx companionChild).residual.cells persistentResidual = ⟨43, by decide⟩ ∧
    (companionEndTx companionChild).residual.cells transientResidual = ⟨0, by decide⟩ ∧
    (companionEndTx companionChild).source.journal = [] ∧
    (companionEndTx companionChild).residual.journal = [] := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A source-owned slot cannot be supplied as a residual key. -/
theorem cannot_key_owned_persistent : ¬∃ k : ResidualKey boolOwnership,
    k.transient = false ∧ k.slot = scalarSlot := by
  rintro ⟨k, ht, hs⟩
  apply k.unowned
  simp only [boolOwnership, ht, hs, Bool.false_eq_true, ↓reduceIte, scalarSlot]

theorem cannot_key_owned_transient : ¬∃ k : ResidualKey boolOwnership,
    k.transient = true ∧ k.slot.val = 0 := by
  rintro ⟨k, ht, hs⟩
  apply k.unowned
  simp only [boolOwnership, ht, ↓reduceIte, hs]

#print axioms residual_outer_revert_after_child_commit
#print axioms residual_inner_revert_prefix
#print axioms residual_transaction_reset
end Solidity.Yul.Views.Controls
