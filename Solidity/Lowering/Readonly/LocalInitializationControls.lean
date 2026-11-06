import Solidity.Lowering.Readonly.LocalInitializationEffects
import Solidity.Lowering.Readonly.CopyControls

/-! Inhabited Source initialization controls with distinct caller/result contexts.
Memory allocation before a later refusal remains in the raw reached state;
there is no implicit rollback or native deployment provenance. -/
namespace Solidity.Lowering.Readonly.LocalInitializationControls
open Solidity.Source
open SourceHistory

abbrev E := CopyControls.E
abbrev entry := CopyControls.loaded.2.2
def caller : Locals E.layout [.bool] := .cons (.bool false) .nil
def slots : Locals E.layout [.bytes .memory, .bool] :=
  .cons (.memRef rfl 0) (.cons (.bool true) .nil)

def reset := (zeroInner (Γ' := [.bool]) 2 1 slots).run (caller, entry)
def exhausted := (zeroInner (Γ' := [.bool]) 0 1 slots).run (caller, entry)
def skipped := (zeroInner (Γ' := [.bool]) 0 0 slots).run (caller, entry)
def values := (zeroVals 2 [.bytes .memory, .bool] : EM E [.bool] _).run (caller, entry)
def failedAfterAllocation := (zeroVals 2 [.bytes .memory, .bytes .storage] : EM E [.bool] _).run (caller, entry)
def empty := (zeroVals 0 [] : EM E [.bool] _).run (caller, entry)


theorem observations : reset.1 = .ok (.cons (.memRef (by rfl) 1) (.cons (.bool true) .nil)) ∧
 reset.2.1 = caller ∧
 reset.2.2.heap.get 1 = some ⟨.bytes .memory, .bytes []⟩ ∧
 reset.2.2.heap.next = 2 ∧
 reset.2.2.ex = entry.ex ∧
 exhausted.1 = .error .timeout ∧
 exhausted.2.2.heap.next = 1 ∧
 exhausted.2.1 = caller ∧
 skipped.1 = .ok slots ∧
 skipped.2.2.heap.next = 1 ∧
 values.1 = .ok (.cons (.memRef (by rfl) 1) (.cons (.bool false) .nil)) ∧
 values.2.2.ex = entry.ex ∧
 failedAfterAllocation.1 = .error (.stuck "no default value") ∧
 failedAfterAllocation.2.2.heap.next = 2 ∧
 failedAfterAllocation.2.2.heap.get 1 = some ⟨.bytes .memory, .bytes []⟩ ∧
 failedAfterAllocation.2.1 = caller ∧
 failedAfterAllocation.2.2.ex = entry.ex ∧
 empty.1 = .ok .nil ∧
 empty.2.2.heap.next = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

theorem client : ∀ mode n k, Solidity.Lowering.Readonly.SourceHistory.Effect mode (Solidity.Source.zeroInner (Γ' := [.bool]) n k slots) := by
  intro mode n k
  exact SourceHistory.zeroInner_effect mode n k slots

end Solidity.Lowering.Readonly.LocalInitializationControls
