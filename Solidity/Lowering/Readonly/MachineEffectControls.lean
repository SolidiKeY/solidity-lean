import Solidity.Lowering.Readonly.MachineEffects
import Solidity.Lowering.Readonly.Controls

/-! Inhabited memory effects, type refusal and caught-revert controls. Catching
a halt does not rewind heap writes; this is not a child-frame rollback claim. -/
namespace Solidity.Lowering.Readonly.MachineEffectControls
open Solidity.Source Solidity.Source.SemanticsExamples
open SourceHistory

def program : EM EB [] Unit := do
  let a ← alloc (Data.bytes (l := .memory) [1])
  heapPut a ⟨.bytes .memory, .bytes [2]⟩
  EM.halt (.revert [7])

def badType : EM EB [] Unit := do
  let a ← alloc (Data.bytes (l := .memory) [1])
  heapPut a ⟨.string .memory, .string [3]⟩

def result := program.run (L0 EB, sB)
def caught := (EM.attempt program).run (L0 EB, sB)
def refused := badType.run (L0 EB, sB)


theorem observations :
    result.1 = .error (.revert [7]) ∧
    result.2.2.heap.get 0 = some ⟨.bytes .memory, .bytes [2]⟩ ∧
    caught.1 = .ok (.error (.revert [7])) ∧
    caught.2.2.heap.get 0 = some ⟨.bytes .memory, .bytes [2]⟩ ∧
    refused.1 = .error (.stuck "memory write type") ∧
    refused.2.2.heap.get 0 = some ⟨.bytes .memory, .bytes [1]⟩ ∧
    result.2.2.ex = sB.ex ∧ refused.2.2.ex = sB.ex := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

theorem program_effect (mode : Bool) : Effect mode program := by
  unfold program
  apply Effect.bind
  · exact alloc_effect mode _
  · intro a
    apply Effect.bind
    · exact heapPut_effect mode _ _
    · intro done
      exact Effect.halt mode _

theorem refused_effect (mode : Bool) : Effect mode badType := by
  unfold badType
  apply Effect.bind
  · exact alloc_effect mode _
  · intro a
    exact heapPut_effect mode _ _

/-- The parent rule cannot be reversed on an actual mutating operation. -/
theorem ordinary_cannot_upgrade :
    ¬ Effect true (applyOp (E := EB) (Γ := []) {FC with static := false}
      Controls.writeOp) := by
  intro h
  have history := h (L0 EB) sB
  exact Controls.static_cannot_write history

end Solidity.Lowering.Readonly.MachineEffectControls
