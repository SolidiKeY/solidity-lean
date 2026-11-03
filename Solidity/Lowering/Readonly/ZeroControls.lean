import Solidity.Lowering.Readonly.ZeroEffects
import Solidity.Lowering.Readonly.Controls

/-! Inhabited actual Source zero-initialization controls. These observe memory
allocation without a journal write, plus exhaustion and missing-default refusal. -/
namespace Solidity.Lowering.Readonly.ZeroControls
open Solidity.Source Solidity.Source.SemanticsExamples
open SourceHistory

def allocated := (zeroVal 2 (.bytes .memory) : EM EB [] _).run (L0 EB, sB)
def exhausted := (zeroVal 1 (.bytes .memory) : EM EB [] _).run (L0 EB, sB)
def refused := (zeroVal 2 (.bytes .storage) : EM EB [] _).run (L0 EB, sB)
def scalar := (zeroVal 1 uint : EM EB [] _).run (L0 EB, sB)


theorem observations :
    allocated.1 = .ok (.memRef (by rfl) 0) ∧
    allocated.2.2.heap.get 0 = some ⟨.bytes .memory, .bytes []⟩ ∧
    allocated.2.2.heap.next = 1 ∧
    allocated.2.2.ex = sB.ex ∧
    exhausted.1 = .error .timeout ∧
    exhausted.2.2.heap.next = 0 ∧
    refused.1 = .error (.stuck "no default value") ∧
    refused.2.2.heap.next = 0 ∧
    scalar.1 = .ok (.int 0 (by decide)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

theorem history (mode : Bool) (n : Nat) :
    StaticJournal.History sB.ex mode
      ((zeroVal n (.bytes .memory) : EM EB [] _).run (L0 EB, sB)).2.2.ex :=
  (zero_histories (E := EB) (Γ := []) mode n).2.1 (.bytes .memory) (L0 EB) sB

end Solidity.Lowering.Readonly.ZeroControls
