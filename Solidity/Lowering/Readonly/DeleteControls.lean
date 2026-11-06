import Solidity.Lowering.Readonly.DeleteEffects
import Solidity.Lowering.Readonly.Controls

/-! Populated actual Source deletion/read controls: ordinary writes remain
permitted; static scalar deletion refuses; horizon exhaustion is a distinct halt. -/
namespace Solidity.Lowering.Readonly.DeleteControls
open Solidity.Source Solidity.Source.SemanticsExamples
open SourceHistory

def deleted (mode : Bool) (n : Nat) :=
  (deleteStor {FC with static := mode} n uint dX.path : EM EB [] Unit).run (L0 EB, sB)

def readGood := (readAt FC dX.path uint : EM EB [] (Solidity.Source.Val EB.layout uint)).run (L0 EB, sB)
def readBad := (readAt FC dX.path .bool : EM EB [] (Solidity.Source.Val EB.layout .bool)).run (L0 EB, sB)
def dangling := (heapObj 0 : EM EB [] _).run (L0 EB, sB)
def badReference := (storRef uint dX.path : EM EB [] _).run (L0 EB, sB)


theorem observations :
    (deleted false 1).1 = .ok () ∧
    readX (deleted false 1).2.2 = some 0 ∧
    (deleted false 1).2.2.ex.journal.length = sB.ex.journal.length + 1 ∧
    (deleted true 1).1 = .error (.revert []) ∧
    readX (deleted true 1).2.2 = some 3 ∧
    (deleted true 1).2.2.ex.journal.length = sB.ex.journal.length ∧
    (deleted false 0).1 = .error .timeout ∧
    readX (deleted false 0).2.2 = some 3 ∧
    readGood.1 = .ok x3 ∧
    readBad.1 = .error (.stuck "storage cell type") ∧
    dangling.1 = .error (.stuck "dangling memory reference") ∧
    badReference.1 = .error (.stuck "storage reference type") := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

/-- Inhabited direct use of the general producer, including both modes and
every horizon; the concrete ordinary success still changes caller storage. -/
theorem history (mode : Bool) (n : Nat) :
    StaticJournal.History sB.ex mode (deleted mode n).2.2.ex :=
  (delete_histories (E := EB) (Γ := []) {FC with static := mode} n).1
    uint dX.path (L0 EB) sB

theorem ordinary_changes : readX (deleted false 1).2.2 ≠ readX sB := by decide

end Solidity.Lowering.Readonly.DeleteControls
