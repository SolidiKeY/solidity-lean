import Solidity.Backend.Passes.AllocatedReferenceRead
import Solidity.Backend.Passes.MemoryJoinedAllocationControls

namespace Solidity.Backend.Passes.AllocatedReferenceRead.Controls
open Evm Evm.Memory Evm.Compiler
open Backend.Passes.Controls.Fixture
open AllocatingControls MemoryJoinCost.Controls MemoryJoinedAllocation
open MemoryJoinedAllocation.Controls (wholeCode whole_public)

def code : List Instr := wholeCode.code ++ readerCode.code
def badCode : List Instr := wholeCode.code ++ wrongCode.code

theorem runs : ∃ (final : Machine) (selected : Nat → Fin W), final.stack = [] ∧ ∀ tail,
    run wholeCode.code {initialMachine with stack := tail} = .ok {final with stack := tail} 0 ∧
    StateRepr 1 1 6 suffixCode.frag (suffixOut σ).st selected {final with stack := tail} ∧
    run code {initialMachine with stack := tail} = .ok ({final with stack := tail}.push w[0]) 0 ∧
    run badCode {initialMachine with stack := tail} = .revert := by
  obtain ⟨joined,accepted,final,selected,stack,allTails⟩ := AllocatedReferenceRead.execution
  have same : joined = wholeCode := Option.some.inj (accepted.symm.trans whole_public)
  have codes : joined.code = wholeCode.code := congrArg (fun result => result.code) same
  refine ⟨final,selected,stack,?_⟩
  intro tail
  rcases allTails tail with ⟨prefixRun,_,represented,_,readRun,_,badRun,_⟩
  rw [codes] at prefixRun readRun badRun
  exact ⟨prefixRun,represented,readRun,badRun⟩

theorem old_alias_fails (tail : List Word) :
    run badCode {initialMachine with stack := tail} = .revert := by
  obtain ⟨final,selected,_,allTails⟩ := runs
  exact (allTails tail).2.2.2

theorem fresh_reference_succeeds (tail : List Word) :
    run code {initialMachine with stack := tail} ≠ .revert := by
  obtain ⟨final,selected,_,allTails⟩ := runs
  rw [(allTails tail).2.2.1]
  intro impossible
  cases impossible

private def readCell (n : Nat) : Evm.Out → Option Nat
  | .ok machine _ => match machine.mem n with | .val word => some word.val | _ => none
  | _ => none
private theorem cell0 : readCell 5 (run code initialMachine) = some 21 := by decide +kernel
private theorem cell1 : readCell 4 (run code initialMachine) = some 0 := by decide +kernel
private theorem cell2 : readCell 2 (run code initialMachine) = some 16 := by decide +kernel
private theorem cell3 : readCell 3 (run code initialMachine) = some 16 := by decide +kernel
private theorem cell4 : readCell 1 (run code initialMachine) = some 19 := by decide +kernel
private theorem cell5 : readCell 6 (run code initialMachine) = some 0 := by decide +kernel
private theorem cell6 : readCell 16 (run code initialMachine) = some 2 := by decide +kernel
private theorem cell7 : readCell 17 (run code initialMachine) = some 7 := by decide +kernel
private theorem cell8 : readCell 18 (run code initialMachine) = some 9 := by decide +kernel
private theorem cell9 : readCell 19 (run code initialMachine) = some 1 := by decide +kernel
private theorem cell10 : readCell 20 (run code initialMachine) = some 4 := by decide +kernel
private theorem cell11 : readCell 21 (run code initialMachine) = some 3 := by decide +kernel
private theorem cell12 : readCell 22 (run code initialMachine) = some 0 := by decide +kernel
private theorem cell13 : readCell 23 (run code initialMachine) = some 0 := by decide +kernel
private theorem cell14 : readCell 24 (run code initialMachine) = some 0 := by decide +kernel
private theorem cell15 : readCell 0 (run code initialMachine) = some 25 := by decide +kernel

theorem complete_memory :
    [5,4,2,3,1,6,16,17,18,19,20,21,22,23,24,0].mapM
      (fun n => readCell n (run code initialMachine)) =
      some [21,0,16,16,19,0,2,7,9,1,4,3,0,0,0,25] := by
  simp only [List.mapM_cons,List.mapM_nil,cell0,cell1,cell2,cell3,cell4,cell5,cell6,cell7,cell8,cell9,cell10,cell11,cell12,cell13,cell14,cell15]
  rfl

/-- The corrupt suffix keeps the returned zero but deletes the caller's99.
A top-word-only observation would miss this corruption. -/
theorem corrupted_tail : ∃ final : Machine,
    run code {initialMachine with stack := [w[99]]} =
      .ok ({final with stack := [w[99]]}.push w[0]) 0 ∧
    run (code ++ [.swap 1,.pop]) {initialMachine with stack := [w[99]]} =
      .ok ({final with stack := []}.push w[0]) 0 := by
  obtain ⟨final,selected,_,allTails⟩ := runs
  have good := (allTails [w[99]]).2.2.1
  refine ⟨final,good,?_⟩
  rw [run_append_ok good]
  rfl

#print axioms runs
#print axioms complete_memory
#print axioms corrupted_tail
end Solidity.Backend.Passes.AllocatedReferenceRead.Controls
