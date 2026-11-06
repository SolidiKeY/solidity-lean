import Solidity.Backend.Passes.MemoryJoinedAllocation

namespace Solidity.Backend.Passes.MemoryJoinedAllocation.Controls
open Evm Evm.Memory Evm.Compiler
open Backend.Passes.Controls.Fixture
open AllocatingControls
open MemoryJoinCost.Controls

theorem whole_some : (Memory.compileProg 1 (Frag.init [])
    (ReachabilityControls.populatedBuilder.join appendAllocation)).isSome = true := by
  obtain ⟨joined,accepted,_,_,_⟩ := joined_selection
  rw [accepted]
  rfl

def wholeCode : CompiledProg 1 (Frag.init [])
    (ReachabilityControls.populatedBuilder.join appendAllocation) :=
  (Memory.compileProg 1 (Frag.init [])
    (ReachabilityControls.populatedBuilder.join appendAllocation)).get whole_some

theorem whole_public : Memory.compileProg 1 (Frag.init [])
    (ReachabilityControls.populatedBuilder.join appendAllocation) = some wholeCode := by
  exact (Option.some_get _).symm

theorem whole_tail : ∃ final : Machine, final.stack = [] ∧ ∀ tail,
    run wholeCode.code {initialMachine with stack := tail} = .ok {final with stack := tail} 0 := by
  obtain ⟨joined,accepted,_,middle,final,middleBase,finalBase,stack,_,_,allTails⟩ := execution
  have same : joined = wholeCode := Option.some.inj (accepted.symm.trans whole_public)
  have codes : joined.code = wholeCode.code := congrArg (fun result => result.code) same
  refine ⟨final,stack,?_⟩
  intro tail
  rw [←codes]
  exact (allTails tail).2.2.2.2.2.1

private def readCell (n : Nat) : Evm.Out → Option Nat
  | .ok machine _ => match machine.mem n with | .val word => some word.val | _ => none
  | _ => none

private theorem cell0 : readCell 5 (run wholeCode.code initialMachine) = some 21 := by decide +kernel
private theorem cell1 : readCell 4 (run wholeCode.code initialMachine) = some 0 := by decide +kernel
private theorem cell2 : readCell 2 (run wholeCode.code initialMachine) = some 16 := by decide +kernel
private theorem cell3 : readCell 3 (run wholeCode.code initialMachine) = some 16 := by decide +kernel
private theorem cell4 : readCell 1 (run wholeCode.code initialMachine) = some 19 := by decide +kernel
private theorem cell5 : readCell 6 (run wholeCode.code initialMachine) = some 0 := by decide +kernel
private theorem cell6 : readCell 16 (run wholeCode.code initialMachine) = some 2 := by decide +kernel
private theorem cell7 : readCell 17 (run wholeCode.code initialMachine) = some 7 := by decide +kernel
private theorem cell8 : readCell 18 (run wholeCode.code initialMachine) = some 9 := by decide +kernel
private theorem cell9 : readCell 19 (run wholeCode.code initialMachine) = some 1 := by decide +kernel
private theorem cell10 : readCell 20 (run wholeCode.code initialMachine) = some 4 := by decide +kernel
private theorem cell11 : readCell 21 (run wholeCode.code initialMachine) = some 3 := by decide +kernel
private theorem cell12 : readCell 22 (run wholeCode.code initialMachine) = some 0 := by decide +kernel
private theorem cell13 : readCell 23 (run wholeCode.code initialMachine) = some 0 := by decide +kernel
private theorem cell14 : readCell 24 (run wholeCode.code initialMachine) = some 0 := by decide +kernel
private theorem cell15 : readCell 0 (run wholeCode.code initialMachine) = some 25 := by decide +kernel

theorem complete_result :
    [5,4,2,3,1,6,16,17,18,19,20,21,22,23,24,0].mapM
      (fun n => readCell n (run wholeCode.code initialMachine)) =
      some [21,0,16,16,19,0,2,7,9,1,4,3,0,0,0,25] := by
  simp only [List.mapM_cons,List.mapM_nil,cell0,cell1,cell2,cell3,cell4,cell5,cell6,cell7,cell8,cell9,cell10,cell11,cell12,cell13,cell14,cell15]
  rfl

theorem wrong_cursor : readCell 0 (run wholeCode.code initialMachine) ≠ some 21 := by
  rw [cell15]
  decide

theorem wrong_new_reference : readCell 5 (run wholeCode.code initialMachine) ≠ some 16 := by
  rw [cell0]
  decide

theorem stale_initial_map (machine : Machine) :
    ¬ StateRepr 1 1 6 suffixCode.frag (suffixOut σ).st initialBase machine := by
  intro represented
  have bound := represented.heap.above (CompileExamples.r0.wk (suffixOut σ).ext)
  change 6 ≤ 0 at bound
  omega

theorem corrupted_saved_tail : ∃ final : Machine,
    run wholeCode.code {initialMachine with stack := [w[99]]} =
      .ok {final with stack := [w[99]]} 0 ∧
    run (wholeCode.code ++ [.pop]) {initialMachine with stack := [w[99]]} =
      .ok {final with stack := []} 0 := by
  obtain ⟨final,_,allTails⟩ := whole_tail
  refine ⟨final,allTails [w[99]],?_⟩
  rw [run_append_ok (allTails [w[99]])]
  rfl

#print axioms whole_tail
#print axioms complete_result
#print axioms stale_initial_map
end Solidity.Backend.Passes.MemoryJoinedAllocation.Controls
