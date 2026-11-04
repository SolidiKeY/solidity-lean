import Solidity.Backend.MemoryCopies.RangeOverlap
import Solidity.Backend.MemoryCopies.ForwardOverlapControls

/-! Runtime direction selection repairs the actual forward-corruption case.
Both overlap directions, empty/self ranges, long traversal and endpoint cells execute. -/
namespace Solidity.Backend.MemoryCopies.RangeOverlapControls
open Evm Evm.Memory
private def input : Machine := {Machine.init with stack := [w[77]],mem := fun address =>
  if address = 0 then w[256] else if address = 7 then w[99] else
  if address = 16 then w[11] else if address = 17 then w[23] else
  if address = 18 then w[37] else if address = 19 then w[41] else w[0]}


theorem certificate_inhabited : RangeOverlapCertificate := rangeOverlap

theorem right_overlap : ∃ target,
    run (rangeOverlapCode 3) ((input.push w[16]).push w[17]) = .ok target 0 ∧
    target.mem 17 = w[11] ∧ target.mem 18 = w[23] ∧ target.mem 19 = w[37] ∧ target.mem 16 = w[11] ∧
    target.mem 0 = w[256] ∧ target.mem 7 = w[99] ∧ target.stack = [w[77]] := by
  obtain ⟨target,ran,shape,contents,outside⟩ := range_overlap_success input (wmod 16) (wmod 17) 3
    (by decide) (by decide) (by decide)
  exact ⟨target,ran,contents 0 (by decide),contents 1 (by decide),contents 2 (by decide),
    outside 16 (.inl (by decide)),outside 0 (.inl (by decide)),outside 7 (.inl (by decide)),congrArg Machine.stack shape⟩

theorem left_overlap : ∃ target,
    run (rangeOverlapCode 3) ((input.push w[16]).push w[15]) = .ok target 0 ∧
    target.mem 15 = w[11] ∧ target.mem 16 = w[23] ∧ target.mem 17 = w[37] ∧ target.mem 18 = w[37] ∧
    target.mem 0 = w[256] ∧ target.mem 7 = w[99] ∧ target.stack = [w[77]] := by
  obtain ⟨target,ran,shape,contents,outside⟩ := range_overlap_success input (wmod 16) (wmod 15) 3
    (by decide) (by decide) (by decide)
  exact ⟨target,ran,contents 0 (by decide),contents 1 (by decide),contents 2 (by decide),
    outside 18 (.inr (by decide)),outside 0 (.inl (by decide)),outside 7 (.inl (by decide)),congrArg Machine.stack shape⟩

theorem self_copy (machine : Machine) (source : Fin W) (count : Nat)
    (bounded : count < W) (room : source.val + count ≤ W) :
    run (rangeOverlapCode count) ((machine.push (.val source)).push (.val source)) = .ok machine 0 := by
  obtain ⟨target,ran,shape,contents,outside⟩ := range_overlap_success machine source source count bounded room room
  have same : target.mem = machine.mem := by
    funext address
    by_cases inside : source.val ≤ address ∧ address < source.val + count
    · have offset : address - source.val < count := by omega
      have position : source.val + (address - source.val) = address := by omega
      simpa only [position] using contents (address - source.val) offset
    · exact outside address (by omega)
  rw [same] at shape
  rw [shape] at ran
  exact ran

theorem empty_copy (machine : Machine) (source destination : Fin W) :
    run (rangeOverlapCode 0) ((machine.push (.val source)).push (.val destination)) = .ok machine 0 := by
  obtain ⟨target,ran,shape,_,outside⟩ := range_overlap_success machine source destination 0 (by decide) (by omega) (by omega)
  have same : target.mem = machine.mem := by
    funext address
    exact outside address (by omega)
  rw [same] at shape
  rw [shape] at ran
  exact ran

private def longInput : Machine := {Machine.init with stack := [w[77]],mem := fun address =>
  if (16 ≤ address ∧ address < 80) then (Word.val (wmod (address - 15))) else w[0]}

theorem long_right_overlap : ∃ target,
    run (rangeOverlapCode 64) ((longInput.push w[16]).push w[32]) = .ok target 0 ∧
    target.mem 32 = w[1] ∧ target.mem 95 = w[64] ∧ target.mem 79 = w[48] ∧ target.mem 16 = w[1] ∧ target.stack = [w[77]] := by
  obtain ⟨target,ran,shape,contents,outside⟩ := range_overlap_success longInput (wmod 16) (wmod 32) 64
    (by decide) (by decide) (by decide)
  exact ⟨target,ran,contents 0 (by decide),contents 63 (by decide),contents 47 (by decide),outside 16 (.inl (by decide)),congrArg Machine.stack shape⟩

theorem list_model : ∃ target,
    run (rangeOverlapCode 3) ((({input with mem := fun index => ([w[11],w[23],w[37],w[41]][index]?).getD w[0]}).push w[0]).push w[1]) = .ok target 0 ∧
    target.mem 0 = w[11] ∧ target.mem 1 = w[11] ∧ target.mem 2 = w[23] ∧ target.mem 3 = w[37] := by
  let xs : List Word := [w[11],w[23],w[37],w[41]]
  let machine := {input with mem := fun index => xs[index]?.getD w[0]}
  have represented : ∀ index word, xs[index]? = some word → machine.mem index = word := by
    intro index word selected
    simp only [machine,selected,Option.getD_some]
  obtain ⟨ys,target,model,ran,reached⟩ := range_overlap_list xs machine (wmod 0) (wmod 1) 3 represented
    (by decide) (by decide) (by decide) (by decide)
  have expected : MemoryOps.checkedSnapshotCopy xs 0 3 1 = some [w[11],w[11],w[23],w[37]] := by decide +kernel
  simp only [wmod_def,Nat.zero_mod,Nat.mod_eq_of_lt (show 1 < W by decide)] at model
  rw [expected] at model
  cases model
  exact ⟨target,ran,reached 0 w[11] rfl,reached 1 w[11] rfl,reached 2 w[23] rfl,reached 3 w[37] rfl⟩

theorem corruption_repaired : ∃ target previous,
    run (rangeOverlapCode 3) ((input.push w[16]).push w[17]) = .ok target 0 ∧
    run (forwardRangeCode 3) ((input.push w[16]).push w[17]) = .ok previous 0 ∧
    target.mem 18 = w[23] ∧ previous.mem 18 = w[11] := by
  obtain ⟨target,ran,_,correct,_,_,_,_,_⟩ := right_overlap
  obtain ⟨previous,oldRun,oldValue,_⟩ := ForwardOverlapControls.right_overlap_counterexample
  exact ⟨target,previous,ran,oldRun,correct,oldValue⟩

theorem streaming_value_rejected (target : Machine)
    (ran : run (rangeOverlapCode 3) ((input.push w[16]).push w[17]) = .ok target 0) : target.mem 18 ≠ w[11] := by
  obtain ⟨actual,execution,_,correct,_,_,_,_,_⟩ := right_overlap
  rw [ran] at execution
  have same : target.mem 18 = actual.mem 18 := congrArg (fun machine => machine.mem 18) (Out.ok.inj execution).1
  rw [same,correct]
  decide

theorem last_cell_copy (machine : Machine) :
    run (rangeOverlapCode 1) ((machine.push (.val (wmod (W - 1)))).push (.val (wmod (W - 1)))) = .ok machine 0 := by
  apply self_copy machine (wmod (W - 1)) 1 (by decide)
  have positive : 0 < W := W_pos
  simp only [wmod_def,Nat.mod_eq_of_lt (show W - 1 < W by omega)]
  omega

theorem disjoint_right : ∃ target,
    run (rangeOverlapCode 4) ((input.push w[16]).push w[64]) = .ok target 0 ∧
    target.mem 64 = w[11] ∧ target.mem 67 = w[41] ∧ target.mem 16 = w[11] := by
  obtain ⟨target,ran,_,contents,outside⟩ := range_overlap_success input (wmod 16) (wmod 64) 4
    (by decide) (by decide) (by decide)
  exact ⟨target,ran,contents 0 (by decide),contents 3 (by decide),outside 16 (.inl (by decide))⟩

theorem boundary_not_in_range : ¬ ((W - 1) + 2 ≤ W) := by omega

#print axioms certificate_inhabited
#print axioms right_overlap
#print axioms left_overlap
#print axioms self_copy
#print axioms empty_copy
#print axioms long_right_overlap
#print axioms list_model
#print axioms corruption_repaired
#print axioms streaming_value_rejected
#print axioms last_cell_copy
#print axioms disjoint_right
#print axioms boundary_not_in_range
end Solidity.Backend.MemoryCopies.RangeOverlapControls
