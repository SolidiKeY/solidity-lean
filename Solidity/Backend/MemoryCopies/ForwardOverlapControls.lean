import Solidity.Backend.MemoryCopies.ForwardOverlap

/-! Actual forward-loop overlap, self-copy and empty-range executions, plus
an actual right-overlap counterexample requiring another traversal direction. -/
namespace Solidity.Backend.MemoryCopies.ForwardOverlapControls
open Evm Evm.Memory
private def input : Machine := {Machine.init with stack := [w[77]],mem := fun address =>
  if address = 0 then w[256] else if address = 7 then w[99] else
  if address = 16 then w[11] else if address = 17 then w[23] else
  if address = 18 then w[37] else if address = 19 then w[41] else w[0]}

theorem certificate_inhabited : ForwardOverlapCertificate := forwardOverlap

theorem left_overlap : ∃ target,
    run (forwardRangeCode 3) ((input.push w[16]).push w[15]) = .ok target 0 ∧
    target.mem 15 = w[11] ∧ target.mem 16 = w[23] ∧ target.mem 17 = w[37] ∧ target.mem 18 = w[37] ∧
    target.mem 0 = w[256] ∧ target.mem 7 = w[99] ∧ target.stack = [w[77]] := by
  obtain ⟨target,ran,shape,contents,outside⟩ := forward_range_success input (wmod 16) (wmod 15) 3
    (by decide) (by decide) (by decide) (.inl (by decide))
  exact ⟨target,ran,contents 0 (by decide),contents 1 (by decide),contents 2 (by decide),
    outside 18 (.inr (by decide)),outside 0 (.inl (by decide)),outside 7 (.inl (by decide)),congrArg Machine.stack shape⟩

theorem self_copy (machine : Machine) (source : Fin W) (count : Nat)
    (bounded : count < W) (room : source.val + count ≤ W) :
    run (forwardRangeCode count) ((machine.push (.val source)).push (.val source)) = .ok machine 0 := by
  obtain ⟨target,ran,shape,contents,outside⟩ := forward_range_success machine source source count bounded room room (.inl (Nat.le_refl _))
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
    run (forwardRangeCode 0) ((machine.push (.val source)).push (.val destination)) = .ok machine 0 := by
  exact forward_range_run machine source destination 0 (by decide) (by omega) (by omega)
    (by unfold ForwardReadable; omega)

private def longInput : Machine := {Machine.init with stack := [w[77]],mem := fun address =>
  if (32 ≤ address ∧ address < 96) then (Word.val (wmod (address - 31))) else w[0]}

theorem long_overlap : ∃ target,
    run (forwardRangeCode 64) ((longInput.push w[32]).push w[16]) = .ok target 0 ∧
    target.mem 16 = w[1] ∧ target.mem 79 = w[64] ∧ target.mem 95 = w[64] ∧ target.stack = [w[77]] := by
  obtain ⟨target,ran,shape,contents,outside⟩ := forward_range_success longInput (wmod 32) (wmod 16) 64
    (by decide) (by decide) (by decide) (.inl (by decide))
  exact ⟨target,ran,contents 0 (by decide),contents 63 (by decide),outside 95 (.inr (by decide)),congrArg Machine.stack shape⟩

theorem list_model : ∃ target,
    run (forwardRangeCode 3) ((({input with mem := fun index => ([w[11],w[23],w[37],w[41]][index]?).getD w[0]}).push w[1]).push w[0]) = .ok target 0 ∧
    target.mem 0 = w[23] ∧ target.mem 2 = w[41] ∧ target.mem 3 = w[41] := by
  let xs : List Word := [w[11],w[23],w[37],w[41]]
  let machine := {input with mem := fun index => xs[index]?.getD w[0]}
  have represented : ∀ index word, xs[index]? = some word → machine.mem index = word := by
    intro index word selected
    simp only [machine,selected,Option.getD_some]
  obtain ⟨ys,target,model,ran,reached⟩ := forward_range_list xs machine (wmod 1) (wmod 0) 3 represented
    (by decide) (by decide) (by decide) (by decide) (.inl (by decide))
  have expected : MemoryOps.checkedSnapshotCopy xs 1 3 0 = some [w[23],w[37],w[41],w[41]] := by decide +kernel
  simp only [wmod_def,Nat.zero_mod,Nat.mod_eq_of_lt (show 1 < W by decide)] at model
  rw [expected] at model
  cases model
  exact ⟨target,ran,reached 0 w[23] rfl,reached 2 w[41] rfl,reached 3 w[41] rfl⟩

private def corrupted : Machine :=
  writeMachine (writeMachine (writeMachine input 17 w[11]) 18 w[11]) 19 w[11]

theorem right_overlap_run : run (forwardRangeCode 3) ((input.push w[16]).push w[17]) = .ok corrupted 0 := by
  have step (machine : Machine) (index : Nat) (lower : index < 3)
      (selected : machine.mem ((wmod 16).val + index) = w[11]) :
      loopTurn (run copyRangeCond) (run memoryReadRangeBody) (memoryRangeMachine machine index 3 (wmod 17) (wmod 16)) =
        .inl (memoryRangeMachine (writeMachine machine ((wmod 17).val + index) w[11]) (index + 1) 3 (wmod 17) (wmod 16)) := by
    have large : 100 < W := by decide
    have condition : run copyRangeCond (memoryRangeMachine machine index 3 (wmod 17) (wmod 16)) =
        .ok ((memoryRangeMachine machine index 3 (wmod 17) (wmod 16)).push w[1]) 0 := by
      simpa only [lower,decide_true,bword] using memory_read_condition machine index 3 (wmod 17) (wmod 16) (by omega) (by decide)
    have body : run memoryReadRangeBody (memoryRangeMachine machine index 3 (wmod 17) (wmod 16)) =
        .ok (memoryRangeMachine (writeMachine machine ((wmod 17).val + index) w[11]) (index + 1) 3 (wmod 17) (wmod 16)) 0 :=
      memory_read_turn machine index 3 (wmod 17) (wmod 16) (by omega) (by decide) (by change 17 + index < W; omega)
        (by change 16 + index < W; omega) w[11] selected
    rw [loopTurn,condition]
    change (if (1 : Nat) = 0 then _ else _) = _
    rw [if_neg (by decide)]
    simp only [Machine.push]
    rw [body]
  have done : loopTurn (run copyRangeCond) (run memoryReadRangeBody) (memoryRangeMachine corrupted 3 3 (wmod 17) (wmod 16)) =
      .inr (.ok (memoryRangeMachine corrupted 3 3 (wmod 17) (wmod 16)) 0) := by
    have condition : run copyRangeCond (memoryRangeMachine corrupted 3 3 (wmod 17) (wmod 16)) =
        .ok ((memoryRangeMachine corrupted 3 3 (wmod 17) (wmod 16)).push w[0]) 0 := by
      simpa only [Nat.lt_irrefl,decide_false,bword] using memory_read_condition corrupted 3 3 (wmod 17) (wmod 16) (by decide) (by decide)
    rw [loopTurn,condition]
    rfl
  have first : loopTurn (run copyRangeCond) (run memoryReadRangeBody)
      (memoryRangeMachine input 0 3 (wmod 17) (wmod 16)) =
      .inl (memoryRangeMachine (writeMachine input 17 w[11]) 1 3 (wmod 17) (wmod 16)) := by
    exact step input 0 (by decide) rfl
  have second : loopTurn (run copyRangeCond) (run memoryReadRangeBody)
      (memoryRangeMachine (writeMachine input 17 w[11]) 1 3 (wmod 17) (wmod 16)) =
      .inl (memoryRangeMachine (writeMachine (writeMachine input 17 w[11]) 18 w[11]) 2 3 (wmod 17) (wmod 16)) := by
    exact step (writeMachine input 17 w[11]) 1 (by decide) rfl
  have third : loopTurn (run copyRangeCond) (run memoryReadRangeBody)
      (memoryRangeMachine (writeMachine (writeMachine input 17 w[11]) 18 w[11]) 2 3 (wmod 17) (wmod 16)) =
      .inl (memoryRangeMachine corrupted 3 3 (wmod 17) (wmod 16)) := by
    exact step (writeMachine (writeMachine input 17 w[11]) 18 w[11]) 2 (by decide) rfl
  have iterations : loopIterN (run copyRangeCond) (run memoryReadRangeBody) 4
      (memoryRangeMachine input 0 3 (wmod 17) (wmod 16)) =
      .inr (.ok (memoryRangeMachine corrupted 3 3 (wmod 17) (wmod 16)) 0) := by
    simp only [loopIterN,first,second,third,done]
  have loop : loopRun (run copyRangeCond) (run memoryReadRangeBody)
      (memoryRangeMachine input 0 3 (wmod 17) (wmod 16)) =
      .ok (memoryRangeMachine corrupted 3 3 (wmod 17) (wmod 16)) 0 := loopRun_of_iterN iterations
  have single : run [.loop copyRangeCond memoryReadRangeBody] (memoryRangeMachine input 0 3 (wmod 17) (wmod 16)) =
      .ok (memoryRangeMachine corrupted 3 3 (wmod 17) (wmod 16)) 0 := by
    change (loopRun (run copyRangeCond) (run memoryReadRangeBody) _).bind _ = _
    rw [loop]
    rfl
  have entered : run [.push (.val (wmod 3)),.push w[0]] ((input.push w[16]).push w[17]) =
      .ok (memoryRangeMachine input 0 3 (wmod 17) (wmod 16)) 0 := by rfl
  change run ([.push (.val (wmod 3)),.push w[0]] ++ [.loop copyRangeCond memoryReadRangeBody] ++ [.pop,.pop,.pop,.pop]) _ = _
  rw [List.append_assoc,run_append_ok entered,run_append_ok single]
  rfl

theorem right_overlap_counterexample : ∃ target,
    run (forwardRangeCode 3) ((input.push w[16]).push w[17]) = .ok target 0 ∧
    target.mem 18 = w[11] ∧ target.mem 18 ≠ input.mem 17 := by
  exact ⟨corrupted,right_overlap_run,rfl,by decide +kernel⟩

theorem right_snapshot_expected : MemoryOps.checkedSnapshotCopy [w[11],w[23],w[37],w[41]] 0 3 1 =
    some [w[11],w[11],w[23],w[37]] := by decide +kernel

theorem right_not_forward_readable : ¬ ForwardReadable (wmod 16) (wmod 17) 3 := by
  change ¬ (17 ≤ 16 ∨ 16 + 3 ≤ 17)
  decide

theorem last_cell_copy (machine : Machine) :
    run (forwardRangeCode 1) ((machine.push (.val (wmod (W - 1)))).push (.val (wmod (W - 1)))) = .ok machine 0 := by
  apply self_copy machine (wmod (W - 1)) 1 (by decide)
  have positive : 0 < W := W_pos
  simp only [wmod_def,Nat.mod_eq_of_lt (show W - 1 < W by omega)]
  omega

theorem boundary_not_in_range : ¬ ((W - 1) + 2 ≤ W) := by omega

#print axioms certificate_inhabited
#print axioms left_overlap
#print axioms self_copy
#print axioms empty_copy
#print axioms long_overlap
#print axioms list_model
#print axioms right_overlap_run
#print axioms right_overlap_counterexample
#print axioms right_snapshot_expected
#print axioms right_not_forward_readable
#print axioms last_cell_copy
#print axioms boundary_not_in_range
end Solidity.Backend.MemoryCopies.ForwardOverlapControls
