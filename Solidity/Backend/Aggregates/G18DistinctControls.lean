import Solidity.Backend.Aggregates.G18DistinctClient

namespace Solidity.Backend.Aggregates.DistinctClient.Controls
open MemoryOps

def sourceSequence (slot : Nat) : Source.EM E [.int .u8] Unit := do
  Source.writeLoc frame 0 (.mem (τ := .array .memory .bool none) 2 slot) (.memRef rfl 1)
  Source.writeLoc frame 0 (.mem 1 0) (.bool false)

def rebindCode (slot : Fin Evm.W) : List Evm.Instr :=
  [.push (.val (base other.id)),.push (.val slot)] ++ Evm.Memory.writeArrayCode (base r.id)
def suffix : List Evm.Instr :=
  [.push (.val (Evm.bword false)),.push (.val (Evm.wmod 0))] ++ Evm.Memory.writeArrayCode (base other.id)

theorem source_sequence : (sourceSequence 2).run callerSource=(.ok (),outSource) := by
  rw [sourceSequence,Source.Hoare.run_bind,source_rebind]
  exact source_mutate

theorem prefix_run : Evm.run (rebindCode (Evm.wmod 2)) callerMachine=.ok midMachine 0 := by
  have hp : Evm.run [.push (.val (base other.id)),.push (.val (Evm.wmod 2))] callerMachine=
      .ok ((callerMachine.push (.val (base other.id))).push (.val (Evm.wmod 2))) 0 := rfl
  exact (Evm.run_append_ok hp).trans actual_sequence.2.2.1

theorem suffix_run : Evm.run suffix midMachine=.ok outMachine 0 := by
  have hp : Evm.run [.push (.val (Evm.bword false)),.push (.val (Evm.wmod 0))] midMachine=
      .ok ((midMachine.push (.val (Evm.bword false))).push (.val (Evm.wmod 0))) 0 := rfl
  exact (Evm.run_append_ok hp).trans actual_sequence.2.2.2.1

/-- Actual composed word code, including the operand pushes and protected tail.
The source sequence uses the existing monad; no evaluator is introduced. -/
theorem target_sequence : Evm.run (rebindCode (Evm.wmod 2) ++ suffix) callerMachine=.ok outMachine 0 :=
  (Evm.run_append_ok prefix_run).trans suffix_run

/-- This rejects conflating the intermediate pointer checkpoint with the
final child observation. The final writes commute; no opposite claim is made. -/
theorem wrong_phase : Evm.run (rebindCode (Evm.wmod 2)) callerMachine≠.ok outMachine 0 := by
  intro h
  have bad := congrArg (MemoryClient.cellOfResult 25) (prefix_run.symm.trans h)
  exact (by decide +kernel : some (midMachine.mem 25)≠some (outMachine.mem 25)) bad

theorem wrong_child : Evm.run (rebindCode (Evm.wmod 2) ++ suffix) callerMachine ≠
    .ok (Evm.Memory.writeMachine midMachine 17 (.val (Evm.bword false))) 0 := by
  intro h
  have bad := congrArg (MemoryClient.cellOfResult 25) (target_sequence.symm.trans h)
  exact (by decide +kernel : some (outMachine.mem 25)≠some (midMachine.mem 25)) bad

theorem wrong_slot : Evm.run (rebindCode (Evm.wmod 2) ++ suffix) callerMachine ≠
    .ok (Evm.Memory.writeMachine (Evm.Memory.writeMachine callerMachine 33 (.val (base other.id)))
      25 (.val (Evm.bword false))) 0 := by
  intro h
  have bad := congrArg (MemoryClient.cellOfResult 35) (target_sequence.symm.trans h)
  exact (by decide +kernel : some (outMachine.mem 35)≠some (callerMachine.mem 35)) bad

theorem wrong_stack : Evm.run (rebindCode (Evm.wmod 2) ++ suffix) callerMachine≠
    .ok {outMachine with stack := [.val (Evm.wmod 78)]} 0 := by
  intro h
  have bad := congrArg (fun o : Evm.Out => match o with | .ok m _ => m.stack.head? | _ => none)
    (target_sequence.symm.trans h)
  exact (by decide +kernel : some (.val (Evm.wmod 77) : Evm.Word)≠some (.val (Evm.wmod 78))) bad

theorem wrong_escape : Evm.run (Evm.Memory.readArrayCode (base r.id))
    (outMachine.push (.val (Evm.wmod 2)))≠.ok (outMachine.push (.val (base q.id))) 0 := by
  intro h
  have bad := congrArg (fun o : Evm.Out => match o with | .ok m _ => m.stack.head? | _ => none)
    (escaped_other.2.2.1.symm.trans h)
  exact (by decide +kernel : some (.val (base other.id) : Evm.Word)≠some (.val (base q.id))) bad

theorem wrong_frame : ¬ Evm.Memory.RefArrayStateRepr 1 1 20 F caller base callerMachine := by
  intro h
  have hb := h.state.heap.above q
  exact (by decide +kernel : ¬ 20≤(base q.id).val) hb

theorem collapsed_separation : ¬ (∀ t ∈ MObj.elems .dyn (caller.heap.get r),
    t.id≠other.id → (fun _ : Nat => 0) t.id≠(fun _ : Nat => 0) other.id) := by
  intro h
  exact h q separation_nonvacuous.1 separation_nonvacuous.2.1 rfl

/-- Source bounds failure happens before either heap changes. -/
theorem source_bad_first :
    (Source.writeLoc (E := E) (Γ := [.int .u8]) frame 0
      (.mem (τ := .array .memory .bool none) 2 3) (.memRef rfl 1)).run callerSource=
      (.error (.revert (Source.panicData .index)),callerSource) := by
  have hb := caller_source.parent
  change callerSource.2.heap.get 2=some ⟨SourceBoolRefsTy,sourceBoolRefMemory address (MObj.elems .dyn (hp.get r))⟩ at hb
  rw [parent_elems] at hb
  change (Source.memSet (E := E) (Γ := [.int .u8]) 2 3 (τ := .array .memory .bool none) (.memRef rfl 1)).run callerSource=_
  rw [Source.memSet,Source.Hoare.run_bind,source_heapObj_run callerSource 2 _ hb]
  simp only [sourceBoolRefMemory,List.length_cons,List.length_nil,Nat.lt_irrefl,↓reduceDIte]
  rfl

theorem source_first_failure_stops_second : (sourceSequence 3).run callerSource=
    (.error (.revert (Source.panicData .index)),callerSource) := by
  rw [sourceSequence,Source.Hoare.run_bind,source_bad_first]

theorem target_bad_first : Evm.run (rebindCode (Evm.wmod 3)) callerMachine=.revert := by
  have hn : caller.heap.writeAddr (.index r .dyn (Evm.Memory.indexValue (Evm.wmod 3))) other=none := by
    simp only [Heap.writeAddr,Heap.setIndex]
    exact if_neg (by decide +kernel)
  have hp : Evm.run [.push (.val (base other.id)),.push (.val (Evm.wmod 3))] callerMachine=
      .ok ((callerMachine.push (.val (base other.id))).push (.val (Evm.wmod 3))) 0 := rfl
  rw [rebindCode,Evm.run_append_ok hp]
  obtain ⟨out,ho,_⟩ | ⟨_,ht⟩ := (caller_word.arrays.arrays r).write (Evm.wmod 3) other
  · rw [hn] at ho
    cases ho
  · exact ht

/-- Every continuation is skipped, not merely the chosen mutation suffix. -/
theorem target_first_failure_stops_second (continuation : List Evm.Instr) :
    Evm.run (rebindCode (Evm.wmod 3) ++ continuation) callerMachine=.revert :=
  Evm.run_append_revert target_bad_first

theorem failure_not_timeout : (sourceSequence 3).run callerSource≠(.error .timeout,callerSource) := by
  rw [source_first_failure_stops_second]
  intro h
  cases h

theorem failure_not_success : Evm.run (rebindCode (Evm.wmod 3) ++ suffix) callerMachine≠.ok outMachine 0 := by
  rw [target_first_failure_stops_second]
  intro h
  cases h

theorem wrong_failure_data : (sourceSequence 3).run callerSource ≠
    (.error (.revert (Source.panicData .arithmetic)),callerSource) := by
  intro h
  have bad := congrArg (fun x : Source.R Unit × Source.EMState E [.int .u8] => match x.1 with
    | .error (.revert data) => some data | _ => none)
      (source_first_failure_stops_second.symm.trans h)
  exact (by decide +kernel : some (Source.panicData .index)≠some (Source.panicData .arithmetic)) bad

end Solidity.Backend.Aggregates.DistinctClient.Controls
