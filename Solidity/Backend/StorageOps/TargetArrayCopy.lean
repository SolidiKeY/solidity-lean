import Solidity.Backend.StorageOps.TargetArrayClear

/-! Actual current-storage primitive copy instructions and their snapshot prefix.
The original store appears only in the proof invariant, never in the code. -/
namespace Solidity.Backend.StorageOps.TargetArrayCopy

def setup : List Evm.Instr :=
  [.dup 2,.sload,.swap 2,.swap 1,.dup 1,.sload,.push (.val ⟨0,by decide⟩)]
def condition : List Evm.Instr := TargetArrayClear.condition
def body : List Evm.Instr :=
  [.dup 3,.keccakArr,.dup 2,.add,.sload,.dup 5,.keccakArr,.dup 3,.add,.sstore,
   .push (.val ⟨1,by decide⟩),.add]
def transition : List Evm.Instr := [.pop,.swap 1,.pop,.dup 1,.swap 3,.swap 1]
def finish : List Evm.Instr := [.pop,.pop,.sstore]
def code : List Evm.Instr := setup ++ [.loop condition body] ++ transition ++
  [.loop TargetArrayClear.condition TargetArrayClear.body] ++ finish

/-- Snapshot invariant for writes already performed by the current-read loop. -/
def copyPrefix (original : Evm.WordStore) (src dst : Evm.Slot) : Nat → Evm.WordStore
  | 0 => original
  | count+1 => Evm.WordStore.write (copyPrefix original src dst count)
      (.data dst count) (original (.data src count))

theorem prefix_outside (original : Evm.WordStore) (src dst observer : Evm.Slot) (count : Nat)
    (apart : ∀ j, j < count → observer ≠ .data dst j) :
    copyPrefix original src dst count observer = original observer := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [copyPrefix,Evm.WordStore.write_other _ _ (apart count (by omega))]
    exact ih (fun j inside => apart j (by omega))

/-- A later current source read is still the captured source word, including
self-copy: equal data slots necessarily have equal offsets. -/
theorem prefix_source_future (original : Evm.WordStore) (src dst : Evm.Slot) (count j : Nat)
    (future : count ≤ j) :
    copyPrefix original src dst count (.data src j) = original (.data src j) := by
  apply prefix_outside
  intro k inside same
  have equal := (Evm.Slot.data.inj same).2
  omega

theorem prefix_unvisited (original : Evm.WordStore) (src dst : Evm.Slot) (count j : Nat)
    (future : count ≤ j) :
    copyPrefix original src dst count (.data dst j) = original (.data dst j) := by
  apply prefix_outside
  intro k inside same
  have equal := (Evm.Slot.data.inj same).2
  omega

theorem prefix_visited (original : Evm.WordStore) (src dst : Evm.Slot) (count j : Nat)
    (inside : j < count) :
    copyPrefix original src dst count (.data dst j) = original (.data src j) := by
  induction count with
  | zero => omega
  | succ count ih =>
    by_cases last : j = count
    · subst j
      rw [copyPrefix]
      exact Evm.WordStore.write_same_of_lt _ _ _ (original.cells (.data src count)).isLt
    · have different : Evm.Slot.data dst j ≠ .data dst count := by
        intro same; exact last (Evm.Slot.data.inj same).2
      rw [copyPrefix,Evm.WordStore.write_other _ _ different]
      exact ih (by omega)

theorem run_setup (machine : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot) :
    Evm.run setup { machine with stack := .slot src :: .slot dst :: tail } =
      .ok { machine with stack := .val ⟨0,by decide⟩ :: .val (machine.store.cells src) :: .slot src :: .slot dst :: .val (machine.store.cells dst) :: tail } 0 := by
  rfl

theorem run_body (machine : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (i limit oldLength : Fin Evm.W) (next : i.val+1 < Evm.W) :
    Evm.run body { machine with stack := .val i :: .val limit :: .slot src :: .slot dst :: .val oldLength :: tail } =
      .ok { machine with stack := .val ⟨i.val+1,next⟩ :: .val limit :: .slot src :: .slot dst :: .val oldLength :: tail, store := Evm.WordStore.write machine.store (.data dst i.val) (machine.store (.data src i.val)) } 0 := by
  simp only [body,Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Evm.Slot.add,Nat.zero_add]
  rw [show 1 + i.val = i.val + 1 by omega,Evm.wmod_of_lt next]
  rfl


def iterationMachine (machine : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (oldLength limit i : Fin Evm.W) : Evm.Machine :=
  { machine with stack := .val i :: .val limit :: .slot src :: .slot dst :: .val oldLength :: tail, store := copyPrefix machine.store src dst i.val }

theorem condition_at (machine : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (oldLength limit i : Fin Evm.W) :
    Evm.run condition (iterationMachine machine tail src dst oldLength limit i) =
      .ok { iterationMachine machine tail src dst oldLength limit i with stack := .val (Evm.bword (decide (i.val < limit.val))) :: (iterationMachine machine tail src dst oldLength limit i).stack } 0 := by
  exact TargetArrayClear.run_condition { machine with store := copyPrefix machine.store src dst i.val }
    (.slot dst :: .val oldLength :: tail) src i limit

theorem body_at (machine : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (oldLength limit i : Fin Evm.W) (next : i.val+1 < Evm.W) :
    Evm.run body (iterationMachine machine tail src dst oldLength limit i) =
      .ok (iterationMachine machine tail src dst oldLength limit ⟨i.val+1,next⟩) 0 := by
  have step := run_body { machine with store := copyPrefix machine.store src dst i.val }
    tail src dst i limit oldLength next
  have snapshot := prefix_source_future machine.store src dst i.val i.val (Nat.le_refl _)
  change Evm.run body (iterationMachine machine tail src dst oldLength limit i) = _ at step
  rw [snapshot] at step
  exact step

private theorem turn_step (rc rb : Evm.Machine → Evm.Out) (machine result : Evm.Machine)
    (flag : Fin Evm.W) (nonzero : flag.val ≠ 0)
    (cond : rc machine = .ok { machine with stack := .val flag :: machine.stack } 0)
    (step : rb machine = .ok result 0) : Evm.loopTurn rc rb machine = .inl result := by
  unfold Evm.loopTurn
  rw [cond]
  change (if flag.val = 0 then (Sum.inr (Evm.Out.ok machine 0) : Evm.Machine ⊕ Evm.Out) else
      match rb machine with
      | .ok current 0 => Sum.inl current
      | .ok _ (_+1) => Sum.inr Evm.Out.fault
      | current => Sum.inr current) = _
  rw [if_neg nonzero,step]

theorem turn_more (machine : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (oldLength limit i : Fin Evm.W) (live : i.val < limit.val) :
    Evm.loopTurn (Evm.run condition) (Evm.run body) (iterationMachine machine tail src dst oldLength limit i) =
      .inl (iterationMachine machine tail src dst oldLength limit ⟨i.val+1,by omega⟩) := by
  have guard : (Evm.bword (decide (i.val < limit.val))).val ≠ 0 := by
    simpa only [live,decide_true,Evm.bword,if_true] using Nat.one_ne_zero
  exact turn_step (Evm.run condition) (Evm.run body) _ _ _ guard
    (condition_at machine tail src dst oldLength limit i) (body_at machine tail src dst oldLength limit i (by have h := limit.isLt; omega))


private theorem turn_exit (rc rb : Evm.Machine → Evm.Out) (machine : Evm.Machine)
    (cond : rc machine = .ok { machine with stack := .val ⟨0,by decide⟩ :: machine.stack } 0) :
    Evm.loopTurn rc rb machine = .inr (.ok machine 0) := by
  unfold Evm.loopTurn
  rw [cond]
  rfl

theorem turn_done (machine : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (oldLength limit : Fin Evm.W) :
    Evm.loopTurn (Evm.run condition) (Evm.run body) (iterationMachine machine tail src dst oldLength limit limit) =
      .inr (.ok (iterationMachine machine tail src dst oldLength limit limit) 0) := by
  have zero : Evm.bword (decide (limit.val < limit.val)) = ⟨0,by decide⟩ := by
    apply Fin.ext
    simp only [Nat.lt_irrefl,decide_false,Evm.bword,Bool.false_eq_true,if_false]
  have cond := condition_at machine tail src dst oldLength limit limit
  rw [zero] at cond
  exact turn_exit (Evm.run condition) (Evm.run body) _ cond

/-- Every finite runtime word length terminates after exactly its remaining
body turns plus one final false condition. This is not a source fuel bound. -/
theorem iterations_finish (machine : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (oldLength limit : Fin Evm.W) (remaining : Nat) (i : Fin Evm.W) (distance : i.val+remaining = limit.val) :
    Evm.loopIterN (Evm.run condition) (Evm.run body) (remaining+1) (iterationMachine machine tail src dst oldLength limit i) =
      .inr (.ok (iterationMachine machine tail src dst oldLength limit limit) 0) := by
  induction remaining generalizing i with
  | zero =>
    have same : i = limit := Fin.ext (by omega)
    subst i
    rw [Evm.loopIterN,turn_done]
  | succ remaining ih =>
    have live : i.val < limit.val := by omega
    rw [Evm.loopIterN,turn_more machine tail src dst oldLength limit i live]
    apply ih
    change i.val + 1 + remaining = limit.val
    omega

/-- Matching prefix/progress before the final false condition, for every
runtime start index. Unvisited words are preserved by prefix_outside. -/
theorem iterations_prefix (machine : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (oldLength limit : Fin Evm.W) (steps : Nat) (i : Fin Evm.W) (bound : i.val+steps ≤ limit.val) :
    Evm.loopIterN (Evm.run condition) (Evm.run body) steps (iterationMachine machine tail src dst oldLength limit i) =
      .inl (iterationMachine machine tail src dst oldLength limit ⟨i.val+steps,by omega⟩) := by
  induction steps generalizing i with
  | zero =>
    have same : (⟨i.val+0,by have h := limit.isLt; omega⟩ : Fin Evm.W) = i := Fin.ext (by change i.val + 0 = i.val; omega)
    rw [same]
    rfl
  | succ steps ih =>
    have live : i.val < limit.val := by omega
    rw [Evm.loopIterN,turn_more machine tail src dst oldLength limit i live]
    have next : i.val+1 < Evm.W := by have h := limit.isLt; omega
    have prefixResult := ih (⟨i.val+1,next⟩ : Fin Evm.W) (by change i.val+1+steps ≤ limit.val; omega)
    refine prefixResult.trans ?_
    apply congrArg (fun j => Sum.inl (iterationMachine machine tail src dst oldLength limit j))
    apply Fin.ext
    change i.val+1+steps = i.val+(steps+1)
    omega

private theorem run_single_loop (cond body : List Evm.Instr) (machine result : Evm.Machine)
    (finished : Evm.loopRun (Evm.run cond) (Evm.run body) machine = .ok result 0) :
    Evm.run [.loop cond body] machine = .ok result 0 := by
  change (Evm.loopRun (Evm.run cond) (Evm.run body) machine).bind (fun m k => Evm.exec [] k m) = _
  rw [finished]
  rfl

/-- Kernel loop specification: restart at ANY matching prefix. The existing
compiled loopImpl twin is not evaluated to prove termination or the result. -/
theorem run_loop_from (machine : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (oldLength limit i : Fin Evm.W) (bound : i.val ≤ limit.val) :
    Evm.run [.loop condition body] (iterationMachine machine tail src dst oldLength limit i) =
      .ok (iterationMachine machine tail src dst oldLength limit limit) 0 := by
  apply run_single_loop
  exact Evm.loopRun_of_iterN (iterations_finish machine tail src dst oldLength limit (limit.val-i.val) i (by omega))

theorem run_loop (machine : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (oldLength limit : Fin Evm.W) :
    Evm.run [.loop condition body] (iterationMachine machine tail src dst oldLength limit ⟨0,by decide⟩) =
      .ok (iterationMachine machine tail src dst oldLength limit limit) 0 :=
  run_loop_from machine tail src dst oldLength limit ⟨0,by decide⟩ (by change (0 : Nat) ≤ limit.val; exact Nat.zero_le _)


/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopy.prefix_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prefix_outside
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopy.prefix_source_future' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prefix_source_future
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopy.prefix_unvisited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prefix_unvisited
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopy.prefix_visited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prefix_visited
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopy.run_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_setup
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopy.run_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_body
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopy.condition_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms condition_at
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopy.body_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms body_at
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopy.turn_more' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms turn_more
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopy.turn_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms turn_done
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopy.iterations_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms iterations_finish
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopy.iterations_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms iterations_prefix
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopy.run_loop_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_loop_from
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopy.run_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_loop

end Solidity.Backend.StorageOps.TargetArrayCopy
