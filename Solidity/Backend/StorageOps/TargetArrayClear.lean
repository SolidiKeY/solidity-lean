import Solidity.Evm.MemoryStorageCopyLoop
import Solidity.Backend.StorageOps.LoopLaws
import Solidity.Backend.StorageOps.TargetArrayWrite

/-! A genuine structured target runtime loop clears primitive array live slots.
Its old length is loaded by SLOAD, not read from a graph-value oracle. Kernel
loopIterN/loopRun proofs retain the existing instruction/loop semantics. -/
namespace Solidity.Backend.StorageOps.TargetArrayClear

def condition : List Evm.Instr := Evm.Memory.copyRangeCond
def body : List Evm.Instr := [.push (.val ⟨0,by decide⟩),.dup 4,.keccakArr,.dup 3,.add,.sstore,
  .push (.val ⟨1,by decide⟩),.add]
def setup : List Evm.Instr := [.dup 1,.sload,.push (.val ⟨0,by decide⟩)]
def finish : List Evm.Instr := [.pop,.pop,.push (.val ⟨0,by decide⟩),.swap 1,.sstore]
def code : List Evm.Instr := setup ++ ([.loop condition body] ++ finish)

/-- Operation-generated prefix writes over the EXISTING target WordStore. -/
def clearPrefix (store : Evm.WordStore) (slot : Evm.Slot) : Nat → Evm.WordStore
  | 0 => store
  | count+1 => Evm.WordStore.write (clearPrefix store slot count) (.data slot count) 0

theorem prefix_outside (store : Evm.WordStore) (slot observer : Evm.Slot) (count : Nat)
    (apart : ∀ j, j < count → observer ≠ .data slot j) : clearPrefix store slot count observer = store observer := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [clearPrefix,Evm.WordStore.write_other _ _ (apart count (by omega))]
    exact ih (fun j inside => apart j (by omega))

theorem prefix_visited (store : Evm.WordStore) (slot : Evm.Slot) (count j : Nat)
    (inside : j < count) : clearPrefix store slot count (.data slot j) = 0 := by
  induction count with
  | zero => omega
  | succ count ih =>
    by_cases last : j = count
    · subst j
      rw [clearPrefix,Evm.WordStore.write_same]
      rfl
    · have different : Evm.Slot.data slot j ≠ .data slot count := by
        intro same; exact last (Evm.Slot.data.inj same).2
      rw [clearPrefix,Evm.WordStore.write_other _ _ different]
      exact ih (by omega)

theorem prefix_unvisited (store : Evm.WordStore) (slot : Evm.Slot) (count j : Nat)
    (outside : count ≤ j) : clearPrefix store slot count (.data slot j) = store (.data slot j) := by
  apply prefix_outside
  intro k inside same
  have equal := (Evm.Slot.data.inj same).2
  omega

theorem prefix_header (store : Evm.WordStore) (slot : Evm.Slot) (count : Nat) :
    clearPrefix store slot count slot = store slot := by
  apply prefix_outside
  intro j _ same
  have depths := congrArg (fun s => (Solidity.Storage.ofSlot s).depth) same
  change (Solidity.Storage.ofSlot slot).depth = (Solidity.Storage.ofSlot slot).depth + 1 at depths
  omega

/-- The loop condition observes the captured runtime header/actual counter. -/
theorem run_condition (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (i limit : Fin Evm.W) :
    Evm.run condition { machine with stack := .val i :: .val limit :: .slot slot :: tail } =
      .ok { machine with stack := .val (Evm.bword (decide (i.val < limit.val))) :: .val i :: .val limit :: .slot slot :: tail } 0 := by
  simp only [condition,Evm.Memory.copyRangeCond,Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
    List.getElem?_cons_zero,List.getElem?_cons_succ]

/-- One ACTUAL SSTORE turn clears only current index, then advances the runtime
counter. The loop invariant supplies the nonwrapping increment bound. -/
theorem run_body (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (i limit : Fin Evm.W) (next : i.val + 1 < Evm.W) :
    Evm.run body { machine with stack := .val i :: .val limit :: .slot slot :: tail } =
      .ok { machine with stack := .val ⟨i.val+1,next⟩ :: .val limit :: .slot slot :: tail, store := Evm.WordStore.write machine.store (.data slot i.val) 0 } 0 := by
  simp only [body,Evm.run,Evm.exec,Evm.Instr.step,Evm.Machine.next,Evm.Out.bind,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Evm.Slot.add,Nat.zero_add]
  rw [show 1 + i.val = i.val + 1 by omega,Evm.wmod_of_lt next]


/-- Only a record-update invariant over EXISTING Machine/WordStore types. -/
def iterationMachine (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (limit i : Fin Evm.W) : Evm.Machine :=
  { machine with stack := .val i :: .val limit :: .slot slot :: tail, store := clearPrefix machine.store slot i.val }

theorem condition_at (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (limit i : Fin Evm.W) :
    Evm.run condition (iterationMachine machine tail slot limit i) =
      .ok { iterationMachine machine tail slot limit i with stack := .val (Evm.bword (decide (i.val < limit.val))) :: (iterationMachine machine tail slot limit i).stack } 0 := by
  exact run_condition { machine with store := clearPrefix machine.store slot i.val } tail slot i limit

theorem body_at (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (limit i : Fin Evm.W) (next : i.val+1 < Evm.W) :
    Evm.run body (iterationMachine machine tail slot limit i) =
      .ok (iterationMachine machine tail slot limit ⟨i.val+1,next⟩) 0 := by
  exact run_body { machine with store := clearPrefix machine.store slot i.val } tail slot i limit next



theorem turn_more (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (limit i : Fin Evm.W) (live : i.val < limit.val) :
    Evm.loopTurn (Evm.run condition) (Evm.run body) (iterationMachine machine tail slot limit i) =
      .inl (iterationMachine machine tail slot limit ⟨i.val+1,by omega⟩) := by
  have guard : (Evm.bword (decide (i.val < limit.val))).val ≠ 0 := by
    simpa only [live,decide_true,Evm.bword,if_true] using Nat.one_ne_zero
  exact LoopLaws.turn_step (Evm.run condition) (Evm.run body) _ _ _ guard
    (condition_at machine tail slot limit i) (body_at machine tail slot limit i (by have h := limit.isLt; omega))


theorem turn_done (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (limit : Fin Evm.W) :
    Evm.loopTurn (Evm.run condition) (Evm.run body) (iterationMachine machine tail slot limit limit) =
      .inr (.ok (iterationMachine machine tail slot limit limit) 0) := by
  have zero : Evm.bword (decide (limit.val < limit.val)) = ⟨0,by decide⟩ := by
    apply Fin.ext
    simp only [Nat.lt_irrefl,decide_false,Evm.bword,Bool.false_eq_true,if_false]
  have cond := condition_at machine tail slot limit limit
  rw [zero] at cond
  exact LoopLaws.turn_exit (Evm.run condition) (Evm.run body) _ cond

/-- Every finite runtime word length terminates after exactly its remaining
body turns plus one final false condition. This is not a source fuel bound. -/
theorem iterations_finish (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (limit : Fin Evm.W) (remaining : Nat) (i : Fin Evm.W) (distance : i.val+remaining = limit.val) :
    Evm.loopIterN (Evm.run condition) (Evm.run body) (remaining+1) (iterationMachine machine tail slot limit i) =
      .inr (.ok (iterationMachine machine tail slot limit limit) 0) := by
  induction remaining generalizing i with
  | zero =>
    have same : i = limit := Fin.ext (by omega)
    subst i
    rw [Evm.loopIterN,turn_done]
  | succ remaining ih =>
    have live : i.val < limit.val := by omega
    rw [Evm.loopIterN,turn_more machine tail slot limit i live]
    apply ih
    change i.val + 1 + remaining = limit.val
    omega

/-- Matching prefix/progress before the final false condition, for every
runtime start index. Unvisited words are preserved by prefix_outside. -/
theorem iterations_prefix (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (limit : Fin Evm.W) (steps : Nat) (i : Fin Evm.W) (bound : i.val+steps ≤ limit.val) :
    Evm.loopIterN (Evm.run condition) (Evm.run body) steps (iterationMachine machine tail slot limit i) =
      .inl (iterationMachine machine tail slot limit ⟨i.val+steps,by omega⟩) := by
  induction steps generalizing i with
  | zero =>
    have same : (⟨i.val+0,by have h := limit.isLt; omega⟩ : Fin Evm.W) = i := Fin.ext (by change i.val + 0 = i.val; omega)
    rw [same]
    rfl
  | succ steps ih =>
    have live : i.val < limit.val := by omega
    rw [Evm.loopIterN,turn_more machine tail slot limit i live]
    have next : i.val+1 < Evm.W := by have h := limit.isLt; omega
    have prefixResult := ih (⟨i.val+1,next⟩ : Fin Evm.W) (by change i.val+1+steps ≤ limit.val; omega)
    refine prefixResult.trans ?_
    apply congrArg (fun j => Sum.inl (iterationMachine machine tail slot limit j))
    apply Fin.ext
    change i.val+1+steps = i.val+(steps+1)
    omega

/-- Kernel loop specification: restart at ANY matching prefix. The existing
compiled loopImpl twin is not evaluated to prove termination or the result. -/
theorem run_loop_from (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (limit i : Fin Evm.W) (bound : i.val ≤ limit.val) :
    Evm.run [.loop condition body] (iterationMachine machine tail slot limit i) =
      .ok (iterationMachine machine tail slot limit limit) 0 := by
  apply LoopLaws.run_single_loop
  exact Evm.loopRun_of_iterN (iterations_finish machine tail slot limit (limit.val-i.val) i (by omega))

theorem run_loop (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (limit : Fin Evm.W) :
    Evm.run [.loop condition body] (iterationMachine machine tail slot limit ⟨0,by decide⟩) =
      .ok (iterationMachine machine tail slot limit limit) 0 :=
  run_loop_from machine tail slot limit ⟨0,by decide⟩ (by change (0 : Nat) ≤ limit.val; exact Nat.zero_le _)


def afterClear (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot) : Evm.Machine :=
  { machine with stack := tail, store := Evm.WordStore.write (clearPrefix machine.store slot (machine.store slot)) slot 0 }

/-- SLOAD captures the ACTUAL header before starting the counter at zero. -/
theorem run_setup (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot) :
    Evm.run setup { machine with stack := .slot slot :: tail } =
      .ok (iterationMachine machine tail slot (machine.store.cells slot) ⟨0,by decide⟩) 0 := rfl

theorem run_finish (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (limit : Fin Evm.W) :
    Evm.run finish (iterationMachine machine tail slot limit limit) =
      .ok { machine with stack := tail, store := Evm.WordStore.write (clearPrefix machine.store slot limit.val) slot 0 } 0 := rfl

/-- ACTUAL current-header runtime loop, with no fixed traversal length/cap.
The full original tail/non-store context is restored; header zero is LAST. -/
theorem run_current (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot) :
    Evm.run code { machine with stack := .slot slot :: tail } = .ok (afterClear machine tail slot) 0 := by
  unfold code
  rw [Evm.run_append_ok (run_setup machine tail slot),Evm.run_append_ok (run_loop machine tail slot (machine.store.cells slot)),run_finish]
  rfl

theorem after_header (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot) :
    (afterClear machine tail slot).store slot = 0 := by
  rw [afterClear,Evm.WordStore.write_same]
  rfl

/-- Exact visited/unvisited word behavior for ALL symbolic data offsets,
including older retained shadows and failed logical-read garbage. -/
theorem after_data (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot) (j : Nat) :
    (afterClear machine tail slot).store (.data slot j) =
      if j < machine.store slot then 0 else machine.store (.data slot j) := by
  have different : Evm.Slot.data slot j ≠ slot := by
    intro same
    have depths := congrArg (fun s => (Solidity.Storage.ofSlot s).depth) same
    change (Solidity.Storage.ofSlot slot).depth+1 = (Solidity.Storage.ofSlot slot).depth at depths
    omega
  unfold afterClear
  rw [Evm.WordStore.write_other _ _ different]
  by_cases visited : j < machine.store slot
  · rw [if_pos visited]
    exact prefix_visited machine.store slot (machine.store slot) j visited
  · rw [if_neg visited]
    exact prefix_unvisited machine.store slot (machine.store slot) j (by omega)

theorem after_outside (machine : Evm.Machine) (tail : List Evm.Word) (slot observer : Evm.Slot)
    (headerApart : observer ≠ slot) (dataApart : ∀ j, j < machine.store slot → observer ≠ .data slot j) :
    (afterClear machine tail slot).store observer = machine.store observer := by
  unfold afterClear
  rw [Evm.WordStore.write_other _ _ headerApart]
  exact prefix_outside machine.store slot observer (machine.store slot) dataApart


/-- info: 'Solidity.Backend.StorageOps.TargetArrayClear.prefix_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prefix_outside
/-- info: 'Solidity.Backend.StorageOps.TargetArrayClear.prefix_visited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prefix_visited
/-- info: 'Solidity.Backend.StorageOps.TargetArrayClear.prefix_unvisited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prefix_unvisited
/-- info: 'Solidity.Backend.StorageOps.TargetArrayClear.prefix_header' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prefix_header
/-- info: 'Solidity.Backend.StorageOps.TargetArrayClear.run_condition' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_condition
/-- info: 'Solidity.Backend.StorageOps.TargetArrayClear.run_body' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_body
/-- info: 'Solidity.Backend.StorageOps.TargetArrayClear.condition_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms condition_at
/-- info: 'Solidity.Backend.StorageOps.TargetArrayClear.body_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms body_at
/-- info: 'Solidity.Backend.StorageOps.TargetArrayClear.turn_more' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms turn_more
/-- info: 'Solidity.Backend.StorageOps.TargetArrayClear.turn_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms turn_done
/-- info: 'Solidity.Backend.StorageOps.TargetArrayClear.iterations_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms iterations_finish
/-- info: 'Solidity.Backend.StorageOps.TargetArrayClear.iterations_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms iterations_prefix
/-- info: 'Solidity.Backend.StorageOps.TargetArrayClear.run_loop_from' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_loop_from
/-- info: 'Solidity.Backend.StorageOps.TargetArrayClear.run_loop' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_loop
/-- info: 'Solidity.Backend.StorageOps.TargetArrayClear.run_setup' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_setup
/-- info: 'Solidity.Backend.StorageOps.TargetArrayClear.run_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_finish
/-- info: 'Solidity.Backend.StorageOps.TargetArrayClear.run_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_current
/-- info: 'Solidity.Backend.StorageOps.TargetArrayClear.after_header' depends on axioms: [propext] -/
#guard_msgs in #print axioms after_header
/-- info: 'Solidity.Backend.StorageOps.TargetArrayClear.after_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms after_data
/-- info: 'Solidity.Backend.StorageOps.TargetArrayClear.after_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms after_outside

end Solidity.Backend.StorageOps.TargetArrayClear
