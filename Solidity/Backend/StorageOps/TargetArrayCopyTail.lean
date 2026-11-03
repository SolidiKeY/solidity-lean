import Solidity.Backend.StorageOps.TargetArrayCopy

/-! The actual copy program's second runtime loop clears only the stale tail.
Its starting counter is the captured source length, not zero. -/
namespace Solidity.Backend.StorageOps.TargetArrayCopyTail

def clearSuffix (store : Evm.WordStore) (slot : Evm.Slot) (start : Nat) : Nat → Evm.WordStore
  | 0 => store
  | count+1 => if start ≤ count then Evm.WordStore.write (clearSuffix store slot start count) (.data slot count) 0
      else clearSuffix store slot start count

theorem suffix_before (store : Evm.WordStore) (slot : Evm.Slot) (start count : Nat)
    (before : count ≤ start) : clearSuffix store slot start count = store := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [clearSuffix,if_neg (by omega)]
    exact ih (by omega)

theorem suffix_outside (store : Evm.WordStore) (slot observer : Evm.Slot) (start count : Nat)
    (apart : ∀ j, start ≤ j → j < count → observer ≠ .data slot j) :
    clearSuffix store slot start count observer = store observer := by
  induction count with
  | zero => rfl
  | succ count ih =>
    by_cases active : start ≤ count
    · rw [clearSuffix,if_pos active,Evm.WordStore.write_other _ _ (apart count active (by omega))]
      exact ih (fun j begun inside => apart j begun (by omega))
    · rw [clearSuffix,if_neg active]
      exact ih (fun j begun inside => apart j begun (by omega))

theorem suffix_visited (store : Evm.WordStore) (slot : Evm.Slot) (start count j : Nat)
    (begun : start ≤ j) (inside : j < count) :
    clearSuffix store slot start count (.data slot j) = 0 := by
  induction count with
  | zero => omega
  | succ count ih =>
    have active : start ≤ count := by omega
    rw [clearSuffix,if_pos active]
    by_cases last : j = count
    · subst j; rw [Evm.WordStore.write_same]; rfl
    · have different : Evm.Slot.data slot j ≠ .data slot count := by
        intro same; exact last (Evm.Slot.data.inj same).2
      rw [Evm.WordStore.write_other _ _ different]
      exact ih (by omega)

theorem suffix_unvisited (store : Evm.WordStore) (slot : Evm.Slot) (start count j : Nat)
    (outside : j < start ∨ count ≤ j) :
    clearSuffix store slot start count (.data slot j) = store (.data slot j) := by
  apply suffix_outside
  intro k begun inside same
  have equal := (Evm.Slot.data.inj same).2
  omega

def iterationMachine (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (start : Nat) (limit i : Fin Evm.W) : Evm.Machine :=
  { machine with stack := .val i :: .val limit :: .slot slot :: tail, store := clearSuffix machine.store slot start i.val }

theorem condition_at (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (start : Nat) (limit i : Fin Evm.W) :
    Evm.run TargetArrayClear.condition (iterationMachine machine tail slot start limit i) =
      .ok { iterationMachine machine tail slot start limit i with stack := .val (Evm.bword (decide (i.val < limit.val))) :: (iterationMachine machine tail slot start limit i).stack } 0 := by
  exact TargetArrayClear.run_condition { machine with store := clearSuffix machine.store slot start i.val } tail slot i limit

theorem body_at (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (start : Nat) (limit i : Fin Evm.W) (begun : start ≤ i.val) (next : i.val+1 < Evm.W) :
    Evm.run TargetArrayClear.body (iterationMachine machine tail slot start limit i) =
      .ok (iterationMachine machine tail slot start limit ⟨i.val+1,next⟩) 0 := by
  have step := TargetArrayClear.run_body { machine with store := clearSuffix machine.store slot start i.val }
    tail slot i limit next
  change Evm.run TargetArrayClear.body (iterationMachine machine tail slot start limit i) = _ at step
  simpa only [iterationMachine,clearSuffix,if_pos begun] using step

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

theorem turn_more (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (start : Nat) (limit i : Fin Evm.W) (begun : start ≤ i.val) (live : i.val < limit.val) :
    Evm.loopTurn (Evm.run TargetArrayClear.condition) (Evm.run TargetArrayClear.body) (iterationMachine machine tail slot start limit i) =
      .inl (iterationMachine machine tail slot start limit ⟨i.val+1,by omega⟩) := by
  have guard : (Evm.bword (decide (i.val < limit.val))).val ≠ 0 := by
    simpa only [live,decide_true,Evm.bword,if_true] using Nat.one_ne_zero
  exact turn_step (Evm.run TargetArrayClear.condition) (Evm.run TargetArrayClear.body) _ _ _ guard
    (condition_at machine tail slot start limit i) (body_at machine tail slot start limit i begun (by have h := limit.isLt; omega))


private theorem turn_exit (rc rb : Evm.Machine → Evm.Out) (machine : Evm.Machine)
    (cond : rc machine = .ok { machine with stack := .val ⟨0,by decide⟩ :: machine.stack } 0) :
    Evm.loopTurn rc rb machine = .inr (.ok machine 0) := by
  unfold Evm.loopTurn
  rw [cond]
  rfl

theorem turn_done (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (start : Nat) (limit : Fin Evm.W) :
    Evm.loopTurn (Evm.run TargetArrayClear.condition) (Evm.run TargetArrayClear.body) (iterationMachine machine tail slot start limit limit) =
      .inr (.ok (iterationMachine machine tail slot start limit limit) 0) := by
  have zero : Evm.bword (decide (limit.val < limit.val)) = ⟨0,by decide⟩ := by
    apply Fin.ext
    simp only [Nat.lt_irrefl,decide_false,Evm.bword,Bool.false_eq_true,if_false]
  have cond := condition_at machine tail slot start limit limit
  rw [zero] at cond
  exact turn_exit (Evm.run TargetArrayClear.condition) (Evm.run TargetArrayClear.body) _ cond

/-- Every finite runtime word length terminates after exactly its remaining
body turns plus one final false condition. This is not a source fuel bound. -/
theorem iterations_finish (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (start : Nat) (limit : Fin Evm.W) (remaining : Nat) (i : Fin Evm.W) (begun : start ≤ i.val) (distance : i.val+remaining = limit.val) :
    Evm.loopIterN (Evm.run TargetArrayClear.condition) (Evm.run TargetArrayClear.body) (remaining+1) (iterationMachine machine tail slot start limit i) =
      .inr (.ok (iterationMachine machine tail slot start limit limit) 0) := by
  induction remaining generalizing i with
  | zero =>
    have same : i = limit := Fin.ext (by omega)
    subst i
    rw [Evm.loopIterN,turn_done]
  | succ remaining ih =>
    have live : i.val < limit.val := by omega
    rw [Evm.loopIterN,turn_more machine tail slot start limit i begun live]
    apply ih _ (by change start ≤ i.val+1; omega)
    change i.val + 1 + remaining = limit.val
    omega

/-- Matching prefix/progress before the final false condition, for every
runtime start index. Unvisited words are preserved by prefix_outside. -/
theorem iterations_prefix (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (start : Nat) (limit : Fin Evm.W) (steps : Nat) (i : Fin Evm.W) (begun : start ≤ i.val) (bound : i.val+steps ≤ limit.val) :
    Evm.loopIterN (Evm.run TargetArrayClear.condition) (Evm.run TargetArrayClear.body) steps (iterationMachine machine tail slot start limit i) =
      .inl (iterationMachine machine tail slot start limit ⟨i.val+steps,by omega⟩) := by
  induction steps generalizing i with
  | zero =>
    have same : (⟨i.val+0,by have h := limit.isLt; omega⟩ : Fin Evm.W) = i := Fin.ext (by change i.val + 0 = i.val; omega)
    rw [same]
    rfl
  | succ steps ih =>
    have live : i.val < limit.val := by omega
    rw [Evm.loopIterN,turn_more machine tail slot start limit i begun live]
    have next : i.val+1 < Evm.W := by have h := limit.isLt; omega
    have prefixResult := ih (⟨i.val+1,next⟩ : Fin Evm.W) (by change start ≤ i.val+1; omega) (by change i.val+1+steps ≤ limit.val; omega)
    refine prefixResult.trans ?_
    apply congrArg (fun j => Sum.inl (iterationMachine machine tail slot start limit j))
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
theorem run_loop_from (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (start : Nat) (limit i : Fin Evm.W) (begun : start ≤ i.val) (bound : i.val ≤ limit.val) :
    Evm.run [.loop TargetArrayClear.condition TargetArrayClear.body] (iterationMachine machine tail slot start limit i) =
      .ok (iterationMachine machine tail slot start limit limit) 0 := by
  apply run_single_loop
  exact Evm.loopRun_of_iterN (iterations_finish machine tail slot start limit (limit.val-i.val) i begun (by omega))



def endIndex (start limit : Fin Evm.W) : Fin Evm.W :=
  ⟨max start.val limit.val,by have a := start.isLt; have b := limit.isLt; omega⟩

/-- Exact stale-tail execution also covers growth, where the first condition
is already false and the previously copied prefix is untouched. -/
theorem run_tail (machine : Evm.Machine) (tail : List Evm.Word) (slot : Evm.Slot)
    (start limit : Fin Evm.W) :
    Evm.run [.loop TargetArrayClear.condition TargetArrayClear.body]
      { machine with stack := .val start :: .val limit :: .slot slot :: tail } =
      .ok { machine with stack := .val (endIndex start limit) :: .val limit :: .slot slot :: tail, store := clearSuffix machine.store slot start.val (max start.val limit.val) } 0 := by
  by_cases ordered : start.val ≤ limit.val
  · have bound := run_loop_from machine tail slot start.val limit start (Nat.le_refl _) ordered
    have endEq : endIndex start limit = limit := Fin.ext (Nat.max_eq_right ordered)
    simpa only [iterationMachine,suffix_before machine.store slot start.val start.val (Nat.le_refl _),Nat.max_eq_right ordered,endEq] using bound
  · have endEq : endIndex start limit = start := Fin.ext (Nat.max_eq_left (by omega))
    have zero : Evm.bword (decide (start.val < limit.val)) = ⟨0,by decide⟩ := by
      apply Fin.ext
      simp only [show ¬ start.val < limit.val by omega,decide_false,Evm.bword,Bool.false_eq_true,if_false]
    have cond := TargetArrayClear.run_condition machine tail slot start limit
    rw [zero] at cond
    have finished := turn_exit (Evm.run TargetArrayClear.condition) (Evm.run TargetArrayClear.body)
      { machine with stack := .val start :: .val limit :: .slot slot :: tail } cond
    have result := Evm.loopRun_of_iterN (show Evm.loopIterN (Evm.run TargetArrayClear.condition)
      (Evm.run TargetArrayClear.body) 1 { machine with stack := .val start :: .val limit :: .slot slot :: tail } =
        .inr (.ok { machine with stack := .val start :: .val limit :: .slot slot :: tail } 0) by
          rw [Evm.loopIterN,finished])
    have executed := run_single_loop _ _ _ _ result
    simpa only [Nat.max_eq_left (show limit.val ≤ start.val by omega),endEq,
      suffix_before machine.store slot start.val start.val (Nat.le_refl _)] using executed

theorem run_transition (machine : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (sourceLength oldLength : Fin Evm.W) :
    Evm.run TargetArrayCopy.transition { machine with stack := .val sourceLength :: .val sourceLength :: .slot src :: .slot dst :: .val oldLength :: tail } =
      .ok { machine with stack := .val sourceLength :: .val oldLength :: .slot dst :: .val sourceLength :: tail } 0 := by
  rfl

theorem run_finish (machine : Evm.Machine) (tail : List Evm.Word) (dst : Evm.Slot)
    (counter oldLength sourceLength : Fin Evm.W) :
    Evm.run TargetArrayCopy.finish { machine with stack := .val counter :: .val oldLength :: .slot dst :: .val sourceLength :: tail } =
      .ok { machine with stack := tail, store := Evm.WordStore.write machine.store dst sourceLength.val } 0 := by
  rfl

def afterCopy (machine : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot) : Evm.Machine :=
  { machine with stack := tail, store := Evm.WordStore.write (clearSuffix (TargetArrayCopy.copyPrefix machine.store src dst (machine.store src)) dst (machine.store src) (max (machine.store src) (machine.store dst))) dst (machine.store src) }

/-- Complete ACTUAL two-loop target program: current headers are captured before
writes, source payloads are current SLOADs, stale tail only is cleared, and the
captured source header is stored last. No graph or snapshot oracle is executed. -/
theorem run_current (machine : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot) :
    Evm.run TargetArrayCopy.code { machine with stack := .slot src :: .slot dst :: tail } =
      .ok (afterCopy machine tail src dst) 0 := by
  unfold TargetArrayCopy.code
  simp only [List.append_assoc]
  rw [Evm.run_append_ok (TargetArrayCopy.run_setup machine tail src dst)]
  change Evm.run ([.loop TargetArrayCopy.condition TargetArrayCopy.body] ++ (TargetArrayCopy.transition ++ ([.loop TargetArrayClear.condition TargetArrayClear.body] ++ TargetArrayCopy.finish))) (TargetArrayCopy.iterationMachine machine tail src dst (machine.store.cells dst) (machine.store.cells src) ⟨0,by decide⟩) = _
  rw [Evm.run_append_ok (TargetArrayCopy.run_loop machine tail src dst (machine.store.cells dst) (machine.store.cells src))]
  simp only [TargetArrayCopy.iterationMachine]
  rw [Evm.run_append_ok (run_transition { machine with store := TargetArrayCopy.copyPrefix machine.store src dst (machine.store.cells src).val } tail src dst (machine.store.cells src) (machine.store.cells dst))]
  rw [Evm.run_append_ok (run_tail { machine with store := TargetArrayCopy.copyPrefix machine.store src dst (machine.store.cells src).val } (.val (machine.store.cells src) :: tail) dst (machine.store.cells src) (machine.store.cells dst))]
  exact run_finish { machine with store := clearSuffix (TargetArrayCopy.copyPrefix machine.store src dst (machine.store src)) dst (machine.store src) (max (machine.store src) (machine.store dst)) } tail dst (endIndex (machine.store.cells src) (machine.store.cells dst)) (machine.store.cells dst) (machine.store.cells src)


theorem after_header (machine : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot) :
    (afterCopy machine tail src dst).store dst = machine.store src := by
  exact Evm.WordStore.write_same_of_lt _ _ _ (machine.store.cells src).isLt

theorem after_data (machine : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot) (j : Nat) :
    (afterCopy machine tail src dst).store (.data dst j) =
      if j < machine.store src then machine.store (.data src j)
      else if j < machine.store dst then 0 else machine.store (.data dst j) := by
  have different : Evm.Slot.data dst j ≠ dst := by
    intro same
    have depths := congrArg (fun s => (Solidity.Storage.ofSlot s).depth) same
    change (Solidity.Storage.ofSlot dst).depth+1 = (Solidity.Storage.ofSlot dst).depth at depths
    omega
  change Evm.WordStore.write _ dst (machine.store src) (.data dst j) = _
  rw [Evm.WordStore.write_other _ _ different]
  by_cases copied : j < machine.store src
  · rw [if_pos copied,suffix_unvisited _ _ _ _ _ (Or.inl copied)]
    exact TargetArrayCopy.prefix_visited _ _ _ _ _ copied
  · rw [if_neg copied]
    by_cases cleared : j < machine.store dst
    · rw [if_pos cleared]
      exact suffix_visited _ _ _ _ _ (by omega) (by omega)
    · rw [if_neg cleared,suffix_unvisited _ _ _ _ _ (Or.inr (by omega))]
      exact TargetArrayCopy.prefix_unvisited _ _ _ _ _ (by omega)

theorem after_outside (machine : Evm.Machine) (tail : List Evm.Word) (src dst observer : Evm.Slot)
    (header : observer ≠ dst)
    (payload : ∀ j, j < max (machine.store src) (machine.store dst) → observer ≠ .data dst j) :
    (afterCopy machine tail src dst).store observer = machine.store observer := by
  change Evm.WordStore.write _ dst (machine.store src) observer = _
  rw [Evm.WordStore.write_other _ _ header]
  rw [suffix_outside _ _ _ _ _ (fun j _ inside => payload j inside)]
  exact TargetArrayCopy.prefix_outside _ _ _ _ _ (fun j inside => payload j (by omega))

/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyTail.suffix_before' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms suffix_before
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyTail.suffix_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms suffix_outside
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyTail.suffix_visited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms suffix_visited
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyTail.suffix_unvisited' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms suffix_unvisited
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyTail.condition_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms condition_at
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyTail.body_at' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms body_at
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyTail.turn_more' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms turn_more
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyTail.turn_done' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms turn_done
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyTail.iterations_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms iterations_finish
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyTail.iterations_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms iterations_prefix
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyTail.run_loop_from' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_loop_from
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyTail.run_tail' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_tail
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyTail.run_transition' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_transition
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyTail.run_finish' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_finish
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyTail.run_current' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms run_current
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyTail.after_header' depends on axioms: [propext] -/
#guard_msgs in #print axioms after_header
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyTail.after_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms after_data
/-- info: 'Solidity.Backend.StorageOps.TargetArrayCopyTail.after_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms after_outside

end Solidity.Backend.StorageOps.TargetArrayCopyTail
