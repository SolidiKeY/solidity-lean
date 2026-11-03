import Solidity.Backend.StorageOps.TargetNestedArrayCopy

/-! Kernel runtime OUTER copy-loop prefix and termination over the existing
Machine. Current nested inputs evolve; independent snapshot correspondence is
not inferred merely from loop execution. -/
namespace Solidity.Backend.StorageOps.TargetNestedArrayCopyLoop

def prefixMachine (initial : Evm.Machine) (src dst : Evm.Slot) : Nat → Evm.Machine
  | 0 => initial
  | count+1 => TargetArrayCopyTail.afterCopy (prefixMachine initial src dst count) initial.stack
      (.data src count) (.data dst count)

def iterationMachine (initial : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (oldLength limit i : Fin Evm.W) : Evm.Machine :=
  { prefixMachine initial src dst i.val with stack := .val i :: .val limit :: .slot src :: .slot dst :: .val oldLength :: tail }

theorem condition_at (initial : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (oldLength limit i : Fin Evm.W) :
    Evm.run TargetArrayCopy.condition (iterationMachine initial tail src dst oldLength limit i) =
      .ok { iterationMachine initial tail src dst oldLength limit i with stack := .val (Evm.bword (decide (i.val < limit.val))) :: (iterationMachine initial tail src dst oldLength limit i).stack } 0 :=
  TargetArrayClear.run_condition (prefixMachine initial src dst i.val) (.slot dst :: .val oldLength :: tail) src i limit

theorem body_at (initial : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (oldLength limit i : Fin Evm.W) (next : i.val+1 < Evm.W) :
    Evm.run TargetNestedArrayCopy.copyBody (iterationMachine initial tail src dst oldLength limit i) =
      .ok (iterationMachine initial tail src dst oldLength limit ⟨i.val+1,next⟩) 0 := by
  rw [iterationMachine,TargetNestedArrayCopy.run_copy_body]
  rfl

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

theorem turn_more (initial : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (oldLength limit i : Fin Evm.W) (live : i.val < limit.val) :
    Evm.loopTurn (Evm.run TargetArrayCopy.condition) (Evm.run TargetNestedArrayCopy.copyBody)
      (iterationMachine initial tail src dst oldLength limit i) =
      .inl (iterationMachine initial tail src dst oldLength limit ⟨i.val+1,by omega⟩) := by
  have flag : (Evm.bword (decide (i.val < limit.val))).val ≠ 0 := by
    simpa only [live,decide_true,Evm.bword,if_true] using Nat.one_ne_zero
  exact turn_step _ _ _ _ _ flag (condition_at initial tail src dst oldLength limit i)
    (body_at initial tail src dst oldLength limit i (by omega))

private theorem turn_exit (rc rb : Evm.Machine → Evm.Out) (machine : Evm.Machine)
    (cond : rc machine = .ok { machine with stack := .val ⟨0,by decide⟩ :: machine.stack } 0) :
    Evm.loopTurn rc rb machine = .inr (.ok machine 0) := by
  unfold Evm.loopTurn
  rw [cond]
  rfl

theorem turn_done (initial : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (oldLength limit : Fin Evm.W) :
    Evm.loopTurn (Evm.run TargetArrayCopy.condition) (Evm.run TargetNestedArrayCopy.copyBody)
      (iterationMachine initial tail src dst oldLength limit limit) =
      .inr (.ok (iterationMachine initial tail src dst oldLength limit limit) 0) := by
  have zero : Evm.bword (decide (limit.val < limit.val)) = ⟨0,by decide⟩ := by
    apply Fin.ext
    simp only [Nat.lt_irrefl,decide_false,Evm.bword,Bool.false_eq_true,if_false]
  have cond := condition_at initial tail src dst oldLength limit limit
  rw [zero] at cond
  exact turn_exit _ _ _ cond

/-- Every finite runtime outer word length terminates. Remaining is a proof
index for the existing loopIterN specification, never executable source fuel. -/
theorem iterations_finish (initial : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (oldLength limit : Fin Evm.W) (remaining : Nat) (i : Fin Evm.W) (distance : i.val+remaining = limit.val) :
    Evm.loopIterN (Evm.run TargetArrayCopy.condition) (Evm.run TargetNestedArrayCopy.copyBody) (remaining+1)
      (iterationMachine initial tail src dst oldLength limit i) =
      .inr (.ok (iterationMachine initial tail src dst oldLength limit limit) 0) := by
  induction remaining generalizing i with
  | zero =>
    have same : i = limit := Fin.ext (by omega)
    subst i
    rw [Evm.loopIterN,turn_done]
  | succ remaining ih =>
    have live : i.val < limit.val := by omega
    rw [Evm.loopIterN,turn_more initial tail src dst oldLength limit i live]
    apply ih
    change i.val+1+remaining = limit.val
    omega

private theorem run_single_loop (cond body : List Evm.Instr) (machine result : Evm.Machine)
    (finished : Evm.loopRun (Evm.run cond) (Evm.run body) machine = .ok result 0) :
    Evm.run [.loop cond body] machine = .ok result 0 := by
  change (Evm.loopRun (Evm.run cond) (Evm.run body) machine).bind (fun m k => Evm.exec [] k m) = _
  rw [finished]
  rfl

/-- Restart from any matching actual prefix, using kernel loop specification. -/
theorem run_loop_from (initial : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (oldLength limit i : Fin Evm.W) (bound : i.val ≤ limit.val) :
    Evm.run [.loop TargetArrayCopy.condition TargetNestedArrayCopy.copyBody]
      (iterationMachine initial tail src dst oldLength limit i) =
      .ok (iterationMachine initial tail src dst oldLength limit limit) 0 := by
  apply run_single_loop
  exact Evm.loopRun_of_iterN (iterations_finish initial tail src dst oldLength limit (limit.val-i.val) i (by omega))

/-- Matching actual progress before exit, with no executable fuel cap. -/
theorem iterations_prefix (initial : Evm.Machine) (tail : List Evm.Word) (src dst : Evm.Slot)
    (oldLength limit : Fin Evm.W) (steps : Nat) (i : Fin Evm.W) (bound : i.val+steps ≤ limit.val) :
    Evm.loopIterN (Evm.run TargetArrayCopy.condition) (Evm.run TargetNestedArrayCopy.copyBody) steps
      (iterationMachine initial tail src dst oldLength limit i) =
      .inl (iterationMachine initial tail src dst oldLength limit ⟨i.val+steps,by omega⟩) := by
  induction steps generalizing i with
  | zero =>
    have same : (⟨i.val+0,by omega⟩ : Fin Evm.W) = i := Fin.ext (by rfl)
    rw [same]
    rfl
  | succ steps ih =>
    have live : i.val < limit.val := by omega
    rw [Evm.loopIterN,turn_more initial tail src dst oldLength limit i live]
    have next : i.val+1 < Evm.W := by omega
    have actual := ih (⟨i.val+1,next⟩ : Fin Evm.W) (by change i.val+1+steps ≤ limit.val; omega)
    refine actual.trans ?_
    apply congrArg (fun j => Sum.inl (iterationMachine initial tail src dst oldLength limit j))
    apply Fin.ext
    change i.val+1+steps = i.val+(steps+1)
    omega

/-- Actual finite nested writes use EACH CURRENT inner pair of headers. -/
def touched (initial : Evm.Machine) (src dst : Evm.Slot) : Nat → List Evm.Slot
  | 0 => []
  | count+1 =>
    let current := prefixMachine initial src dst count
    let target := Evm.Slot.data dst count
    let source := Evm.Slot.data src count
    touched initial src dst count ++ target ::
      (List.range (max (current.store source) (current.store target))).map (fun j => Evm.Slot.data target j)

theorem prefix_outside (initial : Evm.Machine) (src dst observer : Evm.Slot) (count : Nat)
    (outside : observer ∉ touched initial src dst count) :
    (prefixMachine initial src dst count).store observer = initial.store observer := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have earlier : observer ∉ touched initial src dst count := by
      intro member; exact outside (List.mem_append.mpr (Or.inl member))
    have header : observer ≠ .data dst count := by
      intro same; exact outside (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl same))))
    have payload : ∀ j, j < max ((prefixMachine initial src dst count).store (.data src count))
        ((prefixMachine initial src dst count).store (.data dst count)) → observer ≠ .data (.data dst count) j := by
      intro j inside same
      exact outside (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j,List.mem_range.mpr inside,same.symm⟩))))
    change (TargetArrayCopyTail.afterCopy _ _ _ _).store observer = _
    rw [TargetArrayCopyTail.after_outside _ _ _ _ _ header payload]
    exact ih earlier

/-- Any as-yet unvisited OUTER child header and all of its retained payloads
remain exactly unchanged. This is stronger than live-only observation framing. -/
theorem unvisited_child (initial : Evm.Machine) (src dst : Evm.Slot) (count outer : Nat) (future : count ≤ outer) :
    (prefixMachine initial src dst count).store (.data dst outer) = initial.store (.data dst outer) ∧
    ∀ inner, (prefixMachine initial src dst count).store (.data (.data dst outer) inner) =
      initial.store (.data (.data dst outer) inner) := by
  have separated : ∀ observer, (observer = Evm.Slot.data dst outer ∨ ∃ inner, observer = .data (.data dst outer) inner) →
      observer ∉ touched initial src dst count := by
    intro observer kind
    induction count with
    | zero => exact List.not_mem_nil
    | succ count ih =>
      intro member
      rcases List.mem_append.mp member with earlier | latest
      · exact ih (by omega) earlier
      · rcases List.mem_cons.mp latest with header | payload
        · rcases kind with rfl | ⟨inner,rfl⟩
          · have same := (Evm.Slot.data.inj header).2
            omega
          · have depths := congrArg (fun slot => (Solidity.Storage.ofSlot slot).depth) header
            change (Solidity.Storage.ofSlot dst).depth+1+1 = (Solidity.Storage.ofSlot dst).depth+1 at depths
            omega
        · obtain ⟨inner,_,same⟩ := List.mem_map.mp payload
          rcases kind with rfl | ⟨j,rfl⟩
          · have depths := congrArg (fun slot => (Solidity.Storage.ofSlot slot).depth) same
            change (Solidity.Storage.ofSlot dst).depth+1+1 = (Solidity.Storage.ofSlot dst).depth+1 at depths
            omega
          · have equal := (Evm.Slot.data.inj (Evm.Slot.data.inj same).1).2
            omega
  refine ⟨prefix_outside initial src dst _ count (separated _ (Or.inl rfl)),?_⟩
  intro inner
  exact prefix_outside initial src dst _ count (separated _ (Or.inr ⟨inner,rfl⟩))

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopyLoop.prefixMachine' does not depend on any axioms -/
#guard_msgs in #print axioms prefixMachine
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopyLoop.iterationMachine' does not depend on any axioms -/
#guard_msgs in #print axioms iterationMachine
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopyLoop.condition_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms condition_at
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopyLoop.body_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms body_at
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopyLoop.turn_more' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms turn_more
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopyLoop.turn_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms turn_done
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopyLoop.iterations_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms iterations_finish
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopyLoop.run_loop_from' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_loop_from
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopyLoop.iterations_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms iterations_prefix
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopyLoop.touched' does not depend on any axioms -/
#guard_msgs in #print axioms touched
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopyLoop.prefix_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prefix_outside
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayCopyLoop.unvisited_child' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms unvisited_child

end Solidity.Backend.StorageOps.TargetNestedArrayCopyLoop
