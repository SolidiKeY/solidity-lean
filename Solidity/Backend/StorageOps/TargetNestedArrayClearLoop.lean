import Solidity.Backend.StorageOps.LoopLaws
import Solidity.Backend.StorageOps.TargetNestedArrayCopyLoop

/-! Runtime OUTER stale-child clear loop. Each active child executes the checked
inner primitive live-prefix clear; older inner and outer shadows are retained. -/
namespace Solidity.Backend.StorageOps.TargetNestedArrayClearLoop

def prefixMachine (initial : Evm.Machine) (dst : Evm.Slot) (start : Nat) : Nat → Evm.Machine
  | 0 => initial
  | count+1 => if start ≤ count then TargetArrayClear.afterClear (prefixMachine initial dst start count) initial.stack (.data dst count)
      else prefixMachine initial dst start count

theorem prefix_before (initial : Evm.Machine) (dst : Evm.Slot) (start count : Nat) (before : count ≤ start) :
    prefixMachine initial dst start count = initial := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [prefixMachine,if_neg (by omega)]
    exact ih (by omega)

def iterationMachine (initial : Evm.Machine) (tail : List Evm.Word) (dst : Evm.Slot) (start : Nat)
    (newLength limit i : Fin Evm.W) : Evm.Machine :=
  { prefixMachine initial dst start i.val with stack := .val i :: .val limit :: .slot dst :: .val newLength :: tail }

theorem condition_at (initial : Evm.Machine) (tail : List Evm.Word) (dst : Evm.Slot) (start : Nat)
    (newLength limit i : Fin Evm.W) :
    Evm.run TargetArrayClear.condition (iterationMachine initial tail dst start newLength limit i) =
      .ok { iterationMachine initial tail dst start newLength limit i with stack := .val (Evm.bword (decide (i.val < limit.val))) ::
        (iterationMachine initial tail dst start newLength limit i).stack } 0 :=
  TargetArrayClear.run_condition (prefixMachine initial dst start i.val) (.val newLength :: tail) dst i limit

theorem body_at (initial : Evm.Machine) (tail : List Evm.Word) (dst : Evm.Slot) (start : Nat)
    (newLength limit i : Fin Evm.W) (begun : start ≤ i.val) (next : i.val+1 < Evm.W) :
    Evm.run TargetNestedArrayCopy.clearBody (iterationMachine initial tail dst start newLength limit i) =
      .ok (iterationMachine initial tail dst start newLength limit ⟨i.val+1,next⟩) 0 := by
  rw [iterationMachine,TargetNestedArrayCopy.run_clear_body]
  simp only [iterationMachine,prefixMachine,if_pos begun]
  rfl

theorem turn_more (initial : Evm.Machine) (tail : List Evm.Word) (dst : Evm.Slot) (start : Nat)
    (newLength limit i : Fin Evm.W) (begun : start ≤ i.val) (live : i.val < limit.val) :
    Evm.loopTurn (Evm.run TargetArrayClear.condition) (Evm.run TargetNestedArrayCopy.clearBody)
      (iterationMachine initial tail dst start newLength limit i) =
      .inl (iterationMachine initial tail dst start newLength limit ⟨i.val+1,by omega⟩) := by
  have flag : (Evm.bword (decide (i.val < limit.val))).val ≠ 0 := by
    simpa only [live,decide_true,Evm.bword,if_true] using Nat.one_ne_zero
  exact LoopLaws.turn_step _ _ _ _ _ flag (condition_at initial tail dst start newLength limit i)
    (body_at initial tail dst start newLength limit i begun (by omega))

theorem turn_done (initial : Evm.Machine) (tail : List Evm.Word) (dst : Evm.Slot) (start : Nat)
    (newLength limit i : Fin Evm.W) (done : limit.val ≤ i.val) :
    Evm.loopTurn (Evm.run TargetArrayClear.condition) (Evm.run TargetNestedArrayCopy.clearBody)
      (iterationMachine initial tail dst start newLength limit i) =
      .inr (.ok (iterationMachine initial tail dst start newLength limit i) 0) := by
  have zero : Evm.bword (decide (i.val < limit.val)) = ⟨0,by decide⟩ := by
    apply Fin.ext
    simp only [show ¬ i.val < limit.val by omega,decide_false,Evm.bword,Bool.false_eq_true,if_false]
  have cond := condition_at initial tail dst start newLength limit i
  rw [zero] at cond
  exact LoopLaws.turn_exit _ _ _ cond

/-- Exact termination of the stale OUTER suffix for every runtime word limit. -/
theorem iterations_finish (initial : Evm.Machine) (tail : List Evm.Word) (dst : Evm.Slot) (start : Nat)
    (newLength limit : Fin Evm.W) (remaining : Nat) (i : Fin Evm.W)
    (begun : start ≤ i.val) (distance : i.val+remaining = limit.val) :
    Evm.loopIterN (Evm.run TargetArrayClear.condition) (Evm.run TargetNestedArrayCopy.clearBody) (remaining+1)
      (iterationMachine initial tail dst start newLength limit i) =
      .inr (.ok (iterationMachine initial tail dst start newLength limit limit) 0) := by
  induction remaining generalizing i with
  | zero =>
    have same : i = limit := Fin.ext (by omega)
    subst i
    rw [Evm.loopIterN,turn_done initial tail dst start newLength limit limit (Nat.le_refl _)]
  | succ remaining ih =>
    have live : i.val < limit.val := by omega
    rw [Evm.loopIterN,turn_more initial tail dst start newLength limit i begun live]
    apply ih
    · change start ≤ i.val+1; omega
    · change i.val+1+remaining = limit.val; omega

theorem run_loop_from (initial : Evm.Machine) (tail : List Evm.Word) (dst : Evm.Slot) (start : Nat)
    (newLength limit i : Fin Evm.W) (begun : start ≤ i.val) (bound : i.val ≤ limit.val) :
    Evm.run [.loop TargetArrayClear.condition TargetNestedArrayCopy.clearBody]
      (iterationMachine initial tail dst start newLength limit i) =
      .ok (iterationMachine initial tail dst start newLength limit limit) 0 := by
  apply LoopLaws.run_single_loop
  exact Evm.loopRun_of_iterN (iterations_finish initial tail dst start newLength limit (limit.val-i.val) i begun (by omega))

theorem run_loop_immediate (initial : Evm.Machine) (tail : List Evm.Word) (dst : Evm.Slot) (start : Nat)
    (newLength limit i : Fin Evm.W) (done : limit.val ≤ i.val) :
    Evm.run [.loop TargetArrayClear.condition TargetNestedArrayCopy.clearBody]
      (iterationMachine initial tail dst start newLength limit i) =
      .ok (iterationMachine initial tail dst start newLength limit i) 0 := by
  apply LoopLaws.run_single_loop
  exact Evm.loopRun_of_iterN (show Evm.loopIterN _ _ 1 _ = _ by
    rw [Evm.loopIterN,turn_done initial tail dst start newLength limit i done])

def finalIndex (newLength oldLength : Fin Evm.W) : Fin Evm.W := ⟨max newLength.val oldLength.val,by omega⟩

/-- Growth performs no stale-child clearing; shrinking clears exactly the
old live suffix. Header limits are captured stack words, not reread metadata. -/
theorem run_loop (initial : Evm.Machine) (tail : List Evm.Word) (dst : Evm.Slot) (newLength oldLength : Fin Evm.W) :
    Evm.run [.loop TargetArrayClear.condition TargetNestedArrayCopy.clearBody]
      { initial with stack := .val newLength :: .val oldLength :: .slot dst :: .val newLength :: tail } =
      .ok (iterationMachine initial tail dst newLength.val newLength oldLength (finalIndex newLength oldLength)) 0 := by
  by_cases bound : newLength.val ≤ oldLength.val
  · have final : finalIndex newLength oldLength = oldLength := Fin.ext (Nat.max_eq_right bound)
    rw [final]
    have actual := run_loop_from initial tail dst newLength.val newLength oldLength newLength (Nat.le_refl _) bound
    simpa only [iterationMachine,prefix_before initial dst newLength.val newLength.val (Nat.le_refl _)] using actual
  · have final : finalIndex newLength oldLength = newLength := Fin.ext (Nat.max_eq_left (by omega))
    rw [final]
    have actual := run_loop_immediate initial tail dst newLength.val newLength oldLength newLength (by omega)
    simpa only [iterationMachine,prefix_before initial dst newLength.val newLength.val (Nat.le_refl _)] using actual

/-- Matching progress within the active runtime stale-child suffix. -/
theorem iterations_prefix (initial : Evm.Machine) (tail : List Evm.Word) (dst : Evm.Slot) (start : Nat)
    (newLength limit : Fin Evm.W) (steps : Nat) (i : Fin Evm.W)
    (begun : start ≤ i.val) (bound : i.val+steps ≤ limit.val) :
    Evm.loopIterN (Evm.run TargetArrayClear.condition) (Evm.run TargetNestedArrayCopy.clearBody) steps
      (iterationMachine initial tail dst start newLength limit i) =
      .inl (iterationMachine initial tail dst start newLength limit ⟨i.val+steps,by omega⟩) := by
  induction steps generalizing i with
  | zero =>
    have same : (⟨i.val+0,by omega⟩ : Fin Evm.W) = i := Fin.ext (by rfl)
    rw [same]
    rfl
  | succ steps ih =>
    have live : i.val < limit.val := by omega
    rw [Evm.loopIterN,turn_more initial tail dst start newLength limit i begun live]
    have next : i.val+1 < Evm.W := by omega
    have actual := ih (⟨i.val+1,next⟩ : Fin Evm.W) (by change start ≤ i.val+1; omega)
      (by change i.val+1+steps ≤ limit.val; omega)
    refine actual.trans ?_
    apply congrArg (fun j => Sum.inl (iterationMachine initial tail dst start newLength limit j))
    apply Fin.ext
    change i.val+1+steps = i.val+(steps+1)
    omega

def touched (initial : Evm.Machine) (dst : Evm.Slot) (start : Nat) : Nat → List Evm.Slot
  | 0 => []
  | count+1 => if start ≤ count then
      touched initial dst start count ++ Evm.Slot.data dst count ::
        (List.range ((prefixMachine initial dst start count).store (.data dst count))).map (fun j => Evm.Slot.data (.data dst count) j)
      else touched initial dst start count

theorem prefix_outside (initial : Evm.Machine) (dst observer : Evm.Slot) (start count : Nat)
    (outside : observer ∉ touched initial dst start count) :
    (prefixMachine initial dst start count).store observer = initial.store observer := by
  induction count with
  | zero => rfl
  | succ count ih =>
    by_cases active : start ≤ count
    · have earlier : observer ∉ touched initial dst start count := by
        intro member; exact outside (by rw [touched,if_pos active]; exact List.mem_append.mpr (Or.inl member))
      have header : observer ≠ .data dst count := by
        intro same; apply outside; rw [touched,if_pos active]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl same)))
      have payload : ∀ j, j < (prefixMachine initial dst start count).store (.data dst count) → observer ≠ .data (.data dst count) j := by
        intro j inside same; apply outside; rw [touched,if_pos active]
        exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ (List.mem_map.mpr ⟨j,List.mem_range.mpr inside,same.symm⟩)))
      rw [prefixMachine,if_pos active,TargetArrayClear.after_outside _ _ _ _ header payload]
      exact ih earlier
    · rw [prefixMachine,if_neg active]
      exact ih (by simpa only [touched,if_neg active] using outside)

/-- Both earlier copied children and older OUTER shadows are preserved by the
stale-child phase, including every retained INNER payload observation. -/
theorem outside_child (initial : Evm.Machine) (dst : Evm.Slot) (start count outer : Nat)
    (outside : outer < start ∨ count ≤ outer) :
    (prefixMachine initial dst start count).store (.data dst outer) = initial.store (.data dst outer) ∧
    ∀ inner, (prefixMachine initial dst start count).store (.data (.data dst outer) inner) = initial.store (.data (.data dst outer) inner) := by
  have separated : ∀ observer, (observer = Evm.Slot.data dst outer ∨ ∃ inner, observer = .data (.data dst outer) inner) →
      observer ∉ touched initial dst start count := by
    intro observer kind
    induction count with
    | zero => exact List.not_mem_nil
    | succ count ih =>
      intro member
      by_cases active : start ≤ count
      · rw [touched,if_pos active] at member
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
      · rw [touched,if_neg active] at member
        exact ih (by omega) member
  refine ⟨prefix_outside initial dst _ start count (separated _ (Or.inl rfl)),?_⟩
  intro inner
  exact prefix_outside initial dst _ start count (separated _ (Or.inr ⟨inner,rfl⟩))

/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayClearLoop.prefixMachine' does not depend on any axioms -/
#guard_msgs in #print axioms prefixMachine
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayClearLoop.prefix_before' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prefix_before
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayClearLoop.iterationMachine' does not depend on any axioms -/
#guard_msgs in #print axioms iterationMachine
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayClearLoop.condition_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms condition_at
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayClearLoop.body_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms body_at
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayClearLoop.turn_more' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms turn_more
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayClearLoop.turn_done' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms turn_done
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayClearLoop.iterations_finish' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms iterations_finish
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayClearLoop.run_loop_from' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_loop_from
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayClearLoop.run_loop_immediate' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_loop_immediate
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayClearLoop.finalIndex' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms finalIndex
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayClearLoop.run_loop' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_loop
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayClearLoop.iterations_prefix' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms iterations_prefix
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayClearLoop.touched' does not depend on any axioms -/
#guard_msgs in #print axioms touched
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayClearLoop.prefix_outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms prefix_outside
/-- info: 'Solidity.Backend.StorageOps.TargetNestedArrayClearLoop.outside_child' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms outside_child

end Solidity.Backend.StorageOps.TargetNestedArrayClearLoop
