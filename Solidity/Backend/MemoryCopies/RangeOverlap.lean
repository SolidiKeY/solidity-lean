import Solidity.Backend.MemoryCopies.RangeOverlapInterface

/-! Descending execution preserves every unread lower source cell. The existing
conditional emitter selects between proved ascending and descending traversals. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem backward_range_condition (machine : Machine) (count : Nat) (destination source : Fin W)
    (bounded : count < W) :
    run backwardRangeCond (memoryRangeMachine machine count 0 destination source) =
      .ok ((memoryRangeMachine machine count 0 destination source).push (.val (bword (decide (0 < count))))) 0 := by
  simp only [backwardRangeCond,memoryRangeMachine,run,exec_cons_zero,Instr.step,Machine.push,Machine.next,
    Out.ok_bind,exec_nil,List.getElem?_cons_zero,List.getElem?_cons_succ,List.cons_append,List.nil_append,
    Nat.reduceSub,wmod_def,Nat.zero_mod,Nat.mod_eq_of_lt bounded]

theorem backward_read_turn (machine : Machine) (index : Nat) (destination source : Fin W)
    (bounded : index + 1 < W) (room : destination.val + (index + 1) ≤ W)
    (readable : source.val + (index + 1) ≤ W) (word : Word)
    (selected : machine.mem (source.val + index) = word) :
    run backwardReadRangeBody (memoryRangeMachine machine (index + 1) 0 destination source) =
      .ok (memoryRangeMachine (writeMachine machine (destination.val + index) word) index 0 destination source) 0 := by
  have decrement : wmod ((index + 1) + (W - 1)) = wmod index := by
    apply Fin.ext
    change ((index + 1) + (W - 1)) % W = index % W
    have positive : 0 < W := W_pos
    have arithmetic : (index + 1) + (W - 1) = index + W := by omega
    rw [arithmetic,Nat.add_mod,Nat.mod_self,Nat.add_zero,Nat.mod_mod]
  have entry : run [.push w[1],.swap 1,.sub] (memoryRangeMachine machine (index + 1) 0 destination source) =
      .ok (memoryRangeMachine machine index 0 destination source) 0 := by
    have current : (wmod (index + 1)).val = index + 1 := Nat.mod_eq_of_lt bounded
    simp only [memoryRangeMachine,run,exec_cons_zero,Instr.step,Machine.next,Out.ok_bind,exec_nil,
      List.getElem?_cons_zero,List.set_cons_zero,List.cons_append,
      List.nil_append,current,decrement]
  have lower : index < W := by omega
  have observed : machine.mem ((index + source.val) % W) = word := by
    rw [Nat.add_comm index source.val,Nat.mod_eq_of_lt (show source.val + index < W by omega),selected]
  have payload : run (memoryReadRangeBody.take 8) (memoryRangeMachine machine index 0 destination source) =
      .ok (memoryRangeMachine (writeMachine machine (destination.val + index) word) index 0 destination source) 0 := by
    simp only [memoryReadRangeBody,List.take,run,exec_cons_zero,Instr.step,Machine.next,Out.ok_bind,exec_nil,
      memoryRangeMachine,List.getElem?_cons_zero,List.getElem?_cons_succ,List.cons_append,List.nil_append,Nat.reduceSub,
      wmod_def,Nat.zero_mod,Nat.mod_eq_of_lt lower,observed,Nat.add_comm,writeMachine]
    rw [Nat.mod_eq_of_lt (show index + destination.val < W by omega)]
  rw [backwardReadRangeBody,run_append_ok entry]
  exact payload

theorem backward_read_iter (count : Nat) (machine : Machine) (destination source : Fin W)
    (bounded : count < W) (room : destination.val + count ≤ W) (readable : source.val + count ≤ W)
    (ordered : source.val ≤ destination.val) :
    ∃ target,
      loopIterN (run backwardRangeCond) (run backwardReadRangeBody) (count + 1)
        (memoryRangeMachine machine count 0 destination source) =
        .inr (.ok (memoryRangeMachine target 0 0 destination source) 0) ∧
      target = {machine with mem := target.mem} ∧
      (∀ index, index < count → target.mem (destination.val + index) = machine.mem (source.val + index)) ∧
      (∀ address, address < destination.val ∨ destination.val + count ≤ address → target.mem address = machine.mem address) := by
  induction count generalizing machine with
  | zero =>
    refine ⟨machine,?_,rfl,?_,fun _ _ => rfl⟩
    · have condition : run backwardRangeCond (memoryRangeMachine machine 0 0 destination source) =
          .ok ((memoryRangeMachine machine 0 0 destination source).push w[0]) 0 := by
        simpa only [Nat.lt_irrefl,decide_false,bword] using backward_range_condition machine 0 destination source (by decide)
      rw [loopIterN,loopTurn,condition]
      rfl
    · intro index impossible
      omega
  | succ count ih =>
    let written := writeMachine machine (destination.val + count) (machine.mem (source.val + count))
    have condition : run backwardRangeCond (memoryRangeMachine machine (count + 1) 0 destination source) =
        .ok ((memoryRangeMachine machine (count + 1) 0 destination source).push w[1]) 0 := by
      simpa only [Nat.zero_lt_succ,decide_true,bword] using backward_range_condition machine (count + 1) destination source bounded
    have body : run backwardReadRangeBody (memoryRangeMachine machine (count + 1) 0 destination source) =
        .ok (memoryRangeMachine written count 0 destination source) 0 :=
      backward_read_turn machine count destination source bounded room readable _ rfl
    have turn : loopTurn (run backwardRangeCond) (run backwardReadRangeBody)
        (memoryRangeMachine machine (count + 1) 0 destination source) =
        .inl (memoryRangeMachine written count 0 destination source) := by
      rw [loopTurn,condition]
      change (if (1 : Nat) = 0 then _ else _) = _
      rw [if_neg (by decide)]
      simp only [Machine.push]
      rw [body]
    obtain ⟨target,iterations,shape,contents,outside⟩ := ih written (by omega) (by omega) (by omega)
    refine ⟨target,?_,?_,?_,?_⟩
    · rw [loopIterN,turn]
      exact iterations
    · rw [shape]
      rfl
    · intro index lower
      by_cases before : index < count
      · rw [contents index before]
        change upd machine.mem (destination.val + count) (machine.mem (source.val + count)) (source.val + index) = _
        exact upd_other _ _ (by omega)
      · have last : index = count := by omega
        subst index
        rw [outside (destination.val + count) (.inr (Nat.le_refl _))]
        exact upd_same _ _ _
    · intro address separate
      rw [outside address (by omega)]
      exact upd_other _ _ (by omega)

theorem backward_range_success (machine : Machine) (source destination : Fin W) (count : Nat)
    (bounded : count < W) (readable : source.val + count ≤ W) (room : destination.val + count ≤ W)
    (ordered : source.val ≤ destination.val) :
    ∃ target,
      run (backwardRangeCode count) ((machine.push (.val source)).push (.val destination)) = .ok target 0 ∧
      target = {machine with mem := target.mem} ∧
      (∀ index, index < count → target.mem (destination.val + index) = machine.mem (source.val + index)) ∧
      (∀ address, address < destination.val ∨ destination.val + count ≤ address → target.mem address = machine.mem address) := by
  obtain ⟨target,iterations,shape,contents,outside⟩ := backward_read_iter count machine destination source bounded room readable ordered
  have loop : loopRun (run backwardRangeCond) (run backwardReadRangeBody) (memoryRangeMachine machine count 0 destination source) =
      .ok (memoryRangeMachine target 0 0 destination source) 0 := loopRun_of_iterN iterations
  have single : run [.loop backwardRangeCond backwardReadRangeBody] (memoryRangeMachine machine count 0 destination source) =
      .ok (memoryRangeMachine target 0 0 destination source) 0 := by
    change (loopRun (run backwardRangeCond) (run backwardReadRangeBody) _).bind _ = _
    rw [loop]
    rfl
  have entered : run [.push w[0],.push (.val (wmod count))] ((machine.push (.val source)).push (.val destination)) =
      .ok (memoryRangeMachine machine count 0 destination source) 0 := by rfl
  refine ⟨target,?_,shape,contents,outside⟩
  change run ([.push w[0],.push (.val (wmod count))] ++ [.loop backwardRangeCond backwardReadRangeBody] ++ [.pop,.pop,.pop,.pop]) _ = _
  rw [List.append_assoc,run_append_ok entered,run_append_ok single]
  rfl

theorem overlap_conditional_run (condition left right : List Instr) (machine target : Machine) (choice : Bool)
    (tested : run condition machine = .ok (machine.push (.val (bword choice))) 0)
    (selected : run (if choice then left else right) machine = .ok target 0) :
    run (conditionalCode condition left right) machine = .ok target 0 := by
  simp only [conditionalCode,List.append_assoc]
  rw [run_append_ok tested]
  cases choice with
  | false =>
    change run right machine = .ok target 0 at selected
    rw [run_append_skip (m' := machine) (k := left.length + 1) rfl,exec_append,exec_skip]
    exact selected
  | true =>
    change run left machine = .ok target 0 at selected
    rw [run_append_ok (c₁ := [.iszero,.jumpi (left.length + 1)]) (m' := machine) rfl,run_append_ok selected,
      run_append_skip (c₁ := [.jump right.length]) (m' := target) (k := right.length) rfl,exec_length]

theorem range_direction_run (machine : Machine) (source destination : Fin W) :
    run rangeDirectionCode ((machine.push (.val source)).push (.val destination)) =
      .ok (((machine.push (.val source)).push (.val destination)).push (.val (bword (decide (source.val < destination.val))))) 0 := by
  simp only [rangeDirectionCode,run,exec_cons_zero,Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Nat.reduceSub]

theorem range_overlap_success (machine : Machine) (source destination : Fin W) (count : Nat)
    (bounded : count < W) (readable : source.val + count ≤ W) (room : destination.val + count ≤ W) :
    ∃ target,
      run (rangeOverlapCode count) ((machine.push (.val source)).push (.val destination)) = .ok target 0 ∧
      target = {machine with mem := target.mem} ∧
      (∀ index, index < count → target.mem (destination.val + index) = machine.mem (source.val + index)) ∧
      (∀ address, address < destination.val ∨ destination.val + count ≤ address → target.mem address = machine.mem address) := by
  by_cases less : source.val < destination.val
  · obtain ⟨target,ran,shape,contents,outside⟩ := backward_range_success machine source destination count bounded readable room (Nat.le_of_lt less)
    refine ⟨target,?_,shape,contents,outside⟩
    apply overlap_conditional_run rangeDirectionCode (backwardRangeCode count) (forwardRangeCode count) _ target true _ ran
    simpa only [less,decide_true] using range_direction_run machine source destination
  · obtain ⟨target,ran,shape,contents,outside⟩ := forward_range_success machine source destination count bounded readable room (.inl (by omega))
    refine ⟨target,?_,shape,contents,outside⟩
    apply overlap_conditional_run rangeDirectionCode (backwardRangeCode count) (forwardRangeCode count) _ target false _ ran
    simpa only [less,decide_false] using range_direction_run machine source destination

theorem range_overlap_list (xs : List Word) (machine : Machine) (source destination : Fin W) (count : Nat)
    (represented : ∀ index word, xs[index]? = some word → machine.mem index = word)
    (capacity : xs.length ≤ W) (bounded : count < W)
    (readable : source.val + count ≤ xs.length) (room : destination.val + count ≤ xs.length)
    :
    ∃ ys target,
      MemoryOps.checkedSnapshotCopy xs source.val count destination.val = some ys ∧
      run (rangeOverlapCode count) ((machine.push (.val source)).push (.val destination)) = .ok target 0 ∧
      (∀ index word, ys[index]? = some word → target.mem index = word) := by
  obtain ⟨ys,model,length,copied⟩ := MemoryOps.checkedSnapshotCopy_correct xs source.val count destination.val readable room
  obtain ⟨target,ran,_,contents,outside⟩ := range_overlap_success machine source destination count bounded
    (Nat.le_trans readable capacity) (Nat.le_trans room capacity)
  refine ⟨ys,target,model,ran,?_⟩
  intro index word selected
  by_cases inside : destination.val ≤ index ∧ index < destination.val + count
  · have offset : index - destination.val < count := by omega
    have position : destination.val + (index - destination.val) = index := by omega
    have sourceWord : xs[source.val + (index - destination.val)]? = some word := by
      rw [← copied (index - destination.val) offset,position]
      exact selected
    rw [← position,contents (index - destination.val) offset]
    exact represented _ _ sourceWord
  · have unchanged : ys[index]? = xs[index]? := by
      rw [MemoryOps.checkedSnapshotCopy,if_pos ⟨readable,room⟩] at model
      cases model
      have payloadLength : ((xs.drop source.val).take count).length = count := by
        rw [List.length_take,List.length_drop]
        exact Nat.min_eq_left (by omega)
      by_cases before : index < destination.val
      · exact MemoryOps.replaceSlice_before xs _ destination.val index (by rw [payloadLength]; exact room) before
      · exact MemoryOps.replaceSlice_after xs _ destination.val index (by rw [payloadLength]; exact room) (by rw [payloadLength]; omega)
    rw [outside index (by omega)]
    exact represented _ _ (unchanged ▸ selected)

def rangeOverlap : RangeOverlapCertificate := ⟨range_overlap_success,range_overlap_list⟩

#print axioms backward_range_condition
#print axioms backward_read_turn
#print axioms backward_read_iter
#print axioms backward_range_success
#print axioms overlap_conditional_run
#print axioms range_direction_run
#print axioms range_overlap_success
#print axioms range_overlap_list
#print axioms rangeOverlap
end Solidity.Backend.MemoryCopies
