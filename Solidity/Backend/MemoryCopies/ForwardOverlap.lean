import Solidity.Backend.MemoryCopies.ForwardOverlapInterface

/-! The shared forward loop preserves every unread source word in forward-safe
ranges. Its actual result agrees with the published checked snapshot model. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem forward_read_iter (words : List Word) (index count : Nat) (machine : Machine)
    (destination : Fin W) (source : Fin W) (remaining : index + words.length = count)
    (bounded : count < W) (room : destination.val + count ≤ W) (readable : source.val + count ≤ W) (ordered : ForwardReadable source destination count)
    (contents : ∀ (offset : Nat) (word : Word), words[offset]? = some word →
      machine.mem (source.val + (index + offset)) = word) :
    loopIterN (run copyRangeCond) (run memoryReadRangeBody) (words.length + 1)
      (memoryRangeMachine machine index count destination source) =
      .inr (.ok (memoryRangeMachine (arrayWordsMachine destination index words machine) count count destination source) 0) := by
  induction words generalizing index machine with
  | nil =>
    have equal : index = count := by simpa only [List.length_nil,Nat.add_zero] using remaining
    subst index
    have condition : run copyRangeCond (memoryRangeMachine machine count count destination source) =
        .ok ((memoryRangeMachine machine count count destination source).push w[0]) 0 := by
      simpa only [Nat.lt_irrefl,decide_false,bword] using memory_read_condition machine count count destination source bounded bounded
    rw [loopIterN,loopTurn,condition]
    rfl
  | cons word words ih =>
    have lower : index < count := by simp only [List.length_cons] at remaining; omega
    have condition : run copyRangeCond (memoryRangeMachine machine index count destination source) =
        .ok ((memoryRangeMachine machine index count destination source).push w[1]) 0 := by
      simpa only [lower,decide_true,bword] using memory_read_condition machine index count destination source (by omega) bounded
    have selected : machine.mem (source.val + index) = word := by
      simpa only [Nat.add_zero] using contents 0 word rfl
    have body : run memoryReadRangeBody (memoryRangeMachine machine index count destination source) =
        .ok (memoryRangeMachine (writeMachine machine (destination.val + index) word) (index + 1) count destination source) 0 :=
      memory_read_turn machine index count destination source (by omega) bounded (by omega) (by omega) word selected
    have turn : loopTurn (run copyRangeCond) (run memoryReadRangeBody)
        (memoryRangeMachine machine index count destination source) =
        .inl (memoryRangeMachine (writeMachine machine (destination.val + index) word) (index + 1) count destination source) := by
      rw [loopTurn,condition]
      change (if (1 : Nat) = 0 then _ else _) = _
      rw [if_neg (by decide)]
      simp only [Machine.push]
      rw [body]
    rw [List.length_cons,loopIterN,turn]
    exact ih (index + 1) (writeMachine machine (destination.val + index) word)
      (by simp only [List.length_cons] at remaining; omega)
      (fun offset selected chosen => by
        have offsetBound : offset < words.length := lt_of_getElem? chosen
        have different : source.val + (index + 1 + offset) ≠ destination.val + index := by
          rcases ordered with left | right
          · omega
          · simp only [List.length_cons] at remaining
            omega
        have actual : machine.mem (source.val + (index + (offset + 1))) = selected :=
          contents (offset + 1) selected chosen
        change upd machine.mem (destination.val + index) word (source.val + (index + 1 + offset)) = selected
        rw [upd_other _ _ different]
        simpa only [Nat.add_assoc,Nat.add_comm 1 offset] using actual)

theorem forward_read_loop (words : List Word) (machine : Machine) (destination : Fin W) (source : Fin W)
    (bounded : words.length < W) (room : destination.val + words.length ≤ W) (readable : source.val + words.length ≤ W) (ordered : ForwardReadable source destination words.length)
    (contents : ∀ (index : Nat) (word : Word), words[index]? = some word →
      machine.mem (source.val + index) = word) :
    run [.loop copyRangeCond memoryReadRangeBody] (memoryRangeMachine machine 0 words.length destination source) =
      .ok (memoryRangeMachine (arrayWordsMachine destination 0 words machine) words.length words.length destination source) 0 := by
  have iterations : loopIterN (run copyRangeCond) (run memoryReadRangeBody) (words.length + 1)
      (memoryRangeMachine machine 0 words.length destination source) =
      .inr (.ok (memoryRangeMachine (arrayWordsMachine destination 0 words machine) words.length words.length destination source) 0) :=
    forward_read_iter words 0 words.length machine destination source (Nat.zero_add _) bounded room readable ordered
      (fun index word chosen => by simpa only [Nat.zero_add] using contents index word chosen)
  have loop : loopRun (run copyRangeCond) (run memoryReadRangeBody)
      (memoryRangeMachine machine 0 words.length destination source) =
      .ok (memoryRangeMachine (arrayWordsMachine destination 0 words machine) words.length words.length destination source) 0 :=
    loopRun_of_iterN iterations
  change (loopRun (run copyRangeCond) (run memoryReadRangeBody) _).bind _ = _
  rw [loop]
  rfl


theorem forward_range_run (machine : Machine) (source destination : Fin W) (count : Nat)
    (bounded : count < W) (readable : source.val + count ≤ W) (room : destination.val + count ≤ W)
    (ordered : ForwardReadable source destination count) :
    run (forwardRangeCode count) ((machine.push (.val source)).push (.val destination)) =
      .ok (arrayWordsMachine destination 0 (fixedMemoryWords machine source count) machine) 0 := by
  let words := fixedMemoryWords machine source count
  have sized : words.length = count := List.length_ofFn
  have contents : ∀ index word, words[index]? = some word → machine.mem (source.val + index) = word := by
    intro index word selected
    have lower : index < count := by
      have actual : index < words.length := lt_of_getElem? selected
      rw [sized] at actual
      exact actual
    simp only [words,fixedMemoryWords,List.getElem?_ofFn,dif_pos lower] at selected
    exact Option.some.inj selected
  have loop : run [.loop copyRangeCond memoryReadRangeBody]
      (memoryRangeMachine machine 0 count destination source) =
      .ok (memoryRangeMachine (arrayWordsMachine destination 0 words machine) count count destination source) 0 := by
    simpa only [sized] using forward_read_loop words machine destination source
      (by rw [sized]; exact bounded) (by rw [sized]; exact room)
      (by rw [sized]; exact readable) (by rw [sized]; exact ordered) contents
  change run ([.push (.val (wmod count)),.push w[0]] ++
    [.loop copyRangeCond memoryReadRangeBody] ++ [.pop,.pop,.pop,.pop]) _ = _
  have entered : run [.push (.val (wmod count)),.push w[0]] ((machine.push (.val source)).push (.val destination)) =
      .ok (memoryRangeMachine machine 0 count destination source) 0 := by rfl
  rw [List.append_assoc,run_append_ok entered,run_append_ok loop]
  rfl

theorem forward_range_success (machine : Machine) (source destination : Fin W) (count : Nat)
    (bounded : count < W) (readable : source.val + count ≤ W) (room : destination.val + count ≤ W)
    (ordered : ForwardReadable source destination count) :
    ∃ target,
      run (forwardRangeCode count) ((machine.push (.val source)).push (.val destination)) = .ok target 0 ∧
      target = {machine with mem := target.mem} ∧
      (∀ index, index < count → target.mem (destination.val + index) = machine.mem (source.val + index)) ∧
      (∀ address, address < destination.val ∨ destination.val + count ≤ address → target.mem address = machine.mem address) := by
  let words := fixedMemoryWords machine source count
  refine ⟨arrayWordsMachine destination 0 words machine,forward_range_run machine source destination count bounded readable room ordered,
    array_words_shape destination 0 words machine,?_,?_⟩
  · intro index lower
    exact array_words_selected destination 0 words machine index (machine.mem (source.val + index)) (by
      simp only [words,fixedMemoryWords,List.getElem?_ofFn,dif_pos lower])
  · intro address outside
    apply array_words_other destination 0 words machine address
    simpa only [Nat.add_zero,words,fixedMemoryWords,List.length_ofFn] using outside

theorem forward_range_list (xs : List Word) (machine : Machine) (source destination : Fin W) (count : Nat)
    (represented : ∀ index word, xs[index]? = some word → machine.mem index = word)
    (capacity : xs.length ≤ W) (bounded : count < W)
    (readable : source.val + count ≤ xs.length) (room : destination.val + count ≤ xs.length)
    (ordered : ForwardReadable source destination count) :
    ∃ ys target,
      MemoryOps.checkedSnapshotCopy xs source.val count destination.val = some ys ∧
      run (forwardRangeCode count) ((machine.push (.val source)).push (.val destination)) = .ok target 0 ∧
      (∀ index word, ys[index]? = some word → target.mem index = word) := by
  obtain ⟨ys,model,length,copied⟩ := MemoryOps.checkedSnapshotCopy_correct xs source.val count destination.val readable room
  obtain ⟨target,ran,_,contents,outside⟩ := forward_range_success machine source destination count bounded
    (Nat.le_trans readable capacity) (Nat.le_trans room capacity) ordered
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

def forwardOverlap : ForwardOverlapCertificate := ⟨forward_range_success,forward_range_list⟩

#print axioms forward_read_iter
#print axioms forward_read_loop
#print axioms forward_range_run
#print axioms forward_range_success
#print axioms forward_range_list
#print axioms forwardOverlap
end Solidity.Backend.MemoryCopies
