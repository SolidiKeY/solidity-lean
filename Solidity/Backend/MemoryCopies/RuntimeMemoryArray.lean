import Solidity.Backend.MemoryCopies.RuntimeMemoryArrayInterface

/-! Runtime memory reads populate the already-proved fresh primitive object.
Complete ownership derives read/write separation and preserves all old objects. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem memory_read_condition (machine : Machine) (index count : Nat) (destination source : Fin W)
    (lower : index < W) (bounded : count < W) :
    run copyRangeCond (memoryRangeMachine machine index count destination source) =
      .ok ((memoryRangeMachine machine index count destination source).push (.val (bword (decide (index < count))))) 0 := by
  simp only [copyRangeCond,memoryRangeMachine,run,exec_cons_zero,List.cons_append,List.nil_append,Nat.reduceSub,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Instr.step,Machine.next,Machine.push,Out.ok_bind,exec_nil,
    wmod_def,Nat.mod_eq_of_lt lower,Nat.mod_eq_of_lt bounded]

theorem memory_read_turn (machine : Machine) (index count : Nat) (destination source : Fin W)
    (next : index + 1 < W) (bounded : count < W) (room : destination.val + index < W)
    (readable : source.val + index < W) (word : Word) (selected : machine.mem (source.val + index) = word) :
    run memoryReadRangeBody (memoryRangeMachine machine index count destination source) =
      .ok (memoryRangeMachine (writeMachine machine (destination.val + index) word) (index + 1) count destination source) 0 := by
  have lower : index < W := by omega
  have observed : machine.mem ((index + source.val) % W) = word := by
    rw [Nat.add_comm index source.val,Nat.mod_eq_of_lt readable,selected]
  simp only [memoryReadRangeBody,memoryRangeMachine,run,exec_cons_zero,List.cons_append,List.nil_append,Nat.reduceSub,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Instr.step,Machine.next,Out.ok_bind,exec_nil,
    wmod_def,Nat.mod_eq_of_lt lower,Nat.mod_eq_of_lt bounded,Nat.mod_eq_of_lt next,observed,
    Nat.add_comm,writeMachine]
  rw [Nat.mod_eq_of_lt (show index + destination.val < W by omega)]

theorem memory_read_iter (words : List Word) (index count : Nat) (machine : Machine)
    (destination : Fin W) (source : Fin W) (remaining : index + words.length = count)
    (bounded : count < W) (room : destination.val + count ≤ W) (separated : source.val + count ≤ destination.val)
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
        have before : source.val + (index + 1 + offset) < destination.val + index := by
          simp only [List.length_cons] at remaining
          omega
        have actual : machine.mem (source.val + (index + (offset + 1))) = selected :=
          contents (offset + 1) selected chosen
        change upd machine.mem (destination.val + index) word (source.val + (index + 1 + offset)) = selected
        rw [upd_other _ _ (by omega)]
        simpa only [Nat.add_assoc,Nat.add_comm 1 offset] using actual)

theorem memory_read_loop (words : List Word) (machine : Machine) (destination : Fin W) (source : Fin W)
    (bounded : words.length < W) (room : destination.val + words.length ≤ W) (separated : source.val + words.length ≤ destination.val)
    (contents : ∀ (index : Nat) (word : Word), words[index]? = some word →
      machine.mem (source.val + index) = word) :
    run [.loop copyRangeCond memoryReadRangeBody] (memoryRangeMachine machine 0 words.length destination source) =
      .ok (memoryRangeMachine (arrayWordsMachine destination 0 words machine) words.length words.length destination source) 0 := by
  have iterations : loopIterN (run copyRangeCond) (run memoryReadRangeBody) (words.length + 1)
      (memoryRangeMachine machine 0 words.length destination source) =
      .inr (.ok (memoryRangeMachine (arrayWordsMachine destination 0 words machine) words.length words.length destination source) 0) :=
    memory_read_iter words 0 words.length machine destination source (Nat.zero_add _) bounded room separated
      (fun index word chosen => by simpa only [Nat.zero_add] using contents index word chosen)
  have loop : loopRun (run copyRangeCond) (run memoryReadRangeBody)
      (memoryRangeMachine machine 0 words.length destination source) =
      .ok (memoryRangeMachine (arrayWordsMachine destination 0 words machine) words.length words.length destination source) 0 :=
    loopRun_of_iterN iterations
  change (loopRun (run copyRangeCond) (run memoryReadRangeBody) _).bind _ = _
  rw [loop]
  rfl

theorem memory_read_enter (machine : Machine) (cursor size source : Fin W)
    (cell : machine.mem 0 = .val cursor) (header : machine.mem source.val = .val size) :
    run memoryReadEnter (machine.push (.val source)) =
      .ok (memoryRangeMachine ((allocateMachine machine cursor size).push (.val cursor)) 0 size.val
        (wmod (cursor.val + 1)) (wmod (source.val + 1))) 0 := by
  have prefixRun : run [.dup 1,.mloadAt,.swap 1,.push w[1],.add,.swap 1,.dup 1] (machine.push (.val source)) =
      .ok (({machine with stack := .val size :: .val (wmod (source.val + 1)) :: machine.stack}).push (.val size)) 0 := by
    simp only [run,exec_cons_zero,Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,header,
      List.getElem?_cons_zero,List.set_cons_zero,Nat.reduceSub,Nat.add_comm]
  rw [memoryReadEnter,List.append_assoc,run_append_ok prefixRun,
    run_append_ok (allocateArray_run {machine with stack := .val size :: .val (wmod (source.val + 1)) :: machine.stack} cursor size cell)]
  simp only [run,exec_cons_zero,Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,memoryRangeMachine,
    List.getElem?_cons_zero,List.getElem?_cons_succ,List.set_cons_zero,Nat.reduceSub,List.cons_append,List.nil_append,
    allocateMachine,writeMachine,List.set_cons_succ,wmod_def,Nat.zero_mod,Nat.mod_eq_of_lt size.isLt,Nat.add_comm]

theorem runtime_memory_array_run (machine : Machine) (cursor source : Fin W) (words : List Word)
    (bounded : words.length < W) (cell : machine.mem 0 = .val cursor)
    (header : machine.mem source.val = .val ⟨words.length,bounded⟩)
    (positive : 0 < source.val) (sourceRoom : source.val + 1 + words.length ≤ cursor.val)
    (contents : ∀ (index : Nat) (word : Word), words[index]? = some word →
      machine.mem (source.val + 1 + index) = word)
    (fits : cursor.val + words.length + 1 < W) :
    run runtimeMemoryArrayCode (machine.push (.val source)) =
      .ok ((arrayWordsMachine cursor 1 words (allocateMachine machine cursor ⟨words.length,bounded⟩)).push (.val cursor)) 0 := by
  let payload : Fin W := wmod (cursor.val + 1)
  let input : Fin W := wmod (source.val + 1)
  let allocated := allocateMachine machine cursor ⟨words.length,bounded⟩
  have payloadValue : payload.val = cursor.val + 1 := Nat.mod_eq_of_lt (by omega)
  have inputValue : input.val = source.val + 1 := Nat.mod_eq_of_lt (by omega)
  have loop : run [.loop copyRangeCond memoryReadRangeBody]
      (memoryRangeMachine (allocated.push (.val cursor)) 0 words.length payload input) =
      .ok (memoryRangeMachine (arrayWordsMachine payload 0 words (allocated.push (.val cursor)))
        words.length words.length payload input) 0 := by
    apply memory_read_loop words (allocated.push (.val cursor)) payload input bounded
      (by rw [payloadValue]; omega) (by rw [payloadValue,inputValue]; omega)
    intro index word chosen
    have lower : index < words.length := lt_of_getElem? chosen
    change allocated.mem (input.val + index) = word
    rw [inputValue,allocateMachine_other machine cursor ⟨words.length,bounded⟩ _ (by omega) (by omega)]
    exact contents index word chosen
  rw [runtimeMemoryArrayCode,List.append_assoc,
    run_append_ok (memory_read_enter machine cursor ⟨words.length,bounded⟩ source cell header),run_append_ok loop]
  change Out.ok (arrayWordsMachine payload 0 words (allocated.push (.val cursor))) 0 = _
  rw [array_words_stack,array_words_offset payload cursor 0 1 words allocated (by simpa only [Nat.add_zero] using payloadValue)]

theorem runtime_memory_array_transport (machine : Machine) (cursor source : Fin W) (words : List Word)
    (bounded : words.length < W) (cell : machine.mem 0 = .val cursor)
    (header : machine.mem source.val = .val ⟨words.length,bounded⟩)
    (positive : 0 < source.val) (sourceRoom : source.val + 1 + words.length ≤ cursor.val)
    (contents : ∀ (index : Nat) (word : Word), words[index]? = some word →
      machine.mem (source.val + 1 + index) = word)
    (fits : cursor.val + words.length + 1 < W) :
    run runtimeMemoryArrayCode (machine.push (.val source)) = run (primitiveArrayCode words) machine := by
  rw [runtime_memory_array_run machine cursor source words bounded cell header positive sourceRoom contents fits,
    primitive_array_run words machine cursor bounded cell fits]

def memoryArrayWords (machine : Machine) (source : Fin W) (count : Nat) : List Word :=
  List.ofFn (fun index : Fin count => machine.mem (source.val + 1 + index.val))

theorem memory_array_words {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (input : HRef H (.array (.prim primitive))) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    PrimitiveWords primitive (MObj.elems .dyn (heap.get input)) (memoryArrayWords machine (base input.id) (heap.len input .dyn)) ∧
    (∀ (index : Nat) (word : Word), (memoryArrayWords machine (base input.id) (heap.len input .dyn))[index]? = some word →
      machine.mem ((base input.id).val + 1 + index) = word) := by
  constructor
  · refine ⟨List.length_ofFn ..,?_⟩
    intro index value selected
    have lower : index < heap.len input .dyn := lt_of_getElem? selected
    refine ⟨machine.mem ((base input.id).val + 1 + index),?_,?_⟩
    · simp only [memoryArrayWords,List.getElem?_ofFn,dif_pos lower]
    · exact (allocator.heap.arrays .dyn input).elements index value selected
  · intro index word selected
    have lower : index < heap.len input .dyn := by
      have valid : index < (memoryArrayWords machine (base input.id) (heap.len input .dyn)).length := lt_of_getElem? selected
      simpa only [memoryArrayWords,List.length_ofFn] using valid
    simp only [memoryArrayWords,List.getElem?_ofFn,dif_pos lower] at selected
    exact Option.some.inj selected

theorem runtime_memory_array_success {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (input : HRef H (.array (.prim primitive))) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (fits : cursor.val + (heap.len input .dyn + 1) < W) :
    let grown := (MVal.copyMToSt heap (T := .ref (.array (.prim primitive))) input).copyStToM heap rfl
    ∃ base' target,
      run runtimeMemoryArrayCode (machine.push (.val (base input.id))) = .ok (target.push (.val cursor)) 0 ∧
      Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + (heap.len input .dyn + 1),fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends H base base' ∧ target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
      Heap.Keeps grown.ext heap grown.heap ∧ input.id < grown.val.id := by
  rw [primitiveArray_snapshot]
  obtain ⟨representation,contents⟩ := memory_array_words heap primitive input base frame cursor machine allocator
  obtain ⟨base',target,ran,reached,root,extension,shape,below,gaps⟩ :=
    primitive_array_result heap primitive (MObj.elems .dyn (heap.get input)) (heap.len_dyn_lt input)
      _ representation base frame cursor machine allocator fits
  have wordBound : (memoryArrayWords machine (base input.id) (heap.len input .dyn)).length < W := by
    rw [representation.length]
    exact heap.len_dyn_lt input
  have header : machine.mem (base input.id).val = .val ⟨(memoryArrayWords machine (base input.id) (heap.len input .dyn)).length,wordBound⟩ := by
    rw [(allocator.heap.arrays .dyn input).length rfl]
    apply congrArg Word.val
    apply Fin.ext
    change heap.len input .dyn % W = _
    exact (Nat.mod_eq_of_lt (heap.len_dyn_lt input)).trans representation.length.symm
  have oldRoom : (base input.id).val + 1 + heap.len input .dyn ≤ cursor.val := by
    have live : (base input.id).val + Objects.cells heap input ≤ cursor.val := allocator.live input
    simpa only [Objects.cells,Nat.add_assoc,Nat.add_comm 1 (heap.len input .dyn)] using live
  have positive : 0 < (base input.id).val := Nat.lt_of_lt_of_le allocator.free.reserved (allocator.heap.owner.above input)
  refine ⟨base',target,?_,reached,root,extension,shape,below,gaps,SVal.keeps_copyStToM _ rfl heap,?_⟩
  · rw [runtime_memory_array_transport machine cursor (base input.id) _ wordBound allocator.free.cell header positive
      (by rw [representation.length]; exact oldRoom) contents (by rw [representation.length]; change cursor.val + heap.len input .dyn + 1 < W; omega)]
    exact ran
  · exact Nat.lt_of_lt_of_le input.id_lt (SVal.copyStToM_id_ge heap _ rfl)

def runtimeMemoryArray : RuntimeMemoryArrayCertificate := ⟨runtime_memory_array_success⟩

#print axioms memory_read_condition
#print axioms memory_read_turn
#print axioms memory_read_iter
#print axioms memory_read_loop
#print axioms memory_read_enter
#print axioms runtime_memory_array_run
#print axioms runtime_memory_array_transport
#print axioms memory_array_words
#print axioms runtime_memory_array_success
#print axioms runtimeMemoryArray
end Solidity.Backend.MemoryCopies
