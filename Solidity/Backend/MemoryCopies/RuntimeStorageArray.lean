import Solidity.Backend.MemoryCopies.RuntimeStorageArrayInterface

/-! Runtime word traversal uses the published loop controller and writes the
same arrayWordsMachine whose complete ownership is already proved. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem storage_read_turn (machine : Machine) (index count : Nat) (destination : Fin W) (source : Slot)
    (next : index + 1 < W) (bounded : count < W) (room : destination.val + index < W)
    (word : Word) (selected : .val (machine.store.cells (source.add index)) = word) :
    run storageReadRangeBody (rangeMachine machine index count destination source) =
      .ok (rangeMachine (writeMachine machine (destination.val + index) word) (index + 1) count destination source) 0 := by
  have lower : index < W := by omega
  simp only [storageReadRangeBody,rangeMachine,run,exec_cons_zero,List.cons_append,List.nil_append,Nat.reduceSub,
    List.getElem?_cons_zero,List.getElem?_cons_succ,Instr.step,Machine.next,Out.ok_bind,exec_nil,
    wmod_def,Nat.mod_eq_of_lt lower,Nat.mod_eq_of_lt bounded,Nat.mod_eq_of_lt next,selected,
    Nat.add_comm,writeMachine]
  rw [Nat.mod_eq_of_lt (show index + destination.val < W by omega)]

theorem storage_read_iter (words : List Word) (index count : Nat) (machine : Machine)
    (destination : Fin W) (source : Slot) (remaining : index + words.length = count)
    (bounded : count < W) (room : destination.val + count ≤ W)
    (contents : ∀ (offset : Nat) (word : Word), words[offset]? = some word →
      .val (machine.store.cells (source.add (index + offset))) = word) :
    loopIterN (run copyRangeCond) (run storageReadRangeBody) (words.length + 1)
      (rangeMachine machine index count destination source) =
      .inr (.ok (rangeMachine (arrayWordsMachine destination index words machine) count count destination source) 0) := by
  induction words generalizing index machine with
  | nil =>
    have equal : index = count := by simpa only [List.length_nil,Nat.add_zero] using remaining
    subst index
    have condition : run copyRangeCond (rangeMachine machine count count destination source) =
        .ok ((rangeMachine machine count count destination source).push w[0]) 0 := by
      simpa only [Nat.lt_irrefl,decide_false,bword] using copyRangeCond_run machine count count destination source bounded bounded
    rw [loopIterN,loopTurn,condition]
    rfl
  | cons word words ih =>
    have lower : index < count := by simp only [List.length_cons] at remaining; omega
    have condition : run copyRangeCond (rangeMachine machine index count destination source) =
        .ok ((rangeMachine machine index count destination source).push w[1]) 0 := by
      simpa only [lower,decide_true,bword] using copyRangeCond_run machine index count destination source (by omega) bounded
    have selected : .val (machine.store.cells (source.add index)) = word := by
      simpa only [Nat.add_zero] using contents 0 word rfl
    have body : run storageReadRangeBody (rangeMachine machine index count destination source) =
        .ok (rangeMachine (writeMachine machine (destination.val + index) word) (index + 1) count destination source) 0 :=
      storage_read_turn machine index count destination source (by omega) bounded (by omega) word selected
    have turn : loopTurn (run copyRangeCond) (run storageReadRangeBody)
        (rangeMachine machine index count destination source) =
        .inl (rangeMachine (writeMachine machine (destination.val + index) word) (index + 1) count destination source) := by
      rw [loopTurn,condition]
      change (if (1 : Nat) = 0 then _ else _) = _
      rw [if_neg (by decide)]
      simp only [Machine.push]
      rw [body]
    rw [List.length_cons,loopIterN,turn]
    exact ih (index + 1) (writeMachine machine (destination.val + index) word)
      (by simp only [List.length_cons] at remaining; omega)
      (fun offset selected chosen => by
        have actual : .val (machine.store.cells (source.add (index + (offset + 1)))) = selected :=
          contents (offset + 1) selected chosen
        simpa only [Nat.add_assoc,Nat.add_comm 1 offset] using actual)

theorem storage_read_loop (words : List Word) (machine : Machine) (destination : Fin W) (source : Slot)
    (bounded : words.length < W) (room : destination.val + words.length ≤ W)
    (contents : ∀ (index : Nat) (word : Word), words[index]? = some word →
      .val (machine.store.cells (source.add index)) = word) :
    run [.loop copyRangeCond storageReadRangeBody] (rangeMachine machine 0 words.length destination source) =
      .ok (rangeMachine (arrayWordsMachine destination 0 words machine) words.length words.length destination source) 0 := by
  have iterations : loopIterN (run copyRangeCond) (run storageReadRangeBody) (words.length + 1)
      (rangeMachine machine 0 words.length destination source) =
      .inr (.ok (rangeMachine (arrayWordsMachine destination 0 words machine) words.length words.length destination source) 0) :=
    storage_read_iter words 0 words.length machine destination source (Nat.zero_add _) bounded room
      (fun index word chosen => by simpa only [Nat.zero_add] using contents index word chosen)
  have loop : loopRun (run copyRangeCond) (run storageReadRangeBody)
      (rangeMachine machine 0 words.length destination source) =
      .ok (rangeMachine (arrayWordsMachine destination 0 words machine) words.length words.length destination source) 0 :=
    loopRun_of_iterN iterations
  change (loopRun (run copyRangeCond) (run storageReadRangeBody) _).bind _ = _
  rw [loop]
  rfl

theorem array_words_stack (cursor : Fin W) (offset : Nat) (words : List Word) (machine : Machine) (word : Word) :
    arrayWordsMachine cursor offset words (machine.push word) = (arrayWordsMachine cursor offset words machine).push word := by
  induction words generalizing offset machine with
  | nil => rfl
  | cons first words ih => exact ih (offset + 1) (writeMachine machine (cursor.val + offset) first)

theorem array_words_offset (left right : Fin W) (offset start : Nat) (words : List Word) (machine : Machine)
    (same : left.val + offset = right.val + start) :
    arrayWordsMachine left offset words machine = arrayWordsMachine right start words machine := by
  induction words generalizing offset start machine with
  | nil => rfl
  | cons word words ih =>
    rw [arrayWordsMachine,arrayWordsMachine,same]
    exact ih (offset + 1) (start + 1) _ (by omega)

theorem storage_read_enter (machine : Machine) (cursor size : Fin W) (source : Slot)
    (cell : machine.mem 0 = .val cursor) (header : machine.store.cells source = size) :
    run storageReadEnter (machine.push (.slot source)) =
      .ok (rangeMachine ((allocateMachine machine cursor size).push (.val cursor)) 0 size.val
        (wmod (cursor.val + 1)) (.data source 0)) 0 := by
  have prefixRun : run [.dup 1,.sload,.swap 1,.keccakArr,.swap 1,.dup 1] (machine.push (.slot source)) =
      .ok (({machine with stack := .val size :: .slot (.data source 0) :: machine.stack}).push (.val size)) 0 := by
    simp only [run,exec_cons_zero,Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,header,
      List.getElem?_cons_zero,List.set_cons_zero,Nat.reduceSub]
  rw [storageReadEnter,List.append_assoc,run_append_ok prefixRun,
    run_append_ok (allocateArray_run {machine with stack := .val size :: .slot (.data source 0) :: machine.stack} cursor size cell)]
  simp only [run,exec_cons_zero,Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,rangeMachine,
    List.getElem?_cons_zero,List.getElem?_cons_succ,List.set_cons_zero,Nat.reduceSub,List.cons_append,List.nil_append,
    allocateMachine,writeMachine,List.set_cons_succ,wmod_def,Nat.zero_mod,Nat.mod_eq_of_lt size.isLt,Nat.add_comm]

theorem runtime_storage_array_run (machine : Machine) (cursor : Fin W) (source : Slot) (words : List Word)
    (bounded : words.length < W) (cell : machine.mem 0 = .val cursor)
    (header : machine.store.cells source = ⟨words.length,bounded⟩)
    (contents : ∀ (index : Nat) (word : Word), words[index]? = some word →
      .val (machine.store.cells ((Slot.data source 0).add index)) = word)
    (fits : cursor.val + words.length + 1 < W) :
    run runtimeStorageArrayCode (machine.push (.slot source)) =
      .ok ((arrayWordsMachine cursor 1 words (allocateMachine machine cursor ⟨words.length,bounded⟩)).push (.val cursor)) 0 := by
  let payload : Fin W := wmod (cursor.val + 1)
  let allocated := allocateMachine machine cursor ⟨words.length,bounded⟩
  have payloadValue : payload.val = cursor.val + 1 := Nat.mod_eq_of_lt (by omega)
  have loop : run [.loop copyRangeCond storageReadRangeBody]
      (rangeMachine (allocated.push (.val cursor)) 0 words.length payload (.data source 0)) =
      .ok (rangeMachine (arrayWordsMachine payload 0 words (allocated.push (.val cursor)))
        words.length words.length payload (.data source 0)) 0 :=
    storage_read_loop words (allocated.push (.val cursor)) payload (.data source 0) bounded
      (by rw [payloadValue]; omega) contents
  rw [runtimeStorageArrayCode,List.append_assoc,
    run_append_ok (storage_read_enter machine cursor ⟨words.length,bounded⟩ source cell header),run_append_ok loop]
  change Out.ok (arrayWordsMachine payload 0 words (allocated.push (.val cursor))) 0 = _
  rw [array_words_stack,array_words_offset payload cursor 0 1 words allocated (by simpa only [Nat.add_zero] using payloadValue)]

theorem runtime_storage_array_transport (machine : Machine) (cursor : Fin W) (source : Slot) (words : List Word)
    (bounded : words.length < W) (cell : machine.mem 0 = .val cursor)
    (header : machine.store.cells source = ⟨words.length,bounded⟩)
    (contents : ∀ (index : Nat) (word : Word), words[index]? = some word →
      .val (machine.store.cells ((Slot.data source 0).add index)) = word)
    (fits : cursor.val + words.length + 1 < W) :
    run runtimeStorageArrayCode (machine.push (.slot source)) = run (primitiveArrayCode words) machine := by
  rw [runtime_storage_array_run machine cursor source words bounded cell header contents fits,
    primitive_array_run words machine cursor bounded cell fits]

def storageArrayWords (machine : Machine) (source : Slot) (count : Nat) : List Word :=
  List.ofFn (fun index : Fin count => .val (machine.store.cells (.data source index.val)))

theorem storage_array_words (primitive : PrimTy) (values : List primitive.Denote) (bounded : values.length < W)
    (machine : Machine) (source : Slot) (L : Nat)
    (represented : ReprAt machine.store L (.ref (.array (.prim primitive))) source (primitiveArrayValue primitive values bounded)) :
    machine.store.cells source = wmod values.length ∧
    PrimitiveWords primitive values (storageArrayWords machine source values.length) ∧
    (∀ (index : Nat) (word : Word), (storageArrayWords machine source values.length)[index]? = some word →
      .val (machine.store.cells ((Slot.data source 0).add index)) = word) := by
  cases represented with
  | array header range elements =>
    refine ⟨?_,⟨List.length_ofFn ..,?_⟩,?_⟩
    · apply Fin.ext
      have actual : (machine.store.cells source).val = values.length := by
        simpa only [List.length_map] using header
      exact actual.trans (Nat.mod_eq_of_lt bounded).symm
    · intro index value selected
      have lower : index < values.length := lt_of_getElem? selected
      refine ⟨.val (machine.store.cells (.data source index)),?_,?_⟩
      · simp only [storageArrayWords,List.getElem?_ofFn,dif_pos lower]
      · have stored : ReprAt machine.store L (.prim primitive) (.data source (index * size (.prim primitive))) (.prim value) :=
          elements index (.prim value) (by simp only [SVec.toList_ofList,List.getElem?_map,selected,Option.map_some])
        cases stored with
        | prim representation => simpa only [size_prim,Nat.mul_one] using representation
    · intro index word selected
      have lower : index < values.length := by
        have valid : index < (storageArrayWords machine source values.length).length := lt_of_getElem? selected
        simpa only [storageArrayWords,List.length_ofFn] using valid
      simp only [storageArrayWords,List.getElem?_ofFn,dif_pos lower] at selected
      cases selected
      simp only [Slot.add,Nat.zero_add]

theorem runtime_storage_array_success {H : HTy} (heap : Heap H) (primitive : PrimTy) (values : List primitive.Denote)
    (bounded : values.length < W) (base : Nat → Fin W) (frame : Nat) (cursor : Fin W)
    (machine : Machine) (source : Slot) (L : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store L (.ref (.array (.prim primitive))) source (primitiveArrayValue primitive values bounded))
    (fits : cursor.val + (values.length + 1) < W) :
    let grown := (primitiveArrayValue primitive values bounded).copyStToM heap rfl
    ∃ base' target,
      run runtimeStorageArrayCode (machine.push (.slot source)) = .ok (target.push (.val cursor)) 0 ∧
      Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + (values.length + 1),fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
      target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) := by
  obtain ⟨header,representation,contents⟩ := storage_array_words primitive values bounded machine source L represented
  obtain ⟨base',target,ran,reached,root,extension,shape,below,gaps⟩ :=
    primitive_array_result heap primitive values bounded _ representation base frame cursor machine allocator fits
  have wordBound : (storageArrayWords machine source values.length).length < W := by
    rw [representation.length]
    exact bounded
  have wordHeader : machine.store.cells source = ⟨(storageArrayWords machine source values.length).length,wordBound⟩ := by
    rw [header]
    apply Fin.ext
    simp only [wmod_def,Nat.mod_eq_of_lt bounded,representation.length]
  refine ⟨base',target,?_,reached,root,extension,shape,below,gaps⟩
  rw [runtime_storage_array_transport machine cursor source _ wordBound allocator.free.cell wordHeader contents
    (by rw [representation.length]; omega)]
  exact ran

def runtimeStorageArray : RuntimeStorageArrayCertificate := ⟨runtime_storage_array_success⟩

#print axioms storage_read_turn
#print axioms storage_read_iter
#print axioms storage_read_loop
#print axioms array_words_stack
#print axioms array_words_offset
#print axioms storage_read_enter
#print axioms runtime_storage_array_run
#print axioms runtime_storage_array_transport
#print axioms storage_array_words
#print axioms runtime_storage_array_success
#print axioms runtimeStorageArray
end Solidity.Backend.MemoryCopies
