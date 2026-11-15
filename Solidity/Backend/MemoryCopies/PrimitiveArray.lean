import Solidity.Backend.MemoryCopies.PrimitiveArrayInterface

/-! Populate arbitrary finite primitive payloads inside an existing reservation,
then adopt the represented source object through the published ownership API. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem primitive_array_source {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (values : List primitive.Denote) (bounded : values.length < W) :
    (primitiveArrayValue primitive values bounded).copyStToM heap rfl =
      Grown.alloc ⟨List.prefix_refl H,heap,primitiveArrayObject primitive values bounded⟩ := by
  rw [primitiveArrayValue,SVal.copyStToM_array,SVec.copyStToM_prims]
  rfl

theorem array_words_shape (cursor : Fin W) (offset : Nat) (words : List Word) (machine : Machine) :
    arrayWordsMachine cursor offset words machine =
      {machine with mem := (arrayWordsMachine cursor offset words machine).mem} := by
  induction words generalizing offset machine with
  | nil => rfl
  | cons word words ih =>
    rw [arrayWordsMachine,ih]
    rfl

theorem array_words_other (cursor : Fin W) (offset : Nat) (words : List Word)
    (machine : Machine) (address : Nat)
    (outside : address < cursor.val + offset ∨ cursor.val + offset + words.length ≤ address) :
    (arrayWordsMachine cursor offset words machine).mem address = machine.mem address := by
  induction words generalizing offset machine with
  | nil => rfl
  | cons word words ih =>
    rw [arrayWordsMachine,ih (offset + 1) (writeMachine machine (cursor.val + offset) word) (by
      simp only [List.length_cons] at outside
      omega)]
    exact upd_other _ _ (by simp only [List.length_cons] at outside; omega)

theorem array_words_selected (cursor : Fin W) (offset : Nat) (words : List Word)
    (machine : Machine) (index : Nat) (word : Word) (selected : words[index]? = some word) :
    (arrayWordsMachine cursor offset words machine).mem (cursor.val + offset + index) = word := by
  induction words generalizing offset machine index with
  | nil => cases selected
  | cons first words ih =>
    cases index with
    | zero =>
      cases selected
      rw [arrayWordsMachine,array_words_other cursor (offset + 1) words _ _ (Or.inl (by omega))]
      exact upd_same _ _ _
    | succ index =>
      change words[index]? = some word at selected
      have inner : (arrayWordsMachine cursor (offset + 1) words
          (writeMachine machine (cursor.val + offset) first)).mem (cursor.val + (offset + 1) + index) = word := ih (offset + 1) (writeMachine machine (cursor.val + offset) first) index selected
      simpa only [Nat.add_assoc,Nat.add_comm 1 index] using inner

theorem array_words_run (cursor : Fin W) (offset : Nat) (words : List Word) (machine : Machine)
    (fits : cursor.val + offset + words.length ≤ W) :
    run (arrayWordsCode offset words) (machine.push (.val cursor)) =
      .ok ((arrayWordsMachine cursor offset words machine).push (.val cursor)) 0 := by
  induction words generalizing offset machine with
  | nil => rfl
  | cons word words ih =>
    have pushed : run [.push word,.dup 2] (machine.push (.val cursor)) =
        .ok (((machine.push (.val cursor)).push word).push (.val cursor)) 0 := rfl
    rw [arrayWordsCode,List.append_assoc,run_append_ok pushed,
      run_append_ok (writeFieldWord_run (machine.push (.val cursor)) cursor offset word (by
        simp only [List.length_cons] at fits; omega))]
    exact ih (offset + 1) (writeMachine machine (cursor.val + offset) word) (by
      simp only [List.length_cons] at fits; omega)

theorem array_words_reserved {H : HTy} (heap : Heap H) (base : Nat → Fin W) (frame : Nat)
    (next cursor : Fin W) (offset : Nat) (words : List Word) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame next machine)
    (gap : Objects.Gap heap base cursor.val next.val)
    (positive : 0 < cursor.val + offset) (fits : cursor.val + offset + words.length ≤ next.val) :
    Objects.AllocatorRepr heap base frame next (arrayWordsMachine cursor offset words machine) := by
  induction words generalizing offset machine with
  | nil => exact allocator
  | cons word words ih =>
    have written : Objects.AllocatorRepr heap base frame next (writeMachine machine (cursor.val + offset) word) :=
      allocator.writeGap gap (by omega) (by simp only [List.length_cons] at fits; omega) positive (Nat.le_refl _) word
    exact ih (offset + 1) _ written (by omega) (by simp only [List.length_cons] at fits; omega)

theorem primitive_array_run (words : List Word) (machine : Machine) (cursor : Fin W)
    (bounded : words.length < W) (cell : machine.mem 0 = .val cursor)
    (fits : cursor.val + words.length + 1 < W) :
    run (primitiveArrayCode words) machine =
      .ok ((arrayWordsMachine cursor 1 words (allocateMachine machine cursor ⟨words.length,bounded⟩)).push (.val cursor)) 0 := by
  have length : wmod words.length = (⟨words.length,bounded⟩ : Fin W) := Fin.ext (Nat.mod_eq_of_lt bounded)
  have pushed : run [.push (.val (wmod words.length))] machine = .ok (machine.push (.val ⟨words.length,bounded⟩)) 0 := by
    rw [length]
    rfl
  rw [primitiveArrayCode,List.append_assoc,run_append_ok pushed,run_append_ok (allocateArray_run machine cursor _ cell)]
  exact array_words_run cursor 1 words _ (by omega)

theorem primitive_array_allocator {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (values : List primitive.Denote) (bounded : values.length < W) (words : List Word)
    (representation : PrimitiveWords primitive values words) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (fits : cursor.val + values.length + 1 < W) :
    Objects.AllocatorRepr (heap.alloc (primitiveArrayObject primitive values bounded)).1
      (upd base H.length cursor) frame ⟨cursor.val + values.length + 1,fits⟩
      (arrayWordsMachine cursor 1 words (allocateMachine machine cursor ⟨values.length,bounded⟩)) := by
  let object := primitiveArrayObject (H := H) primitive values bounded
  let target := arrayWordsMachine cursor 1 words (allocateMachine machine cursor ⟨values.length,bounded⟩)
  obtain ⟨reserved,gap⟩ := allocator.reserveArray ⟨values.length,bounded⟩ fits
  have reserved' : Objects.AllocatorRepr heap base frame ⟨cursor.val + values.length + 1,fits⟩ target :=
    array_words_reserved heap base frame _ cursor 1 words _ reserved gap (by omega) (by
      change cursor.val + 1 + words.length ≤ cursor.val + values.length + 1
      rw [representation.length]
      omega)
  have sourceLength : (heap.alloc object).1.len (heap.alloc object).2 .dyn = values.length := by
    simp only [Heap.len,Heap.get_alloc,MObj.elems_dyn,MObj.wk,object,primitiveArrayObject,List.length_map]
  have fresh : Objects.ArrayRepr (heap.alloc object).1 (heap.alloc object).2 .dyn (upd base H.length cursor) target := by
    refine ⟨?_,?_,?_⟩
    · change (upd base H.length cursor H.length).val + (1 + (heap.alloc object).1.len (heap.alloc object).2 .dyn) ≤ W
      rw [upd_same,sourceLength]
      omega
    · intro _
      change target.mem (upd base H.length cursor H.length).val = .val (wmod ((heap.alloc object).1.len (heap.alloc object).2 .dyn))
      rw [upd_same,sourceLength]
      rw [array_words_other cursor 1 words _ _ (Or.inl (by omega))]
      exact (allocateMachine_header machine cursor ⟨values.length,bounded⟩ (by
          have reservedFrame : 0 < frame := allocator.free.reserved
          have cursorAbove : frame ≤ cursor.val := allocator.free.above
          omega)).trans
        (congrArg Word.val (Fin.ext (Nat.mod_eq_of_lt bounded).symm))
    · intro index value selected
      rw [Heap.get_alloc,MObj.elems_dyn] at selected
      change (values.map (MVal.wk (List.prefix_append H [.array (.prim primitive)]) (.prim primitive)))[index]? = some value at selected
      change (values.map id)[index]? = some value at selected
      rw [List.map_id] at selected
      obtain ⟨word,chosen,represented⟩ := representation.elements index value selected
      change ReprV primitive value (target.mem ((upd base H.length cursor H.length).val + 1 + index))
      rw [upd_same,array_words_selected cursor 1 words _ index word chosen]
      exact represented
  apply reserved'.adoptReservedArray .dyn object cursor allocator.free.above fresh
  · change cursor.val + (1 + (heap.alloc object).1.len (heap.alloc object).2 .dyn) ≤ cursor.val + values.length + 1
    rw [sourceLength]
    omega
  · intro R old
    exact Or.inl (allocator.live old)

theorem primitive_array_result {H : HTy} (heap : Heap H) (primitive : PrimTy)
    (values : List primitive.Denote) (bounded : values.length < W) (words : List Word)
    (representation : PrimitiveWords primitive values words) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (fits : cursor.val + (values.length + 1) < W) :
    let grown := (primitiveArrayValue primitive values bounded).copyStToM heap rfl
    ∃ base' target, run (primitiveArrayCode words) machine = .ok (target.push (.val cursor)) 0 ∧
      Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + (values.length + 1),fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
      target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) := by
  rw [primitive_array_source]
  let target := arrayWordsMachine cursor 1 words (allocateMachine machine cursor ⟨values.length,bounded⟩)
  have wordsBound : words.length < W := by rw [representation.length]; exact bounded
  have sameSize : (⟨words.length,wordsBound⟩ : Fin W) = ⟨values.length,bounded⟩ := Fin.ext representation.length
  refine ⟨upd base H.length cursor,target,?_,?_,upd_same _ _ _,(fun old => allocationBase_old base cursor old),?_,?_,?_⟩
  · have ran : run (primitiveArrayCode words) machine =
        .ok ((arrayWordsMachine cursor 1 words (allocateMachine machine cursor ⟨words.length,wordsBound⟩)).push (.val cursor)) 0 :=
      primitive_array_run words machine cursor wordsBound allocator.free.cell (by rw [representation.length]; omega)
    rw [sameSize] at ran
    exact ran
  · exact primitive_array_allocator heap primitive values bounded words representation base frame cursor machine allocator (by omega)
  · dsimp only [target]
    rw [array_words_shape]
    rfl
  · intro address positive below
    rw [array_words_other cursor 1 words _ _ (Or.inl (by omega))]
    exact allocateMachine_other machine cursor _ address (by omega) (by omega)
  · intro lo hi gap below
    exact gap.adoptSingle (primitiveArrayObject primitive values bounded) cursor below

def primitiveArrayWordCopy (primitive : PrimTy) (values : List primitive.Denote)
    (bounded : values.length < W) (words : List Word) (representation : PrimitiveWords primitive values words)
    (feasible : V2.AllocatorWitness (values.length + 1)) : PrimitiveArrayWordCopy primitive values bounded words where
  representation := representation
  certificate := {
    code := primitiveArrayCode words
    heap := storageHeapContents (primitiveArrayValue primitive values bounded) rfl
    positive := Nat.zero_lt_succ _
    feasible := feasible
    correct := by
      intro H heap base frame cursor machine allocator fits
      obtain ⟨base',target,ran,reached,root,extension,shape,below,_⟩ :=
        primitive_array_result heap primitive values bounded words representation base frame cursor machine allocator fits
      refine ⟨base',target,?_,reached,extension,shape,below⟩
      rw [root]
      exact ran }
  rootGap := by
    constructor
    intro H heap base frame cursor machine allocator fits
    obtain ⟨base',target,ran,reached,root,extension,shape,below,gaps⟩ :=
      primitive_array_result heap primitive values bounded words representation base frame cursor machine allocator fits
    refine ⟨base',target,?_,reached,extension,shape,below,root,gaps⟩
    rw [root]
    exact ran
  code := rfl

#print axioms primitive_array_source
#print axioms array_words_shape
#print axioms array_words_other
#print axioms array_words_selected
#print axioms array_words_run
#print axioms array_words_reserved
#print axioms primitive_array_run
#print axioms primitive_array_allocator
#print axioms primitive_array_result
#print axioms primitiveArrayWordCopy
end Solidity.Backend.MemoryCopies
