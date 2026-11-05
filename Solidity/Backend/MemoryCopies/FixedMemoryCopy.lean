import Solidity.Backend.MemoryCopies.FixedMemoryCopyInterface

/-! Fixed payloads are headerless; the existing reservation, gap-write and
array-adoption APIs retain their complete ownership through the runtime copy. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem fixed_primitive_source {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (values : List primitive.Denote) (sized : values.length = count) :
    (fixedPrimitiveValue primitive count values sized).copyStToM heap rfl =
      Grown.alloc ⟨List.prefix_refl H,heap,fixedPrimitiveObject primitive count values sized⟩ := by
  have contents : (SVec.ofLen SVal.prim count values sized).toList.map (fun value => value.view) = values := by
    rw [SVec.toList_ofLen,List.map_map]
    change values.map id = values
    exact List.map_id values
  rw [fixedPrimitiveValue,SVal.copyStToM_fixed,primitive_live_vector]
  simp only [contents]
  rfl

theorem fixed_reservation {H : HTy} (heap : Heap H) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (count : Nat) (fits : cursor.val + max 1 count < W) :
    Objects.AllocatorRepr heap base frame ⟨cursor.val + max 1 count,fits⟩
      (allocateStructMachine machine cursor (max 1 count)) ∧
    Objects.Gap heap base cursor.val (cursor.val + max 1 count) := by
  have represented : Objects.HeapRepr heap base frame (allocateStructMachine machine cursor (max 1 count)) := by
    apply allocator.heap.writeOutside 0 _
    intro Q reference
    exact .inl (Nat.lt_of_lt_of_le allocator.free.reserved (allocator.heap.owner.above reference))
  refine ⟨⟨represented,allocator.free.allocateStruct _ fits,?_⟩,fun reference => .inl (allocator.live reference)⟩
  intro Q reference
  change (base reference.id).val + Objects.cells heap reference ≤ cursor.val + max 1 count
  exact Nat.le_trans (allocator.live reference) (Nat.le_add_right _ _)

theorem fixed_words_allocator {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (values : List primitive.Denote) (sized : values.length = count) (words : List Word)
    (representation : PrimitiveWords primitive values words) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (fits : cursor.val + max 1 count < W) :
    Objects.AllocatorRepr (heap.alloc (fixedPrimitiveObject primitive count values sized)).1
      (upd base H.length cursor) frame ⟨cursor.val + max 1 count,fits⟩
      (arrayWordsMachine cursor 0 words (allocateStructMachine machine cursor (max 1 count))) := by
  let object := fixedPrimitiveObject (H := H) primitive count values sized
  let target := arrayWordsMachine cursor 0 words (allocateStructMachine machine cursor (max 1 count))
  obtain ⟨reserved,gap⟩ := fixed_reservation heap base frame cursor machine allocator count fits
  have positive : 0 < cursor.val + 0 := by
    have below : 0 < frame := allocator.free.reserved
    have above : frame ≤ cursor.val := allocator.free.above
    omega
  have reserved' : Objects.AllocatorRepr heap base frame ⟨cursor.val + max 1 count,fits⟩ target :=
    array_words_reserved heap base frame _ cursor 0 words _ reserved gap positive (by
      change cursor.val + 0 + words.length ≤ cursor.val + max 1 count
      rw [representation.length,sized]
      omega)
  have fresh : Objects.ArrayRepr (heap.alloc object).1 (heap.alloc object).2 .fixed (upd base H.length cursor) target := by
    refine ⟨?_,?_,?_⟩
    · change (upd base H.length cursor H.length).val + max 1 count ≤ W
      rw [upd_same]
      omega
    · intro impossible
      cases impossible
    · intro index value selected
      rw [Heap.get_alloc,MObj.elems_fixed] at selected
      change (values.map (MVal.wk (List.prefix_append H [.fixed (.prim primitive) count]) (.prim primitive)))[index]? = some value at selected
      change (values.map id)[index]? = some value at selected
      rw [List.map_id] at selected
      obtain ⟨word,chosen,represented⟩ := representation.elements index value selected
      change ReprV primitive value (target.mem ((upd base H.length cursor H.length).val + 0 + index))
      rw [upd_same,array_words_selected cursor 0 words _ index word chosen]
      exact represented
  apply reserved'.adoptReservedArray .fixed object cursor allocator.free.above fresh
  · change cursor.val + max 1 count ≤ cursor.val + max 1 count
    exact Nat.le_refl _
  · intro Q reference
    exact .inl (allocator.live reference)
theorem fixed_memory_enter (machine : Machine) (cursor source : Fin W) (count : Nat)
    (cell : machine.mem 0 = .val cursor) :
    run (fixedMemoryEnter count) (machine.push (.val source)) =
      .ok (memoryRangeMachine ((allocateStructMachine machine cursor (max 1 count)).push (.val cursor))
        0 count cursor source) 0 := by
  rw [fixedMemoryEnter,run_append_ok (allocateStruct_run (machine.push (.val source)) cursor (max 1 count) cell)]
  simp only [run,exec_cons_zero,Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,memoryRangeMachine,
    List.getElem?_cons_zero,List.getElem?_cons_succ,List.set_cons_zero,List.set_cons_succ,Nat.reduceSub,
    List.cons_append,List.nil_append,allocateStructMachine,writeMachine,wmod_def,Nat.zero_mod]

theorem runtime_fixed_memory_run (machine : Machine) (cursor source : Fin W) (count : Nat) (words : List Word)
    (sized : words.length = count) (cell : machine.mem 0 = .val cursor)
    (positive : 0 < source.val) (sourceRoom : source.val + count ≤ cursor.val)
    (contents : ∀ (index : Nat) (word : Word), words[index]? = some word → machine.mem (source.val + index) = word)
    (fits : cursor.val + max 1 count < W) :
    run (runtimeFixedMemoryCode count) (machine.push (.val source)) =
      .ok ((arrayWordsMachine cursor 0 words (allocateStructMachine machine cursor (max 1 count))).push (.val cursor)) 0 := by
  subst count
  have countLe : words.length ≤ max 1 words.length := Nat.le_max_right _ _
  have bounded : words.length < W := by omega
  let allocated := allocateStructMachine machine cursor (max 1 words.length)
  have loop : run [.loop copyRangeCond memoryReadRangeBody]
      (memoryRangeMachine (allocated.push (.val cursor)) 0 words.length cursor source) =
      .ok (memoryRangeMachine (arrayWordsMachine cursor 0 words (allocated.push (.val cursor)))
        words.length words.length cursor source) 0 := by
    apply memory_read_loop words (allocated.push (.val cursor)) cursor source bounded (by omega) sourceRoom
    intro index word chosen
    change allocated.mem (source.val + index) = word
    rw [allocateStructMachine_other machine cursor (max 1 words.length) _ (by omega)]
    exact contents index word chosen
  rw [runtimeFixedMemoryCode,List.append_assoc,
    run_append_ok (fixed_memory_enter machine cursor source words.length cell),run_append_ok loop]
  change Out.ok (arrayWordsMachine cursor 0 words (allocated.push (.val cursor))) 0 = _
  rw [array_words_stack]

def fixedMemoryWords (machine : Machine) (source : Fin W) (count : Nat) : List Word :=
  List.ofFn (fun index : Fin count => machine.mem (source.val + index.val))

theorem fixed_memory_words {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (input : HRef H (.fixed (.prim primitive) count)) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (allocator : Objects.AllocatorRepr heap base frame cursor machine) :
    PrimitiveWords primitive (heap.get input).val (fixedMemoryWords machine (base input.id) count) ∧
    (∀ (index : Nat) (word : Word), (fixedMemoryWords machine (base input.id) count)[index]? = some word →
      machine.mem ((base input.id).val + index) = word) := by
  constructor
  · refine ⟨?_,?_⟩
    · simp only [fixedMemoryWords,List.length_ofFn,(heap.get input).property]
    · intro index value selected
      have lower : index < count := by
        have actual : index < (heap.get input).val.length := lt_of_getElem? selected
        rw [(heap.get input).property] at actual
        exact actual
      refine ⟨machine.mem ((base input.id).val + index),?_,?_⟩
      · simp only [fixedMemoryWords,List.getElem?_ofFn,dif_pos lower]
      · exact (allocator.heap.arrays .fixed input).elements index value (by
          simpa only [MObj.elems_fixed] using selected)
  · intro index word selected
    have lower : index < count := by
      have actual : index < (fixedMemoryWords machine (base input.id) count).length := lt_of_getElem? selected
      simpa only [fixedMemoryWords,List.length_ofFn] using actual
    simp only [fixedMemoryWords,List.getElem?_ofFn,dif_pos lower] at selected
    exact Option.some.inj selected

theorem runtime_fixed_memory_success {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (input : HRef H (.fixed (.prim primitive) count)) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (fits : cursor.val + max 1 count < W) :
    let grown := (MVal.copyMToSt heap (T := .ref (.fixed (.prim primitive) count)) input).copyStToM heap rfl
    ∃ base' target,
      run (runtimeFixedMemoryCode count) (machine.push (.val (base input.id))) = .ok (target.push (.val cursor)) 0 ∧
      Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + max 1 count,fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends H base base' ∧ target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
      Heap.Keeps grown.ext heap grown.heap ∧ input.id < grown.val.id := by
  have snapshot : MVal.copyMToSt heap (T := .ref (.fixed (.prim primitive) count)) input =
      fixedPrimitiveValue primitive count (heap.get input).val (heap.get input).property := primitiveFixed_snapshot heap input
  rw [snapshot,fixed_primitive_source]
  obtain ⟨representation,contents⟩ := fixed_memory_words heap primitive count input base frame cursor machine allocator
  let words := fixedMemoryWords machine (base input.id) count
  let target := arrayWordsMachine cursor 0 words (allocateStructMachine machine cursor (max 1 count))
  have wordLength : words.length = count := List.length_ofFn
  have sourceRoom : (base input.id).val + count ≤ cursor.val := by
    have old : (base input.id).val + Objects.cells heap input ≤ cursor.val := allocator.live input
    change (base input.id).val + max 1 count ≤ cursor.val at old
    have countLe : count ≤ max 1 count := Nat.le_max_right _ _
    omega
  have positive : 0 < (base input.id).val := Nat.lt_of_lt_of_le allocator.free.reserved (allocator.heap.owner.above input)
  refine ⟨upd base H.length cursor,target,?_,?_,upd_same _ _ _,(fun old => allocationBase_old base cursor old),?_,?_,?_,?_,?_⟩
  · exact runtime_fixed_memory_run machine cursor (base input.id) count words wordLength allocator.free.cell positive sourceRoom contents fits
  · exact fixed_words_allocator heap primitive count (heap.get input).val (heap.get input).property
      words representation base frame cursor machine allocator fits
  · dsimp only [target]
    rw [array_words_shape]
    rfl
  · intro address nonzero below
    rw [array_words_other cursor 0 words _ _ (Or.inl (by omega))]
    exact allocateStructMachine_other machine cursor (max 1 count) address (by omega)
  · intro lo hi gap below
    exact gap.adoptSingle (fixedPrimitiveObject primitive count (heap.get input).val (heap.get input).property) cursor below
  · exact Heap.keeps_alloc heap _
  · change input.id < H.length
    exact input.id_lt

def fixedMemoryCopy : FixedMemoryCopyCertificate := ⟨runtime_fixed_memory_success⟩

#print axioms fixed_primitive_source
#print axioms fixed_reservation
#print axioms fixed_words_allocator
#print axioms fixed_memory_enter
#print axioms runtime_fixed_memory_run
#print axioms fixed_memory_words
#print axioms runtime_fixed_memory_success
#print axioms fixedMemoryCopy
end Solidity.Backend.MemoryCopies
