import Solidity.Backend.MemoryCopies.FixedStorageCopyInterface

/-! The inline storage loop writes the same reserved fixed object as the
existing word allocator. No source header or copied count is assumed. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem fixed_storage_enter (machine : Machine) (cursor : Fin W) (source : Slot) (count : Nat)
    (cell : machine.mem 0 = .val cursor) :
    run (fixedStorageEnter count) (machine.push (.slot source)) =
      .ok (rangeMachine ((allocateStructMachine machine cursor (max 1 count)).push (.val cursor))
        0 count cursor source) 0 := by
  rw [fixedStorageEnter,run_append_ok (allocateStruct_run (machine.push (.slot source)) cursor (max 1 count) cell)]
  simp only [run,exec_cons_zero,Instr.step,Machine.push,Machine.next,Out.ok_bind,exec_nil,rangeMachine,
    List.getElem?_cons_zero,List.getElem?_cons_succ,List.set_cons_zero,List.set_cons_succ,Nat.reduceSub,
    List.cons_append,List.nil_append,allocateStructMachine,writeMachine,wmod_def,Nat.zero_mod]

theorem runtime_fixed_storage_run (machine : Machine) (cursor : Fin W) (source : Slot) (count : Nat)
    (words : List Word) (sized : words.length = count) (cell : machine.mem 0 = .val cursor)
    (contents : ∀ (index : Nat) (word : Word), words[index]? = some word →
      .val (machine.store.cells (source.add index)) = word) (fits : cursor.val + max 1 count < W) :
    run (runtimeFixedStorageCode count) (machine.push (.slot source)) =
      .ok ((arrayWordsMachine cursor 0 words (allocateStructMachine machine cursor (max 1 count))).push (.val cursor)) 0 := by
  subst count
  let allocated := allocateStructMachine machine cursor (max 1 words.length)
  have loop : run [.loop copyRangeCond storageReadRangeBody]
      (rangeMachine (allocated.push (.val cursor)) 0 words.length cursor source) =
      .ok (rangeMachine (arrayWordsMachine cursor 0 words (allocated.push (.val cursor)))
        words.length words.length cursor source) 0 :=
    storage_read_loop words (allocated.push (.val cursor)) cursor source (by omega) (by omega) contents
  rw [runtimeFixedStorageCode,List.append_assoc,
    run_append_ok (fixed_storage_enter machine cursor source words.length cell),run_append_ok loop]
  change Out.ok (arrayWordsMachine cursor 0 words (allocated.push (.val cursor))) 0 = _
  rw [array_words_stack]

def fixedStorageWords (machine : Machine) (source : Slot) (count : Nat) : List Word :=
  List.ofFn (fun index : Fin count => .val (machine.store.cells (source.add index.val)))

theorem fixed_storage_words (machine : Machine) (source : Slot) (primitive : PrimTy) (count : Nat)
    (values : List primitive.Denote) (sized : values.length = count) (limit : Nat)
    (represented : ReprAt machine.store limit (.ref (.fixed (.prim primitive) count)) source
      (fixedPrimitiveValue primitive count values sized)) :
    PrimitiveWords primitive values (fixedStorageWords machine source count) ∧
    (∀ (index : Nat) (word : Word), (fixedStorageWords machine source count)[index]? = some word →
      .val (machine.store.cells (source.add index)) = word) := by
  cases represented with
  | fixed elements =>
    refine ⟨⟨?_,?_⟩,?_⟩
    · simp only [fixedStorageWords,List.length_ofFn,sized]
    · intro index value selected
      have lower : index < count := by rw [← sized]; exact lt_of_getElem? selected
      refine ⟨.val (machine.store.cells (source.add index)),?_,?_⟩
      · simp only [fixedStorageWords,List.getElem?_ofFn,dif_pos lower]
      · have stored : ReprAt machine.store limit (.prim primitive) (source.add (index * size (.prim primitive))) (.prim value) :=
          elements index (.prim value) (by simp only [SVec.toList_ofLen,List.getElem?_map,selected,Option.map_some])
        cases stored with
        | prim representation => simpa only [size_prim,Nat.mul_one] using representation
    · intro index word selected
      have lower : index < count := by
        have actual : index < (fixedStorageWords machine source count).length := lt_of_getElem? selected
        simpa only [fixedStorageWords,List.length_ofFn] using actual
      simp only [fixedStorageWords,List.getElem?_ofFn,dif_pos lower] at selected
      exact Option.some.inj selected

theorem runtime_fixed_storage_canonical {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (values : List primitive.Denote) (sized : values.length = count) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (source : Slot) (limit : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store limit (.ref (.fixed (.prim primitive) count)) source
      (fixedPrimitiveValue primitive count values sized)) (fits : cursor.val + max 1 count < W) :
    let grown := (fixedPrimitiveValue primitive count values sized).copyStToM heap rfl
    ∃ base' target,
      run (runtimeFixedStorageCode count) (machine.push (.slot source)) = .ok (target.push (.val cursor)) 0 ∧
      Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + max 1 count,fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends H base base' ∧ target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
      Heap.Keeps grown.ext heap grown.heap ∧ (∀ {Q : RefTy} (old : HRef H Q), old.id < grown.val.id) := by
  rw [fixed_primitive_source]
  obtain ⟨representation,contents⟩ := fixed_storage_words machine source primitive count values sized limit represented
  let words := fixedStorageWords machine source count
  let target := arrayWordsMachine cursor 0 words (allocateStructMachine machine cursor (max 1 count))
  have wordLength : words.length = count := List.length_ofFn
  refine ⟨upd base H.length cursor,target,?_,?_,upd_same _ _ _,(fun old => allocationBase_old base cursor old),?_,?_,?_,?_,?_⟩
  · exact runtime_fixed_storage_run machine cursor source count words wordLength allocator.free.cell contents fits
  · exact fixed_words_allocator heap primitive count values sized words representation base frame cursor machine allocator fits
  · dsimp only [target]
    rw [array_words_shape]
    rfl
  · intro address nonzero below
    rw [array_words_other cursor 0 words _ _ (Or.inl (by omega))]
    exact allocateStructMachine_other machine cursor (max 1 count) address (by omega)
  · intro lo hi gap below
    exact gap.adoptSingle (fixedPrimitiveObject primitive count values sized) cursor below
  · exact Heap.keeps_alloc heap _
  · intro Q old
    exact old.id_lt

theorem fixed_storage_vector {primitive : PrimTy} {count : Nat} (elements : SVec (.prim primitive) count) :
    elements = SVec.ofLen SVal.prim count (elements.toList.map (fun element => element.view))
      (by rw [List.length_map,SVec.length_toList]) := by
  cases elements with
  | nil => simp only [SVec.toList_nil,List.map_nil,SVec.ofLen]
  | cons value rest =>
    cases value with
    | prim value =>
      simp only [SVec.toList_cons,List.map_cons,SVal.view_prim,SVec.ofLen]
      exact congrArg (SVec.cons (.prim value)) (fixed_storage_vector rest)

theorem fixed_storage_normalize {primitive : PrimTy} {count : Nat}
    (value : SVal (.ref (.fixed (.prim primitive) count))) :
    ∃ (values : List primitive.Denote) (sized : values.length = count), value = fixedPrimitiveValue primitive count values sized := by
  cases value with
  | fixed elements =>
    refine ⟨elements.toList.map (fun element => element.view),by rw [List.length_map,SVec.length_toList],?_⟩
    apply congrArg SVal.fixed
    exact fixed_storage_vector elements

theorem runtime_fixed_storage_success {H : HTy} (heap : Heap H) (primitive : PrimTy) (count : Nat)
    (value : SVal (.ref (.fixed (.prim primitive) count))) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine) (source : Slot) (limit : Nat)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine)
    (represented : ReprAt machine.store limit (.ref (.fixed (.prim primitive) count)) source value)
    (fits : cursor.val + max 1 count < W) :
    let grown := value.copyStToM heap rfl
    ∃ base' target,
      run (runtimeFixedStorageCode count) (machine.push (.slot source)) = .ok (target.push (.val cursor)) 0 ∧
      Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + max 1 count,fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends H base base' ∧ target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) ∧
      Heap.Keeps grown.ext heap grown.heap ∧ (∀ {Q : RefTy} (old : HRef H Q), old.id < grown.val.id) := by
  obtain ⟨values,sized,rfl⟩ := fixed_storage_normalize value
  exact runtime_fixed_storage_canonical heap primitive count values sized base frame cursor machine source limit allocator represented fits

def fixedStorageCopy : FixedStorageCopyCertificate := ⟨runtime_fixed_storage_success⟩

#print axioms fixed_storage_enter
#print axioms runtime_fixed_storage_run
#print axioms fixed_storage_words
#print axioms runtime_fixed_storage_canonical
#print axioms fixed_storage_vector
#print axioms fixed_storage_normalize
#print axioms runtime_fixed_storage_success
#print axioms fixedStorageCopy
end Solidity.Backend.MemoryCopies
