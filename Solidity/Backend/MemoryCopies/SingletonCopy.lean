import Solidity.Backend.MemoryCopies.SingletonCopyInterface

/-! Populate an actual fresh primitive array using the existing allocator and
single typed-store emitters. Storage loading remains a separate obligation. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

def singletonArrayObject {H : HTy} (primitive : PrimTy) (value : primitive.Denote) :
    MObj H (.array (.prim primitive)) := ⟨[value],by change 1 < 2 ^ 256; decide⟩

theorem singleton_copy_source {H : HTy} (heap : Heap H) (primitive : PrimTy) (value : primitive.Denote) :
    (singletonArrayValue primitive value).copyStToM heap rfl =
      Grown.alloc ⟨List.prefix_refl H,heap,singletonArrayObject primitive value⟩ := by
  with_unfolding_all rfl

def singletonCopyMachine (machine : Machine) (cursor : Fin W) (word : Word) : Machine :=
  writeMachine (allocateMachine machine cursor (wmod 1)) (cursor.val + 1) word

theorem singleton_copy_run (machine : Machine) (cursor : Fin W) (word : Word)
    (cell : machine.mem 0 = .val cursor) (fits : cursor.val + 2 < W) :
    run (singletonCopyCode word) machine =
      .ok ((singletonCopyMachine machine cursor word).push (.val cursor)) 0 := by
  have pushed : run [.push word,.push w[1]] machine =
      .ok ((machine.push word).push w[1]) 0 := rfl
  have allocated : run allocateArrayCode ((machine.push word).push w[1]) =
      .ok ((allocateMachine (machine.push word) cursor (wmod 1)).push (.val cursor)) 0 :=
    allocateArray_run (machine.push word) cursor (wmod 1) cell
  have shuffled : run [.swap 1,.dup 2]
      ((allocateMachine (machine.push word) cursor (wmod 1)).push (.val cursor)) =
      .ok ((((allocateMachine machine cursor (wmod 1)).push (.val cursor)).push word).push (.val cursor)) 0 := rfl
  rw [singletonCopyCode,List.append_assoc,List.append_assoc,run_append_ok pushed,
    run_append_ok allocated,run_append_ok shuffled]
  exact writeFieldWord_run ((allocateMachine machine cursor (wmod 1)).push (.val cursor)) cursor 1 word (by omega)

theorem singleton_copy_allocator {H : HTy} (heap : Heap H) (primitive : PrimTy) (value : primitive.Denote)
    (word : Word) (representation : ReprV primitive value word) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) (fits : cursor.val + 2 < W) :
    Objects.AllocatorRepr (heap.alloc (singletonArrayObject primitive value)).1
      (upd base H.length cursor) frame ⟨cursor.val + 2,fits⟩ (singletonCopyMachine machine cursor word) := by
  let zero : MObj H (.array (.prim primitive)) := defaultArray primitive (wmod 1)
  let fresh := (heap.alloc zero).2
  have allocated : Objects.AllocatorRepr (heap.alloc zero).1 (upd base H.length cursor) frame
      ⟨cursor.val + 2,fits⟩ (allocateMachine machine cursor (wmod 1)) :=
    allocator.allocatePrimitive primitive (wmod 1) (by change cursor.val + 1 + 1 < W; omega)
  have index : 0 < (heap.alloc zero).1.len fresh .dyn := by
    simp only [fresh,Heap.len,Heap.get_alloc,MObj.elems_dyn,MObj.wk,zero,defaultArray,
      List.map_replicate,List.length_replicate]
    decide
  have filled : Objects.AllocatorRepr
      ((heap.alloc zero).1.set fresh (MObj.setElem .dyn ((heap.alloc zero).1.get fresh) 0 value))
      (upd base H.length cursor) frame ⟨cursor.val + 2,fits⟩
      (writeMachine (allocateMachine machine cursor (wmod 1))
        ((upd base H.length cursor fresh.id).val + Objects.header (.dyn : ArrTy (.array (.prim primitive)) (.prim primitive)) + 0) word) :=
    allocated.setArray fresh .dyn 0 index value word representation
  have object : MObj.setElem .dyn ((heap.alloc zero).1.get fresh) 0 value =
      MObj.wk (List.prefix_append H [.array (.prim primitive)]) (.array (.prim primitive))
        (singletonArrayObject primitive value) := by
    rw [Heap.get_alloc,MObj.setElem_dyn]
    rfl
  rw [object,Heap.set_alloc_self] at filled
  simpa only [fresh,Heap.alloc,HRef.id,upd_same,Objects.header,Nat.add_zero,singletonCopyMachine] using filled


theorem singleton_copy_below (machine : Machine) (cursor : Fin W) (word : Word) (address : Nat)
    (positive : 0 < address) (below : address < cursor.val) :
    (singletonCopyMachine machine cursor word).mem address = machine.mem address := by
  change upd (allocateMachine machine cursor (wmod 1)).mem (cursor.val + 1) word address = machine.mem address
  rw [upd_other _ _ (show address ≠ cursor.val + 1 by omega)]
  exact allocateMachine_other machine cursor (wmod 1) address (by omega) (by omega)

theorem singleton_copy_result {H : HTy} (heap : Heap H) (primitive : PrimTy) (value : primitive.Denote)
    (word : Word) (representation : ReprV primitive value word) (base : Nat → Fin W) (frame : Nat)
    (cursor : Fin W) (machine : Machine)
    (allocator : Objects.AllocatorRepr heap base frame cursor machine) (fits : cursor.val + 2 < W) :
    let grown := (singletonArrayValue primitive value).copyStToM heap rfl
    ∃ base' target, run (singletonCopyCode word) machine = .ok (target.push (.val cursor)) 0 ∧
      Objects.AllocatorRepr grown.heap base' frame ⟨cursor.val + 2,fits⟩ target ∧
      base' grown.val.id = cursor ∧ BaseExtends H base base' ∧
      target = {machine with mem := target.mem} ∧
      (∀ address, 0 < address → address < cursor.val → target.mem address = machine.mem address) ∧
      (∀ lo hi, Objects.Gap heap base lo hi → hi ≤ cursor.val → Objects.Gap grown.heap base' lo hi) := by
  rw [singleton_copy_source]
  refine ⟨upd base H.length cursor,singletonCopyMachine machine cursor word,
    singleton_copy_run machine cursor word allocator.free.cell fits,
    singleton_copy_allocator heap primitive value word representation base frame cursor machine allocator fits,
    upd_same _ _ _,(fun old => allocationBase_old base cursor old),rfl,
    (fun address positive below => singleton_copy_below machine cursor word address positive below),?_⟩
  intro lo hi gap below
  exact gap.adoptSingle (singletonArrayObject primitive value) cursor below

def singletonWordCopy (primitive : PrimTy) (value : primitive.Denote) (word : Word)
    (representation : ReprV primitive value word) (feasible : V2.AllocatorWitness 2) :
    SingletonWordCopy primitive value word where
  representation := representation
  certificate := {
    code := singletonCopyCode word
    heap := storageHeapContents (singletonArrayValue primitive value) rfl
    positive := by decide
    feasible := feasible
    correct := by
      intro H heap base frame cursor machine allocator fits
      obtain ⟨base',target,ran,reached,root,extension,shape,below,_⟩ :=
        singleton_copy_result heap primitive value word representation base frame cursor machine allocator fits
      refine ⟨base',target,?_,reached,extension,shape,below⟩
      rw [root]
      exact ran }
  rootGap := by
    constructor
    intro H heap base frame cursor machine allocator fits
    obtain ⟨base',target,ran,reached,root,extension,shape,below,gaps⟩ :=
      singleton_copy_result heap primitive value word representation base frame cursor machine allocator fits
    refine ⟨base',target,?_,reached,extension,shape,below,root,gaps⟩
    rw [root]
    exact ran
  code := rfl

theorem singleton_copy_length {H : HTy} (heap : Heap H) (primitive : PrimTy) (value : primitive.Denote) :
    let grown := (singletonArrayValue primitive value).copyStToM heap rfl
    grown.heap.len grown.val .dyn = 1 := by
  rw [singleton_copy_source]
  simp only [Grown.alloc,Heap.len,Heap.get_alloc,MObj.elems_dyn,MObj.wk,singletonArrayObject,
    List.length_map,List.length_singleton]

#print axioms singleton_copy_source
#print axioms singleton_copy_run
#print axioms singleton_copy_allocator
#print axioms singleton_copy_below
#print axioms singleton_copy_result
#print axioms singletonWordCopy
#print axioms singleton_copy_length
end Solidity.Backend.MemoryCopies
