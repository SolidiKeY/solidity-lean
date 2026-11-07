import Solidity.Backend.MemoryCopies.FixedStorageCopy
import Solidity.Evm.MemoryObjectArrayExamples

/-! Populated inline fixed storage values exercise the shared runtime loop.
Empty objects reserve a cell; fixed payloads never acquire a length header. -/
namespace Solidity.Backend.MemoryCopies.FixedStorageCopyControls
open Evm Evm.Memory
private structure Input where
  H : HTy
  heap : Heap H
  base : Nat → Fin W
  machine : Machine
  allocator : Objects.AllocatorRepr heap base 8 (wmod 40) machine
private def input : Input := ⟨_,_,_,_,ObjectArrayExamples.initial_allocator⟩
private def values (payloads : List (Fin W)) : List PrimTy.uint.Denote := payloads.map indexValue
private def value (payloads : List (Fin W)) : SVal (.ref (.fixed (.prim .uint) payloads.length)) :=
  fixedPrimitiveValue .uint payloads.length (values payloads) (by rw [values,List.length_map])
private def source : Slot := .root 0
private def store (payloads : List (Fin W)) : WordStore := ⟨fun slot => match slot with
  | .root index => payloads[index]?.getD (wmod 0)
  | _ => wmod 71⟩
private def machine (payloads : List (Fin W)) : Machine := {input.machine with store := store payloads}
private def grown (payloads : List (Fin W)) := (value payloads).copyStToM input.heap rfl
private theorem represented (payloads : List (Fin W)) :
    ReprAt (machine payloads).store 128 (.ref (.fixed (.prim .uint) payloads.length)) source (value payloads) := by
  refine .fixed ?_
  intro index item selected
  simp only [SVec.toList_ofLen,values,List.getElem?_map] at selected
  cases chosen : payloads[index]? with
  | none => simp only [chosen,Option.map_none] at selected; cases selected
  | some payload =>
    simp only [chosen,Option.map_some] at selected
    cases selected
    simp only [size_prim,Nat.mul_one]
    refine .prim (ReprV.uint_of ?_)
    simp only [machine,store,source,Slot.add,Nat.zero_add,chosen,Option.getD_some]
    rfl
private theorem allocator (payloads : List (Fin W)) :
    Objects.AllocatorRepr input.heap input.base 8 (wmod 40) (machine payloads) := input.allocator.mem_eq rfl

theorem certificate_inhabited : FixedStorageCopyCertificate := fixedStorageCopy

theorem actual_runtime (payloads : List (Fin W)) (fits : 40 + max 1 payloads.length < W) :
    ∃ (base' : Nat → Fin W) (target : Machine),
      run (runtimeFixedStorageCode payloads.length) ((machine payloads).push (.slot source)) = .ok (target.push w[40]) 0 ∧
      Objects.AllocatorRepr (grown payloads).heap base' 8 ⟨40 + max 1 payloads.length,fits⟩ target ∧
      target.mem 0 = .val (wmod (40 + max 1 payloads.length)) ∧
      target.mem 17 = w[7] ∧ target.store = (machine payloads).store ∧ target.stack = [w[77]] ∧
      (∀ (index : Nat) (payload : Fin W), payloads[index]? = some payload → target.mem (40 + index) = .val payload) := by
  obtain ⟨base',target,ran,allocated,rootAt,_,shape,below,_,_,_⟩ :=
    runtime_fixed_storage_success input.heap .uint payloads.length (value payloads) input.base 8 (wmod 40)
      (machine payloads) source 128 (allocator payloads) (represented payloads) fits
  change base' (grown payloads).val.id = wmod 40 at rootAt
  refine ⟨base',target,ran,allocated,?_,below 17 (by decide) (by decide),?_,congrArg Machine.stack shape,?_⟩
  · refine allocated.free.cell.trans ?_
    apply congrArg Word.val
    apply Fin.ext
    simp only [wmod_def,Nat.mod_eq_of_lt (show 40 < W by decide)]
    exact (Nat.mod_eq_of_lt fits).symm
  · rw [shape]
  · intro index payload selected
    have item : (MObj.elems .fixed ((grown payloads).heap.get (grown payloads).val))[index]? = some (indexValue payload) := by
      dsimp only [grown,value]
      rw [fixed_primitive_source]
      simp only [Grown.alloc,Heap.get_alloc,MObj.elems_fixed,MObj.wk,fixedPrimitiveObject,MVal.wk,values,
        List.getElem?_map,selected,Option.map_some]
    have contents : ReprV .uint (indexValue payload) (target.mem ((base' (grown payloads).val.id).val + 0 + index)) :=
      (allocated.heap.arrays .fixed (grown payloads).val).elements index (indexValue payload) item
    obtain ⟨word,stored,equal⟩ := contents
    have same : word = payload := Fin.ext (Int.ofNat_inj.mp equal.symm)
    subst word
    rw [rootAt] at stored
    exact stored

theorem empty_runtime : ∃ target : Machine,
    run (runtimeFixedStorageCode 0) ((machine []).push (.slot source)) = .ok (target.push w[40]) 0 ∧
      target.mem 0 = w[41] ∧ target.mem 40 = w[0] ∧ target.mem 17 = w[7] := by
  obtain ⟨_,target,ran,_,cursor,old,_,_,_⟩ := actual_runtime [] (by decide)
  have empty : target.mem 40 = w[0] := by
    have execution : run (runtimeFixedStorageCode 0) ((machine []).push (.slot source)) =
        .ok ((allocateStructMachine (machine []) (wmod 40) 1).push w[40]) 0 :=
      runtime_fixed_storage_run (machine []) (wmod 40) source 0 [] rfl rfl
        (by intro i w h; cases i <;> cases h) (by decide)
    have ran' : run (runtimeFixedStorageCode 0) ((machine []).push (.slot source)) = .ok (target.push w[40]) 0 := ran
    rw [ran'] at execution
    have same : target.mem 40 = (allocateStructMachine (machine []) (wmod 40) 1).mem 40 :=
      congrArg (fun m => m.mem 40) (Out.ok.inj execution).1
    rw [same,allocateStructMachine_other _ _ _ 40 (by decide)]
    exact input.allocator.free.zero 40 (Nat.le_refl _)
  exact ⟨target,ran,cursor,empty,old⟩

theorem pair_runtime (left right : Fin W) : ∃ target : Machine,
    run (runtimeFixedStorageCode 2) ((machine [left,right]).push (.slot source)) = .ok (target.push w[40]) 0 ∧
      target.mem 0 = w[42] ∧ target.mem 40 = .val left ∧ target.mem 41 = .val right ∧ target.mem 17 = w[7] := by
  obtain ⟨_,target,ran,_,cursor,old,_,_,contents⟩ := actual_runtime [left,right] (by change 40 + max 1 2 < W; decide)
  exact ⟨target,ran,cursor,contents 0 left rfl,contents 1 right rfl,old⟩

private def long : List (Fin W) := List.ofFn (fun index : Fin 64 => wmod (index.val + 1))
theorem long_runtime : ∃ target : Machine,
    run (runtimeFixedStorageCode 64) ((machine long).push (.slot source)) = .ok (target.push w[40]) 0 ∧
      target.mem 0 = w[104] ∧ target.mem 40 = w[1] ∧ target.mem 103 = w[64] ∧ target.mem 17 = w[7] := by
  obtain ⟨_,target,ran,_,cursor,old,_,_,contents⟩ := actual_runtime long (by rw [long,List.length_ofFn]; decide)
  exact ⟨target,ran,cursor,contents 0 (wmod 1) (by decide +kernel),contents 63 (wmod 64) (by decide +kernel),old⟩

theorem source_fresh (payloads : List (Fin W)) {R : RefTy} (old : HRef input.H R) : old.id < (grown payloads).val.id :=
  Nat.lt_of_lt_of_le old.id_lt (SVal.copyStToM_id_ge input.heap (value payloads) rfl)

theorem wrong_zero (target : Machine)
    (ran : run (runtimeFixedStorageCode 2) ((machine [wmod 11,wmod 23]).push (.slot source)) = .ok (target.push w[40]) 0) :
    target.mem 41 ≠ w[0] := by
  obtain ⟨actual,execution,_,_,second,_⟩ := pair_runtime (wmod 11) (wmod 23)
  rw [ran] at execution
  have same : target.mem 41 = actual.mem 41 := congrArg (fun m => m.mem 41) (Out.ok.inj execution).1
  rw [same,second]
  decide

theorem wrong_header (target : Machine)
    (ran : run (runtimeFixedStorageCode 2) ((machine [wmod 11,wmod 23]).push (.slot source)) = .ok (target.push w[40]) 0) :
    target.mem 40 ≠ w[2] := by
  obtain ⟨actual,execution,_,first,_,_⟩ := pair_runtime (wmod 11) (wmod 23)
  rw [ran] at execution
  have same : target.mem 40 = actual.mem 40 := congrArg (fun m => m.mem 40) (Out.ok.inj execution).1
  rw [same,first]
  decide

theorem room_boundary_refused : ¬ ((W - 2) + max 1 2 < W) := by omega

#print axioms certificate_inhabited
#print axioms actual_runtime
#print axioms empty_runtime
#print axioms pair_runtime
#print axioms long_runtime
#print axioms source_fresh
#print axioms wrong_zero
#print axioms wrong_header
#print axioms room_boundary_refused
end Solidity.Backend.MemoryCopies.FixedStorageCopyControls
