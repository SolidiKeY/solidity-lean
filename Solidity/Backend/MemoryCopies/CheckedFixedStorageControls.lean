import Solidity.Backend.MemoryCopies.CheckedFixedStorage
import Solidity.Evm.MemoryObjectArrayExamples

/-! Populated inline fixed storage values exercise the shared runtime loop.
Empty objects reserve a cell; fixed payloads never acquire a length header.
Capacity failures use represented fixtures; huge-demand refusal is code-only. -/
namespace Solidity.Backend.MemoryCopies.CheckedFixedStorageControls
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

theorem certificate_inhabited : CheckedFixedStorageCertificate := checkedFixedStorage

theorem actual_runtime (payloads : List (Fin W)) (fits : 40 + max 1 payloads.length < W) :
    ∃ (base' : Nat → Fin W) (target : Machine),
      run (checkedFixedStorageCode payloads.length) ((machine payloads).push (.slot source)) = .ok (target.push w[40]) 0 ∧
      Objects.AllocatorRepr (grown payloads).heap base' 8 ⟨40 + max 1 payloads.length,fits⟩ target ∧
      target.mem 0 = .val (wmod (40 + max 1 payloads.length)) ∧
      target.mem 17 = w[7] ∧ target.store = (machine payloads).store ∧ target.stack = [w[77]] ∧
      (∀ (index : Nat) (payload : Fin W), payloads[index]? = some payload → target.mem (40 + index) = .val payload) := by
  obtain ⟨base',target,ran,allocated,rootAt,_,shape,below,_,_,_⟩ :=
    checked_fixed_storage_success input.heap .uint payloads.length (value payloads) input.base 8 (wmod 40)
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
    run (checkedFixedStorageCode 0) ((machine []).push (.slot source)) = .ok (target.push w[40]) 0 ∧
      target.mem 0 = w[41] ∧ target.mem 40 = w[0] ∧ target.mem 17 = w[7] := by
  obtain ⟨_,target,ran,_,cursor,old,_,_,_⟩ := actual_runtime [] (by decide)
  have empty : target.mem 40 = w[0] := by
    have execution : run (checkedFixedStorageCode 0) ((machine []).push (.slot source)) =
        .ok ((allocateStructMachine (machine []) (wmod 40) 1).push w[40]) 0 :=
      by
        rw [checked_fixed_storage_run 0 (machine []) (wmod 40) source rfl,if_pos (by decide)]
        exact runtime_fixed_storage_run (machine []) (wmod 40) source 0 [] rfl rfl
          (by intro i w h; cases i <;> cases h) (by decide)
    have ran' : run (checkedFixedStorageCode 0) ((machine []).push (.slot source)) = .ok (target.push w[40]) 0 := ran
    rw [ran'] at execution
    have same : target.mem 40 = (allocateStructMachine (machine []) (wmod 40) 1).mem 40 :=
      congrArg (fun m => m.mem 40) (Out.ok.inj execution).1
    rw [same,allocateStructMachine_other _ _ _ 40 (by decide)]
    exact input.allocator.free.zero 40 (Nat.le_refl _)
  exact ⟨target,ran,cursor,empty,old⟩

theorem pair_runtime (left right : Fin W) : ∃ target : Machine,
    run (checkedFixedStorageCode 2) ((machine [left,right]).push (.slot source)) = .ok (target.push w[40]) 0 ∧
      target.mem 0 = w[42] ∧ target.mem 40 = .val left ∧ target.mem 41 = .val right ∧ target.mem 17 = w[7] := by
  obtain ⟨_,target,ran,_,cursor,old,_,_,contents⟩ := actual_runtime [left,right] (by change 40 + max 1 2 < W; decide)
  exact ⟨target,ran,cursor,contents 0 left rfl,contents 1 right rfl,old⟩

private def long : List (Fin W) := List.ofFn (fun index : Fin 64 => wmod (index.val + 1))
theorem long_runtime : ∃ target : Machine,
    run (checkedFixedStorageCode 64) ((machine long).push (.slot source)) = .ok (target.push w[40]) 0 ∧
      target.mem 0 = w[104] ∧ target.mem 40 = w[1] ∧ target.mem 103 = w[64] ∧ target.mem 17 = w[7] := by
  obtain ⟨_,target,ran,_,cursor,old,_,_,contents⟩ := actual_runtime long (by rw [long,List.length_ofFn]; decide)
  exact ⟨target,ran,cursor,contents 0 (wmod 1) (by decide +kernel),contents 63 (wmod 64) (by decide +kernel),old⟩

theorem source_fresh (payloads : List (Fin W)) {R : RefTy} (old : HRef input.H R) : old.id < (grown payloads).val.id :=
  Nat.lt_of_lt_of_le old.id_lt (SVal.copyStToM_id_ge input.heap (value payloads) rfl)

theorem wrong_zero (target : Machine)
    (ran : run (checkedFixedStorageCode 2) ((machine [wmod 11,wmod 23]).push (.slot source)) = .ok (target.push w[40]) 0) :
    target.mem 41 ≠ w[0] := by
  obtain ⟨actual,execution,_,_,second,_⟩ := pair_runtime (wmod 11) (wmod 23)
  rw [ran] at execution
  have same : target.mem 41 = actual.mem 41 := congrArg (fun m => m.mem 41) (Out.ok.inj execution).1
  rw [same,second]
  decide

theorem wrong_header (target : Machine)
    (ran : run (checkedFixedStorageCode 2) ((machine [wmod 11,wmod 23]).push (.slot source)) = .ok (target.push w[40]) 0) :
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

private def moved (payloads : List (Fin W)) (cursor : Fin W) : Machine := writeMachine (machine payloads) 0 (.val cursor)
private theorem moved_allocator (payloads : List (Fin W)) (cursor : Fin W) (above : 40 ≤ cursor.val) :
    Objects.AllocatorRepr input.heap input.base 8 cursor (moved payloads cursor) := by
  have initial : Objects.AllocatorRepr input.heap input.base 8 (wmod 40) (machine payloads) := allocator payloads
  refine ⟨initial.heap.localWrite 0 (by decide) (.val cursor),⟨by decide,by omega,?_,?_⟩,?_⟩
  · rfl
  · intro address lower
    exact (upd_other _ _ (by omega : address ≠ 0)).trans (initial.free.zero address (by change 40 ≤ address; omega))
  · intro Q reference
    have live : (input.base reference.id).val + Objects.cells input.heap reference ≤ 40 := initial.live reference
    omega

/-- Actual represented fixed input and complete allocator coexist at saturation. -/
theorem saturated_input (payloads : List (Fin W)) :
    Objects.AllocatorRepr input.heap input.base 8 wMax (moved payloads wMax) ∧
    ReprAt (moved payloads wMax).store 128 (.ref (.fixed (.prim .uint) payloads.length)) source (value payloads) :=
  ⟨moved_allocator payloads wMax (by decide),represented payloads⟩

theorem saturated_refusal (payloads : List (Fin W)) :
    run (checkedFixedStorageCode payloads.length) ((moved payloads wMax).push (.slot source)) = .revert := by
  rw [checked_fixed_storage_run payloads.length (moved payloads wMax) wMax source rfl]
  apply if_neg
  change ¬ (W - 1 + max 1 payloads.length < W)
  have positive : 0 < W := W_pos
  omega

theorem empty_saturated_refusal :
    run (checkedFixedStorageCode 0) ((moved [] wMax).push (.slot source)) = .revert := saturated_refusal []

private theorem cursor_value (n : Nat) (positive : 0 < n) (bounded : n ≤ W) :
    (wmod (W - n)).val = W - n := Nat.mod_eq_of_lt (by omega)
private theorem cursor_above (n : Nat) (positive : 0 < n) (bounded : n ≤ 128) : 40 ≤ (wmod (W - n)).val := by
  have large : 256 < W := by decide
  rw [cursor_value n positive (by omega)]
  omega

theorem pair_boundary_refusal :
    run (checkedFixedStorageCode 2) ((moved [wmod 11,wmod 23] (wmod (W - 2))).push (.slot source)) = .revert := by
  rw [checked_fixed_storage_run 2 (moved [wmod 11,wmod 23] (wmod (W - 2))) (wmod (W - 2)) source rfl,
    cursor_value 2 (by decide) (by decide)]
  apply if_neg
  have large : 2 ≤ W := by decide
  change ¬ (W - 2 + max 1 2 < W)
  omega

theorem pair_last_fitting : ∃ fits,
    CheckedFixedStorageResult input.heap .uint 2 (value [wmod 11,wmod 23]) input.base 8 (wmod (W - 3))
      (moved [wmod 11,wmod 23] (wmod (W - 3))) source fits := by
  have fits : (wmod (W - 3)).val + max 1 2 < W := by
    rw [cursor_value 3 (by decide) (by decide)]
    have large : 3 ≤ W := by decide
    omega
  exact ⟨fits,checked_fixed_storage_success input.heap .uint 2 (value [wmod 11,wmod 23]) input.base 8 (wmod (W - 3))
    (moved [wmod 11,wmod 23] (wmod (W - 3))) source 128
    (moved_allocator [wmod 11,wmod 23] _ (cursor_above 3 (by decide) (by decide)))
    (represented [wmod 11,wmod 23]) fits⟩

theorem fixed_count_selects_capacity :
    (∃ fits, CheckedFixedStorageResult input.heap .uint 0 (value []) input.base 8 (wmod (W - 2))
      (moved [] (wmod (W - 2))) source fits) ∧
    run (checkedFixedStorageCode 2) ((moved [wmod 11,wmod 23] (wmod (W - 2))).push (.slot source)) = .revert := by
  have fits : (wmod (W - 2)).val + max 1 0 < W := by
    rw [cursor_value 2 (by decide) (by decide)]
    have large : 2 ≤ W := by decide
    omega
  exact ⟨⟨fits,checked_fixed_storage_success input.heap .uint 0 (value []) input.base 8 (wmod (W - 2))
    (moved [] (wmod (W - 2))) source 128
    (moved_allocator [] _ (cursor_above 2 (by decide) (by decide))) (represented []) fits⟩,pair_boundary_refusal⟩

/-- Only code execution is claimed: no gigantic represented fixed input is constructed. -/
theorem huge_code_only_refusal :
    run (checkedFixedStorageCode W) ((machine []).push (.slot source)) = .revert :=
  checked_fixed_storage_large_code W (by omega) (machine []) (wmod 40) source rfl

#print axioms saturated_input
#print axioms saturated_refusal
#print axioms empty_saturated_refusal
#print axioms pair_boundary_refusal
#print axioms pair_last_fitting
#print axioms fixed_count_selects_capacity
#print axioms huge_code_only_refusal
end Solidity.Backend.MemoryCopies.CheckedFixedStorageControls
