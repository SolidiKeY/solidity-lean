import Solidity.Backend.MemoryCopies.CheckedStorageArray
import Solidity.Evm.MemoryObjectArrayExamples

/-! The identical runtime code reads actual lengths0/2/64 and nonzero payloads
on a represented old heap. Room predicates are distinct from panic/gas semantics. -/
namespace Solidity.Backend.MemoryCopies.CheckedStorageArrayControls
open Evm Evm.Memory
private structure Input where
  H : HTy
  heap : Heap H
  base : Nat → Fin W
  machine : Machine
  allocator : Objects.AllocatorRepr heap base 8 (wmod 40) machine
private def input : Input := ⟨_,_,_,_,ObjectArrayExamples.initial_allocator⟩
private def values (payloads : List (Fin W)) : List PrimTy.uint.Denote := payloads.map indexValue
private theorem wide : 128 < W := by decide
private def value (payloads : List (Fin W)) (bounded : payloads.length < 128) : SVal (.ref (.array (.prim .uint))) :=
  primitiveArrayValue .uint (values payloads) (by rw [values,List.length_map]; exact Nat.lt_trans bounded wide)
private def source : Slot := .root 0
private def store (payloads : List (Fin W)) : WordStore := ⟨fun slot => match slot with
  | .root 0 => wmod payloads.length
  | .data (.root 0) index => payloads[index]?.getD (wmod 0)
  | _ => wmod 0⟩
private def machine (payloads : List (Fin W)) : Machine := {input.machine with store := store payloads}
private def grown (payloads : List (Fin W)) (bounded : payloads.length < 128) :=
  (value payloads bounded).copyStToM input.heap rfl
private theorem represented (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    ReprAt (machine payloads).store 128 (.ref (.array (.prim .uint))) source (value payloads bounded) := by
  refine .array ?_ (by simpa only [values,List.length_map] using bounded) ?_
  · simp only [values,List.length_map]
    exact Nat.mod_eq_of_lt (Nat.lt_trans bounded wide)
  · intro index item selected
    simp only [SVec.toList_ofList,values,List.getElem?_map] at selected
    cases chosen : payloads[index]? with
    | none => simp only [chosen,Option.map_none] at selected; cases selected
    | some payload =>
      simp only [chosen,Option.map_some] at selected
      cases selected
      simp only [size_prim,Nat.mul_one]
      refine .prim (ReprV.uint_of ?_)
      simp only [machine,store,source,chosen,Option.getD_some]
      rfl
private theorem allocator (payloads : List (Fin W)) :
    Objects.AllocatorRepr input.heap input.base 8 (wmod 40) (machine payloads) := input.allocator.mem_eq rfl

theorem certificate_inhabited : CheckedStorageArrayCertificate := checkedStorageArray

theorem actual_runtime (payloads : List (Fin W)) (bounded : payloads.length < 128)
    (fits : 40 + (payloads.length + 1) < W) :
    ∃ (base' : Nat → Fin W) (target : Machine),
      run checkedStorageArrayCode ((machine payloads).push (.slot source)) = .ok (target.push w[40]) 0 ∧
      Objects.AllocatorRepr (grown payloads bounded).heap base' 8 ⟨40 + (payloads.length + 1),fits⟩ target ∧
      target.mem 0 = .val (wmod (40 + payloads.length + 1)) ∧ target.mem 40 = .val (wmod payloads.length) ∧
      target.mem 17 = w[7] ∧ target.store = (machine payloads).store ∧ target.stack = [w[77]] ∧
      (∀ (index : Nat) (payload : Fin W), payloads[index]? = some payload → target.mem (41 + index) = .val payload) := by
  obtain ⟨base',target,ran,allocated,rootAt,_,shape,below,_⟩ :=
    checked_storage_array_success input.heap .uint (values payloads)
      (by rw [values,List.length_map]; exact Nat.lt_trans bounded wide)
      input.base 8 (wmod 40) (machine payloads) source 128 (allocator payloads) (represented payloads bounded)
      (by simpa only [values,List.length_map] using fits)
  have sourceLength : (grown payloads bounded).heap.len (grown payloads bounded).val .dyn = payloads.length := by
    dsimp only [grown,value]
    rw [primitive_array_source]
    simp only [Grown.alloc,Heap.len,Heap.get_alloc,MObj.elems_dyn,MObj.wk,primitiveArrayObject,values,List.length_map]
  have header : target.mem (base' (grown payloads bounded).val.id).val = .val (wmod payloads.length) := by
    have length : target.mem (base' (grown payloads bounded).val.id).val =
        .val (wmod ((grown payloads bounded).heap.len (grown payloads bounded).val .dyn)) :=
      (allocated.heap.arrays .dyn (grown payloads bounded).val).length rfl
    rw [sourceLength] at length
    exact length
  change base' (grown payloads bounded).val.id = wmod 40 at rootAt
  rw [rootAt] at header
  refine ⟨base',target,ran,?_,?_,header,below 17 (by decide) (by decide),?_,?_,?_⟩
  · simpa only [values,List.length_map] using allocated
  · refine allocated.free.cell.trans ?_
    apply congrArg Word.val
    apply Fin.ext
    simp only [values,List.length_map,wmod_def,Nat.mod_eq_of_lt (show 40 < W by decide),Nat.add_assoc]
    exact (Nat.mod_eq_of_lt fits).symm
  · rw [shape]
  · exact congrArg Machine.stack shape
  · intro index payload selected
    have item : (MObj.elems .dyn ((grown payloads bounded).heap.get (grown payloads bounded).val))[index]? = some (indexValue payload) := by
      dsimp only [grown,value]
      rw [primitive_array_source]
      simp only [Grown.alloc,Heap.get_alloc,MObj.elems_dyn,MObj.wk,primitiveArrayObject,MVal.wk,values,
        List.getElem?_map,selected,Option.map_some]
    have contents : ReprV .uint (indexValue payload) (target.mem ((base' (grown payloads bounded).val.id).val + 1 + index)) :=
      (allocated.heap.arrays .dyn (grown payloads bounded).val).elements index (indexValue payload) item
    obtain ⟨word,stored,equal⟩ := contents
    have same : word = payload := Fin.ext (Int.ofNat_inj.mp equal.symm)
    subst word
    rw [rootAt] at stored
    exact stored

theorem empty_runtime : ∃ target : Machine,
    run checkedStorageArrayCode ((machine []).push (.slot source)) = .ok (target.push w[40]) 0 ∧
      target.mem 0 = w[41] ∧ target.mem 40 = w[0] ∧ target.mem 17 = w[7] := by
  obtain ⟨_,target,ran,_,cursor,length,old,_,_,_⟩ := actual_runtime [] (by decide) (by decide)
  exact ⟨target,ran,cursor,length,old⟩

theorem pair_runtime (left right : Fin W) : ∃ target : Machine,
    run checkedStorageArrayCode ((machine [left,right]).push (.slot source)) = .ok (target.push w[40]) 0 ∧
      target.mem 0 = w[43] ∧ target.mem 40 = w[2] ∧ target.mem 41 = .val left ∧ target.mem 42 = .val right ∧ target.mem 17 = w[7] := by
  obtain ⟨_,target,ran,_,cursor,length,old,_,_,contents⟩ :=
    actual_runtime [left,right] (by change 2 < 128; decide) (by change 40 + (2 + 1) < W; decide)
  exact ⟨target,ran,cursor,length,contents 0 left rfl,contents 1 right rfl,old⟩

private def long : List (Fin W) := List.ofFn (fun index : Fin 64 => wmod (index.val + 1))

theorem long_runtime : ∃ target : Machine,
    run checkedStorageArrayCode ((machine long).push (.slot source)) = .ok (target.push w[40]) 0 ∧
      target.mem 0 = w[105] ∧ target.mem 40 = w[64] ∧ target.mem 41 = w[1] ∧ target.mem 104 = w[64] ∧ target.mem 17 = w[7] := by
  obtain ⟨_,target,ran,_,cursor,length,old,_,_,contents⟩ :=
    actual_runtime long (by rw [long,List.length_ofFn]; decide) (by rw [long,List.length_ofFn]; decide)
  exact ⟨target,ran,cursor,length,contents 0 (wmod 1) (by decide +kernel),contents 63 (wmod 64) (by decide +kernel),old⟩

theorem source_fresh (payloads : List (Fin W)) (bounded : payloads.length < 128)
    {R : RefTy} (old : HRef input.H R) : old.id < (grown payloads bounded).val.id :=
  Nat.lt_of_lt_of_le old.id_lt (SVal.copyStToM_id_ge input.heap (value payloads bounded) rfl)

theorem wrong_zero (target : Machine)
    (ran : run checkedStorageArrayCode ((machine [wmod 11,wmod 23]).push (.slot source)) = .ok (target.push w[40]) 0) :
    target.mem 42 ≠ w[0] := by
  obtain ⟨actual,execution,_,_,_,second,_⟩ := pair_runtime (wmod 11) (wmod 23)
  rw [ran] at execution
  have same : target.mem 42 = actual.mem 42 := congrArg (fun machine => machine.mem 42) (Out.ok.inj execution).1
  rw [same,second]
  decide

theorem wrong_header_rejected :
    ¬ ReprAt (machine [wmod 11,wmod 23]).store 128 (.ref (.array (.prim .uint))) source
      (primitiveArrayValue .uint [] (by decide)) := by
  intro proposed
  cases proposed with
  | array header bound elements =>
    change (2 : Nat) = 0 at header
    cases header

theorem room_boundary_refused : ¬ ((W - 2) + (2 + 1) < W) := by omega

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
private theorem moved_representation (payloads : List (Fin W)) (bounded : payloads.length < 128) (cursor : Fin W) :
    ReprAt (moved payloads cursor).store 128 (.ref (.array (.prim .uint))) source (value payloads bounded) :=
  represented payloads bounded

theorem saturated_refusal (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    run checkedStorageArrayCode ((moved payloads wMax).push (.slot source)) = .revert := by
  rw [checked_storage_array_run input.heap .uint (values payloads)
    (by rw [values,List.length_map]; exact Nat.lt_trans bounded wide) input.base 8 wMax (moved payloads wMax) source 128
    (moved_allocator payloads wMax (by decide)) (moved_representation payloads bounded wMax)]
  apply if_neg
  change ¬ (W - 1 + (_ + 1) < W)
  have positive : 0 < W := W_pos
  omega

theorem empty_saturated_refusal : run checkedStorageArrayCode ((moved [] wMax).push (.slot source)) = .revert :=
  saturated_refusal [] (by decide)

private theorem cursor_value (n : Nat) (positive : 0 < n) (bounded : n ≤ W) :
    (wmod (W - n)).val = W - n := Nat.mod_eq_of_lt (by omega)
private theorem cursor_above (n : Nat) (positive : 0 < n) (bounded : n ≤ 128) : 40 ≤ (wmod (W - n)).val := by
  have large : 256 < W := by decide
  rw [cursor_value n positive (by omega)]
  omega

theorem pair_boundary_refusal :
    run checkedStorageArrayCode ((moved [wmod 11,wmod 23] (wmod (W - 3))).push (.slot source)) = .revert := by
  rw [checked_storage_array_run input.heap .uint (values [wmod 11,wmod 23]) (by decide) input.base 8 (wmod (W - 3))
    (moved [wmod 11,wmod 23] (wmod (W - 3))) source 128
    (moved_allocator _ _ (cursor_above 3 (by decide) (by decide))) (moved_representation _ (by decide) _),cursor_value 3 (by decide) (by decide)]
  apply if_neg
  change ¬ (W - 3 + (2 + 1) < W)
  have large : 3 ≤ W := by decide
  omega

theorem pair_last_fitting : ∃ fits,
    CheckedStorageArrayResult input.heap .uint (values [wmod 11,wmod 23]) (by decide) input.base 8 (wmod (W - 4))
      (moved [wmod 11,wmod 23] (wmod (W - 4))) source fits := by
  have fits : (wmod (W - 4)).val + ((values [wmod 11,wmod 23]).length + 1) < W := by
    rw [cursor_value 4 (by decide) (by decide)]
    change W - 4 + (2 + 1) < W
    have large : 4 ≤ W := by decide
    omega
  exact ⟨fits,checked_storage_array_success input.heap .uint _ (by decide) input.base 8 _ _ source 128
    (moved_allocator _ _ (cursor_above 4 (by decide) (by decide))) (moved_representation _ (by decide) _) fits⟩

theorem header_selects_capacity :
    (∃ fits, CheckedStorageArrayResult input.heap .uint (values []) (by decide) input.base 8 (wmod (W - 3))
      (moved [] (wmod (W - 3))) source fits) ∧
    run checkedStorageArrayCode ((moved [wmod 11,wmod 23] (wmod (W - 3))).push (.slot source)) = .revert := by
  have fits : (wmod (W - 3)).val + ((values []).length + 1) < W := by
    rw [cursor_value 3 (by decide) (by decide)]
    change W - 3 + (0 + 1) < W
    have large : 3 ≤ W := by decide
    omega
  exact ⟨⟨fits,checked_storage_array_success input.heap .uint _ (by decide) input.base 8 _ _ source 128
    (moved_allocator _ _ (cursor_above 3 (by decide) (by decide))) (moved_representation _ (by decide) _) fits⟩,pair_boundary_refusal⟩

#print axioms certificate_inhabited
#print axioms actual_runtime
#print axioms empty_runtime
#print axioms pair_runtime
#print axioms long_runtime
#print axioms source_fresh
#print axioms wrong_zero
#print axioms wrong_header_rejected
#print axioms room_boundary_refused
#print axioms saturated_refusal
#print axioms empty_saturated_refusal
#print axioms pair_boundary_refusal
#print axioms pair_last_fitting
#print axioms header_selects_capacity
end Solidity.Backend.MemoryCopies.CheckedStorageArrayControls
