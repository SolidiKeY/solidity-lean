import Solidity.Backend.MemoryCopies.CheckedFixedMemory

/-! Actual fixed copies have no header, preserve old pointer aliases and
reserve one cell even when their static payload length is zero. -/
namespace Solidity.Backend.MemoryCopies.CheckedFixedMemoryControls
open Evm Evm.Memory
private def R (count : Nat) : RefTy := .fixed (.prim .uint) count
private def H (count : Nat) : HTy := [R count]
private def old (count : Nat) : HRef (H count) (R count) := ⟨0,rfl⟩
private def values (payloads : List (Fin W)) : List PrimTy.uint.Denote := payloads.map indexValue
private theorem wide : 256 < W := by decide
private def heap (payloads : List (Fin W)) : Heap (H payloads.length) :=
  (⟨values payloads,by rw [values,List.length_map]⟩,())
private def bases : Nat → Fin W := fun _ => wmod 16
private def machine (payloads : List (Fin W)) : Machine :=
  {Machine.init with stack := [w[77]],mem := fun address =>
    if address = 0 then w[256] else if address = 1 ∨ address = 2 then w[16]
    else if address = 7 then w[99]
    else if 16 ≤ address ∧ address < 16 + payloads.length then .val (payloads[address - 16]?.getD (wmod 0)) else w[0]}
private theorem refs {count : Nat} {Q : RefTy} (reference : HRef (H count) Q) : Q = R count ∧ HEq reference (old count) := by
  rcases reference with ⟨index,selected⟩
  cases index with
  | zero => cases selected; exact ⟨rfl,HEq.rfl⟩
  | succ index => cases selected
private theorem snapshot (payloads : List (Fin W)) :
    MVal.copyMToSt (heap payloads) (T := .ref (R payloads.length)) (old payloads.length) =
      fixedPrimitiveValue .uint payloads.length (values payloads) (by rw [values,List.length_map]) := by
  rw [primitiveFixed_snapshot]
  with_unfolding_all rfl
private theorem heap_repr (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.HeapRepr (heap payloads) bases 8 (machine payloads) := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
  · intro Q reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    change 8 ≤ 16
    decide
  · intro Q reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    have large : 256 < W := wide
    with_unfolding_all change 16 + max 1 payloads.length ≤ W
    omega
  · intro Q S left right different
    obtain ⟨rfl,leftEq⟩ := refs left
    obtain ⟨rfl,rightEq⟩ := refs right
    cases leftEq
    cases rightEq
    exact (different rfl).elim
  · intro A E shape reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    cases shape
    refine ⟨?_,?_,?_⟩
    · have large : 256 < W := wide
      with_unfolding_all change 16 + max 1 payloads.length ≤ W
      omega
    · intro impossible
      cases impossible
    · intro index item selected
      with_unfolding_all change (values payloads)[index]? = some item at selected
      simp only [values,List.getElem?_map] at selected
      cases chosen : payloads[index]? with
      | none => simp only [chosen,Option.map_none] at selected; cases selected
      | some payload =>
        simp only [chosen,Option.map_some] at selected
        cases selected
        have lower : index < payloads.length := lt_of_getElem? chosen
        change ReprV .uint (indexValue payload) ((machine payloads).mem (16 + index))
        simp only [machine,if_neg (show 16 + index ≠ 0 by omega),
          if_neg (show ¬(16 + index = 1 ∨ 16 + index = 2) by omega),if_neg (show 16 + index ≠ 7 by omega),
          if_pos (show 16 ≤ 16 + index ∧ 16 + index < 16 + payloads.length by omega),
          Nat.add_sub_cancel_left,chosen,Option.getD_some]
        exact ReprV.uint_of rfl
  · intro name reference
    obtain ⟨different,_⟩ := refs reference
    cases different
  · intro name field Q reference fieldType
    obtain ⟨different,_⟩ := refs reference
    cases different
private theorem allocator (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.AllocatorRepr (heap payloads) bases 8 (wmod 256) (machine payloads) := by
  refine ⟨heap_repr payloads bounded,⟨by decide,by decide,rfl,?_⟩,?_⟩
  · intro address above
    change 256 ≤ address at above
    simp only [machine,if_neg (show address ≠ 0 by omega),
      if_neg (show ¬(address = 1 ∨ address = 2) by omega),if_neg (show address ≠ 7 by omega),
      if_neg (show ¬(16 ≤ address ∧ address < 16 + payloads.length) by omega)]
  · intro Q reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    with_unfolding_all change 16 + max 1 payloads.length ≤ 256
    omega
private def grown (payloads : List (Fin W)) :=
  (MVal.copyMToSt (heap payloads) (T := .ref (R payloads.length)) (old payloads.length)).copyStToM (heap payloads) rfl

theorem certificate_inhabited : CheckedFixedMemoryCertificate := checkedFixedMemory

theorem actual_runtime (payloads : List (Fin W)) (bounded : payloads.length < 128)
    (fits : 256 + max 1 payloads.length < W) :
    ∃ (base' : Nat → Fin W) (target : Machine),
      run (checkedFixedMemoryCode payloads.length) ((machine payloads).push w[16]) = .ok (target.push w[256]) 0 ∧
      Objects.AllocatorRepr (grown payloads).heap base' 8 ⟨256 + max 1 payloads.length,fits⟩ target ∧
      target.mem 0 = .val (wmod (256 + max 1 payloads.length)) ∧ target.mem 1 = w[16] ∧ target.mem 2 = w[16] ∧
      target.mem 7 = w[99] ∧ target.stack = [w[77]] ∧ target.store = (machine payloads).store ∧
      (∀ (index : Nat) (payload : Fin W), payloads[index]? = some payload →
        target.mem (256 + index) = .val payload ∧ target.mem (16 + index) = .val payload) := by
  obtain ⟨base',target,ran,allocated,root,_,shape,below,_,_,_⟩ :=
    checked_fixed_memory_success (heap payloads) .uint payloads.length (old payloads.length) bases 8
      (wmod 256) (machine payloads) (allocator payloads bounded) fits
  change base' (grown payloads).val.id = wmod 256 at root
  refine ⟨base',target,ran,allocated,?_,below 1 (by decide) (by decide),
    below 2 (by decide) (by decide),below 7 (by decide) (by decide),congrArg Machine.stack shape,?_,?_⟩
  · refine allocated.free.cell.trans ?_
    apply congrArg Word.val
    apply Fin.ext
    change 256 + max 1 payloads.length = (256 + max 1 payloads.length) % W
    exact (Nat.mod_eq_of_lt fits).symm
  · rw [shape]
  · intro index payload selected
    have lower : index < payloads.length := lt_of_getElem? selected
    have item : (MObj.elems .fixed ((grown payloads).heap.get (grown payloads).val))[index]? = some (indexValue payload) := by
      dsimp only [grown]
      rw [snapshot,fixed_primitive_source]
      simp only [Grown.alloc,Heap.get_alloc,MObj.elems_fixed,MObj.wk,fixedPrimitiveObject,MVal.wk,
        values,List.getElem?_map,selected,Option.map_some]
    have contents : ReprV .uint (indexValue payload) (target.mem ((base' (grown payloads).val.id).val + 0 + index)) :=
      (allocated.heap.arrays .fixed (grown payloads).val).elements index (indexValue payload) item
    obtain ⟨word,stored,equal⟩ := contents
    have same : word = payload := Fin.ext (Int.ofNat_inj.mp equal.symm)
    subst word
    rw [root] at stored
    refine ⟨stored,?_⟩
    rw [below (16 + index) (by omega) (by change 16 + index < 256; omega)]
    simp only [machine,if_neg (show 16 + index ≠ 0 by omega),
      if_neg (show ¬(16 + index = 1 ∨ 16 + index = 2) by omega),if_neg (show 16 + index ≠ 7 by omega),
      if_pos (show 16 ≤ 16 + index ∧ 16 + index < 16 + payloads.length by omega),
      Nat.add_sub_cancel_left,selected,Option.getD_some]

theorem pair_runtime (left right : Fin W) : ∃ target : Machine,
    run (checkedFixedMemoryCode 2) ((machine [left,right]).push w[16]) = .ok (target.push w[256]) 0 ∧
      target.mem 0 = w[258] ∧ target.mem 256 = .val left ∧ target.mem 257 = .val right ∧
      target.mem 16 = .val left ∧ target.mem 17 = .val right ∧ target.mem 1 = w[16] ∧ target.mem 2 = w[16] := by
  obtain ⟨_,target,ran,_,cursor,first,second,_,_,_,contents⟩ :=
    actual_runtime [left,right] (by change 2 < 128; decide) (by change 256 + max 1 2 < W; decide)
  exact ⟨target,ran,cursor,(contents 0 left rfl).1,(contents 1 right rfl).1,
    (contents 0 left rfl).2,(contents 1 right rfl).2,first,second⟩

theorem empty_runtime : ∃ target : Machine,
    run (checkedFixedMemoryCode 0) ((machine []).push w[16]) = .ok (target.push w[256]) 0 ∧
      target.mem 0 = w[257] ∧ target.mem 1 = w[16] ∧ target.mem 2 = w[16] := by
  obtain ⟨_,target,ran,_,cursor,first,second,_,_,_,_⟩ := actual_runtime [] (by decide) (by decide)
  exact ⟨target,ran,cursor,first,second⟩
private def long : List (Fin W) := List.ofFn (fun index : Fin 64 => wmod (index.val + 1))
theorem long_runtime : ∃ target : Machine,
    run (checkedFixedMemoryCode 64) ((machine long).push w[16]) = .ok (target.push w[256]) 0 ∧
      target.mem 0 = w[320] ∧ target.mem 319 = w[64] ∧ target.mem 79 = w[64] ∧ target.mem 1 = w[16] := by
  obtain ⟨_,target,ran,_,cursor,first,_,_,_,_,contents⟩ :=
    actual_runtime long (by rw [long,List.length_ofFn]; decide) (by rw [long,List.length_ofFn]; decide)
  exact ⟨target,ran,cursor,(contents 63 (wmod 64) (by decide +kernel)).1,
    (contents 63 (wmod 64) (by decide +kernel)).2,first⟩

theorem header_word_rejected (target : Machine)
    (ran : run (checkedFixedMemoryCode 2) ((machine [wmod 11,wmod 23]).push w[16]) = .ok (target.push w[256]) 0) :
    target.mem 256 ≠ w[2] := by
  obtain ⟨actual,execution,_,first,_,_,_,_,_⟩ := pair_runtime (wmod 11) (wmod 23)
  rw [ran] at execution
  have same : target.mem 256 = actual.mem 256 := congrArg (fun state => state.mem 256) (Out.ok.inj execution).1
  rw [same,first]
  decide

theorem no_old_alias_result (target : Machine)
    (ran : run (checkedFixedMemoryCode 0) ((machine []).push w[16]) = .ok (target.push w[16]) 0) : False := by
  obtain ⟨actual,execution,_,_,_⟩ := empty_runtime
  rw [ran] at execution
  have stack : (target.push w[16]).stack = (actual.push w[256]).stack := congrArg Machine.stack (Out.ok.inj execution).1
  have pointers : w[16] = w[256] := List.cons.inj stack |>.1
  cases pointers

theorem empty_reservation_required (target : Machine)
    (ran : run (checkedFixedMemoryCode 0) ((machine []).push w[16]) = .ok (target.push w[256]) 0) : target.mem 0 ≠ w[256] := by
  obtain ⟨actual,execution,cursor,_,_⟩ := empty_runtime
  rw [ran] at execution
  have same : target.mem 0 = actual.mem 0 := congrArg (fun state => state.mem 0) (Out.ok.inj execution).1
  rw [same,cursor]
  decide

theorem room_boundary_refused : ¬ ((W - 1) + max 1 0 < W) := by omega

#print axioms certificate_inhabited
#print axioms actual_runtime
#print axioms pair_runtime
#print axioms empty_runtime
#print axioms long_runtime
#print axioms header_word_rejected
#print axioms no_old_alias_result
#print axioms empty_reservation_required
#print axioms room_boundary_refused

private def moved (payloads : List (Fin W)) (cursor : Fin W) : Machine := writeMachine (machine payloads) 0 (.val cursor)
private theorem moved_allocator (payloads : List (Fin W)) (bounded : payloads.length < 128)
    (cursor : Fin W) (above : 256 ≤ cursor.val) :
    Objects.AllocatorRepr (heap payloads) bases 8 cursor (moved payloads cursor) := by
  have initial : Objects.AllocatorRepr (heap payloads) bases 8 (wmod 256) (machine payloads) := allocator payloads bounded
  refine ⟨initial.heap.localWrite 0 (by decide) (.val cursor),⟨by decide,by omega,?_,?_⟩,?_⟩
  · rfl
  · intro address lower
    exact (upd_other _ _ (by omega : address ≠ 0)).trans (initial.free.zero address (by change 256 ≤ address; omega))
  · intro Q reference
    have live : (bases reference.id).val + Objects.cells (heap payloads) reference ≤ 256 := initial.live reference
    omega

theorem saturated_input (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.AllocatorRepr (heap payloads) bases 8 wMax (moved payloads wMax) ∧
    (moved payloads wMax).mem 1 = w[16] ∧ (moved payloads wMax).mem 2 = w[16] :=
  ⟨moved_allocator payloads bounded wMax (by decide),rfl,rfl⟩

theorem saturated_refusal (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.AllocatorRepr (heap payloads) bases 8 wMax (moved payloads wMax) ∧
    run (checkedFixedMemoryCode payloads.length) ((moved payloads wMax).push w[16]) = .revert := by
  have allocated : Objects.AllocatorRepr (heap payloads) bases 8 wMax (moved payloads wMax) :=
    moved_allocator payloads bounded wMax (by decide)
  refine ⟨allocated,?_⟩
  rw [checked_fixed_memory_run payloads.length (moved payloads wMax) wMax ⟨16,by decide⟩ allocated.free.cell]
  apply if_neg
  change ¬ (W - 1 + max 1 payloads.length < W)
  have positive : 0 < W := W_pos
  omega

theorem empty_saturated_refusal :
    run (checkedFixedMemoryCode 0) ((moved [] wMax).push w[16]) = .revert :=
  (saturated_refusal [] (by decide)).2

private theorem cursor_value (n : Nat) (positive : 0 < n) (bounded : n ≤ W) :
    (wmod (W - n)).val = W - n := Nat.mod_eq_of_lt (by omega)
private theorem cursor_above (n : Nat) (positive : 0 < n) (bounded : n ≤ 128) : 256 ≤ (wmod (W - n)).val := by
  have large : 1024 < W := by decide
  rw [cursor_value n positive (by omega)]
  omega

theorem pair_boundary_refusal :
    run (checkedFixedMemoryCode 2) ((moved [wmod 11,wmod 23] (wmod (W - 2))).push w[16]) = .revert := by
  have allocated : Objects.AllocatorRepr (heap [wmod 11,wmod 23]) bases 8 (wmod (W - 2))
      (moved [wmod 11,wmod 23] (wmod (W - 2))) :=
    moved_allocator [wmod 11,wmod 23] (by decide) _ (cursor_above 2 (by decide) (by decide))
  rw [checked_fixed_memory_run 2 (moved [wmod 11,wmod 23] (wmod (W - 2))) (wmod (W - 2)) ⟨16,by decide⟩
    allocated.free.cell,cursor_value 2 (by decide) (by decide)]
  apply if_neg
  have large : 2 ≤ W := by decide
  change ¬ (W - 2 + max 1 2 < W)
  omega

theorem pair_last_fitting : ∃ fits,
    CheckedFixedMemoryResult (heap [wmod 11,wmod 23]) .uint 2 (old 2) bases 8 (wmod (W - 3))
      (moved [wmod 11,wmod 23] (wmod (W - 3))) fits := by
  have fits : (wmod (W - 3)).val + max 1 2 < W := by
    rw [cursor_value 3 (by decide) (by decide)]
    have large : 3 ≤ W := by decide
    omega
  exact ⟨fits,checked_fixed_memory_success (heap [wmod 11,wmod 23]) .uint 2 (old 2) bases 8 (wmod (W - 3))
    (moved [wmod 11,wmod 23] (wmod (W - 3)))
    (moved_allocator [wmod 11,wmod 23] (by decide) _ (cursor_above 3 (by decide) (by decide))) fits⟩

theorem fixed_count_selects_capacity :
    (∃ fits, CheckedFixedMemoryResult (heap []) .uint 0 (old 0) bases 8 (wmod (W - 2))
      (moved [] (wmod (W - 2))) fits) ∧
    run (checkedFixedMemoryCode 2) ((moved [wmod 11,wmod 23] (wmod (W - 2))).push w[16]) = .revert := by
  have fits : (wmod (W - 2)).val + max 1 0 < W := by
    rw [cursor_value 2 (by decide) (by decide)]
    have large : 2 ≤ W := by decide
    omega
  exact ⟨⟨fits,checked_fixed_memory_success (heap []) .uint 0 (old 0) bases 8 (wmod (W - 2))
    (moved [] (wmod (W - 2)))
    (moved_allocator [] (by decide) _ (cursor_above 2 (by decide) (by decide))) fits⟩,pair_boundary_refusal⟩

/-- Code-only refusal: this constructs no represented object of size W. -/
theorem huge_code_only_refusal :
    run (checkedFixedMemoryCode W) ((machine []).push w[16]) = .revert :=
  checked_fixed_memory_large_code W (by omega) (machine []) (wmod 256) (wmod 16) rfl

#print axioms saturated_input
#print axioms saturated_refusal
#print axioms empty_saturated_refusal
#print axioms pair_boundary_refusal
#print axioms pair_last_fitting
#print axioms fixed_count_selects_capacity
#print axioms huge_code_only_refusal
end Solidity.Backend.MemoryCopies.CheckedFixedMemoryControls
