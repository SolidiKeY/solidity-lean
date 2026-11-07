import Solidity.Backend.MemoryCopies.RuntimeMemoryArray

/-! Actual runtime copies of populated, empty and long primitive arrays retain
old aliases and payloads while allocating a distinct represented object. -/
namespace Solidity.Backend.MemoryCopies.RuntimeMemoryArrayControls
open Evm Evm.Memory
private abbrev R : RefTy := .array (.prim .uint)
private abbrev H : HTy := [R]
private def old : HRef H R := ⟨0,rfl⟩
private def values (payloads : List (Fin W)) : List PrimTy.uint.Denote := payloads.map indexValue
private theorem wide : 256 < W := by decide
private def heap (payloads : List (Fin W)) (bounded : payloads.length < 128) : Heap H :=
  (⟨values payloads,by rw [values,List.length_map]; omega⟩,())
private theorem heap_length (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    (heap payloads bounded).len old .dyn = payloads.length := by
  with_unfolding_all change (values payloads).length = payloads.length
  rw [values,List.length_map]
private theorem snapshot (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    MVal.copyMToSt (heap payloads bounded) (T := .ref R) old =
      primitiveArrayValue .uint (values payloads) (by rw [values,List.length_map]; have large : 256 < W := wide; omega) := by
  rw [primitiveArray_snapshot]
  with_unfolding_all rfl
private def bases : Nat → Fin W := fun _ => wmod 16
private def machine (payloads : List (Fin W)) : Machine :=
  {Machine.init with stack := [w[77]],mem := fun address =>
    if address = 0 then w[256] else if address = 1 ∨ address = 2 then w[16]
    else if address = 7 then w[99] else if address = 16 then .val (wmod payloads.length)
    else if 17 ≤ address ∧ address < 17 + payloads.length then .val (payloads[address - 17]?.getD (wmod 0)) else w[0]}
private theorem refs {Q : RefTy} (reference : HRef H Q) : Q = R ∧ HEq reference old := by
  rcases reference with ⟨index,selected⟩
  cases index with
  | zero => cases selected; exact ⟨rfl,HEq.rfl⟩
  | succ index => cases selected
private theorem heap_repr (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.HeapRepr (heap payloads bounded) bases 8 (machine payloads) := by
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_⟩
  · intro Q reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    decide
  · intro Q reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    have large : 256 < W := wide
    with_unfolding_all change 16 + (1 + (values payloads).length) ≤ W
    rw [values,List.length_map]
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
      with_unfolding_all change 16 + (1 + (values payloads).length) ≤ W
      rw [values,List.length_map]
      omega
    · intro _
      with_unfolding_all change .val (wmod payloads.length) = Word.val (wmod (values payloads).length)
      rw [values,List.length_map]
    · intro index item selected
      with_unfolding_all change ((values payloads)[index]? = some item) at selected
      simp only [values,List.getElem?_map] at selected
      cases chosen : payloads[index]? with
      | none => simp only [chosen,Option.map_none] at selected; cases selected
      | some payload =>
        simp only [chosen,Option.map_some] at selected
        cases selected
        have lower : index < payloads.length := lt_of_getElem? chosen
        change ReprV .uint (indexValue payload) ((machine payloads).mem (17 + index))
        simp only [machine,if_neg (show 17 + index ≠ 0 by omega),
          if_neg (show ¬(17 + index = 1 ∨ 17 + index = 2) by omega),
          if_neg (show 17 + index ≠ 7 by omega),if_neg (show 17 + index ≠ 16 by omega),
          if_pos (show 17 ≤ 17 + index ∧ 17 + index < 17 + payloads.length by omega),
          Nat.add_sub_cancel_left,chosen,Option.getD_some]
        exact ReprV.uint_of rfl
  · intro name reference
    obtain ⟨different,_⟩ := refs reference
    cases different
  · intro name field Q reference fieldType
    obtain ⟨different,_⟩ := refs reference
    cases different
private theorem allocator (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.AllocatorRepr (heap payloads bounded) bases 8 (wmod 256) (machine payloads) := by
  refine ⟨heap_repr payloads bounded,⟨by decide,by decide,rfl,?_⟩,?_⟩
  · intro address above
    change 256 ≤ address at above
    simp only [machine,if_neg (show address ≠ 0 by omega),
      if_neg (show ¬(address = 1 ∨ address = 2) by omega),if_neg (show address ≠ 7 by omega),
      if_neg (show address ≠ 16 by omega),
      if_neg (show ¬(17 ≤ address ∧ address < 17 + payloads.length) by omega)]
  · intro Q reference
    obtain ⟨rfl,equal⟩ := refs reference
    cases equal
    with_unfolding_all change 16 + (1 + (values payloads).length) ≤ 256
    rw [values,List.length_map]
    omega
private def grown (payloads : List (Fin W)) (bounded : payloads.length < 128) :=
  (MVal.copyMToSt (heap payloads bounded) (T := .ref R) old).copyStToM (heap payloads bounded) rfl

theorem certificate_inhabited : RuntimeMemoryArrayCertificate := runtimeMemoryArray

theorem actual_runtime (payloads : List (Fin W)) (bounded : payloads.length < 128)
    (fits : 256 + (payloads.length + 1) < W) :
    ∃ (base' : Nat → Fin W) (target : Machine),
      run runtimeMemoryArrayCode ((machine payloads).push w[16]) = .ok (target.push w[256]) 0 ∧
      Objects.AllocatorRepr (grown payloads bounded).heap base' 8 ⟨256 + (payloads.length + 1),fits⟩ target ∧
      target.mem 0 = .val (wmod (256 + payloads.length + 1)) ∧
      target.mem 256 = .val (wmod payloads.length) ∧ target.mem 1 = w[16] ∧ target.mem 2 = w[16] ∧
      target.mem 7 = w[99] ∧ target.stack = [w[77]] ∧ target.store = (machine payloads).store ∧
      (∀ (index : Nat) (payload : Fin W), payloads[index]? = some payload →
        target.mem (257 + index) = .val payload ∧ target.mem (17 + index) = .val payload) := by
  obtain ⟨base',target,ran,allocated,root,_,shape,below,_,_,_⟩ :=
    runtime_memory_array_success (heap payloads bounded) .uint old bases 8 (wmod 256) (machine payloads)
      (allocator payloads bounded) (by simpa only [heap_length] using fits)
  have reached : Objects.AllocatorRepr (grown payloads bounded).heap base' 8 ⟨256 + (payloads.length + 1),fits⟩ target := by
    simpa only [heap_length] using allocated
  change base' (grown payloads bounded).val.id = wmod 256 at root
  have sourceLength : (grown payloads bounded).heap.len (grown payloads bounded).val .dyn = payloads.length := by
    dsimp only [grown]
    rw [snapshot,primitive_array_source]
    simp only [Grown.alloc,Heap.len,Heap.get_alloc,MObj.elems_dyn,MObj.wk,primitiveArrayObject,
      heap,values,List.length_map]
  have header : target.mem (base' (grown payloads bounded).val.id).val = .val (wmod payloads.length) := by
    have stored : target.mem (base' (grown payloads bounded).val.id).val =
        .val (wmod ((grown payloads bounded).heap.len (grown payloads bounded).val .dyn)) :=
      (allocated.heap.arrays .dyn (grown payloads bounded).val).length rfl
    rw [sourceLength] at stored
    exact stored
  rw [root] at header
  refine ⟨base',target,ran,reached,?_,header,below 1 (by decide) (by decide),below 2 (by decide) (by decide),
    below 7 (by decide) (by decide),congrArg Machine.stack shape,?_,?_⟩
  · refine reached.free.cell.trans ?_
    apply congrArg Word.val
    apply Fin.ext
    change 256 + (payloads.length + 1) = (256 + payloads.length + 1) % W
    exact (Nat.mod_eq_of_lt (by omega)).symm
  · rw [shape]
  · intro index payload selected
    have lower : index < payloads.length := lt_of_getElem? selected
    have item : (MObj.elems .dyn ((grown payloads bounded).heap.get (grown payloads bounded).val))[index]? = some (indexValue payload) := by
      dsimp only [grown]
      rw [snapshot,primitive_array_source]
      simp only [Grown.alloc,Heap.get_alloc,MObj.elems_dyn,MObj.wk,primitiveArrayObject,MVal.wk,
        heap,values,List.getElem?_map,selected,Option.map_some]
    have contents : ReprV .uint (indexValue payload) (target.mem ((base' (grown payloads bounded).val.id).val + 1 + index)) :=
      (allocated.heap.arrays .dyn (grown payloads bounded).val).elements index (indexValue payload) item
    obtain ⟨word,stored,equal⟩ := contents
    have same : word = payload := Fin.ext (Int.ofNat_inj.mp equal.symm)
    subst word
    rw [root] at stored
    refine ⟨stored,?_⟩
    rw [below (17 + index) (by omega) (by change 17 + index < 256; omega)]
    simp only [machine,if_neg (show 17 + index ≠ 0 by omega),
      if_neg (show ¬(17 + index = 1 ∨ 17 + index = 2) by omega),
      if_neg (show 17 + index ≠ 7 by omega),if_neg (show 17 + index ≠ 16 by omega),
      if_pos (show 17 ≤ 17 + index ∧ 17 + index < 17 + payloads.length by omega),
      Nat.add_sub_cancel_left,selected,Option.getD_some]

theorem pair_runtime (left right : Fin W) : ∃ target : Machine,
    run runtimeMemoryArrayCode ((machine [left,right]).push w[16]) = .ok (target.push w[256]) 0 ∧
      target.mem 0 = w[259] ∧ target.mem 257 = .val left ∧ target.mem 258 = .val right ∧
      target.mem 17 = .val left ∧ target.mem 18 = .val right ∧ target.mem 1 = w[16] ∧ target.mem 2 = w[16] := by
  obtain ⟨_,target,ran,_,cursor,_,first,second,_,_,_,contents⟩ := actual_runtime [left,right] (by change 2 < 128; decide) (by change 256 + (2 + 1) < W; decide)
  exact ⟨target,ran,cursor,(contents 0 left rfl).1,(contents 1 right rfl).1,
    (contents 0 left rfl).2,(contents 1 right rfl).2,first,second⟩

theorem empty_runtime : ∃ target : Machine,
    run runtimeMemoryArrayCode ((machine []).push w[16]) = .ok (target.push w[256]) 0 ∧
      target.mem 0 = w[257] ∧ target.mem 256 = w[0] ∧ target.mem 1 = w[16] ∧ target.mem 2 = w[16] := by
  obtain ⟨_,target,ran,_,cursor,header,first,second,_,_,_,_⟩ := actual_runtime [] (by decide) (by decide)
  exact ⟨target,ran,cursor,header,first,second⟩
private def long : List (Fin W) := List.ofFn (fun index : Fin 64 => wmod (index.val + 1))
theorem long_runtime : ∃ target : Machine,
    run runtimeMemoryArrayCode ((machine long).push w[16]) = .ok (target.push w[256]) 0 ∧
      target.mem 0 = w[321] ∧ target.mem 320 = w[64] ∧ target.mem 80 = w[64] ∧ target.mem 1 = w[16] := by
  obtain ⟨_,target,ran,_,cursor,_,first,_,_,_,_,contents⟩ :=
    actual_runtime long (by rw [long,List.length_ofFn]; decide) (by rw [long,List.length_ofFn]; decide)
  exact ⟨target,ran,cursor,(contents 63 (wmod 64) (by decide +kernel)).1,
    (contents 63 (wmod 64) (by decide +kernel)).2,first⟩

theorem wrong_zero (target : Machine)
    (ran : run runtimeMemoryArrayCode ((machine [wmod 11,wmod 23]).push w[16]) = .ok (target.push w[256]) 0) :
    target.mem 258 ≠ w[0] := by
  obtain ⟨actual,execution,_,_,second,_,_,_,_⟩ := pair_runtime (wmod 11) (wmod 23)
  rw [ran] at execution
  have same : target.mem 258 = actual.mem 258 := congrArg (fun state => state.mem 258) (Out.ok.inj execution).1
  rw [same,second]
  decide

theorem no_old_alias_result (target : Machine)
    (ran : run runtimeMemoryArrayCode ((machine []).push w[16]) = .ok (target.push w[16]) 0) : False := by
  obtain ⟨actual,execution,_,_,_,_⟩ := empty_runtime
  rw [ran] at execution
  have stack : (target.push w[16]).stack = (actual.push w[256]).stack := congrArg Machine.stack (Out.ok.inj execution).1
  have pointers : w[16] = w[256] := List.cons.inj stack |>.1
  cases pointers

theorem room_boundary_refused : ¬ ((W - 1) + (0 + 1) < W) := by omega

#print axioms certificate_inhabited
#print axioms actual_runtime
#print axioms pair_runtime
#print axioms empty_runtime
#print axioms long_runtime
#print axioms wrong_zero
#print axioms no_old_alias_result
#print axioms room_boundary_refused
end Solidity.Backend.MemoryCopies.RuntimeMemoryArrayControls
