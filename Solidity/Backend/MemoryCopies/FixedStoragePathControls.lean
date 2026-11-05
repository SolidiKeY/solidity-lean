import Solidity.Backend.MemoryCopies.FixedStoragePath
import Solidity.Evm.Correct

/-! Nested storage paths select represented fixed children and bind fresh
headerless copies while old memory aliases and failed paths stay observable. -/
namespace Solidity.Backend.MemoryCopies.FixedStoragePathControls
open Evm Evm.Memory Semantics
private def R (count : Nat) : RefTy := .fixed (.prim .uint) count
private def H (count : Nat) : HTy := [R count]
private def old (count : Nat) : HRef (H count) (R count) := ⟨0,rfl⟩
private def values (payloads : List (Fin W)) : List PrimTy.uint.Denote := payloads.map indexValue
private theorem wide : 256 < W := by decide
private def heap (payloads : List (Fin W)) : Heap (H payloads.length) :=
  (⟨values payloads,by rw [values,List.length_map]⟩,())
private def bases : Nat → Fin W := fun _ => wmod 16
private def store (payloads : List (Fin W)) : WordStore := ⟨fun slot => match slot with
  | .root 0 => wmod 1
  | .data (.root 0) index => payloads[index]?.getD (wmod 0)
  | _ => wmod 71⟩
private def machine (payloads : List (Fin W)) : Machine :=
  {Machine.init with store := store payloads,stack := [w[77]],mem := fun address =>
    if address = 0 then w[256] else if address = 1 ∨ address = 2 then w[16]
    else if address = 7 then w[99]
    else if 16 ≤ address ∧ address < 16 + payloads.length then .val (payloads[address - 16]?.getD (wmod 0)) else w[0]}
private theorem refs {count : Nat} {Q : RefTy} (reference : HRef (H count) Q) : Q = R count ∧ HEq reference (old count) := by
  rcases reference with ⟨index,selected⟩
  cases index with
  | zero => cases selected; exact ⟨rfl,HEq.rfl⟩
  | succ index => cases selected
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

private def C (count : Nat) : Contract := {vars := [("matrix",.ref (.array (.ref (R count))))],vars_ok := by rfl,vars_nodup := by rfl}
private def Γ (count : Nat) : Ctx := [.mem (R count),.mem (R count)]
private def root (count : Nat) : (C count).rootType "matrix" = some (.ref (.array (.ref (R count)))) := by rfl
private def value (payloads : List (Fin W)) : SVal (.ref (R payloads.length)) :=
  fixedPrimitiveValue .uint payloads.length (values payloads) (by rw [values,List.length_map])
private def matrix (payloads : List (Fin W)) : SVal (.ref (.array (.ref (R payloads.length)))) :=
  .array (.cons (value payloads) .nil) .nil (by decide)
private def state (payloads : List (Fin W)) : State (C payloads.length) (Γ payloads.length) :=
  {storage := .cons (matrix payloads) .nil,H := H payloads.length,heap := heap payloads,
    env := (some (old payloads.length),(some (old payloads.length),()))}
private def path (count index : Nat) : SPath (C count) (Γ count) (.ref (R count)) :=
  .loc (.index (.arr .dyn) (.loc (.root "matrix" (root count)))
    (.simple (.lit (indexValue (wmod index)).val (indexValue (wmod index)).property)))
private def reference (count : Nat) : SRef (C count) (.ref (R count)) :=
  (SRef.ofRoot "matrix" (root count)).index (.arr .dyn) (indexValue (wmod 0))
private def destination (count : Nat) : Idx (Γ count) (.mem (R count)) := .there .here
private theorem leaf_repr (payloads : List (Fin W)) :
    ReprAt (store payloads) 128 (.ref (R payloads.length)) (.data (.root 0) 0) (value payloads) := by
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
    simp only [store,Slot.add,Nat.zero_add,chosen,Option.getD_some]
    rfl
private theorem storage_repr (payloads : List (Fin W)) :
    ReprStore (C payloads.length) 128 (store payloads) (state payloads).storage := by
  intro name type found
  change (if name = "matrix" then some (.ref (.array (.ref (R payloads.length)))) else none) = some type at found
  split at found
  · rename_i same
    subst name
    cases found
    change ReprAt (store payloads) 128 (.ref (.array (.ref (R payloads.length)))) (.root 0) (matrix payloads)
    refine .array rfl (by decide) ?_
    intro index item selected
    simp only [SVec.toList_cons,SVec.toList_nil] at selected
    cases index with
    | zero => cases selected; simpa only [Nat.zero_mul] using leaf_repr payloads
    | succ index => simp only [List.getElem?_cons_succ,List.getElem?_nil] at selected; cases selected
  · cases found
private theorem core (payloads : List (Fin W)) :
    Sim (C payloads.length) 128 1 (Frag.init (Γ payloads.length)) (state payloads) (machine payloads) := by
  have initial : Sim (C payloads.length) 1 0 (Frag.init []) (freshT (C payloads.length) 0 W_pos ⟨0,W_pos⟩)
      (Machine.init (fun _ => 0) ⟨0,W_pos⟩) := Sim.init (C payloads.length) 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  refine ⟨storage_repr payloads,?_,?_,initial.net,initial.netSelf,by unfold Lmax; decide,?_,initial.env,initial.funds,initial.oracle⟩
  all_goals intro p index
  all_goals cases index with
    | there index => cases index with
      | there index => nomatch index
private theorem represented (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.StateRepr 128 1 8 (Frag.init (Γ payloads.length)) (state payloads) bases (machine payloads) := by
  refine ⟨core payloads,heap_repr payloads bounded,?_,by change 1 + 2 ≤ 8; decide⟩
  intro Q index
  cases index with
  | here => exact ⟨old payloads.length,rfl,rfl⟩
  | there index => cases index with
    | here => exact ⟨old payloads.length,rfl,rfl⟩
    | there index => nomatch index
private theorem resolved (payloads : List (Fin W)) :
    (path payloads.length 0).resolveT (state payloads) = .ok (reference payloads.length) := by with_unfolding_all rfl
private theorem found (payloads : List (Fin W)) :
    (state payloads).storage.find (reference payloads.length) = some (value payloads) := by with_unfolding_all rfl
private def grown (payloads : List (Fin W)) := (value payloads).copyStToM (heap payloads) rfl
private def after (payloads : List (Fin W)) :=
  ((state payloads).adopt (grown payloads)).1.setLocal (destination payloads.length) (some (grown payloads).val)
private theorem payload_observations (payloads : List (Fin W)) (base' : Nat → Fin W) (target : Machine)
    (fits : 256 + max 1 payloads.length < W)
    (allocated : Objects.AllocatorRepr (grown payloads).heap base' 8 ⟨256 + max 1 payloads.length,fits⟩ target)
    (rootAt : base' (grown payloads).val.id = wmod 256) :
    ∀ (index : Nat) (payload : Fin W), payloads[index]? = some payload → target.mem (256 + index) = .val payload := by
  intro index payload selected
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

theorem certificate_inhabited : FixedStoragePathCertificate := fixedStoragePath

theorem declaration (payloads : List (Fin W)) (bounded : payloads.length < 128) (fits : 256 + max 1 payloads.length < W) :
    ∃ target : Machine, run (fixedStoragePathDeclareCode 1 (path payloads.length 0)) (machine payloads) = .ok target 0 ∧
      target.mem 0 = .val (wmod (256 + max 1 payloads.length)) ∧ target.mem 3 = w[256] ∧
      target.mem 1 = w[16] ∧ target.mem 2 = w[16] ∧ target.mem 7 = w[99] ∧ target.stack = [w[77]] ∧
      (∀ (index : Nat) (payload : Fin W), payloads[index]? = some payload → target.mem (256 + index) = .val payload) := by
  obtain ⟨base',target,_,ran,_,allocated,_,stack,rootAt,localAt,below⟩ :=
    fixed_storage_path_declaration (state payloads) bases (wmod 256) (machine payloads) (path payloads.length 0)
      (reference payloads.length) (value payloads) (represented payloads bounded) (allocator payloads bounded)
      (by decide) rfl (resolved payloads) (found payloads) fits (by change 1 + (2 + 1) ≤ 8; decide)
  change base' (grown payloads).val.id = wmod 256 at rootAt
  refine ⟨target,ran,?_,localAt,below 1 (by decide) (by decide) (by change 1 ≠ 3; decide),below 2 (by decide) (by decide) (by change 2 ≠ 3; decide),
    below 7 (by decide) (by decide) (by change 7 ≠ 3; decide),stack,payload_observations payloads base' target fits allocated rootAt⟩
  refine allocated.free.cell.trans ?_
  apply congrArg Word.val
  apply Fin.ext
  exact (Nat.mod_eq_of_lt fits).symm

theorem rebinding (payloads : List (Fin W)) (bounded : payloads.length < 128) (fits : 256 + max 1 payloads.length < W) :
    ∃ target : Machine, run (fixedStoragePathRebindCode 1 (destination payloads.length) (path payloads.length 0)) (machine payloads) = .ok target 0 ∧
      target.mem 0 = .val (wmod (256 + max 1 payloads.length)) ∧ target.mem 1 = w[256] ∧ target.mem 2 = w[16] ∧
      target.mem 7 = w[99] ∧ target.stack = [w[77]] ∧
      (∀ (index : Nat) (payload : Fin W), payloads[index]? = some payload → target.mem (256 + index) = .val payload) := by
  obtain ⟨base',target,_,ran,_,allocated,_,stack,rootAt,localAt,below,_,_⟩ :=
    fixed_storage_path_rebind (state payloads) bases (wmod 256) (machine payloads) (destination payloads.length)
      (path payloads.length 0) (reference payloads.length) (value payloads) (represented payloads bounded) (allocator payloads bounded)
      (by decide) rfl (resolved payloads) (found payloads) fits
  change base' (grown payloads).val.id = wmod 256 at rootAt
  refine ⟨target,ran,?_,localAt,below 2 (by decide) (by decide) (by change 2 ≠ 1; decide),
    below 7 (by decide) (by decide) (by change 7 ≠ 1; decide),stack,payload_observations payloads base' target fits allocated rootAt⟩
  refine allocated.free.cell.trans ?_
  apply congrArg Word.val
  apply Fin.ext
  exact (Nat.mod_eq_of_lt fits).symm

theorem old_source_alias (payloads : List (Fin W)) :
    TEnv.get (.here : Idx (Γ payloads.length) (.mem (R payloads.length))) (after payloads).env =
      some ((old payloads.length).wk (grown payloads).ext) := by with_unfolding_all rfl

theorem actual_source_rebinding (payloads : List (Fin W)) :
    TRun.rebindMem (destination payloads.length) (.copy (path payloads.length 0) rfl) (state payloads) =
      .ok ⟨after payloads,(grown payloads).ext⟩ :=
  fixed_storage_path_rebind_source (state payloads) (destination payloads.length) (path payloads.length 0)
    (reference payloads.length) (value payloads) (resolved payloads) (found payloads)

theorem pair_declaration (left right : Fin W) : ∃ target : Machine,
    run (fixedStoragePathDeclareCode 1 (path 2 0)) (machine [left,right]) = .ok target 0 ∧
      target.mem 0 = w[258] ∧ target.mem 3 = w[256] ∧ target.mem 256 = .val left ∧ target.mem 257 = .val right ∧ target.mem 2 = w[16] := by
  obtain ⟨target,ran,cursor,localAt,_,alias,_,_,contents⟩ := declaration [left,right] (by change 2 < 128; decide) (by change 256 + max 1 2 < W; decide)
  exact ⟨target,ran,cursor,localAt,contents 0 left rfl,contents 1 right rfl,alias⟩

theorem empty_rebind : ∃ target : Machine,
    run (fixedStoragePathRebindCode 1 (destination 0) (path 0 0)) (machine []) = .ok target 0 ∧
      target.mem 0 = w[257] ∧ target.mem 1 = w[256] ∧ target.mem 2 = w[16] := by
  obtain ⟨target,ran,cursor,localAt,alias,_,_,_⟩ := rebinding [] (by decide) (by decide)
  exact ⟨target,ran,cursor,localAt,alias⟩

private def long : List (Fin W) := List.ofFn (fun index : Fin 64 => wmod (index.val + 1))
theorem long_rebind : ∃ target : Machine,
    run (fixedStoragePathRebindCode 1 (destination 64) (path 64 0)) (machine long) = .ok target 0 ∧
      target.mem 0 = w[320] ∧ target.mem 1 = w[256] ∧ target.mem 2 = w[16] ∧ target.mem 319 = w[64] := by
  obtain ⟨target,ran,cursor,localAt,alias,_,_,contents⟩ :=
    rebinding long (by rw [long,List.length_ofFn]; decide) (by rw [long,List.length_ofFn]; decide)
  exact ⟨target,ran,cursor,localAt,alias,contents 63 (wmod 64) (by decide +kernel)⟩

theorem invalid_declaration (payloads : List (Fin W)) :
    TRun.declMem (R payloads.length) (some (.copy (path payloads.length 1) rfl)) rfl (state payloads) = .error .revert ∧
      run (fixedStoragePathDeclareCode 1 (path payloads.length 1)) (machine payloads) = .revert :=
  fixed_storage_path_declaration_refusal (state payloads) (machine payloads) (path payloads.length 1) (core payloads) rfl (by with_unfolding_all rfl)

theorem invalid_rebind (payloads : List (Fin W)) :
    TRun.rebindMem (destination payloads.length) (.copy (path payloads.length 1) rfl) (state payloads) = .error .revert ∧
      run (fixedStoragePathRebindCode 1 (destination payloads.length) (path payloads.length 1)) (machine payloads) = .revert :=
  fixed_storage_path_rebind_refusal (state payloads) (machine payloads) (destination payloads.length)
    (path payloads.length 1) (core payloads) rfl (by with_unfolding_all rfl)

theorem invalid_empty : run (fixedStoragePathDeclareCode 1 (path 0 1)) (machine []) = .revert := (invalid_declaration []).2

theorem old_pointer_rejected (target : Machine)
    (ran : run (fixedStoragePathRebindCode 1 (destination 0) (path 0 0)) (machine []) = .ok target 0) : target.mem 1 ≠ w[16] := by
  obtain ⟨actual,execution,_,fresh,_⟩ := empty_rebind
  rw [ran] at execution
  have same : target.mem 1 = actual.mem 1 := congrArg (fun m => m.mem 1) (Out.ok.inj execution).1
  rw [same,fresh]
  decide

theorem header_rejected (target : Machine)
    (ran : run (fixedStoragePathDeclareCode 1 (path 2 0)) (machine [wmod 11,wmod 23]) = .ok target 0) : target.mem 256 ≠ w[2] := by
  obtain ⟨actual,execution,_,_,first,_,_⟩ := pair_declaration (wmod 11) (wmod 23)
  rw [ran] at execution
  have same : target.mem 256 = actual.mem 256 := congrArg (fun m => m.mem 256) (Out.ok.inj execution).1
  rw [same,first]
  decide

#print axioms certificate_inhabited
#print axioms declaration
#print axioms rebinding
#print axioms old_source_alias
#print axioms actual_source_rebinding
#print axioms pair_declaration
#print axioms empty_rebind
#print axioms long_rebind
#print axioms invalid_declaration
#print axioms invalid_rebind
#print axioms invalid_empty
#print axioms old_pointer_rejected
#print axioms header_rejected
end Solidity.Backend.MemoryCopies.FixedStoragePathControls
