import Solidity.Backend.MemoryCopies.CanonicalArray
import Solidity.Evm.Correct

/-! Canonical paths select all actual storage indices, including distinct long
payloads. The guard rejects invalid outer paths even for an empty array. -/
namespace Solidity.Backend.MemoryCopies.CanonicalArrayControls
open Evm Evm.Memory Semantics
private abbrev leaf : RefTy := .array (.prim .uint)
private def C : Contract := {vars := [("matrix",.ref (.array (.ref leaf)))]}
private def root : C.rootType "matrix" = some (.ref (.array (.ref leaf))) := by decide +kernel
private def values (payloads : List (Fin W)) : List PrimTy.uint.Denote := payloads.map indexValue
private def wide : 128 < W := by decide
private def array (payloads : List (Fin W)) (bounded : payloads.length < 128) : SVal (.ref leaf) :=
  primitiveArrayValue .uint (values payloads) (by rw [values,List.length_map]; exact Nat.lt_trans bounded wide)
private def matrix (payloads : List (Fin W)) (bounded : payloads.length < 128) : SVal (.ref (.array (.ref leaf))) :=
  .array (.cons (array payloads bounded) .nil) .nil (by decide)
private def state (payloads : List (Fin W)) (bounded : payloads.length < 128) : State C [] :=
  {State.init C with storage := .cons (matrix payloads bounded) .nil}
private def store (payloads : List (Fin W)) : WordStore := ⟨fun slot => match slot with
  | .root 0 => wmod 1
  | .data (.root 0) 0 => wmod payloads.length
  | .data (.data (.root 0) 0) index => payloads[index]?.getD (wmod 0)
  | _ => wmod 0⟩
private def machine (payloads : List (Fin W)) : Machine :=
  {Machine.init with
    store := store payloads
    stack := [w[77]]
    mem := fun address => if address = 0 then w[40] else if address = 7 then w[99] else w[0]}
private def bases : Nat → Fin W := fun _ => wmod 0
private def path (index : Nat) : SPath C [] (.ref leaf) :=
  .loc (.index (.arr .dyn) (.loc (.root "matrix" root))
    (.simple (.lit (indexValue (wmod index)).val (indexValue (wmod index)).property)))
private def reference : SRef C (.ref leaf) := (SRef.ofRoot "matrix" root).index (.arr .dyn) (indexValue (wmod 0))
private def code (count : Nat) (bounded : count < 128) : List Instr :=
  canonicalArrayCode 1 (path 0) count (Nat.lt_trans bounded wide)
private theorem noRefs {R : RefTy} (reference : HRef [] R) : False := by
  simpa only [List.getElem?_nil,reduceCtorEq] using reference.get?

private theorem leaf_repr (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    ReprAt (store payloads) 128 (.ref leaf) (.data (.root 0) 0) (array payloads bounded) := by
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
      simp only [store,chosen,Option.getD_some]
      rfl

private theorem storage_repr (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    ReprStore C 128 (store payloads) (state payloads bounded).storage := by
  intro name type found
  change (if name = "matrix" then some (.ref (.array (.ref leaf))) else none) = some type at found
  split at found
  · rename_i same
    subst name
    cases found
    change ReprAt (store payloads) 128 (.ref (.array (.ref leaf))) (.root 0) (matrix payloads bounded)
    refine .array rfl (by decide) ?_
    intro index item selected
    simp only [SVec.toList_cons,SVec.toList_nil] at selected
    cases index with
    | zero => cases selected; exact leaf_repr payloads bounded
    | succ index => simp only [List.getElem?_cons_succ,List.getElem?_nil] at selected; cases selected
  · cases found

private theorem core (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Sim C 128 1 (Frag.init []) (state payloads bounded) (machine payloads) := by
  have initial : Sim C 1 0 (Frag.init []) (freshT C 0 W_pos ⟨0,W_pos⟩) (Machine.init (fun _ => 0) ⟨0,W_pos⟩) :=
    Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl
  exact ⟨storage_repr payloads bounded,(fun index => nomatch index),(fun index => nomatch index),
    initial.net,initial.netSelf,by unfold Lmax; decide,(fun index => nomatch index),initial.env,initial.funds,initial.oracle⟩
private theorem heap_repr (payloads : List (Fin W)) : Objects.HeapRepr (Heap.empty) bases 8 (machine payloads) :=
  ⟨⟨fun reference => (noRefs reference).elim,fun reference => (noRefs reference).elim,
    fun reference _ _ => (noRefs reference).elim⟩,
    (fun _ reference => (noRefs reference).elim),(fun reference => (noRefs reference).elim),
    (fun reference _ => (noRefs reference).elim)⟩
private theorem represented (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    Objects.StateRepr 128 1 8 (Frag.init []) (state payloads bounded) bases (machine payloads) :=
  ⟨core payloads bounded,heap_repr payloads,(fun index => nomatch index),by decide⟩
private theorem allocator (payloads : List (Fin W)) : Objects.AllocatorRepr Heap.empty bases 8 (wmod 40) (machine payloads) := by
  refine ⟨heap_repr payloads,⟨by decide,by decide,rfl,?_⟩,fun reference => (noRefs reference).elim⟩
  intro address above
  change 40 ≤ address at above
  simp only [machine,if_neg (show address ≠ 0 by omega),if_neg (show address ≠ 7 by omega)]

private theorem resolved (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    (path 0).resolveT (state payloads bounded) = .ok reference := by with_unfolding_all rfl
private theorem found (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    (state payloads bounded).storage.find reference = some (array payloads bounded) := by with_unfolding_all rfl

theorem certificate_inhabited : CanonicalArrayCertificate := canonicalArray

theorem derived_inputs (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    PrimitiveLoadInputs (Frag.init []) (state payloads bounded)
      (canonicalArrayExpressions (path 0) (values payloads).length (by rw [values,List.length_map]; exact Nat.lt_trans bounded wide))
      (values payloads) :=
  canonical_array_inputs (Frag.init []) (state payloads bounded) (path 0) reference (values payloads)
    (by rw [values,List.length_map]; exact Nat.lt_trans bounded wide) rfl (resolved payloads bounded) (found payloads bounded)

theorem actual_declaration (payloads : List (Fin W)) (bounded : payloads.length < 128)
    (fits : 40 + (payloads.length + 1) < W) :
    ∃ target : Machine, run (code payloads.length bounded) (machine payloads) = .ok target 0 ∧
      target.mem 0 = .val (wmod (40 + payloads.length + 1)) ∧ target.mem 1 = w[40] ∧
      target.mem 40 = .val (wmod payloads.length) ∧ target.mem 7 = w[99] ∧ target.stack = [w[77]] ∧
      (∀ (index : Nat) (payload : Fin W), payloads[index]? = some payload → target.mem (41 + index) = .val payload) := by
  let grown := (array payloads bounded).copyStToM (state payloads bounded).heap rfl
  obtain ⟨base',target,_,ran,_,allocated,_,stack,rootAt,localAt,below⟩ :=
    canonical_array_declaration (state payloads bounded) bases (wmod 40) (machine payloads) (path 0) reference
      (values payloads) (by rw [values,List.length_map]; exact Nat.lt_trans bounded wide)
      (represented payloads bounded) (allocator payloads) (by decide) rfl (resolved payloads bounded) (found payloads bounded)
      (by simpa only [values,List.length_map] using fits) (by decide)
  have sourceLength : grown.heap.len grown.val .dyn = payloads.length := by
    dsimp only [grown,array]
    rw [primitive_array_source]
    simp only [Grown.alloc,Heap.len,Heap.get_alloc,MObj.elems_dyn,MObj.wk,primitiveArrayObject,values,List.length_map]
  have header : target.mem (base' grown.val.id).val = .val (wmod payloads.length) := by
    have length : target.mem (base' grown.val.id).val = .val (wmod (grown.heap.len grown.val .dyn)) :=
      (allocated.heap.arrays .dyn grown.val).length rfl
    rw [sourceLength] at length
    exact length
  change base' grown.val.id = wmod 40 at rootAt
  rw [rootAt] at header
  refine ⟨target,?_,?_,localAt,header,below 7 (by decide) (by decide) (by decide),stack,?_⟩
  · simpa only [code,values,List.length_map] using ran
  · refine allocated.free.cell.trans ?_
    apply congrArg Word.val
    apply Fin.ext
    simp only [values,List.length_map,wmod_def,Nat.mod_eq_of_lt (show 40 < W by decide),Nat.add_assoc]
    exact (Nat.mod_eq_of_lt fits).symm
  · intro index payload selected
    have item : (MObj.elems .dyn (grown.heap.get grown.val))[index]? = some (indexValue payload) := by
      dsimp only [grown,array]
      rw [primitive_array_source]
      simp only [Grown.alloc,Heap.get_alloc,MObj.elems_dyn,MObj.wk,primitiveArrayObject,MVal.wk,values,
        List.getElem?_map,selected,Option.map_some]
    have contents : ReprV .uint (indexValue payload) (target.mem ((base' grown.val.id).val + 1 + index)) :=
      (allocated.heap.arrays .dyn grown.val).elements index (indexValue payload) item
    obtain ⟨word,stored,equal⟩ := contents
    have same : word = payload := Fin.ext (Int.ofNat_inj.mp equal.symm)
    subst word
    rw [rootAt] at stored
    exact stored

theorem pair_copy (left right : Fin W) :
    ∃ target : Machine, run (code 2 (by decide)) (machine [left,right]) = .ok target 0 ∧
      target.mem 0 = w[43] ∧ target.mem 40 = w[2] ∧ target.mem 41 = .val left ∧ target.mem 42 = .val right ∧
      target.mem 7 = w[99] ∧ target.stack = [w[77]] := by
  obtain ⟨target,ran,cursor,_,length,reserved,stack,contents⟩ :=
    actual_declaration [left,right] (by change 2 < 128; decide) (by change 40 + (2 + 1) < W; decide)
  exact ⟨target,ran,cursor,length,contents 0 left rfl,contents 1 right rfl,reserved,stack⟩

theorem empty_copy : ∃ target : Machine, run (code 0 (by decide)) (machine []) = .ok target 0 ∧
    target.mem 0 = w[41] ∧ target.mem 40 = w[0] := by
  obtain ⟨target,ran,cursor,_,length,_,_,_⟩ := actual_declaration [] (by decide) (by decide)
  exact ⟨target,ran,cursor,length⟩

private def long : List (Fin W) := List.ofFn (fun index : Fin 64 => wmod (index.val + 1))

theorem distinct_long_copy : ∃ target : Machine, run (code 64 (by decide)) (machine long) = .ok target 0 ∧
    target.mem 0 = w[105] ∧ target.mem 40 = w[64] ∧ target.mem 41 = w[1] ∧ target.mem 104 = w[64] ∧ target.mem 7 = w[99] := by
  obtain ⟨target,ran,cursor,_,length,reserved,_,contents⟩ :=
    actual_declaration long (by rw [long,List.length_ofFn]; decide) (by rw [long,List.length_ofFn]; decide)
  exact ⟨target,ran,cursor,length,contents 0 (wmod 1) (by decide +kernel),contents 63 (wmod 64) (by decide +kernel),reserved⟩

theorem source_copy (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    let grown := (array payloads bounded).copyStToM (state payloads bounded).heap rfl
    TRun.declMem leaf (some (.copy (path 0) rfl)) rfl (state payloads bounded) =
      .ok ⟨((state payloads bounded).adopt grown).1.push (t := .mem leaf) (some grown.val),grown.ext⟩ :=
  storage_array_decl (state payloads bounded) (path 0) reference (values payloads)
    (by rw [values,List.length_map]; exact Nat.lt_trans bounded wide) (resolved payloads bounded) (found payloads bounded)

theorem invalid_path (payloads : List (Fin W)) (bounded : payloads.length < 128)
    (count : Nat) (countBound : count < W) :
    TRun.declMem leaf (some (.copy (path 1) rfl)) rfl (state payloads bounded) = .error .revert ∧
    run (canonicalArrayCode 1 (path 1) count countBound) (machine payloads) = .revert :=
  canonical_array_refusal (state payloads bounded) (machine payloads) (path 1) count countBound
    (core payloads bounded) rfl (by with_unfolding_all rfl)

theorem invalid_empty : run (canonicalArrayCode 1 (path 1) 0 (by decide)) (machine []) = .revert :=
  (invalid_path [] (by decide) 0 (by decide)).2

theorem wrong_zero (target : Machine)
    (ran : run (code 2 (by decide)) (machine [wmod 11,wmod 23]) = .ok target 0) : target.mem 42 ≠ w[0] := by
  obtain ⟨actual,execution,_,_,_,second,_,_⟩ := pair_copy (wmod 11) (wmod 23)
  rw [ran] at execution
  cases execution
  rw [second]
  decide

#print axioms certificate_inhabited
#print axioms derived_inputs
#print axioms actual_declaration
#print axioms pair_copy
#print axioms empty_copy
#print axioms distinct_long_copy
#print axioms source_copy
#print axioms invalid_path
#print axioms invalid_empty
#print axioms wrong_zero
end Solidity.Backend.MemoryCopies.CanonicalArrayControls
