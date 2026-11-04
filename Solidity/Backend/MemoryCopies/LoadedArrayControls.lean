import Solidity.Backend.MemoryCopies.LoadedArray
import Solidity.Evm.Correct

/-! Actual represented storage reads feed populated arrays. Pair code is
independent of payloads; long controls use repeated reads of an actual value. -/
namespace Solidity.Backend.MemoryCopies.LoadedArrayControls
open Evm Evm.Memory Semantics
private abbrev leaf : RefTy := .array (.prim .uint)
private def C : Contract := {vars := [("items",.ref leaf)]}
private def root : C.rootType "items" = some (.ref leaf) := by decide +kernel
private def values (payloads : List (Fin W)) : List PrimTy.uint.Denote := payloads.map indexValue
private def array (payloads : List (Fin W)) (bounded : payloads.length < 128) : SVal (.ref leaf) :=
  primitiveArrayValue .uint (values payloads) (by
    have length : (values payloads).length = payloads.length := List.length_map _
    have wide : 128 < W := by decide
    omega)
private def state (payloads : List (Fin W)) (bounded : payloads.length < 128) : State C [] :=
  {State.init C with storage := .cons (array payloads bounded) .nil}
private def store (payloads : List (Fin W)) : WordStore := ⟨fun slot => match slot with
  | .root 0 => wmod payloads.length
  | .data (.root 0) index => payloads[index]?.getD (wmod 0)
  | _ => wmod 0⟩
private def machine (payloads : List (Fin W)) : Machine :=
  {Machine.init with
    store := store payloads
    stack := [w[77]]
    mem := fun address => if address = 0 then w[40] else if address = 7 then w[99] else w[0]}
private def bases : Nat → Fin W := fun _ => wmod 0
private def path : SPath C [] (.ref leaf) := .loc (.root "items" root)
private def reference : SRef C (.ref leaf) := SRef.ofRoot "items" root
private def expression (index : Nat) : Val C [] .uint :=
  .read (.index (.arr .dyn) path (.simple (.lit (indexValue (wmod index)).val (indexValue (wmod index)).property)))
private def pairExpressions : List (Val C [] .uint) := [expression 0,expression 1]
private theorem noRefs {R : RefTy} (reference : HRef [] R) : False := by
  simpa only [List.getElem?_nil,reduceCtorEq] using reference.get?

private theorem storage_repr (payloads : List (Fin W)) (bounded : payloads.length < 128) :
    ReprStore C 128 (store payloads) (state payloads bounded).storage := by
  intro name type found
  change (if name = "items" then some (.ref leaf) else none) = some type at found
  split at found
  · rename_i same
    subst name
    cases found
    change ReprAt (store payloads) 128 (.ref leaf) (.root 0) (array payloads bounded)
    refine .array ?_ (by simpa only [values,List.length_map] using bounded) ?_
    · simp only [values,List.length_map]
      change payloads.length % W = payloads.length
      exact Nat.mod_eq_of_lt (Nat.lt_trans bounded (by decide))
    · intro index item selected
      simp only [SVec.toList_ofList,values,List.getElem?_map] at selected
      cases chosen : payloads[index]? with
      | none => simp only [chosen,Option.map_none] at selected; cases selected
      | some payload =>
        simp only [chosen,Option.map_some] at selected
        cases selected
        simp only [size_prim,Nat.mul_one]
        change ReprAt (store payloads) 128 (.prim .uint) (.data (.root 0) index) (.prim (indexValue payload))
        refine .prim (ReprV.uint_of ?_)
        simp only [store,chosen,Option.getD_some]
        rfl
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

private theorem pair_inputs (left right : Fin W) :
    PrimitiveLoadInputs (Frag.init []) (state [left,right] (by change 2 < 128; decide)) pairExpressions (values [left,right]) := by
  refine ⟨?_,by with_unfolding_all rfl⟩
  intro e member
  rcases List.mem_cons.mp member with same | member
  · subst e; rfl
  · rcases List.mem_cons.mp member with same | member
    · subst e; rfl
    · cases member

private theorem repeated_inputs (payloads : List (Fin W)) (bounded : payloads.length < 128)
    (e : Val C [] .uint) (value : PrimTy.uint.Denote) (count : Nat)
    (supported : valIn (Frag.init []) e = true) (evaluated : e.evalT (state payloads bounded) = .ok value) :
    PrimitiveLoadInputs (Frag.init []) (state payloads bounded) (List.replicate count e) (List.replicate count value) := by
  refine ⟨?_,?_⟩
  · intro selected member
    have equal : selected = e := List.eq_of_mem_replicate member
    rw [equal]
    exact supported
  · induction count with
    | zero => rfl
    | succ count ih => simp only [List.replicate_succ,List.mapM_cons,evaluated,ih,bind,Except.bind,pure,Except.pure]

theorem certificate_inhabited : LoadedArrayCertificate := loadedArray

theorem actual_declaration (payloads : List (Fin W)) (bounded : payloads.length < 128)
    (expressions : List (Val C [] .uint))
    (inputs : PrimitiveLoadInputs (Frag.init []) (state payloads bounded) expressions (values payloads))
    (fits : 40 + (payloads.length + 1) < W) :
    ∃ target : Machine, run (loadedArrayDeclareCode 1 expressions) (machine payloads) = .ok target 0 ∧
      target.mem 0 = .val (wmod (40 + payloads.length + 1)) ∧ target.mem 1 = w[40] ∧
      target.mem 40 = .val (wmod payloads.length) ∧ target.mem 7 = w[99] ∧ target.stack = [w[77]] ∧
      (∀ (index : Nat) (payload : Fin W), payloads[index]? = some payload → target.mem (41 + index) = .val payload) := by
  let grown := (array payloads bounded).copyStToM (state payloads bounded).heap rfl
  obtain ⟨base',target,_,ran,_,allocated,_,stack,rootAt,localAt,below⟩ :=
    loaded_array_declaration expressions (values payloads) (by
      have length : (values payloads).length = payloads.length := List.length_map _
      have wide : 128 < W := by decide
      omega)
      (state payloads bounded) bases (wmod 40) (machine payloads) (represented payloads bounded) (allocator payloads)
      (by decide) inputs path reference rfl rfl (by simpa only [values,List.length_map] using fits) (by decide)
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
  refine ⟨target,ran,?_,localAt,header,below 7 (by decide) (by decide) (by decide),stack,?_⟩
  · refine allocated.free.cell.trans ?_
    apply congrArg Word.val
    apply Fin.ext
    simp only [values,List.length_map,wmod_def,Nat.mod_eq_of_lt (show 40 < W by decide),
      Nat.add_assoc]
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

theorem pair_loaded (left right : Fin W) :
    ∃ target : Machine, run (loadedArrayDeclareCode 1 pairExpressions) (machine [left,right]) = .ok target 0 ∧
      target.mem 0 = w[43] ∧ target.mem 1 = w[40] ∧ target.mem 40 = w[2] ∧
      target.mem 41 = .val left ∧ target.mem 42 = .val right ∧ target.mem 7 = w[99] ∧ target.stack = [w[77]] := by
  obtain ⟨target,ran,cursor,localAt,length,reserved,stack,contents⟩ :=
    actual_declaration [left,right] (by change 2 < 128; decide) pairExpressions (pair_inputs left right) (by change 40 + (2 + 1) < W; decide)
  exact ⟨target,ran,cursor,localAt,length,contents 0 left rfl,contents 1 right rfl,reserved,stack⟩

theorem pair_source (left right : Fin W) :
    let grown := (array [left,right] (by change 2 < 128; decide)).copyStToM (state [left,right] (by change 2 < 128; decide)).heap rfl
    TRun.declMem leaf (some (.copy path rfl)) rfl (state [left,right] (by change 2 < 128; decide)) =
      .ok ⟨((state [left,right] (by change 2 < 128; decide)).adopt grown).1.push (t := .mem leaf) (some grown.val),grown.ext⟩ :=
  storage_array_decl (state [left,right] (by change 2 < 128; decide)) path reference (values [left,right]) (by change 2 < W; decide) rfl rfl

theorem empty_loaded : ∃ target : Machine,
    run (loadedArrayDeclareCode 1 ([] : List (Val C [] .uint))) (machine []) = .ok target 0 ∧
    target.mem 0 = w[41] ∧ target.mem 40 = w[0] := by
  obtain ⟨target,ran,cursor,_,length,_,_,_⟩ := actual_declaration [] (by decide) [] ⟨(fun _ member => by cases member),rfl⟩ (by decide)
  exact ⟨target,ran,cursor,length⟩

theorem long_loaded (payload : Fin W) : ∃ target : Machine,
    run (loadedArrayDeclareCode 1 (List.replicate 64 (expression 0))) (machine (List.replicate 64 payload)) = .ok target 0 ∧
    target.mem 0 = w[105] ∧ target.mem 40 = w[64] ∧ target.mem 104 = .val payload ∧ target.mem 7 = w[99] := by
  have evaluated : (expression 0).evalT (state (List.replicate 64 payload) (by rw [List.length_replicate]; decide)) = .ok (indexValue payload) := by
    with_unfolding_all rfl
  have inputs : PrimitiveLoadInputs (Frag.init []) (state (List.replicate 64 payload) (by rw [List.length_replicate]; decide))
      (List.replicate 64 (expression 0)) (values (List.replicate 64 payload)) := by
    simpa only [values,List.map_replicate] using repeated_inputs (List.replicate 64 payload) (by rw [List.length_replicate]; decide) (expression 0) (indexValue payload) 64 rfl evaluated
  obtain ⟨target,ran,cursor,_,length,reserved,_,contents⟩ :=
    actual_declaration (List.replicate 64 payload) (by rw [List.length_replicate]; decide) _ inputs (by rw [List.length_replicate]; decide)
  exact ⟨target,ran,cursor,length,contents 63 payload rfl,reserved⟩

theorem wrong_zero (target : Machine)
    (ran : run (loadedArrayDeclareCode 1 pairExpressions) (machine [wmod 11,wmod 23]) = .ok target 0) : target.mem 42 ≠ w[0] := by
  obtain ⟨actual,execution,_,_,_,_,second,_,_⟩ := pair_loaded (wmod 11) (wmod 23)
  rw [ran] at execution
  cases execution
  rw [second]
  decide

theorem failed_expression (left right : Fin W) :
    (expression 2).evalT (state [left,right] (by change 2 < 128; decide)) = .error .revert := by
  with_unfolding_all rfl

theorem failed_load (left right : Fin W) :
    run (loadedArrayCode 1 (expression 2 :: pairExpressions)) (machine [left,right]) = .revert :=
  loaded_array_head_refusal (state [left,right] (by change 2 < 128; decide)) (expression 2) pairExpressions (values [left,right])
    (machine [left,right]) (core [left,right] (by change 2 < 128; decide)) (pair_inputs left right) rfl (failed_expression left right)

#print axioms certificate_inhabited
#print axioms actual_declaration
#print axioms pair_loaded
#print axioms pair_source
#print axioms empty_loaded
#print axioms long_loaded
#print axioms wrong_zero
#print axioms failed_expression
#print axioms failed_load
end Solidity.Backend.MemoryCopies.LoadedArrayControls
