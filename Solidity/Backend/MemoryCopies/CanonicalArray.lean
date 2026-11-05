import Solidity.Backend.MemoryCopies.CanonicalArrayInterface

/-! Every selected array index is derived from the actual copied path and
lookup. The existing compiled path guard executes even when count is zero. -/
namespace Solidity.Backend.MemoryCopies
open Evm Evm.Memory

theorem canonical_array_supported {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (frag : Frag Γ) (path : SPath C Γ (.ref (.array (.prim primitive)))) (index : Fin W)
    (supported : spathIn frag false path = true) : valIn frag (canonicalArrayExpression path index) = true := by
  change (true && spathIn frag false path && true) = true
  rw [supported]
  rfl

theorem canonical_array_evaluation {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (state : State C Γ) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (reference : SRef C (.ref (.array (.prim primitive)))) (values : List primitive.Denote)
    (bounded : values.length < W) (index : Fin W) (value : primitive.Denote)
    (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (primitiveArrayValue primitive values bounded))
    (selected : values[index.val]? = some value) :
    (canonicalArrayExpression path index).evalT state = .ok value := by
  have lower : index.val < values.length := lt_of_getElem? selected
  have checked : state.storage.checkIndex reference (.arr .dyn) (indexValue index) = some () := by
    rw [Storage.checkIndex,found]
    simp only [bind,Option.bind,Storage.inBounds,primitiveArrayValue,SVal.view_array,indexValue,Int.toNat_natCast,
      List.length_map,if_pos lower]
  have indexed : state.storage.find (reference.index (.arr .dyn) (indexValue index)) = some (.prim value) := by
    rw [SRef.index,Storage.find_appendM,found]
    simp only [Option.bind_some,Path.index,SVal.findM,primitiveArrayValue,SVec.toList_ofList,SList.toList_nil,
      List.append_nil,indexValue,Int.toNat_natCast,List.getElem?_map,selected,Option.map_some]
  dsimp only [indexValue] at checked indexed
  simp only [canonicalArrayExpression,indexValue,Val.evalT,Loc.resolveT,resolved,Simple.evalT,PrimTy.ofLit,
    checked,indexed,TRes.ofOpt,bind,Except.bind,pure,Except.pure,SVal.view_prim]

private theorem pointwise_loads_evaluation {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (state : State C Γ) (expressions : List (Val C Γ primitive)) (values : List primitive.Denote)
    (length : expressions.length = values.length)
    (pointwise : ∀ (index : Nat) (expression : Val C Γ primitive) (value : primitive.Denote),
      expressions[index]? = some expression → values[index]? = some value → expression.evalT state = .ok value) :
    expressions.mapM (fun expression => expression.evalT state) = .ok values := by
  induction expressions generalizing values with
  | nil => cases values with
    | nil => rfl
    | cons value values => cases length
  | cons expression expressions ih =>
    cases values with
    | nil => cases length
    | cons value values =>
      have headEval : expression.evalT state = .ok value := pointwise 0 expression value rfl rfl
      have tailEval : expressions.mapM (fun e => e.evalT state) = .ok values :=
        ih values (Nat.succ.inj length) (fun index e v chosen selected => pointwise (index + 1) e v chosen selected)
      simp only [List.mapM_cons,headEval,tailEval,bind,Except.bind,pure,Except.pure]

theorem canonical_array_inputs {C : Contract} {Γ : Ctx} {primitive : PrimTy}
    (frag : Frag Γ) (state : State C Γ) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (reference : SRef C (.ref (.array (.prim primitive)))) (values : List primitive.Denote)
    (bounded : values.length < W) (supported : spathIn frag false path = true)
    (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (primitiveArrayValue primitive values bounded)) :
    PrimitiveLoadInputs frag state (canonicalArrayExpressions path values.length bounded) values := by
  refine ⟨?_,?_⟩
  · intro expression member
    obtain ⟨index,equal⟩ := List.mem_ofFn.mp member
    rw [← equal]
    exact canonical_array_supported frag path _ supported
  · apply pointwise_loads_evaluation state _ values (List.length_ofFn ..)
    intro index expression value chosen selected
    have lower : index < values.length := lt_of_getElem? selected
    simp only [List.getElem?_ofFn,dif_pos lower] at chosen
    cases chosen
    exact canonical_array_evaluation state path reference values bounded ⟨index,Nat.lt_trans lower bounded⟩ value resolved found selected

theorem canonical_array_guard {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (reference : SRef C (.ref (.array (.prim primitive)))) (represented : Sim C L b frag state machine)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference) :
    run (canonicalArrayGuardCode b path) machine = .ok machine 0 := by
  rcases spath_sim path represented supported with ⟨actual,slot,value,source,_,_,_,ran⟩ | ⟨refused,_⟩
  · rw [canonicalArrayGuardCode,run_append_ok ran]
    rfl
  · rw [resolved] at refused
    cases refused

theorem canonical_array_declaration {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b frame : Nat} {frag : Frag Γ}
    (state : State C Γ) (base : Nat → Fin W) (cursor : Fin W) (machine : Machine)
    (path : SPath C Γ (.ref (.array (.prim primitive)))) (reference : SRef C (.ref (.array (.prim primitive))))
    (values : List primitive.Denote) (bounded : values.length < W)
    (represented : Objects.StateRepr L b frame frag state base machine)
    (allocator : Objects.AllocatorRepr state.heap base frame cursor machine) (positive : 0 < b)
    (supported : spathIn frag false path = true) (resolved : path.resolveT state = .ok reference)
    (found : state.storage.find reference = some (primitiveArrayValue primitive values bounded))
    (fits : cursor.val + (values.length + 1) < W) (locals : b + (Γ.length + 1) ≤ frame) :
    CanonicalArrayResult L b frame frag state base cursor machine path values bounded fits := by
  obtain ⟨base',target,source,ran,reached,allocated,extension,stack,root,localAt,below⟩ :=
    loaded_array_declaration (canonicalArrayExpressions path values.length bounded) values bounded state base cursor machine
      represented allocator positive (canonical_array_inputs frag state path reference values bounded supported resolved found)
      path reference resolved found fits locals
  refine ⟨base',target,source,?_,reached,allocated,extension,stack,root,localAt,below⟩
  rw [canonicalArrayCode,run_append_ok (canonical_array_guard state machine path reference represented.core supported resolved)]
  exact ran

theorem canonical_array_refusal {C : Contract} {Γ : Ctx} {primitive : PrimTy} {L b : Nat} {frag : Frag Γ}
    (state : State C Γ) (machine : Machine) (path : SPath C Γ (.ref (.array (.prim primitive))))
    (count : Nat) (bounded : count < W) (represented : Sim C L b frag state machine)
    (supported : spathIn frag false path = true) (refused : path.resolveT state = .error .revert) :
    TRun.declMem (.array (.prim primitive)) (some (.copy path rfl)) rfl state = .error .revert ∧
    run (canonicalArrayCode b path count bounded) machine = .revert := by
  constructor
  · simp only [TRun.declMem,MRhs.evalT,refused,bind,Except.bind]
  · rcases spath_sim path represented supported with ⟨actual,slot,value,source,_,_,_,_⟩ | ⟨_,failed⟩
    · rw [refused] at source
      cases source
    · exact run_append_revert (run_append_revert failed)

def canonicalArray : CanonicalArrayCertificate :=
  ⟨canonical_array_inputs,canonical_array_declaration,canonical_array_refusal⟩

#print axioms canonical_array_supported
#print axioms canonical_array_evaluation
#print axioms canonical_array_inputs
#print axioms canonical_array_guard
#print axioms canonical_array_declaration
#print axioms canonical_array_refusal
#print axioms canonicalArray
end Solidity.Backend.MemoryCopies
