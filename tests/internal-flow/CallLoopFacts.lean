import tests.«internal-flow».PublishedMemoryLoops

/-! Small kernel-checked facts about the unchanged call/loop fixture.
These imported theorem boundaries avoid reducing a whole compiler certificate
inside the dependent target endpoint. No compilation result is assumed. -/
namespace Solidity.Backend.InternalFlow.PublishedLoopChecks
open Evm Evm.Memory PublishedLoops

theorem callPrefix_cost : callBefore.cost (State.init C) = 4 := by decide +kernel
theorem callPrefix_frame : 1 + callBefore.need ≤ 64 := by decide +kernel
theorem callScope_frame : 1 + callScope.cert.need ≤ 64 := by decide +kernel
theorem callScope_nonalloc : callScope.cert.allocates = false := by decide +kernel

private theorem some_ref_of_id {H : HTy} (v : Option (HRef H A)) (r : HRef H A)
    (h : v.map (fun s => s.id) = some r.id) : v = some r := by
  cases v with
  | none => cases h
  | some t =>
    have same : t.id = r.id := Option.some.inj h
    have eq : t = r := by cases t; cases r; cases same; rfl
    exact congrArg some eq

theorem call_alias_first : TEnv.get (.here : Idx Caller (.mem A)) callEnd.st.env =
    some (returned.wk callEnd.ext) := some_ref_of_id _ _ (by decide +kernel)
theorem call_alias_second : TEnv.get (.there .here : Idx Caller (.mem A)) callEnd.st.env =
    some (returned.wk callEnd.ext) := some_ref_of_id _ _ (by decide +kernel)
theorem call_capacity : AllocationInput 1 64 (callBefore.cost (State.init C) + 0)
    (State.init C) bases machine := by
  rw [callPrefix_cost]
  exact .inr ⟨by decide,wmod 128,(initial_repr C).2,by decide +kernel⟩

/-- Actual target midpoint and final execution from the existing generic
producer, with no supplied midpoint representation or target preservation. -/
theorem call_target_reached : ∃ m₁ base₁ m₂ base₂ cost,
    run callBefore.code machine = .ok m₁ 0 ∧ run callScope.code m₁ = .ok m₂ 0 ∧
    run (callBefore.code ++ callScope.code) machine = .ok m₂ 0 ∧
    LoopScopes.Cost callScope.cert callMid.st callEnd cost ∧
    StateRepr 1 1 64 callBefore.frag callMid.st base₁ m₁ ∧
    StateRepr 1 1 64 callScope.frag callEnd.st base₂ m₂ ∧
    BaseExtends callMid.st.H base₁ base₂ ∧
    GrowsAllocator 1 64 cost callMid.st base₁ m₁ callEnd.st base₂ m₂ ∧
    m₂.stack = machine.stack ∧ BaseExtends (State.init C).H bases base₂ ∧
    GrowsAllocator 1 64 (callBefore.cost (State.init C) + cost)
      (State.init C) bases machine callEnd.st base₂ m₂ := by
  exact after_allocating_prefix callBefore callScope.cert (initial_repr C).1
    callPrefix_frame callScope_frame (budget := 0) call_capacity callMid call_prefix_actual
    (fun amount demand => Nat.le_of_eq (LoopScopes.demand_nonallocating callScope.cert callScope_nonalloc demand))
    callEnd call_scope_actual

/-- The private default object and actual source values are independently
observed in the reached heap; neither is inferred from target execution. -/
def callPrivate : HRef callMid.st.H A := ⟨0,by decide +kernel⟩
theorem call_private_length : callEnd.st.heap.len (callPrivate.wk callEnd.ext) .dyn = 0 := by decide +kernel
theorem call_returned_length : callEnd.st.heap.len (returned.wk callEnd.ext) .dyn = 2 := by decide +kernel
theorem call_element_first :
    (MObj.elems .dyn (callEnd.st.heap.get (returned.wk callEnd.ext)))[0]? =
      some (indexValue (wmod 3)) := by decide +kernel
theorem call_element_second :
    (MObj.elems .dyn (callEnd.st.heap.get (returned.wk callEnd.ext)))[1]? =
      some (indexValue (wmod 4)) := by decide +kernel
theorem call_count_value : callEnd.st.storage.get (rfl : C.rootType "count" = some (.prim .uint)) =
    .prim (indexValue (wmod 11)) := by decide +kernel
theorem call_marker_value : Look.ofTEnv callEnd.st.env (.there (.there (.here : Idx [.val .uint] (.val .uint)))) =
    indexValue (wmod 42) := by decide +kernel

/-- A real false selected branch after the same allocating call prefix.
The compiler checks both branches; only the reached revert is executed. -/
def callRejected := (LoopScopes.compileProg 1 (scope false) callBefore.frag).get (by decide +kernel)
attribute [irreducible] callRejected
theorem call_rejected_frame : 1 + callRejected.cert.need ≤ 64 := by decide +kernel
theorem call_rejected_nonalloc : callRejected.cert.allocates = false := by decide +kernel
theorem call_rejected_source : (scope false).run callMid.st = .error .revert := by
  have hf : (scope false).runF 3 callMid.st = .error .revert := rfl
  exact ((Prog.runF_approx 3 (scope false) callMid.st).eq (by rw [hf]; intro h; cases h)).symm.trans hf

#print axioms call_rejected_frame
#print axioms call_rejected_nonalloc
#print axioms call_rejected_source
#print axioms call_private_length
#print axioms call_returned_length
#print axioms call_element_first
#print axioms call_element_second
#print axioms call_count_value
#print axioms call_marker_value
#print axioms call_target_reached
#print axioms callPrefix_cost
#print axioms callPrefix_frame
#print axioms callScope_frame
#print axioms callScope_nonalloc
#print axioms call_alias_first
#print axioms call_alias_second
#print axioms call_capacity
end Solidity.Backend.InternalFlow.PublishedLoopChecks
