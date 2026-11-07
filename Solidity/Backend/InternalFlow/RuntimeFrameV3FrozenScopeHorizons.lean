import Solidity.Backend.InternalFlow.RuntimeFrameV3FrozenScopeRuntime

/-! All-index outcome and represented-return controls for the exact frozen
scoped family. The source uses its original exhausted base. A common target
image does not simulate exhausted source runs. These are runtime-side facts,
not an approved-profile domain or a general recursive compiler. -/
namespace Solidity.Backend.InternalFlow.RuntimeFrame.FrozenScopeHorizons
open Evm Evm.Memory

/-- Exact source outcomes for arbitrary compatible callers and argument
values, including every insufficient quotation index. -/
theorem source_value {C : Contract} {Γ : Ctx} {R : RefTy}
 (hm : (Ty.ref R).mapFree=true) (p : PrimTy) (name : Var) (function : Name)
 (args : Args C Γ (RecursiveSource.Parameters R)) (destination : Idx Γ (.val .uint))
 (depth : Nat) (caller : State C Γ) (count : Nat) (bound : count<W)
 (ref : HRef caller.H R)
 (evaluated : args.evalT caller=.ok (RecursiveSource.countValue count bound,(some ref,()))) :
 (InterfaceV1.recursiveSource function args (.val .uint (.user "result") (some destination))
   (FrozenScopeFamily.step R hm p name) depth).run caller=
 if count<depth then .ok ⟨caller.setLocal destination (RecursiveSource.countValue count bound),List.prefix_refl _⟩
 else .error .exhausted :=
 (congrFun (FrozenScopeFamily.source_run hm p name function args
   (.val .uint (.user "result") (some destination)) depth) caller).trans
   (ScalarRecursiveSource.call_all_horizons hm function args destination depth caller count bound ref evaluated)

/-- The actual populated caller has read the mutated old array. No equality
with a hand-built initial caller or a pre-mutation count is assumed. -/
theorem populated_source (depth : Nat) :
 (FrozenScopeClient.statement depth).run ScalarContinuation.final=
 if 3<depth then .ok ⟨ScalarReentry.Endpoint.resultState,List.prefix_refl _⟩ else .error .exhausted :=
 (FrozenScopeClient.source_eq depth ScalarContinuation.final).trans
   (((SameCallDual.selected depth).source_run ScalarContinuation.final).trans (ScalarReentry.source depth))

theorem populated_entry (depth : Nat) :
 InterfaceV1.Entry (FrozenScopeClient.selected depth).plan 1 1 16 DisjointScalarReturn.Client.F
 ScalarContinuation.final ScalarContinuation.finalBase ScalarContinuation.target 10 :=
 ScalarReentry.entry depth

/-- Every sufficient index has a genuine successful source run and a
represented target return with the original allocator, stack and frame duties. -/
theorem populated_return (depth : Nat) (enough : 3<depth) :
 InterfaceV1.Returned (FrozenScopeClient.selected depth).plan 1 1 16 ScalarContinuation.final
 ScalarContinuation.finalBase ScalarContinuation.target 10
 ⟨ScalarReentry.Endpoint.resultState,List.prefix_refl _⟩ :=
 FrozenScopeRuntime.producer.required_return depth 1 16 ScalarContinuation.final
   ScalarContinuation.finalBase ScalarContinuation.target 10 (populated_entry depth) _
   ((populated_source depth).trans (if_pos enough))

theorem successful_entry (depth : Nat) (enough : 3<depth) :
 InterfaceV2.SuccessfulEntry 1 DisjointScalarReturn.Client.F (FrozenScopeClient.statement depth)
 (FrozenScopeClient.selected depth).plan :=
 ⟨1,16,ScalarContinuation.final,ScalarContinuation.finalBase,ScalarContinuation.target,10,
  ⟨ScalarReentry.Endpoint.resultState,List.prefix_refl _⟩,populated_entry depth,
  (populated_source depth).trans (if_pos enough)⟩

/-- Insufficient source horizons remain exhausted even though the same
physical image returns. No exhausted-to-revert or full-result equivalence. -/
theorem exhausted_boundary (depth : Nat) (short : depth≤3) :
 (FrozenScopeClient.statement depth).run ScalarContinuation.final=.error .exhausted ∧
 run (FrozenScopeClient.selected depth).plan.code ScalarContinuation.target=.ok ScalarReentry.Endpoint.machine 0 :=
 ⟨(populated_source depth).trans (if_neg (Nat.not_lt.mpr short)),FrozenScopeClient.good_target⟩

end Solidity.Backend.InternalFlow.RuntimeFrame.FrozenScopeHorizons
