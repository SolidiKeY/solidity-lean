import Solidity.Correctness.Lowering.Total.EnumDecode
import Solidity.Correctness.Lowering.Total.Versions.CalleeBinding.Functions

/-!
Request-context assembly obligations. These facts preserve the unrestricted
successful-production domain; they do not supply its complete decoder.
The empty-body fact exposes why declaration representability cannot be inferred
from production success. The callee bridge records the exact conditional P2 use,
including the actual declared body, without claiming W3 semantic binding.
-/
namespace Solidity.Correctness.Lowering.Total.Decode.SuccessfulContext

/-- Lowering an empty body preserves both state layers for arbitrary caller
locals, return slots and scope. It does not inspect declaration metadata. -/
theorem empty_run (input : ProductionInput) :
    SuccessfulProductionRun { input with raw := [] } ⟨[], input.before⟩ := by
  letI : FreshNames := input.names
  change (((lowerLoops input.returnSlots []).run input.scope).run input.before.locals).run
    input.before.memo = .ok (([], input.before.locals), input.before.memo)
  rw [lowerLoops, lowerList.eq_def]
  rfl

/-- Full-domain caller success does not entail the existing enum decoder's
representability obligation. This is a component coverage obstruction, not a
replacement admission predicate or a claim that every possible decoder fails. -/
theorem success_without_enum_representation (input : ProductionInput) :
    ∃ r : Request, ∃ o : ProductionOutput,
      r.success o ∧ ¬ EnumDecode.Representable r.contract := by
  refine ⟨⟨{ vars := [], enums := [("E", [])] }, { input with raw := [] }, none⟩,
    ⟨[], input.before⟩, empty_run input, ?_⟩
  intro h
  exact h ("E", []) (List.mem_cons_self) rfl

/-- W2's exact conditional P2 use: the fixed existing producer must publish its
binding before its selected output supplies the original request's body spelling
and actual declaration/body association. Discharge `published` after P2 lands;
it remains a premise here, and is not inferred from production success. -/
theorem published_callee_context
    (published : Version.CalleeBinding.Publishes fun σ r =>
      Version.CalleeBinding.fromFunctions σ.tables σ.registry σ.settings σ.scope
        σ.leadingParts r.contract.funs σ.index)
    {σ : Version.CalleeBinding.Site} {r : Request} {c : CalleeRequest}
    {s : Version.CalleeBinding.Output} {o : ProductionOutput}
    (hc : r.callee = some c) (ordinary : c.constructor = false)
    (entry : ∃ a, r.contract.funs[σ.index]? = some (a, c.declaration))
    (produced : Version.CalleeBinding.fromFunctions σ.tables σ.registry σ.settings
      σ.scope σ.leadingParts r.contract.funs σ.index = some s)
    (success : r.success o) :
    Version.CalleeBinding.Bound σ r c s ∧
    Tables.WithExpr.items σ.tables (Calls.expr σ.tables σ.registry) .body
      r.input.raw = some s.frame.body ∧
    Version.CalleeBinding.Declared (fun _ => some s.declaration) r c s := by
  have bound := published σ r c s hc ordinary entry produced
  exact ⟨bound, bound.spelledInput success, bound.declared success⟩

end Solidity.Correctness.Lowering.Total.Decode.SuccessfulContext
