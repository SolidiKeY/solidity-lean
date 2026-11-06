import tests.h62.item1.«infer-helpers».SharedAgreement
import Solidity.Frontend.Static.InferComplete

/-!
Guarded regression: shared-helper premises must not drop delete-context refusal,
inferred-operand membership, nonpayable conversion or payable-argument conditions
when invoking the existing production completeness consumers. These lemmas only
transport the helper observations; neither inferencer is changed or identified.
-/
namespace Solidity.H62.InferHelpers.SharedConsumers

open Solidity.Source Solidity.Frontend.Static
open SharedAgreement

/-- The mapping observation changes representation; context refusal is retained. -/
theorem shared_delete_res {Γ : Ctx} {a : Syn .expr} {τ : STy}
    (d : LVal Γ a τ) (hm : Shared.isMapping τ = false)
    (hp : Γ.deleteRefused τ a = false) :
    Res.expr (Typed.delete d ((source_mapping τ).symm.trans hm) hp) ∈
      prefixOne Γ .delete (.lval d) :=
  delete_res d ((source_mapping τ).symm.trans hm) hp

/-- Conversion retains the inferred operand and the exact explicit-conversion test. -/
theorem shared_convElem_mem {Γ : Ctx} {el : Elem} {h : el ≠ .addressPayable}
    {x : Syn .expr} {σ : STy} {dx : Typed Γ x σ}
    (hx : Res.expr dx ∈ infer Γ x)
    (he : σ.explicit Γ.isBase Γ.mapFree (el.ty (Shared.convLoc σ)) = true) :
    Res.expr (Typed.convElem (h := h) dx rfl
      (by simpa only [source_location] using he)) ∈
      infer Γ (.call (.elemType el h) (.positional (.cons x .nil))) :=
  convElem_mem hx (by simpa only [source_location] using he)

/-- Payable conversion retains the actual inferred operand and helper condition. -/
theorem shared_payable_mem {Γ : Ctx} {x : Syn .expr} {σ : STy} {dx : Typed Γ x σ}
    (hx : Res.expr dx ∈ infer Γ x) (hp : Shared.payableArg σ = true) :
    Res.expr (Typed.payable dx ((source_payable σ).symm.trans hp)) ∈
      infer Γ (.payableConv (.positional (.cons x .nil))) :=
  payable_mem hx ((source_payable σ).symm.trans hp)

#print axioms shared_delete_res
#print axioms shared_convElem_mem
#print axioms shared_payable_mem
end Solidity.H62.InferHelpers.SharedConsumers
