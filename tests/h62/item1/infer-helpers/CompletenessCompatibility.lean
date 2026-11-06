import Solidity.Source.Infer
import Solidity.Frontend.Static.InferComplete

/-!
Candidate compatibility statements for the existing static completeness
consumers when their premise is expressed with the source helper. This file
is additive and does not merge inferencers. Its statements and proof terms
are not evidence until checked with the pinned toolchain.
-/

namespace Solidity.H62.InferHelpers

open Solidity.Source
open Solidity.Frontend.Static

/-- The delete consumer retains both the mapping and context-refusal premises. -/
theorem source_delete_res {Γ : Ctx} {a : Syn .expr} {τ : STy}
    (d : LVal Γ a τ) (hm : τ.isMapping = false)
    (hp : Γ.deleteRefused τ a = false) :
    Res.expr (Typed.delete d hm hp) ∈ prefixOne Γ .delete (.lval d) :=
  delete_res d hm hp

/-- A source-location conversion premise is passed to the existing consumer. -/
theorem source_convElem_mem {Γ : Ctx} {el : Elem} {h : el ≠ .addressPayable}
    {x : Syn .expr} {σ : STy} {dx : Typed Γ x σ}
    (hx : Res.expr dx ∈ infer Γ x)
    (he : σ.explicit Γ.isBase (el.ty σ.convLoc) = true) :
    Res.expr (Typed.convElem (h := h) dx rfl he) ∈
      infer Γ (.call (.elemType el h) (.positional (.cons x .nil))) :=
  convElem_mem hx he

/-- A source-payable premise is passed to the existing consumer. -/
theorem source_payable_mem {Γ : Ctx} {x : Syn .expr} {σ : STy} {dx : Typed Γ x σ}
    (hx : Res.expr dx ∈ infer Γ x) (hp : σ.isPayableArg = true) :
    Res.expr (Typed.payable dx hp) ∈ infer Γ (.payableConv (.positional (.cons x .nil))) :=
  payable_mem hx hp

end Solidity.H62.InferHelpers
