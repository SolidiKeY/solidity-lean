import Solidity.Calculus.FunContract

/-!
# Reusable typed function specifications

A summary keeps the original body and both specification clauses. Its
certificate is independent of the caller's arguments and local frame. Reusing
it discharges only the callee obligation: callers still prove the original
precondition and postcondition continuation. Frame checks are certified once
with the callee and reused with its specification.
-/

namespace Solidity.Automation.Summary

/-- A specification for one intrinsically typed function body. -/
structure Specification (C : Contract) (ps rs Γf : Ctx) where
  body : Prog C (rs ++ ps) Γf
  requires : Fml C ps
  ensures : Fml C (rs ++ (Olds ++ ps))
  modality : Modality := .box
  mutability : Mutability := .nonpayable

/-- A verified specification is valid for every caller frame and return target.
No hash, external verifier result, or sampled execution can construct this fact. -/
structure Specification.Certified {C : Contract} {ps rs Γf : Ctx}
    (spec : Specification C ps rs Γf) : Prop where
  contract : ∀ {Γ Γ' : Ctx} (ret : CallRet Γ rs Γ'),
    FunContract ret spec.body spec.requires spec.ensures spec.modality
  within : Prog.within spec.mutability spec.body = true
  writes : ∀ {Γ Γ' : Ctx} (ret : CallRet Γ rs Γ'),
    writesRets ret.nVals spec.body = true

/-- Use the same callee certificate at any call site. Both caller obligations
are retained verbatim from `useContractC_of_valid`; its frame conditions
come from the certificate instead of being recomputed at each call. -/
theorem Specification.use {C : Contract} {ps rs Γf : Ctx}
    (spec : Specification C ps rs Γf) (certificate : spec.Certified)
    {Γ Γ' Γ₂ Γ₀ : Ctx} {H : Hyps C [] Γ} {f : Name}
    {args : Args C Γ ps} {ret : CallRet Γ rs Γ'}
    {ω : Prog C Γ' Γ₂} {κ : Frames C Γ₂ Γ₀} {φ : Fml C Γ₀}
    (pre : Fml.Valid (H.wrap (Fml.callPre args spec.requires spec.modality)))
    (post : Fml.Valid (H.wrap
      (Fml.callPost spec.mutability args ret spec.ensures ω κ φ spec.modality))) :
    Fml.Valid (H.wrap
      (.modal spec.modality (.cons (.call f args ret spec.body) ω) κ φ)) :=
  useContractC_of_valid (certificate.contract ret) pre post
    certificate.within (certificate.writes ret)

/-- A summary's certificate can be supplied directly from proofs of the
existing typed function obligations. This introduces no alternative semantics. -/
theorem Specification.certify {C : Contract} {ps rs Γf : Ctx}
    (spec : Specification C ps rs Γf)
    (proof : ∀ {Γ Γ' : Ctx} (ret : CallRet Γ rs Γ') (σ : State C ps),
      holds σ (FunContract.obligation ret spec.body spec.requires spec.ensures spec.modality))
    (within : Prog.within spec.mutability spec.body = true)
    (writes : ∀ {Γ Γ' : Ctx} (ret : CallRet Γ rs Γ'),
      writesRets ret.nVals spec.body = true) : spec.Certified :=
  ⟨fun ret => FunContract.ofValid (proof ret), within, writes⟩

end Solidity.Automation.Summary
