import Solidity.Correctness.Panic.Provenance.Control
import Solidity.Examples.Panic.ProvenanceEval

/-!
# Checks: step leaves of panic code provenance

A failing `assert` inside a loop and inside a self-catch. The leaves of
`Correctness/Panic/Provenance/Control.lean` fix the emitted code from the
retained site: the loop halts with code 1 read off the assertion site, and the
self-catch hands its panic handler the word of that site's code.
-/

namespace Solidity.Examples.Panic.ProvenanceControl
open Solidity.Panic Solidity.Semantics.Panic Solidity.Correctness.Panic
open Solidity.Examples.Panic.ProvenanceEval (code? site? code_of_site)

variable {C : Contract} {Γ : Ctx}

/-- `assert(false)`. -/
def fail : Val C Γ .bool := .simple (.bool false)

/-! ## A failing assertion inside a loop -/

/-- `while (true) { assert(false); }`. -/
def assertLoop : Step C Γ Γ := Run.loop (.simple (.bool true)) .refl (Run.assert fail)

/-- The loop is coded by the loop and assertion leaves. -/
theorem assertLoop_coded : StepCoded (assertLoop : Step C Γ Γ) :=
  Run.loop_coded _ _ (Run.assert_coded fail)

/-- The loop's first iteration fails at the assertion site. -/
theorem assertLoop_site (σ : State C Γ) : site? (assertLoop σ) = some .assertion := by
  have e : assertLoop σ = .error (.intrinsic .assert
      (Raised.ofOrigin (.assertion false) .assertion rfl)) :=
    Loop.run_body_error _ _ _ _ rfl (by rw [Run.assert_false fail σ rfl]; rfl)
  rw [e]
  exact congrArg some (Raised.ofOrigin_site _ _ _)

/-- Hence the loop halts with solc code 1, read off the retained site. -/
example (σ : State C Γ) : code? (assertLoop σ) = some 0x01 := by
  rw [code_of_site (assertLoop_coded σ), assertLoop_site]
  rfl

/-! ## A failing assertion inside a self-catch -/

/-- The self-call's body `assert(false)` fails with a coded intrinsic halt. -/
theorem selfCall_fails {ρ : Ctx} (rets : Binders ρ) (σ : State C Γ) :
    ∃ origin, origin.site = .assertion ∧
      Run.call .nil (.rets rets.toRet) .refl (Run.assert fail) σ =
        .error (.intrinsic (siteCode origin.site) origin) := by
  refine ⟨Raised.ofOrigin (.assertion false) .assertion rfl, Raised.ofOrigin_site _ _ _, ?_⟩
  have e := Run.call_error .nil (.rets rets.toRet) .refl (Run.assert fail) σ () _ rfl
    (Run.assert_false fail _ rfl)
  rw [e, ← Run.call_coded .nil (.rets rets.toRet) .refl (Run.assert_coded fail) σ _ e]

/-- `try this.f() … catch Panic(uint c) { … }` with `f` asserting `false`: the panic
handler is entered with the word of the assertion site's code, 1, and the whole
statement is coded whenever its handlers are. -/
example {ρ κ Γ₁ Γ₂ Γ₃ Γ₄ : Ctx} (ext : ExtCall C Γ) (rets : Binders ρ)
    (h₁ : Ext (ρ ++ Γ) Γ₁) (ok : Step C (ρ ++ Γ) Γ₁)
    (h₂ : Ext Γ Γ₂) (err : Step C Γ Γ₂) (code : CodeBinder κ)
    (h₃ : Ext (κ ++ Γ) Γ₃) (pnc : Step C (κ ++ Γ) Γ₃)
    (h₄ : Ext Γ Γ₄) (other : Step C Γ Γ₄)
    (hok : StepCoded ok) (herr : StepCoded err) (hpnc : StepCoded pnc)
    (hother : StepCoded other) (σ : State C Γ)
    (nonzero : (ext.addr.evalT σ).1 ≠ 0)
    (self : (ext.addr.evalT σ).1 = σ.tx.selfAddress.1) :
    let caught := Run.tryCall ext rets h₁ ok h₂ err code h₃ pnc h₄ other .nil .refl
      (Run.assert fail) true
    ErrCoded (caught σ) ∧
    caught σ = (pnc (σ.withEnv (TEnv.append κ
        (code.decodeT (H := σ.H) (Run.codeWord .assert)) σ.env))).map
      fun o => ⟨o.st.drop ((Ext.append Γ κ).trans h₃), o.ext⟩ := by
  obtain ⟨origin, site, failed⟩ := selfCall_fails rets σ
  refine ⟨Run.tryCall_coded ext rets h₁ h₂ code h₃ h₄ .nil .refl _ true
    hok herr hpnc hother σ, ?_⟩
  rw [Run.tryCall_self_failure ext rets h₁ ok h₂ err code h₃ pnc h₄ other .nil .refl _ σ _
    nonzero self failed, Run.catchHalt_coded_intrinsic rfl, site]
  rfl

/-- The word handed to the panic handler is 1. -/
example : (Run.codeWord .assert).val = 1 := rfl

end Solidity.Examples.Panic.ProvenanceControl
