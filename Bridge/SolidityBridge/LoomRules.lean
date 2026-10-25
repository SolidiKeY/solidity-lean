import SolidityBridge.Loom
import Solidity.Calculus.ChainKit

/-!
# Every taclet as a Loom sufficient-precondition rule

Postconditions in this module are deep formulas, read as `holds · ψ`.
`Post` may be used when the strategy must treat such a formula opaquely.
There is one translation and one soundness theorem for all statements;
there are no Loom-specific statement or loop rules.

Loom's `WPGen.get` takes every Lean predicate. With the existing deep formula
language, a generator therefore uses Loom's
`spec_triple`: the strategy's last line together with entailment from its
fixed deep post to the requested continuation. At that same deep post,
this entailment is reflexive and `get` is exactly the last line's reading.
-/

namespace Solidity

open Bridge.Loom

variable {C : Contract} {Γ Γ' Γ₁ Γ₀ : Ctx}

/-- Translate any taclet premise, with post restricted to a deep formula. -/
def Premise.toLoom (m : Modality) (p : Premise C Γ Γ') (ψ : Fml C Γ₀)
    (ω : Prog C Γ' Γ₁) (κ : Frames C Γ₁ Γ₀) : State C Γ → Prop :=
  fun σ => holds σ (p.fml m ω κ ψ)

/-- All taclets inherit `Stmt.sound`; this theorem never inspects a statement. -/
theorem Premise.toLoom_sound (m : Modality) (k : Nat) (s : Stmt C Γ Γ')
    (p : Premise C Γ Γ') (hp : s.step k m = p) (ψ : Fml C Γ₀)
    (ω : Prog C Γ' Γ₁) (κ : Frames C Γ₁ Γ₀) :
    p.toLoom m ψ ω κ ≤
      fun σ => loomWp m (Prog.runFrames σ (.cons s ω) κ) (holds · ψ) :=
  fun σ h => (loomWp_iff_afterRunTR m _ _).mpr
    ((Bridge.holds_modal m (.cons s ω) κ ψ σ).mp
      (Stmt.sound k m s p hp σ ω κ ψ h))

namespace Bridge.Loom

/-- A strategy chain gives only a sufficient precondition, in the `Leads` direction. -/
theorem leads_sound (m : Modality) (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀)
    (ψ : Fml C Γ₀) (last : Fml C Γ)
    (h : Fml.Leads (.modal m P κ ψ) last) (σ : State C Γ) :
    holds σ last → loomWp m (Prog.runFrames σ P κ) (holds · ψ) :=
  fun hlast => (loomWp_iff_afterRunTR m _ _).mpr
    ((Bridge.holds_modal m P κ ψ σ).mp (h σ hlast))

/-- Package a strategy's last line using Loom's fixed-post specification rule.
The deep-post restriction and the additional entailment for other continuations
are intentional; this does not claim the strategy computes weakest preconditions. -/
noncomputable def generator (m : Modality) (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀)
    (ψ : Fml C Γ₀) (last : Fml C Γ)
    (h : Fml.Leads (.modal m P κ ψ) last) (σ : State C Γ) :
    Generator m (Prog.runFrames σ P κ) :=
  letI : MAlgOrdered (ExceptT THalt Id) Prop := algebra m
  WPGen.spec_triple (m := ExceptT THalt Id) (l := Prop)
    (pre := holds σ last) (post := (holds · ψ))
    (Prog.runFrames σ P κ) (leads_sound m P κ ψ last h σ)

/-- At the specified deep post, the generator leaves exactly the strategy's last line. -/
theorem generator_get (m : Modality) (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀)
    (ψ : Fml C Γ₀) (last : Fml C Γ)
    (h : Fml.Leads (.modal m P κ ψ) last) (σ : State C Γ) :
    letI : MAlgOrdered (ExceptT THalt Id) Prop := algebra m
    (generator m P κ ψ last h σ).get (holds · ψ) ↔ holds σ last := by
  simp only [generator, WPGen.spec_triple, spec, le_refl, trueE, inf_top_eq]

/-- An actual strategy derivation is enough to build the Loom generator. -/
noncomputable def stepsGenerator (m : Modality) (P : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (ψ : Fml C Γ₀) (last : Fml C Γ)
    (steps : Fml.Steps (.modal m P κ ψ) last) (σ : State C Γ) :
    Generator m (Prog.runFrames σ P κ) :=
  generator m P κ ψ last steps.sound σ

/-- The existing bounded strategy supplies both the last line and its certificate. -/
noncomputable def symexGenerator (fuel : Nat) (m : Modality) (P : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (ψ : Fml C Γ₀) (σ : State C Γ) :
    Generator m (Prog.runFrames σ P κ) :=
  stepsGenerator m P κ ψ (symex fuel (.modal m P κ ψ))
    (Fml.Steps.ofSymex fuel (.modal m P κ ψ)) σ

end Bridge.Loom
end Solidity

/-- info: 'Solidity.Premise.toLoom_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Premise.toLoom_sound
/-- info: 'Solidity.Bridge.Loom.leads_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.Loom.leads_sound
/-- info: 'Solidity.Bridge.Loom.generator_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.Loom.generator_get
/-- info: 'Solidity.Bridge.Loom.symexGenerator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.Loom.symexGenerator
