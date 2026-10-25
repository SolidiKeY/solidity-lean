import SolidityBridge.LoomRules

/-!
# Deep-post annotations for Loom's VC generator

The annotation makes a fixed dynamic-logic post and a strategy budget
visible to Loom's specification lookup. Execution is exactly `runFrames`;
neither the post nor the VC budget changes the run. The registered generator
is the existing strategy certificate packaged by `symexGenerator`.

Arbitrary Lean continuations are supported by an explicit entailment from
the chosen deep post. They are never reified into a new formula constructor.
-/

namespace Solidity.Bridge.Loom

variable {C : Contract} {Γ Γ₁ Γ₀ : Ctx}

/-- Annotate the core run with the deep post and budget used to generate VCs. -/
def runWithPost (_fuel : Nat) (_m : Modality) (P : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (_ψ : Fml C Γ₀) (σ : State C Γ) : TRes (State C Γ₀) :=
  Prog.runFrames σ P κ

/-- The annotated arrow has the existing bridge WP, with the actual halt policy. -/
theorem runWithPost_wp (fuel : Nat) (m : Modality) (P : Prog C Γ Γ₁)
    (κ : Frames C Γ₁ Γ₀) (ψ : Fml C Γ₀) (q : Set (State C Γ₀)) :
    (fun σ => loomWp m (runWithPost fuel m P κ ψ σ) q) =
      Bridge.wp m (fun σ => Prog.runFrames σ P κ) q :=
  loomWp_eq_wp m (fun σ => Prog.runFrames σ P κ) q

/-- One Loom registration for all programs, contexts, frames and deep posts. -/
@[loomSpec] noncomputable def runWithPostGenerator (fuel : Nat) (m : Modality)
    (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (ψ : Fml C Γ₀) (σ : State C Γ) :
    @WPGen (ExceptT THalt Id) inferInstance (State C Γ₀) Prop inferInstance
      (algebra m) (runWithPost fuel m P κ ψ σ) :=
  symexGenerator fuel m P κ ψ σ

/-- Generated VCs are the core strategy's last line and a continuation entailment.
The post supplied to the Solidity strategy is always the fixed deep `ψ`. -/
@[loomWpSimp] theorem runWithPostGenerator_get (fuel : Nat) (m : Modality)
    (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀) (ψ : Fml C Γ₀) (σ : State C Γ)
    (q : State C Γ₀ → Prop) :
    letI : MAlgOrdered (ExceptT THalt Id) Prop := algebra m
    (runWithPostGenerator fuel m P κ ψ σ).get q ↔
      holds σ (symex fuel (.modal m P κ ψ)) ∧ ∀ τ, holds τ ψ → q τ := by
  simp only [runWithPostGenerator, symexGenerator, stepsGenerator, generator,
    WPGen.spec_triple, spec, purePropE]
  rfl

end Solidity.Bridge.Loom

/-- info: 'Solidity.Bridge.Loom.runWithPost_wp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.Loom.runWithPost_wp
/-- info: 'Solidity.Bridge.Loom.runWithPostGenerator' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.Loom.runWithPostGenerator
/-- info: 'Solidity.Bridge.Loom.runWithPostGenerator_get' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms Solidity.Bridge.Loom.runWithPostGenerator_get
