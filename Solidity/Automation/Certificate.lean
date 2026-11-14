import Solidity.Automation.LeafReflection
import Solidity.Automation.LeafSpine

/-! Typed certificates contain selected rule applications and local witnesses.
Their interpretation reconstructs a calculus proof without invoking the walk.
A producer may refuse to produce a certificate; `useOr` retains its existing
verified proof path. This module does not replace that producer or its limits. -/
namespace Solidity.Automation
open Decide
variable {C : Contract}

/-- A local leaf witness. Premise deletion is recorded explicitly. -/
inductive LeafWitness : LFml C → Type where
  | spine {φ} (checked : Leaf.spine φ = true) : LeafWitness φ
  | trimmed {φ} (drop : LFml C → Bool) (child : LeafWitness (φ.dropPrem drop)) :
      LeafWitness φ
  | andIntro {φ ψ} (left : LeafWitness φ) (right : LeafWitness ψ) :
      LeafWitness (.and φ ψ)
  | hideLeft {φ ψ} (child : LeafWitness ψ) : LeafWitness (.imp φ ψ)
  | allIntro {k p φ} (child : LeafWitness φ) : LeafWitness (.all k p φ)
  /-- The pre-existing verified closer remains available for other fragments. -/
  | decided {φ} (checked : φ.decideLift = true) : LeafWitness φ

theorem LeafWitness.valid {φ : LFml C} (cert : LeafWitness φ) : φ.Valid := by
  induction cert with
  | spine checked => exact Leaf.spine_valid checked
  | trimmed drop child ih => exact fun g ν => LFml.dropPrem_holds drop g _ ν (ih g ν)
  | andIntro left right ihl ihr => exact fun g ν => ⟨ihl g ν, ihr g ν⟩
  | hideLeft child ih => exact fun g ν _ => ih g ν
  | allIntro child ih => exact fun g ν v => ih g (ν.set _ _ v)
  | decided checked => exact LFml.decideLift_valid checked

/-- Certificates for selected sequent rules. Indices retain the entire sequent,
rule set, contexts, modalities, and the original rule side conditions. -/
inductive Certificate (C : Contract) (R : RuleSet) :
    {Γ : Ctx} → Hyps C [] Γ → Fml C Γ → Type where
  | leaf {Γ} {H : Hyps C [] Γ} {φ : Fml C Γ} (l : LFml C)
      (lowered : (H.wrap φ).toLS true SymS.init = some l)
      (witness : LeafWitness l) (modalFree : (H.wrap φ).modalFree = true) :
      Certificate C R H φ
  | closeTrue {Γ} {H : Hyps C [] Γ} (boxOnly : H.boxOnly = true) :
      Certificate C R H .tt
  | intro {Γ} {H : Hyps C [] Γ} {a φ : Fml C Γ}
      (child : Certificate C R (H.pre a) φ) : Certificate C R H (.imp a φ)
  | hideLeft {Γ} {H : Hyps C [] Γ} {a φ : Fml C Γ}
      (child : Certificate C R H φ) : Certificate C R H (.imp a φ)
  | andIntro {Γ} {H : Hyps C [] Γ} {φ ψ : Fml C Γ}
      (left : Certificate C R H φ) (right : Certificate C R H ψ) :
      Certificate C R H (.and φ ψ)
  | allIntro {Γ} {H : Hyps C [] Γ} {x : Var} {p : PrimTy} {φ : Fml C (.val p :: Γ)}
      (child : Certificate C R (H.all x p) φ) : Certificate C R H (.all x p φ)
  | updIntro {Γ Δ} {H : Hyps C [] Γ} {m : Modality} {U : Upd C Γ Δ} {φ : Fml C Δ}
      (child : Certificate C R (H.upd m U) φ) : Certificate C R H (.upd m U φ)
  | update {Γ Γ' Γ₁ Γ₂} {H : Hyps C [] Γ} {m : Modality} {s : Stmt C Γ Γ'}
      {ω : Prog C Γ' Γ₁} {κ : Frames C Γ₁ Γ₂} {φ : Fml C Γ₂} {U : Upd C Γ Γ'}
      (selected : s.step (H.fresh (.modal m (.cons s ω) κ φ)) m = .update U)
      (admitted : R.admits m s = true)
      (child : Certificate C R (H.upd m U) (.modalK m ω κ φ)) :
      Certificate C R H (.modal m (.cons s ω) κ φ)
  /-- Reuse an already verified derivation for any rule not encoded above. -/
  | verified {Γ} {H : Hyps C [] Γ} {φ : Fml C Γ}
      (proof : Proves C R [] H φ) : Certificate C R H φ

theorem Certificate.proves {R : RuleSet} {Γ : Ctx} {H : Hyps C [] Γ} {φ : Fml C Γ}
    (cert : Certificate C R H φ) : Proves C R [] H φ := by
  induction cert with
  | leaf l lowered witness modalFree =>
    exact .closeHolds (Fml.Valid.of_toLS lowered witness.valid) modalFree
  | closeTrue boxOnly => exact .closeTrue boxOnly
  | intro child ih => exact .intro ih
  | hideLeft child ih => exact .hideLeft ih
  | andIntro left right ihl ihr => exact .andIntro ihl ihr
  | allIntro child ih => exact .allIntro ih
  | updIntro child ih => exact .updIntro ih
  | update selected admitted child ih => exact .update selected ih admitted
  | verified proof => exact proof

/-- Refusal to supply a certificate cannot remove a verified proof path. -/
def Certificate.useOr {R : RuleSet} {Γ : Ctx} {H : Hyps C [] Γ} {φ : Fml C Γ}
    (candidate : Option (Certificate C R H φ)) (fallback : Unit → Proves C R [] H φ) :
    Proves C R [] H φ :=
  match candidate with
  | some cert => cert.proves
  | none => fallback ()

end Solidity.Automation
