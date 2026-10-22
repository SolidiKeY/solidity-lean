import Solidity.Theorems
import SolidityBridge.Rewriting
import CslibBackport.Foundations.Logic.InferenceSystem
import CslibBackport.Foundations.Logic.LogicalEquivalence
import CslibBackport.Logics.Propositional.NaturalDeduction.Basic
import Mathlib.Order.BooleanAlgebra.Basic
import Mathlib.Data.Set.Basic

/-!
# The calculus in CSLib's proof theory

The calculus's judgement `Proves C R Γ₀ H φ` (`Calculus/Proves.lean`) and its
soundness (`Calculus/Sound.lean`) in CSLib's vocabulary (backported to
4.24, `vendor/CslibBackport/VENDOR.md`), with Mathlib's algebra of
propositions:

* **Inference systems.**  A sequent `H ⊢ φ` is a judgement (`Seq C Γ₀`);
  the calculus with rule set `R` is a CSLib `InferenceSystem` on it
  (`Calculus R⇓j`), and so is validity (`Semantics⇓j`).  Soundness is a map
  of inference systems (`Calculus.sound`), solkey's rules a sub-system of the
  calculus (`Calculus.solkey_le`), strictly (`Calculus.solkey_lt`).
* **Logical equivalence.**  Formulas with one hole anywhere — under
  connectives, updates, modalities and binders (`FCtx`) — are CSLib
  contexts; equivalence in every state is a CSLib `Congruence` and a
  `LogicalEquivalence` (`Fml.fill_congr`).
* **The Lindenbaum–Tarski algebra.**  Formulas up to equivalence are a
  Mathlib `BooleanAlgebra` (`Lindenbaum C Γ`), embedded in the states' sets
  by their meaning; a derivable formula is its top (`Proves.mk_eq_top`), and
  the strategy only goes down in it (`Fml.mk_le_of_mred`).
* **Natural deduction.**  CSLib's propositional natural deduction over the
  calculus's formulas as atoms is sound (`PL.Theory.Derivation.sound`): with
  the calculus's theorems and classical logic as axioms
  (`Fml.provedTheory`), what it derives is valid (`Fml.valid_of_derivable`).
  A formula's own connectives are its propositional skeleton
  (`Fml.skeleton`), so a formula whose skeleton follows by natural deduction
  from what the calculus proves is valid (`Fml.valid_of_skeleton`).
-/

namespace Solidity

open Cslib Cslib.Logic Cslib.Logic.InferenceSystem

variable {C : Contract}

/-! ## Inference systems -/

/-- A sequent `H ⊢ φ` of the calculus, its hypotheses opening `Γ₀`. -/
structure Seq (C : Contract) (Γ₀ : Ctx) where
  {Γ : Ctx}
  H : Hyps C Γ₀ Γ
  φ : Fml C Γ

/-- The sequent `⊢ φ`. -/
abbrev Seq.closed (φ : Fml C []) : Seq C [] := ⟨.nil, φ⟩

/-- The tag of the calculus with rule set `R`. -/
structure Calculus (R : RuleSet) : Type

/-- The tag of validity: a sequent holds in every state. -/
structure Semantics : Type

/-- **The calculus is an inference system**: a derivation of `H ⊢ φ` is a
proof of `Proves C R Γ₀ H φ`. -/
instance (R : RuleSet) (Γ₀ : Ctx) : InferenceSystem (Calculus R) (Seq C Γ₀) where
  derivation j := Proves C R Γ₀ j.H j.φ

/-- **Validity is an inference system**: `H ⊢ φ` is valid when
`H.wrap φ` holds in every state of `Γ₀`. -/
instance (Γ₀ : Ctx) : InferenceSystem Semantics (Seq C Γ₀) where
  derivation j := ∀ σ : State C Γ₀, holds σ (j.H.wrap j.φ)

/-- **Soundness**, as a map of inference systems. -/
theorem Calculus.sound {R : RuleSet} {Γ₀ : Ctx} {j : Seq C Γ₀} (d : Calculus R⇓j) :
    Semantics⇓j :=
  Proves.sound d

/-- Soundness of derivability. -/
theorem Calculus.derivable_sound {R : RuleSet} {Γ₀ : Ctx} {j : Seq C Γ₀}
    (h : DerivableIn (Calculus R) j) : DerivableIn Semantics j :=
  let ⟨d⟩ := h
  ⟨Calculus.sound d⟩

/-- `⊢ φ` derivable is `Fml.Valid φ`. -/
theorem Calculus.valid {R : RuleSet} {φ : Fml C []}
    (h : DerivableIn (Calculus R) (Seq.closed φ)) : Fml.Valid φ :=
  let ⟨d⟩ := h
  Proves.fmlValid d

/-- **solkey's rules are a sub-system of the calculus.** -/
theorem Calculus.solkey_le {Γ₀ : Ctx} {j : Seq C Γ₀} (d : Calculus .solkey⇓j) :
    Calculus .all⇓j :=
  Proves.toAll d

/-- On solkey's fragment the two systems derive the same sequents. -/
theorem Calculus.solkey_iff {Γ₀ : Ctx} {j : Seq C Γ₀} (h : j.φ.inSolkey = true) :
    DerivableIn (Calculus .solkey) j ↔ DerivableIn (Calculus .all) j :=
  ⟨fun ⟨d⟩ => ⟨Calculus.solkey_le d⟩, fun ⟨d⟩ => ⟨(Main.solkey_eq_calculus h).2 d⟩⟩

/-- **Strictly**: the calculus derives a sequent solkey's rules do not. -/
theorem Calculus.solkey_lt :
    ∃ φ : Fml C [], DerivableIn (Calculus .all) (Seq.closed φ) ∧
      ¬ DerivableIn (Calculus .solkey) (Seq.closed φ) :=
  let ⟨φ, h, h'⟩ := Main.solkey_lt_calculus (C := C)
  ⟨φ, ⟨h⟩, fun ⟨d⟩ => h' d⟩

/-! ## Contexts and logical equivalence -/

/-- **A formula with one hole**, of `Δ`, in a formula of `Γ`: anywhere, under
a connective, an update, a modality or a binder. -/
inductive FCtx (C : Contract) : Ctx → Ctx → Type where
  | hole {Γ : Ctx} : FCtx C Γ Γ
  | not {Γ Δ : Ctx} (c : FCtx C Γ Δ) : FCtx C Γ Δ
  | andL {Γ Δ : Ctx} (c : FCtx C Γ Δ) (ψ : Fml C Γ) : FCtx C Γ Δ
  | andR {Γ Δ : Ctx} (ψ : Fml C Γ) (c : FCtx C Γ Δ) : FCtx C Γ Δ
  | impL {Γ Δ : Ctx} (c : FCtx C Γ Δ) (ψ : Fml C Γ) : FCtx C Γ Δ
  | impR {Γ Δ : Ctx} (ψ : Fml C Γ) (c : FCtx C Γ Δ) : FCtx C Γ Δ
  | upd {Γ Γ' Δ : Ctx} (m : Modality) (U : Upd C Γ Γ') (c : FCtx C Γ' Δ) : FCtx C Γ Δ
  | modal {Γ Γ₁ Γ₀ Δ : Ctx} (m : Modality) (P : Prog C Γ Γ₁) (κ : Frames C Γ₁ Γ₀)
      (c : FCtx C Γ₀ Δ) : FCtx C Γ Δ
  | havoc {Γ Δ : Ctx} (c : FCtx C Γ Δ) : FCtx C Γ Δ
  | all {Γ Δ : Ctx} (x : Var) (p : PrimTy) (c : FCtx C (.val p :: Γ) Δ) : FCtx C Γ Δ
  | bind {Γ Δ : Ctx} (m : Modality) (x : Var) (t : LTy) (c : FCtx C (t :: Γ) Δ) : FCtx C Γ Δ
  | anon {Γ Δ : Ctx} (xs : List ((t : LTy) × Idx Γ t)) (c : FCtx C Γ Δ) : FCtx C Γ Δ
  | allocAll {Γ Δ : Ctx} (x : Var) (R : RefTy) (c : FCtx C (.mem R :: Γ) Δ) : FCtx C Γ Δ
  | grow {Γ Δ : Ctx} (c : FCtx C Γ Δ) : FCtx C Γ Δ

/-- The hole filled. -/
def FCtx.fill {Δ : Ctx} (φ : Fml C Δ) : {Γ : Ctx} → FCtx C Γ Δ → Fml C Γ
  | _, .hole => φ
  | _, .not c => .not (c.fill φ)
  | _, .andL c ψ => .and (c.fill φ) ψ
  | _, .andR ψ c => .and ψ (c.fill φ)
  | _, .impL c ψ => .imp (c.fill φ) ψ
  | _, .impR ψ c => .imp ψ (c.fill φ)
  | _, .upd m U c => .upd m U (c.fill φ)
  | _, .modal m P κ c => .modal m P κ (c.fill φ)
  | _, .havoc c => .havoc (c.fill φ)
  | _, .all x p c => .all x p (c.fill φ)
  | _, .bind m x t c => .bind m x t (c.fill φ)
  | _, .anon xs c => .anon xs (c.fill φ)
  | _, .allocAll x R c => .allocAll x R (c.fill φ)
  | _, .grow c => .grow (c.fill φ)

/-- Two formulas equivalent: they hold in the same states. -/
def Fml.Equiv {Γ : Ctx} (φ ψ : Fml C Γ) : Prop := ∀ σ : State C Γ, holds σ φ ↔ holds σ ψ

/-- What a context holds of depends only on what its hole holds of. -/
theorem Fml.fill_eq {Δ : Ctx} {φ ψ : Fml C Δ} (e : ∀ σ, holds σ φ = holds σ ψ) :
    {Γ : Ctx} → (c : FCtx C Γ Δ) → ∀ σ, holds σ (c.fill φ) = holds σ (c.fill ψ)
  | _, .hole => e
  | _, .not c => fun σ => by simp only [FCtx.fill, holds, Fml.fill_eq e c]
  | _, .andL c _ => fun σ => by simp only [FCtx.fill, holds, Fml.fill_eq e c]
  | _, .andR _ c => fun σ => by simp only [FCtx.fill, holds, Fml.fill_eq e c]
  | _, .impL c _ => fun σ => by simp only [FCtx.fill, holds, Fml.fill_eq e c]
  | _, .impR _ c => fun σ => by simp only [FCtx.fill, holds, Fml.fill_eq e c]
  | _, .upd _ _ c => fun σ => by simp only [FCtx.fill, holds, Fml.fill_eq e c]
  | _, .modal _ _ _ c => fun σ => by simp only [FCtx.fill, holds, Fml.fill_eq e c]
  | _, .havoc c => fun σ => by simp only [FCtx.fill, holds, Fml.fill_eq e c]
  | _, .all _ _ c => fun σ => by simp only [FCtx.fill, holds, Fml.fill_eq e c]
  | _, .bind _ _ _ c => fun σ => by simp only [FCtx.fill, holds, Fml.fill_eq e c]
  | _, .anon _ c => fun σ => by simp only [FCtx.fill, holds, Fml.fill_eq e c]
  | _, .allocAll _ _ c => fun σ => by simp only [FCtx.fill, holds, Fml.fill_eq e c]
  | _, .grow c => fun σ => by simp only [FCtx.fill, holds, Fml.fill_eq e c]

/-- **Equivalence is a congruence for every context**, a hole under an
update, a modality or a binder among them: `holds` reads a subformula only
through what it holds of (`Fml.fill_eq`). -/
theorem Fml.fill_congr {Δ : Ctx} {φ ψ : Fml C Δ} (h : Fml.Equiv φ ψ) {Γ : Ctx}
    (c : FCtx C Γ Δ) : Fml.Equiv (c.fill φ) (c.fill ψ) :=
  fun σ => (Fml.fill_eq (fun τ => propext (h τ)) c σ).to_iff

/-- The contexts that keep the scope, CSLib's contexts of a formula. -/
instance (Γ : Ctx) : HasContext (Fml C Γ) := ⟨FCtx C Γ Γ, fun c φ => c.fill φ⟩

/-- **Equivalence is a CSLib congruence.** -/
instance (Γ : Ctx) : Congruence (Fml C Γ) Fml.Equiv where
  refl _ _ := Iff.rfl
  symm _ _ h σ := (h σ).symm
  trans _ _ _ h₁ h₂ σ := (h₁ σ).trans (h₂ σ)
  elim c _ _ h := Fml.fill_congr h (Γ := Γ) (show FCtx C Γ Γ from c)

/-- A judgement `σ ⊧ φ`, its context the state. -/
instance (Γ : Ctx) : HasHContext (State C Γ × Fml C Γ) (Fml C Γ) :=
  ⟨State C Γ, fun σ φ => (σ, φ)⟩

/-- **Equivalence is CSLib's logical equivalence** for the judgement
`σ ⊧ φ`. -/
instance (Γ : Ctx) : LogicalEquivalence (Fml C Γ) (State C Γ × Fml C Γ)
    (fun j => holds j.1 j.2) where
  eqv := Fml.Equiv
  eqvFillValid h σ hv := (h σ).1 hv

/-! ## The Lindenbaum–Tarski algebra -/

/-- Equivalence as a Mathlib `Setoid`. -/
def Fml.setoid (C : Contract) (Γ : Ctx) : Setoid (Fml C Γ) where
  r := Fml.Equiv
  iseqv := ⟨fun _ _ => Iff.rfl, fun h σ => (h σ).symm, fun h₁ h₂ σ => (h₁ σ).trans (h₂ σ)⟩

/-- **The Lindenbaum–Tarski algebra**: formulas up to equivalence. -/
def Lindenbaum (C : Contract) (Γ : Ctx) : Type := Quotient (Fml.setoid C Γ)

namespace Lindenbaum

variable {Γ : Ctx}

/-- A formula's class. -/
def mk (φ : Fml C Γ) : Lindenbaum C Γ := Quotient.mk (Fml.setoid C Γ) φ

theorem mk_eq_mk {φ ψ : Fml C Γ} : mk φ = mk ψ ↔ Fml.Equiv φ ψ := Quotient.eq

/-- `φ ∨ ψ`, KeY's, as `¬φ → ψ`. -/
def _root_.Solidity.Fml.or {Γ : Ctx} (φ ψ : Fml C Γ) : Fml C Γ := .imp (.not φ) ψ

/-- What a class means: the states its formulas hold in. -/
def sem : Lindenbaum C Γ → Set (State C Γ) :=
  Quotient.lift (fun φ => {σ | holds σ φ}) (fun _ _ h => Set.ext h)

@[simp] theorem sem_mk (φ : Fml C Γ) : sem (mk φ) = {σ | holds σ φ} := rfl

theorem sem_injective : Function.Injective (sem (C := C) (Γ := Γ)) := by
  intro a b
  refine Quotient.inductionOn₂ a b fun φ ψ h => Quotient.sound fun σ => ?_
  exact Set.ext_iff.1 h σ

/-- A connective lifted to classes. -/
def lift₂ (f : Fml C Γ → Fml C Γ → Fml C Γ)
    (hf : ∀ {φ φ' ψ ψ'}, Fml.Equiv φ φ' → Fml.Equiv ψ ψ' → Fml.Equiv (f φ ψ) (f φ' ψ')) :
    Lindenbaum C Γ → Lindenbaum C Γ → Lindenbaum C Γ :=
  Quotient.map₂ f fun _ _ h _ _ h' => hf h h'

instance : Max (Lindenbaum C Γ) :=
  ⟨lift₂ Fml.or fun h h' σ => imp_congr (not_congr (h σ)) (h' σ)⟩
instance : Min (Lindenbaum C Γ) :=
  ⟨lift₂ Fml.and fun h h' σ => and_congr (h σ) (h' σ)⟩
instance : HImp (Lindenbaum C Γ) :=
  ⟨lift₂ Fml.imp fun h h' σ => imp_congr (h σ) (h' σ)⟩
instance : SDiff (Lindenbaum C Γ) :=
  ⟨lift₂ (fun φ ψ => .and φ (.not ψ)) fun h h' σ => and_congr (h σ) (not_congr (h' σ))⟩
instance : HasCompl (Lindenbaum C Γ) :=
  ⟨Quotient.map Fml.not fun _ _ h σ => not_congr (h σ)⟩
instance : Top (Lindenbaum C Γ) := ⟨mk .tt⟩
instance : Bot (Lindenbaum C Γ) := ⟨mk .ff⟩

/-- **Formulas up to equivalence are a Boolean algebra**, embedded in the
states' sets by what they mean. -/
noncomputable instance : BooleanAlgebra (Lindenbaum C Γ) := by
  classical
  exact Function.Injective.booleanAlgebra sem sem_injective
    (fun a b => Quotient.inductionOn₂ a b fun φ ψ => Set.ext fun σ => by
      show (¬holds σ φ → holds σ ψ) ↔ _
      change (¬holds σ φ → holds σ ψ) ↔ holds σ φ ∨ holds σ ψ
      tauto)
    (fun a b => Quotient.inductionOn₂ a b fun _ _ => rfl)
    (Set.ext fun _ => ⟨fun _ => trivial, fun _ => trivial⟩)
    (Set.ext fun _ => by change (¬True) ↔ False; exact ⟨fun h => h trivial, False.elim⟩)
    (fun a => Quotient.inductionOn a fun _ => rfl)
    (fun a b => Quotient.inductionOn₂ a b fun _ _ => rfl)
    (fun a b => Quotient.inductionOn₂ a b fun φ ψ => Set.ext fun σ => by
      show (holds σ φ → holds σ ψ) ↔ _
      simp only [himp_eq, Set.mem_union, Set.mem_compl_iff,
        Set.sup_eq_union]
      tauto)

/-- The order is inclusion of meanings: `sem` is an order embedding. -/
theorem mk_le_mk {φ ψ : Fml C Γ} : mk φ ≤ mk ψ ↔ ∀ σ, holds σ φ → holds σ ψ := Iff.rfl

/-- **A class is the top exactly when its formulas hold everywhere.** -/
theorem mk_eq_top {φ : Fml C Γ} : mk φ = ⊤ ↔ ∀ σ, holds σ φ :=
  eq_top_iff.trans ⟨fun h _ => h trivial, fun h σ _ => h σ⟩

/-- `Fml.Leads` is the reverse order. -/
theorem leads_iff {φ ψ : Fml C Γ} : Fml.Leads φ ψ ↔ mk ψ ≤ mk φ := Iff.rfl

end Lindenbaum

/-- **A derivable formula is the top of the Lindenbaum algebra.** -/
theorem Proves.mk_eq_top {R : RuleSet} {φ : Fml C []} (d : Proves C R [] .nil φ) :
    Lindenbaum.mk φ = ⊤ :=
  Lindenbaum.mk_eq_top.2 d.fmlValid

/-- **The strategy only goes down** in the Lindenbaum algebra: a reduct
implies what it reduces from (`Fml.mred_leads`). -/
theorem Fml.mk_le_of_mred {Γ : Ctx} {φ ψ : Fml C Γ} (h : (Fml.strategy C Γ).MRed φ ψ) :
    Lindenbaum.mk ψ ≤ Lindenbaum.mk φ :=
  Fml.mred_leads h

/-! ## Natural deduction over the calculus -/

namespace NatDed

open Cslib.Logic.PL

variable {Γ : Ctx}

/-- `false` is the bottom atom. -/
instance : Bot (Fml C Γ) := ⟨Fml.ff⟩

/-- **A proposition over formulas as a formula**: its connectives the
calculus's, `A ∨ B` as `¬A → B`. -/
def interp : Proposition (Fml C Γ) → Fml C Γ
  | .atom φ => φ
  | .and A B => .and (interp A) (interp B)
  | .or A B => Fml.or (interp A) (interp B)
  | .impl A B => .imp (interp A) (interp B)

/-- A proposition holds where its formula does. -/
abbrev Holds (σ : State C Γ) (A : Proposition (Fml C Γ)) : Prop := holds σ (interp A)

/-- A theory of propositions holds where all of its members do. -/
def Sound (T : PL.Theory (Fml C Γ)) : Prop := ∀ A ∈ T, ∀ σ, Holds σ A

open Classical in
/-- **CSLib's natural deduction is sound** over the calculus's formulas:
from sound axioms, a derivation's conclusion holds wherever its hypotheses
do. -/
theorem derivation_sound {T : PL.Theory (Fml C Γ)} (hT : Sound T) {Δ : PL.Ctx (Fml C Γ)}
    {A : Proposition (Fml C Γ)} (D : T.Derivation Δ A) :
    ∀ σ, (∀ B ∈ Δ, Holds σ B) → Holds σ A := by
  induction D with
  | ax h => exact fun σ _ => hT _ h σ
  | ass h => exact fun σ hΔ => hΔ _ h
  | andI _ _ ih₁ ih₂ => exact fun σ hΔ => ⟨ih₁ σ hΔ, ih₂ σ hΔ⟩
  | andE₁ _ ih => exact fun σ hΔ => (ih σ hΔ).1
  | andE₂ _ ih => exact fun σ hΔ => (ih σ hΔ).2
  | orI₁ _ ih => exact fun σ hΔ hn => absurd (ih σ hΔ) hn
  | orI₂ _ ih => exact fun σ hΔ _ => ih σ hΔ
  | @orE Δ A B D _ _ _ ih ih₁ ih₂ =>
    intro σ hΔ
    by_cases ha : Holds σ A
    · exact ih₁ σ fun B hB => (Finset.mem_insert.1 hB).elim (· ▸ ha) (hΔ B)
    · exact ih₂ σ fun B hB => (Finset.mem_insert.1 hB).elim (· ▸ ih σ hΔ ha) (hΔ B)
  | implI _ _ ih =>
    exact fun σ hΔ ha => ih σ fun B hB => (Finset.mem_insert.1 hB).elim (· ▸ ha) (hΔ B)
  | implE _ _ ih₁ ih₂ => exact fun σ hΔ => ih₁ σ hΔ (ih₂ σ hΔ)

/-- Classical logic's axioms hold: double negation elimination is
classical. -/
theorem sound_CPL : Sound (PL.Theory.CPL (Atom := Fml C Γ)) := by
  rintro _ ⟨A, rfl⟩ σ h
  by_contra hA
  exact h (fun ha => absurd ha hA) trivial

/-- **The calculus's theorems as axioms**: the formulas `⊢ φ` derives, as
atoms, and classical logic. -/
def provedTheory (R : RuleSet) : PL.Theory (Fml C []) :=
  {A | ∃ φ, A = .atom φ ∧ Proves C R [] .nil φ} ∪ PL.Theory.CPL

instance (R : RuleSet) : PL.Theory.IsClassical (provedTheory (C := C) R) :=
  PL.Theory.instIsClassicalExtention Set.subset_union_right

theorem sound_provedTheory (R : RuleSet) : Sound (provedTheory (C := C) R) := by
  rintro A (⟨φ, rfl, d⟩ | h) σ
  · exact d.fmlValid σ
  · exact sound_CPL A h σ

open Classical in
/-- **What natural deduction derives from the calculus's theorems is
valid.** -/
theorem valid_of_derivable {R : RuleSet} {A : Proposition (Fml C [])}
    (h : DerivableIn (provedTheory (C := C) R) A) : Fml.Valid (interp A) :=
  let ⟨D⟩ := h
  fun σ => derivation_sound (sound_provedTheory R) D σ fun _ h => absurd h (Finset.notMem_empty _)

/-- **The propositional skeleton** of a formula: its own connectives
CSLib's, everything else an atom. -/
def skeleton : Fml C Γ → Proposition (Fml C Γ)
  | .not φ => .impl (skeleton φ) ⊥
  | .and φ ψ => .and (skeleton φ) (skeleton ψ)
  | .imp φ ψ => .impl (skeleton φ) (skeleton ψ)
  | φ => .atom φ

/-- A formula holds where its skeleton does. -/
theorem holds_skeleton (σ : State C Γ) : (φ : Fml C Γ) → (Holds σ (skeleton φ) ↔ holds σ φ)
  | .not φ => by
    show (holds σ (interp (skeleton φ)) → ¬True) ↔ ¬holds σ φ
    rw [show holds σ (interp (skeleton φ)) ↔ holds σ φ from holds_skeleton σ φ]
    exact ⟨fun h h' => h h' trivial, fun h h' _ => h h'⟩
  | .and φ ψ => and_congr (holds_skeleton σ φ) (holds_skeleton σ ψ)
  | .imp φ ψ => imp_congr (holds_skeleton σ φ) (holds_skeleton σ ψ)
  | .tt | .eq .. | .wellFormed .. | .upd .. | .modal .. | .havoc .. | .all .. | .bind ..
  | .anon .. | .allocAll .. | .grow .. => Iff.rfl

open Classical in
/-- **A formula whose skeleton natural deduction derives from the
calculus's theorems is valid.** -/
theorem valid_of_skeleton {R : RuleSet} {φ : Fml C []}
    (h : DerivableIn (provedTheory (C := C) R) (skeleton φ)) : Fml.Valid φ :=
  fun σ => (holds_skeleton σ φ).1 (valid_of_derivable h σ)

end NatDed

end Solidity
