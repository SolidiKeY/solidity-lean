import Solidity.Calculus.ChainKit
import Cslib.Foundations.Semantics.ReductionSystem.Basic
import Cslib.Foundations.Semantics.LTS.TraceEq
import Cslib.Foundations.Data.Relation
import Mathlib.Computability.Language
import Mathlib.Order.Basic

/-!
# The strategy as a reduction system

`Fml.step` (`Calculus/Step.lean`) rewrites a formula one rule at a time, and
`Calculus/ChainKit.lean` builds its closures by hand: `Fml.Steps`, a
derivation of zero or more steps; `Fml.Via`, a chain of labelled links;
`Fml.Leads`, the implication a chain composes to.  Here they are CSLib's and
Mathlib's notions:

* the strategy is a CSLib `ReductionSystem` (`Fml.strategy`), its
  multi-step reduction Mathlib's `Relation.ReflTransGen`, which `Fml.Steps`
  inhabits and `symex` computes along;
* it is deterministic, hence confluent in CSLib's sense (`Confluence`, by
  Mathlib's `Relation.church_rosser`);
* a chain is a run of a CSLib `LTS` labelled by its arrows (`Fml.chainLTS`),
  and its traces a Mathlib `Language` of arrows;
* `Fml.Leads` is a preorder, and every multi-step reduction and every trace
  of the chain LTS lies in it: the soundness of the strategy, and of chains,
  is `ReflTransGen`'s and `LTS.MTr`'s induction.
-/

namespace Solidity

variable {C : Contract} {Γ : Ctx}

/-! ## The strategy -/

/-- **The strategy**, a reduction system on the formulas of `Γ`: `φ` reduces
to `ψ` when `Fml.step` turns one into the other (`φ ~> ψ`). -/
def Fml.strategy (C : Contract) (Γ : Ctx) : ReductionSystem (Fml C Γ) where
  Red := Fml.OneStep

@[simp] theorem Fml.strategy_red (φ ψ : Fml C Γ) : (Fml.strategy C Γ).Red φ ψ ↔ φ.step = some ψ :=
  Iff.rfl

/-- A derivation `φ ~*> ψ` is a multi-step reduction. -/
theorem Fml.Steps.mred {φ ψ : Fml C Γ} : Fml.Steps φ ψ → (Fml.strategy C Γ).MRed φ ψ
  | .refl _ => .refl
  | .cons s c => Relation.ReflTransGen.head s c.mred

/-- Every multi-step reduction has a derivation. -/
theorem Fml.Steps.of_mred {φ ψ : Fml C Γ} (h : (Fml.strategy C Γ).MRed φ ψ) :
    Nonempty (Fml.Steps φ ψ) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨.refl _⟩
  | head s _ ih => exact ih.elim fun c => ⟨.cons s c⟩

/-- `φ ~*> ψ` is `Relation.ReflTransGen` of `~>`. -/
theorem Fml.steps_iff_mred {φ ψ : Fml C Γ} :
    Nonempty (Fml.Steps φ ψ) ↔ (Fml.strategy C Γ).MRed φ ψ :=
  ⟨fun ⟨c⟩ => c.mred, Fml.Steps.of_mred⟩

/-- `symex n` reduces along the strategy. -/
theorem symex_mred : (n : Nat) → (φ : Fml C Γ) → (Fml.strategy C Γ).MRed φ (symex n φ)
  | 0, _ => .refl
  | n + 1, φ => by
    unfold symex
    split
    · rename_i ψ h
      exact Relation.ReflTransGen.head h (symex_mred n ψ)
    · exact .refl

/-- **The strategy is deterministic**: `Fml.step` is a function. -/
theorem Fml.strategy_deterministic {φ ψ χ : Fml C Γ}
    (h : (Fml.strategy C Γ).Red φ ψ) (h' : (Fml.strategy C Γ).Red φ χ) : ψ = χ :=
  Option.some.inj (h.symm.trans h')

/-- **The strategy is confluent** (CSLib's `Confluence`): any two reducts of
one formula meet, by Mathlib's Church–Rosser lemma. -/
theorem Fml.strategy_confluent : Confluence (Fml.strategy C Γ).Red := by
  intro φ ψ χ hψ hχ
  exact Relation.church_rosser
    (fun _ b c hb hc => ⟨b, Relation.ReflGen.refl,
      (Fml.strategy_deterministic hb hc) ▸ Relation.ReflTransGen.refl⟩) hψ hχ

/-! ## Leads, a preorder -/

/-- `Fml.Leads` is reflexive and transitive: a Mathlib `IsPreorder`. -/
instance Fml.leads_isPreorder : IsPreorder (Fml C Γ) Fml.Leads where
  refl _ _ h := h
  trans _ _ _ h₁ h₂ := h₁.comp h₂

/-- **The strategy is sound**: every multi-step reduction leads back,
`Relation.ReflTransGen.lift` of `Fml.OneStep.sound`. -/
theorem Fml.mred_leads {φ ψ : Fml C Γ} (h : (Fml.strategy C Γ).MRed φ ψ) : Fml.Leads φ ψ := by
  induction h with
  | refl => exact fun _ h => h
  | tail _ s ih => exact ih.comp s.sound

/-- `symex_sound` again, from the reduction system. -/
theorem symex_leads (n : Nat) (φ : Fml C Γ) : Fml.Leads φ (symex n φ) :=
  Fml.mred_leads (symex_mred n φ)

/-- A formula that reduces to a valid one is valid. -/
theorem Fml.valid_of_mred {φ ψ : Fml C []} (h : (Fml.strategy C []).MRed φ ψ) (hψ : Fml.Valid ψ) :
    Fml.Valid φ :=
  fun σ => Fml.mred_leads h σ (hψ σ)

/-! ## Chains, runs of a labelled transition system -/

/-- **The chain LTS**: a formula steps to another along an arrow when the
arrow's relation (`Link.Rel`) holds of them. -/
def Fml.chainLTS (C : Contract) (Γ : Ctx) : LTS (Fml C Γ) (Link C) where
  Tr φ l ψ := l.Rel φ ψ

/-- The rule LTS: `φ ~[r]~> ψ`, labelled by the strategy's rule. -/
def Fml.ruleLTS (C : Contract) (Γ : Ctx) : LTS (Fml C Γ) (StepRule C) where
  Tr φ r ψ := Fml.StepBy r φ ψ

/-- The rule LTS is deterministic, as the strategy is. -/
theorem Fml.ruleLTS_deterministic : (Fml.ruleLTS C Γ).Deterministic := by
  intro φ r ψ χ h h'
  exact Fml.strategy_deterministic h.oneStep h'.oneStep

/-- A rule step is a step of the strategy: the rule LTS forgets to the
reduction system. -/
theorem Fml.ruleLTS_red {φ ψ : Fml C Γ} {r : StepRule C} (h : (Fml.ruleLTS C Γ).Tr φ r ψ) :
    (Fml.strategy C Γ).Red φ ψ :=
  h.oneStep

/-- **A chain is a run** of the chain LTS, labelled by its arrows, from its
first line to its last. -/
theorem Fml.Via.mtr : {φ : Fml C Γ} → {ws : List (Link C × Fml C Γ)} → Fml.Via φ ws →
    (Fml.chainLTS C Γ).MTr φ (ws.map Prod.fst) (Fml.Via.last φ ws)
  | _, [], _ => .refl
  | _, [(_, _)], v => .stepL v .refl
  | _, (_, _) :: _ :: _, v => .stepL v.1 (Fml.Via.mtr v.2)

/-- **Every run of the chain LTS leads back**: `Fml.Via.leads` for any run. -/
theorem Fml.chainLTS_leads {φ ψ : Fml C Γ} {ls : List (Link C)}
    (h : (Fml.chainLTS C Γ).MTr φ ls ψ) : Fml.Leads φ ψ := by
  induction h with
  | refl => exact fun _ h => h
  | stepL t _ ih => exact (Link.Rel.sound t).comp ih

/-- The arrows a chain from `φ` may be written with: a Mathlib `Language`
over the arrows, CSLib's traces of the chain LTS. -/
def Fml.chainLanguage (φ : Fml C Γ) : Language (Link C) :=
  (Fml.chainLTS C Γ).traces φ

/-- The empty chain is always written. -/
theorem Fml.nil_mem_chainLanguage (φ : Fml C Γ) : [] ∈ φ.chainLanguage :=
  ⟨φ, .refl⟩

/-- A chain's arrows are a word of its first line's language. -/
theorem Fml.Via.mem_chainLanguage {φ : Fml C Γ} {ws : List (Link C × Fml C Γ)}
    (v : Fml.Via φ ws) : ws.map Prod.fst ∈ φ.chainLanguage :=
  ⟨_, v.mtr⟩

/-- The language is closed under prefixes: a chain cut short is a chain. -/
theorem Fml.chainLanguage_append {φ : Fml C Γ} {u w : List (Link C)}
    (h : u ++ w ∈ φ.chainLanguage) : u ∈ φ.chainLanguage := by
  obtain ⟨ψ, h⟩ := h
  induction u generalizing φ with
  | nil => exact ⟨φ, .refl⟩
  | cons l u ih =>
    cases h with
    | stepL t h =>
      obtain ⟨χ, hχ⟩ := ih h
      exact ⟨χ, .stepL t hχ⟩

/-- `~>` is a link: the strategy embeds in the chain LTS. -/
theorem Fml.chainLTS_one {φ ψ : Fml C Γ} (h : (Fml.strategy C Γ).Red φ ψ) :
    (Fml.chainLTS C Γ).Tr φ .one ψ :=
  h

/-- `~*>` is a link: a multi-step reduction is one arrow of the chain LTS. -/
theorem Fml.chainLTS_many {φ ψ : Fml C Γ} (h : (Fml.strategy C Γ).MRed φ ψ) :
    (Fml.chainLTS C Γ).Tr φ .many ψ :=
  Fml.Steps.of_mred h

end Solidity
