import Solidity.Calculus.DecisionSourceChain

/-! # Finite intrinsic source-literal discovery
Candidates come from direct uint literals in the equation/implication/universal
skeleton consumed by the existing source-chain parser, plus zero as an instance
candidate. Other formula constructors supply no candidates. Each hit contains the
actual parser witness; neither coverage nor a decision verdict is consulted.
This is a source preparation component, not global target completeness.
-/
namespace Solidity.Decide
variable {C : Contract}

private def sourceUIntOpLiterals {s : Srt} (op : Op0 C s) :
    List PrimTy.uint.Denote := by
  apply @Op0.casesOn C (fun S op => List PrimTy.uint.Denote) s op
  case lit =>
    intro prim value
    cases prim
    case uint => exact [value]
    all_goals exact []
  all_goals intros; exact []

/-- Direct uint literal operands, retaining the intrinsic term's sort/context. -/
def sourceUIntTermLiterals {Γ : Ctx} {s : Srt} (t : Tm C Γ s) :
    List PrimTy.uint.Denote := by
  apply @Tm.casesOn C Γ (fun S t => List PrimTy.uint.Denote) s t
  case netOf => intro i a; exact sourceUIntTermLiterals a
  case app0 => intro S op; exact sourceUIntOpLiterals op
  case app1 => intro A S op a; exact sourceUIntTermLiterals a
  case app2 =>
    intro A B S op a b
    exact sourceUIntTermLiterals a ++ sourceUIntTermLiterals b
  case app3 =>
    intro A B D S op a b d
    exact sourceUIntTermLiterals a ++ sourceUIntTermLiterals b ++ sourceUIntTermLiterals d
  all_goals intros; exact []
termination_by structural t

/-- Literals on the parser's source skeleton; this is not an inventory of
arbitrary program/update formulas. The inspected constructors are explicit. -/
def sourceUIntChainLiterals {Γ : Ctx} (φ : Fml C Γ) :
    List PrimTy.uint.Denote := by
  apply @Fml.casesOn C (fun Γ φ => List PrimTy.uint.Denote) Γ φ
  case eq => intro Γ prim a b; exact sourceUIntTermLiterals a ++ sourceUIntTermLiterals b
  case imp => intro Γ a b; exact sourceUIntChainLiterals a ++ sourceUIntChainLiterals b
  case all => intro Γ name prim body; exact sourceUIntChainLiterals body
  all_goals intros; exact []
termination_by structural φ

/-- Zero also permits a constant body to have a candidate even when its
unused quantified variable contributes no uint literal to the consequent. -/
def sourceUIntDiscoveryValues {Γ : Ctx} (φ : Fml C Γ) :
    List PrimTy.uint.Denote := uintOfNat 0 :: sourceUIntChainLiterals φ

/-- Every actual chain carries its bound as a direct source guard literal. -/
theorem SourceUIntLiteralChain.bound_mem {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} (w : SourceUIntLiteralChain bound value φ) :
    bound ∈ sourceUIntChainLiterals φ := by
  induction w with
  | leaf atom =>
    rw [atom.equation]
    change bound ∈ (([bound] ++ sourceUIntChainLiterals atom.body) ++
      (sourceUIntTermLiterals atom.lhs ++ sourceUIntTermLiterals atom.rhs))
    simp only [List.mem_append, List.mem_singleton, true_or]
  | all name prim chain ih => exact ih

structure SourceUIntLiteralHit {Γ : Ctx} (φ : Fml C Γ) where
  bound : PrimTy.uint.Denote
  value : PrimTy.uint.Denote
  witness : SourceUIntLiteralChain bound value φ

/-- Exact finite source class: a genuine chain with its parameters present in
the stated syntax-derived candidate lists, rather than a verdict predicate. -/
structure SourceUIntLiteralCandidate {Γ : Ctx} (φ : Fml C Γ)
    extends SourceUIntLiteralHit φ where
  boundPresent : bound ∈ sourceUIntChainLiterals φ
  valuePresent : value ∈ sourceUIntDiscoveryValues φ

/-- Search a finite list derived from this actual formula. Bounds are never
expanded into all their uint values; the existing source parser is unchanged. -/
def sourceUIntLiteralDiscovery? {Γ : Ctx} (φ : Fml C Γ) :
    Option (SourceUIntLiteralHit φ) :=
  (sourceUIntChainLiterals φ).findSome? fun bound =>
    (sourceUIntDiscoveryValues φ).findSome? fun value =>
      (sourceUIntLiteralChain? φ bound value).map fun witness => ⟨bound, value, witness⟩

theorem SourceUIntLiteralHit.valid {Γ : Ctx} {φ : Fml C Γ}
    (hit : SourceUIntLiteralHit φ) : ∀ σ : State C Γ, holds σ φ := hit.witness.valid

/-- Hash observations use exactly the existing hash-free transport premise. -/
theorem SourceUIntLiteralHit.validH {φ : Fml C []}
    (hit : SourceUIntLiteralHit φ) (hh : φ.hasHash = false) : Fml.ValidH φ :=
  hit.witness.validH hh

/-- Every exact chain is found when its supplied instance value belongs to the
explicit finite source candidates. No occurrence premise is hidden. -/
theorem sourceUIntLiteralDiscovery_complete {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} (w : SourceUIntLiteralChain bound value φ)
    (hv : value ∈ sourceUIntDiscoveryValues φ) :
    (sourceUIntLiteralDiscovery? φ).isSome = true := by
  unfold sourceUIntLiteralDiscovery?
  simp only [List.findSome?_isSome_iff, Option.isSome_map]
  exact ⟨bound, w.bound_mem, value, hv, sourceUIntLiteralChain_complete w⟩

/-- A discovery hit establishes membership in the independently stated finite
source family, including actual source-parameter occurrence proofs. -/
theorem sourceUIntLiteralDiscovery_witness {Γ : Ctx} {φ : Fml C Γ}
    (h : (sourceUIntLiteralDiscovery? φ).isSome = true) :
    Nonempty (SourceUIntLiteralCandidate φ) := by
  unfold sourceUIntLiteralDiscovery? at h
  simp only [List.findSome?_isSome_iff, Option.isSome_map] at h
  obtain ⟨bound, hb, value, hv, found⟩ := h
  obtain ⟨chain⟩ := sourceUIntLiteralChain_witness found
  exact ⟨{ bound := bound, value := value, witness := chain, boundPresent := hb, valuePresent := hv }⟩

/-- Exact decidable membership for this finite source family, independently
of target, coverage and verdict functions. -/
theorem sourceUIntLiteralDiscovery_iff {Γ : Ctx} {φ : Fml C Γ} :
    (sourceUIntLiteralDiscovery? φ).isSome = true ↔
      Nonempty (SourceUIntLiteralCandidate φ) :=
  ⟨sourceUIntLiteralDiscovery_witness, fun ⟨candidate⟩ =>
    sourceUIntLiteralDiscovery_complete candidate.witness candidate.valuePresent⟩

instance sourceUIntLiteralCandidate_decidable {Γ : Ctx} {φ : Fml C Γ} :
    Decidable (Nonempty (SourceUIntLiteralCandidate φ)) :=
  if h : (sourceUIntLiteralDiscovery? φ).isSome = true then
    isTrue (sourceUIntLiteralDiscovery_witness h)
  else isFalse (fun ⟨candidate⟩ => h
    (sourceUIntLiteralDiscovery_complete candidate.witness candidate.valuePresent))

/-- The actual discovered syntax proof supplies the existing preparation
certificate. This does not register a global decision/coverage route. -/
def sourceUIntLiteralPreparation? {Γ : Ctx} (φ : Fml C Γ) :
    Option (DeclarationReduction φ) :=
  (sourceUIntLiteralDiscovery? φ).map fun hit =>
    DeclarationReduction.certified φ hit.valid

/-- Actual preparation has the original state-by-state equivalence, with
truth obtained from the computed source chain rather than a supplied oracle. -/
theorem sourceUIntLiteralPreparation_complete {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} (w : SourceUIntLiteralChain bound value φ)
    (hv : value ∈ sourceUIntDiscoveryValues φ) :
    ∃ r : DeclarationReduction φ, sourceUIntLiteralPreparation? φ = some r ∧
      r.formula = .tt ∧ ∀ σ : State C Γ, holds σ r.formula ↔ holds σ φ := by
  have hc : (sourceUIntLiteralDiscovery? φ).isSome = true :=
    sourceUIntLiteralDiscovery_complete w hv
  cases he : sourceUIntLiteralDiscovery? φ with
  | none => rw [he] at hc; cases hc
  | some hit =>
    exact ⟨DeclarationReduction.certified φ hit.valid,
      by simp only [sourceUIntLiteralPreparation?, he, Option.map_some], rfl,
      (DeclarationReduction.certified φ hit.valid).correct⟩

theorem sourceUIntLiteralPreparation_iff {Γ : Ctx} {φ : Fml C Γ} :
    (sourceUIntLiteralPreparation? φ).isSome = true ↔
      Nonempty (SourceUIntLiteralCandidate φ) := by
  simpa only [sourceUIntLiteralPreparation?, Option.isSome_map] using
    (sourceUIntLiteralDiscovery_iff (φ := φ))

/-- A real source counterexample forbids discovery; a miss does not assert
invalidity. The existing negative source models can be reused directly. -/
theorem sourceUIntLiteralDiscovery_none_of_invalid {Γ : Ctx} {φ : Fml C Γ}
    (hbad : ¬ (∀ σ : State C Γ, holds σ φ)) :
    sourceUIntLiteralDiscovery? φ = none := by
  cases he : sourceUIntLiteralDiscovery? φ with
  | none => rfl
  | some hit => exact False.elim (hbad hit.valid)

/-- The actual computed hit transports validity through the unchanged
hash-free observation premise; no hash-containing observation is promoted. -/
theorem sourceUIntLiteralDiscovery_validH {φ : Fml C []}
    (h : (sourceUIntLiteralDiscovery? φ).isSome = true) (hh : φ.hasHash = false) :
    Fml.ValidH φ := by
  obtain ⟨candidate⟩ := sourceUIntLiteralDiscovery_witness h
  exact candidate.toSourceUIntLiteralHit.validH hh

/-- The parameters in the actual returned hit belong to the declared source
candidate lists, not merely to some other existential witness. -/
theorem sourceUIntLiteralDiscovery_parameters {Γ : Ctx} {φ : Fml C Γ}
    {hit : SourceUIntLiteralHit φ} (h : sourceUIntLiteralDiscovery? φ = some hit) :
    hit.bound ∈ sourceUIntChainLiterals φ ∧ hit.value ∈ sourceUIntDiscoveryValues φ := by
  unfold sourceUIntLiteralDiscovery? at h
  obtain ⟨bound, hb, foundBound⟩ := List.exists_of_findSome?_eq_some h
  obtain ⟨value, hv, mapped⟩ := List.exists_of_findSome?_eq_some foundBound
  cases hc : sourceUIntLiteralChain? φ bound value with
  | none => rw [hc] at mapped; cases mapped
  | some chain =>
    rw [hc] at mapped
    have heq : ({ bound := bound, value := value, witness := chain } : SourceUIntLiteralHit φ) = hit :=
      Option.some.inj mapped
    cases heq
    exact ⟨hb, hv⟩

end Solidity.Decide
