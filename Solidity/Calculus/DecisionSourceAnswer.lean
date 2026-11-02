import Solidity.Calculus.DecisionSourceDiscovery
import Solidity.Calculus.DecisionGivenHeapExtension

/-! # Lazy certified source-chain answer route
Existing given-heap answers retain their exact certificates and counterstates.
Only an existing miss consults finite intrinsic source-literal discovery.
-/
namespace Solidity.Decide

/-- Constant-work constructor checks at each universal prefix before finite
candidate enumeration. A successful chain always has this source skeleton. -/
def sourceUIntLiteralSkeleton {C : Contract} {Γ : Ctx} (φ : Fml C Γ) : Bool := by
  apply @Fml.casesOn C (fun Γ φ => Bool) Γ φ
  case all => intro Γ name prim body; exact sourceUIntLiteralSkeleton body
  case imp =>
    intro Γ left right
    exact match sourceUIntAllView? left with
      | none => false
      | some q => (sourceImpView? q.body).isSome && (MemoryWitness.eqView right).isSome
  all_goals intros; exact false
termination_by structural φ

/-- The prefilter excludes no member of the independently stated source family. -/
theorem SourceUIntLiteralChain.skeleton {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    {bound value : PrimTy.uint.Denote} (w : SourceUIntLiteralChain bound value φ) :
    sourceUIntLiteralSkeleton φ = true := by
  induction w with
  | leaf atom => rw [atom.equation]; rfl
  | all name prim chain ih => exact ih

theorem sourceUIntLiteralSkeleton_of_discovery {C : Contract} {Γ : Ctx} {φ : Fml C Γ}
    (h : (sourceUIntLiteralDiscovery? φ).isSome = true) :
    sourceUIntLiteralSkeleton φ = true := by
  obtain ⟨candidate⟩ := sourceUIntLiteralDiscovery_witness h
  exact candidate.witness.skeleton

/-- Old certified answers first, then a genuine computed source-chain proof. -/
def givenHeapAnswerWithSources {C : Contract} (φ : Fml C []) :
    Option (MemoryWitness.Answer φ) :=
  (givenHeapAnswerWithReflexive φ).orElse fun _ =>
    if sourceUIntLiteralSkeleton φ then
      (sourceUIntLiteralDiscovery? φ).map fun hit => .proved hit.valid
    else none

/-- Every old successful answer, including its exact counterstate function,
is preserved rather than reconstructed. -/
theorem givenHeapAnswerWithSources_preserves {C : Contract} {φ : Fml C []}
    {answer : MemoryWitness.Answer φ} (h : givenHeapAnswerWithReflexive φ = some answer) :
    givenHeapAnswerWithSources φ = some answer := by
  unfold givenHeapAnswerWithSources
  rw [h]
  rfl

theorem givenHeapAnswerWithSources_old_complete {C : Contract} {φ : Fml C []}
    (h : (givenHeapAnswerWithReflexive φ).isSome = true) :
    (givenHeapAnswerWithSources φ).isSome = true := by
  cases he : givenHeapAnswerWithReflexive φ with
  | none => rw [he] at h; cases h
  | some answer => rw [givenHeapAnswerWithSources_preserves he]; rfl

/-- Discovery is sufficient even if an earlier certified answer also exists. -/
theorem givenHeapAnswerWithSources_source {C : Contract} {φ : Fml C []}
    (h : (sourceUIntLiteralDiscovery? φ).isSome = true) :
    (givenHeapAnswerWithSources φ).isSome = true := by
  cases he : givenHeapAnswerWithReflexive φ with
  | none =>
    unfold givenHeapAnswerWithSources
    rw [he]
    simp only [Option.orElse_none]
    rw [if_pos (sourceUIntLiteralSkeleton_of_discovery h)]
    simpa only [Option.isSome_map] using h
  | some answer => rw [givenHeapAnswerWithSources_preserves he]; rfl

/-- Every old countermodel is returned with its original state function. -/
theorem givenHeapAnswerWithSources_preserves_countermodel {C : Contract} {φ : Fml C []}
    (w : {σ : State C [] // ¬ holds σ φ}) (h : MemoryWitness.countermodel? φ = some w) :
    givenHeapAnswerWithSources φ =
      some (.refuted (fun (_ : State C []) => w.1) (fun _ => w.2)) :=
  givenHeapAnswerWithSources_preserves (givenHeapAnswerWithReflexive_preserves w h)

end Solidity.Decide
