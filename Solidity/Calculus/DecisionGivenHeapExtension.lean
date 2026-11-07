import Solidity.Calculus.DecisionGivenHeapReason
import Solidity.Calculus.MemoryWitness

/-! # Lazy certified given-heap answer extension
The existing negative candidate search is authoritative on success. Only its
miss consults the exact all-heap reflexive-read certificate; no finite positive
check is promoted to global validity.
-/
namespace Solidity.Decide

/-- Preserve the producer countermodel before consulting the global source certificate. -/
def givenHeapAnswerWithReflexive {C : Contract} (φ : Fml C []) :
    Option (MemoryWitness.Answer φ) :=
  ((MemoryWitness.countermodel? φ).map (fun w =>
    MemoryWitness.Answer.refuted (fun (_ : State C []) => w.1) (fun _ => w.2))).orElse
      (fun _ => (ResidueReason.givenHeapLiteralRead? φ).map (fun w => w.answer))

/-- The old countermodel is returned with exactly its original state. -/
theorem givenHeapAnswerWithReflexive_preserves {C : Contract} {φ : Fml C []}
    (w : {σ : State C [] // ¬ holds σ φ}) (h : MemoryWitness.countermodel? φ = some w) :
    givenHeapAnswerWithReflexive φ =
      some (.refuted (fun (_ : State C []) => w.1) (fun _ => w.2)) := by
  unfold givenHeapAnswerWithReflexive
  rw [h]
  rfl

/-- Exact source recognition supplies an answer, independently of existing negatives. -/
theorem givenHeapAnswerWithReflexive_source {C : Contract} {φ : Fml C []}
    (h : φ.givenHeapLiteralReadReflexive = true) :
    (givenHeapAnswerWithReflexive φ).isSome = true := by
  cases he : MemoryWitness.countermodel? φ with
  | some w => rw [givenHeapAnswerWithReflexive_preserves w he]; rfl
  | none =>
    unfold givenHeapAnswerWithReflexive
    rw [he]
    change ((ResidueReason.givenHeapLiteralRead? φ).map (fun w => w.answer)).isSome = true
    simpa only [Option.isSome_map] using h

end Solidity.Decide
