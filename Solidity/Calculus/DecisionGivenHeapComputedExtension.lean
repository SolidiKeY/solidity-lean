import Solidity.Calculus.DecisionSourceAnswer
import Solidity.Calculus.DecisionGivenHeapComputedReason

/-! # Lazy certified computed-index given-heap answers
Every previous answer and exact counterstate remains first. Only an actual miss
consults the independently recognized all-heap computed-index source certificate.
-/
namespace Solidity.Decide

def givenHeapAnswerWithComputed {C : Contract} (φ : Fml C []) :
    Option (MemoryWitness.Answer φ) :=
  (givenHeapAnswerWithSources φ).orElse fun _ =>
    (ResidueReason.givenHeapLinearRead? φ).map fun w => .proved w.valid

theorem givenHeapAnswerWithComputed_preserves {C : Contract} {φ : Fml C []}
    {answer : MemoryWitness.Answer φ} (h : givenHeapAnswerWithSources φ = some answer) :
    givenHeapAnswerWithComputed φ = some answer := by
  unfold givenHeapAnswerWithComputed
  rw [h]
  rfl

theorem givenHeapAnswerWithComputed_old_complete {C : Contract} {φ : Fml C []}
    (h : (givenHeapAnswerWithSources φ).isSome = true) :
    (givenHeapAnswerWithComputed φ).isSome = true := by
  cases he : givenHeapAnswerWithSources φ with
  | none => rw [he] at h; cases h
  | some answer => rw [givenHeapAnswerWithComputed_preserves he]; rfl

theorem givenHeapAnswerWithComputed_source {C : Contract} {φ : Fml C []}
    (h : φ.givenHeapLinearReadReflexive = true) :
    (givenHeapAnswerWithComputed φ).isSome = true := by
  cases he : givenHeapAnswerWithSources φ with
  | none =>
    unfold givenHeapAnswerWithComputed
    rw [he]
    change ((ResidueReason.givenHeapLinearRead? φ).map (fun w =>
      (MemoryWitness.Answer.proved w.valid))).isSome = true
    simpa only [Option.isSome_map] using h
  | some answer => rw [givenHeapAnswerWithComputed_preserves he]; rfl

theorem givenHeapAnswerWithComputed_preserves_countermodel {C : Contract} {φ : Fml C []}
    (w : {σ : State C [] // ¬ holds σ φ}) (h : MemoryWitness.countermodel? φ = some w) :
    givenHeapAnswerWithComputed φ =
      some (.refuted (fun (_ : State C []) => w.1) (fun _ => w.2)) :=
  givenHeapAnswerWithComputed_preserves (givenHeapAnswerWithSources_preserves_countermodel w h)

end Solidity.Decide
