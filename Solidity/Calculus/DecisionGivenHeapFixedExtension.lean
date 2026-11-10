import Solidity.Calculus.DecisionGivenHeapComputedExtension
import Solidity.Calculus.DecisionGivenHeapFixedReason
import Solidity.Calculus.DecisionGapAnswer

/-! # Lazy certified fixed-array given-heap answers
Every previous answer and exact counterstate remains first. Only an actual miss
consults the independently recognized all-heap fixed-array source certificate,
and only a miss of that consults the decided gap families (`gapAnswer?`).
-/
namespace Solidity.Decide

def givenHeapAnswerWithFixed {C : Contract} (φ : Fml C []) :
    Option (MemoryWitness.Answer φ) :=
  ((givenHeapAnswerWithComputed φ).orElse fun _ =>
    (ResidueReason.givenHeapFixedRead? φ).map fun w => .proved w.valid).orElse fun _ =>
    gapAnswer? φ

theorem givenHeapAnswerWithFixed_preserves {C : Contract} {φ : Fml C []}
    {answer : MemoryWitness.Answer φ} (h : givenHeapAnswerWithComputed φ = some answer) :
    givenHeapAnswerWithFixed φ = some answer := by
  unfold givenHeapAnswerWithFixed
  rw [h]
  rfl

theorem givenHeapAnswerWithFixed_old_complete {C : Contract} {φ : Fml C []}
    (h : (givenHeapAnswerWithComputed φ).isSome = true) :
    (givenHeapAnswerWithFixed φ).isSome = true := by
  cases he : givenHeapAnswerWithComputed φ with
  | none => rw [he] at h; cases h
  | some answer => rw [givenHeapAnswerWithFixed_preserves he]; rfl

theorem givenHeapAnswerWithFixed_source {C : Contract} {φ : Fml C []}
    (h : φ.givenHeapFixedReadReflexive = true) :
    (givenHeapAnswerWithFixed φ).isSome = true := by
  cases he : givenHeapAnswerWithComputed φ with
  | none =>
    unfold givenHeapAnswerWithFixed
    rw [he]
    have hs : ((ResidueReason.givenHeapFixedRead? φ).map (fun w =>
        (MemoryWitness.Answer.proved w.valid))).isSome = true := by
      simpa only [Option.isSome_map] using h
    change (((ResidueReason.givenHeapFixedRead? φ).map (fun w =>
      (MemoryWitness.Answer.proved w.valid))).orElse fun _ => gapAnswer? φ).isSome = true
    cases hc : (ResidueReason.givenHeapFixedRead? φ).map (fun w =>
        (MemoryWitness.Answer.proved w.valid)) with
    | none => rw [hc] at hs; cases hs
    | some a => rfl
  | some answer => rw [givenHeapAnswerWithFixed_preserves he]; rfl

/-- A member of a decided gap family is answered. -/
theorem givenHeapAnswerWithFixed_gap {C : Contract} {φ : Fml C []}
    (h : φ.gapCovered = true) : (givenHeapAnswerWithFixed φ).isSome = true := by
  unfold givenHeapAnswerWithFixed
  cases hc : (givenHeapAnswerWithComputed φ).orElse fun _ =>
      (ResidueReason.givenHeapFixedRead? φ).map fun w => .proved w.valid with
  | some a => rfl
  | none => exact gapAnswer_isSome h

theorem givenHeapAnswerWithFixed_preserves_countermodel {C : Contract} {φ : Fml C []}
    (w : {σ : State C [] // ¬ holds σ φ}) (h : MemoryWitness.countermodel? φ = some w) :
    givenHeapAnswerWithFixed φ =
      some (.refuted (fun (_ : State C []) => w.1) (fun _ => w.2)) :=
  givenHeapAnswerWithFixed_preserves (givenHeapAnswerWithComputed_preserves_countermodel w h)

end Solidity.Decide
