import Solidity.Calculus.Decision
import Solidity.Calculus.DecisionGivenHeapReason

/-! # Admission boundary for the given-heap literal-read source family
Actual coverage/proved results and old negative-state preservation.
This proof layer can depend on Decision; the low-level Answer module cannot.
-/
namespace Solidity.Decide.ResidueReason

/-- Every closed member is admitted under every unchanged waiver setting. -/
theorem GivenHeapLiteralReadReflexive.target {C : Contract} {φ : Fml C []}
    (w : GivenHeapLiteralReadReflexive φ) (waivers : Waivers) : φ.inTarget waivers = true := by
  rcases w with ⟨name, key, heq⟩
  subst φ
  rfl

/-- The actual memory coverage test includes this recognized source class. -/
theorem GivenHeapLiteralReadReflexive.memCovered {C : Contract} {φ : Fml C []}
    (w : GivenHeapLiteralReadReflexive φ) : φ.memCovered = true := by
  simp only [Fml.memCovered, givenHeapLiteralRead_complete w, Bool.or_true, Bool.true_or]

/-- No supplied coverage premise: exact source recognition provides the real route. -/
theorem GivenHeapLiteralReadReflexive.covered {C : Contract} {φ : Fml C []}
    (w : GivenHeapLiteralReadReflexive φ) : φ.Covered = true := by
  simp only [Fml.Covered, w.memCovered, Bool.or_true, Bool.true_or]

/-- The actual global verdict is proved; its positive certificate covers every state. -/
theorem GivenHeapLiteralReadReflexive.proved {C : Contract} {φ : Fml C []}
    (w : GivenHeapLiteralReadReflexive φ) : decideGoal φ = .proved := by
  have hd : decideGoal φ ≠ .unknown := decideGoal_complete w.covered w.hashFree
  cases he : decideGoal φ with
  | proved => rfl
  | refuted σ => exact False.elim ((decideGoal_refutes he) (w.validH σ))
  | unknown => exact False.elim (hd he)

/-- Successful finite countermodel search returns the actual unchanged candidate.
The Boolean certificate determines only the checker branch; the state comes
from the producer definition. -/
theorem givenHeapCandidate_answer {C : Contract} {φ : Fml C []}
    (hn : (φ.checkMemoryAt (MemoryWitness.candidate C)).isNo = true) :
    ∃ h : ¬ holds (MemoryWitness.candidate C) φ,
      MemoryWitness.countermodel? φ = some ⟨MemoryWitness.candidate C, h⟩ := by
  unfold MemoryWitness.countermodel?
  dsimp only
  cases hc : φ.checkMemoryAt (MemoryWitness.candidate C) with
  | no h => exact ⟨h, rfl⟩
  | yes h => rw [hc] at hn; cases hn
  | unknown => rw [hc] at hn; cases hn

/-- Exact returned-state preservation through the existing given-heap route.
Every routing premise is separately discharged for the concrete negative controls. -/
theorem givenHeapCandidate_route {C : Contract} {φ : Fml C []}
    (hHash : φ.hasHash = false) (hFirst : decideLeafA φ = .unknown)
    (hAlloc : φ.hasAllocAll = false)
    (hn : (φ.checkMemoryAt (MemoryWitness.candidate C)).isNo = true) :
    decideGoal φ = .refuted (MemoryWitness.candidate C) := by
  obtain ⟨href, hmodel⟩ := givenHeapCandidate_answer hn
  have hmem : decideMem φ = .refuted (MemoryWitness.candidate C) := by
    unfold decideMem
    rw [hAlloc]
    exact decideGiven_preserves_countermodel ⟨MemoryWitness.candidate C, href⟩ hmodel
  unfold decideGoal
  rw [hHash]
  change decideLeaf φ = .refuted (MemoryWitness.candidate C)
  unfold decideLeaf
  rw [hFirst, hmem]

end Solidity.Decide.ResidueReason
