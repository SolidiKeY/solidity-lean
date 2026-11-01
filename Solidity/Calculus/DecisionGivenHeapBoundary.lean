import Solidity.Calculus.Decision
import Solidity.Calculus.DecisionGivenHeapReason

/-! # Admission boundary for the given-heap literal-read source family
This proof layer can depend on Decision; the low-level Answer module cannot.
No coverage extension is asserted; existing negative-result routing is certified below.
-/
namespace Solidity.Decide.ResidueReason

/-- Every closed member is admitted under every unchanged waiver setting. -/
theorem GivenHeapLiteralReadReflexive.target {C : Contract} {φ : Fml C []}
    (w : GivenHeapLiteralReadReflexive φ) (waivers : Waivers) : φ.inTarget waivers = true := by
  rcases w with ⟨name, key, heq⟩
  subst φ
  rfl

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
    change (match MemoryWitness.countermodel? φ with
      | some w => LeafVerdict.refuted w.1
      | none => .unknown) = .refuted (MemoryWitness.candidate C)
    rw [hmodel]
  unfold decideGoal
  rw [hHash]
  change decideLeaf φ = .refuted (MemoryWitness.candidate C)
  unfold decideLeaf
  rw [hFirst, hmem]

end Solidity.Decide.ResidueReason
