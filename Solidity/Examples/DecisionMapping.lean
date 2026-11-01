import Solidity.Examples.DecisionArithmetic

namespace Solidity.Examples.Decision

open Solidity.Decide

set_option Elab.async false

/-! Array property blocks (M7, step 5): each verdict exact, each refutation
a state whose mapping holds, at each key, what the key's floor in the
index set held (`MRoot.surgery`, `FloorShape.rebuild`). -/

/-- info: ["proved", "refuted", "refuted", "proved", "refuted"] -/
#guard_msgs in #eval [apf, apfBad, apfOut, apfTwo, apfTwoBad].map verdict

/-- info: [true, true, true, true, true] -/
#guard_msgs in #eval [apf, apfBad, apfOut, apfTwo, apfTwoBad].map Fml.Covered

theorem apf_covered : apf.Covered = true := by decide +kernel
theorem apfBad_covered : apfBad.Covered = true := by decide +kernel

/-- `decideGoal_complete`, applied to an array property block. -/
theorem apf_answers : decideGoal apf ≠ .unknown := decideGoal_complete apf_covered rfl

/-- `decideLeaf_proved_iff`, applied: the false variant is not valid. -/
theorem apfBad_iff : decideLeaf apfBad = .proved ↔ Fml.Valid apfBad :=
  decideLeaf_proved_iff apfBad_covered

/-! A block over an inner mapping (`allow[3][k]`): every `uint` key along
`allow`'s mappings floored, the outer one too (`FloorShape.rebuild`). -/

theorem rowApf_inTarget : rowApf.inTarget {} = true := by decide +kernel

/-- info: ["proved", "refuted", "refuted", "proved"] -/
#guard_msgs in #eval [rowApf, rowBad, rowOut, rowVar].map verdict

/-- info: [true, true, true, true] -/
#guard_msgs in #eval [rowApf, rowBad, rowOut, rowVar].map Fml.Covered

theorem rowApf_covered : rowApf.Covered = true := by decide +kernel
theorem rowBad_covered : rowBad.Covered = true := by decide +kernel

/-- The entries of `allow`'s rows in a state: the outer keys', each row's. -/
def allowRows (σ : State Allow []) : List Nat :=
  match σ.storage.get (f := "allow") (T := .ref (.mapping .uint (.ref (.mapping .uint (.prim .uint))))) rfl with
  | .map m d => (m.toList.map fun e => match e.2 with | .map m' _ => m'.toList.length) ++
      [match d with | .map m' _ => m'.toList.length]

/-- info: ("refuted", true, true) -/
#guard_msgs in #eval (verdict rowFar, rowFar.Covered, rowFar.inTarget {})

/-! The refutation's `allow`, listed region by region (`regionList`, a
region left out where it holds the default, the far key's word): seven
rows of twelve entries and an empty default row, where the floor
construction listed `2^200` keys. -/

/-- info: some [12, 12, 12, 12, 12, 12, 12, 0] -/
#guard_msgs in #eval match decideGoal rowFar with | .refuted σ => some (allowRows σ) | _ => none

/-- The far key's leaf, by the kernel. -/
theorem rowFar_covered : rowFar.Covered = true := by decide +kernel

/-- `decideGoal_complete`, applied to a block over an inner mapping. -/
theorem rowApf_answers : decideGoal rowApf ≠ .unknown := decideGoal_complete rowApf_covered rfl

/-- `decideLeaf_proved_iff`, applied: the verdict is exact. -/
theorem rowApf_iff : decideLeaf rowApf = .proved ↔ Fml.Valid rowApf :=
  decideLeaf_proved_iff rowApf_covered

/-- info: [false, false, true, true] -/
#guard_msgs in #eval [gridApf, strictSorted, sortedLe, columnApf].map (Fml.inTarget {})

/-- A two-variable block over a root: covered (nine instances, nineteen
reads), decided by the walk (`docs/automation.md`, M7). -/
theorem sortedLe_covered : sortedLe.Covered = true := by
  -- The quantified branch suffices. Reducing the earlier exact-fragment
  -- recognizer first duplicates the nineteen-read expansion in the kernel.
  have cover (φ : Fml Allow []) (h : φ.quantCovered = true) : φ.Covered = true := by
    simp only [Fml.Covered, Fml.CoveredA, h, Bool.or_true, Bool.true_or]
  exact cover sortedLe (by decide +kernel)

/-- The sorted-mapping premise instantiated at keys `2` and `5`. -/
theorem sortedLe_valid : Fml.Valid sortedLe := by
  intro σ h
  exact h (PrimTy.ofIntD .uint 2) (PrimTy.ofIntD .uint 5) rfl

/-- The original decision function's exact verdict, without repeating its
expensive binary-derivative search at every library build. -/
theorem sortedLe_decision : decideGoal sortedLe = .proved := by
  have noHash (φ : Fml Allow []) (hh : φ.hasHash = false)
      (h : decideLeaf φ = .proved) : decideGoal φ = .proved := by
    simp only [decideGoal, hh, Bool.false_eq_true, if_false]
    exact h
  exact noHash sortedLe rfl
    ((decideLeaf_proved_iff (φ := sortedLe) sortedLe_covered).mpr sortedLe_valid)

/-- A cheap output replay carrying equality to the original compiled verdict.
The certificate is checked by the kernel; no expected result is assumed. -/
private def sortedLeReplay : {s : String // s = verdict sortedLe} :=
  have spell (φ : Fml Allow []) (h : decideGoal φ = .proved) : "proved" = verdict φ := by
    simp only [verdict, h]
  ⟨"proved", spell sortedLe sortedLe_decision⟩

/-- info: "proved" -/
#guard_msgs in #eval sortedLeReplay.val

/-- The certified decision cannot replay the opposite verdict. -/
theorem sortedLe_not_refuted : verdict sortedLe ≠ "refuted" := by
  intro h
  have wrong : ("proved" : String) = "refuted" := sortedLeReplay.property.trans h
  exact (by decide +kernel : ("proved" : String) ≠ "refuted") wrong


end Solidity.Examples.Decision
