import Solidity.Examples.Decision

/-!
# The closer's decision on blocks over storage arrays (M7, feature 32)

`decideLeaf` (`Calculus/Decision.lean`) on a negative block over a storage
array, over `Gaps` of `Examples/Decision.lean`: the counterexample once
pinned there (`gapArrayBlock`, proved), its false variant (`arrayBlockBad`,
an element past the guard, refuted) and the shape Bradley, Manna and Sipma
state, a guard against the live length (`arrayLenBlock`, proved).  The
pipeline is `arrayBlockReduction?` (`Calculus/ArrayBlock.lean`): the
lengths read as atoms, the blocks instantiated at the index set, the
Theory's slot reads folded, the array reads cut.  Coverage and the
fragment are the kernel's; the verdicts are the compiled ones, run one
after another as `Examples/Decision.lean`'s are.
-/

namespace Solidity.Examples.Decision

open Solidity.Decide

set_option Elab.async false

section Arrays

local instance : InContract := ⟨Gaps⟩

/-- `gapArrayBlock` read past its guard: refuted. -/
def arrayBlockBad : Fml Gaps [] :=
  dl!{ (∀ uint i; i < 3 → arr[i] == 0) → arr.length > 5 → arr[4] == 0 }

/-- A block guarded by the live length: proved. -/
def arrayLenBlock : Fml Gaps [] :=
  dl!{ (∀ uint i; i < arr.length → arr[i] == 0) → arr.length > 2 → arr[2] == 0 }

end Arrays

theorem gapArrayBlock_block : gapArrayBlock.arrayBlockCovered = true := by decide +kernel
theorem arrayBlockBad_block : arrayBlockBad.arrayBlockCovered = true := by decide +kernel
theorem arrayBlockBad_inTarget : arrayBlockBad.inTarget {} = true := by decide +kernel

theorem gapArrayBlock_covered : gapArrayBlock.Covered = true := by
  simp only [Fml.Covered, Fml.CoveredA, gapArrayBlock_block, Bool.or_true, Bool.true_or]

theorem arrayBlockBad_covered : arrayBlockBad.Covered = true := by
  simp only [Fml.Covered, Fml.CoveredA, arrayBlockBad_block, Bool.or_true, Bool.true_or]

/-- `decideGoal_complete`, applied: no hash, so no premise. -/
theorem gapArrayBlock_answers : decideGoal gapArrayBlock ≠ .unknown :=
  decideGoal_complete gapArrayBlock_covered rfl
theorem arrayBlockBad_answers : decideGoal arrayBlockBad ≠ .unknown :=
  decideGoal_complete arrayBlockBad_covered rfl
theorem gapArrayBlock_iff : decideLeaf gapArrayBlock = .proved ↔ Fml.Valid gapArrayBlock :=
  decideLeaf_proved_iff gapArrayBlock_covered

/-- info: ["proved", "refuted", "proved"] -/
#guard_msgs in #eval [verdict gapArrayBlock, verdict arrayBlockBad, verdict arrayLenBlock]

end Solidity.Examples.Decision
