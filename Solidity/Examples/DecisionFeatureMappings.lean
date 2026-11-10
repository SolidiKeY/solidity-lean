import Solidity.Examples.Decision
import Solidity.Tools.Common

/-! Mapping and array-property decision regressions. Guards the original verdict/coverage checks against exceeding the unchanged per-module replay budget. -/

namespace Solidity.Examples.Decision

open Solidity.Decide

set_option Elab.async false

/-- info: ["proved", "proved", "refuted", "refuted", "proved", "proved", "proved"] -/
#guard_msgs in #eval [netOk, netSame, netNeg, netOther, netStore, netWrite, netDistinct].map verdict

/-- info: true -/
#guard_msgs in #eval [netOk, netSame, netNeg, netOther, netStore, netWrite, netDistinct].all Fml.Covered

-- Four ledger reads: decided by the walk (M7, the running time).
/-- info: "proved" -/
#guard_msgs in #eval verdict netSwap

theorem net_covered : netOk.Covered = true := by decide +kernel
theorem netSame_covered : netSame.Covered = true := by decide +kernel
theorem netSwap_covered : netSwap.Covered = true := by decide +kernel

/-- `decideLeaf_proved_iff`, applied to a leaf that reads the ledger. -/
theorem net_iff : decideLeaf netOk = .proved ↔ Fml.Valid netOk :=
  decideLeaf_proved_iff net_covered

/-- info: [true, false, false, false] -/
#guard_msgs in #eval [apf, notApf, guardNe, guardArith].map (Fml.inTarget {})

/-- A program-free leaf both covered and in the named fragment. -/
theorem nested_inTarget : nested.inTarget {} = true := by decide +kernel

/-- `apf` is in the named fragment, and decided (below). -/
theorem apf_inTarget : apf.inTarget {} = true := by decide +kernel

/-- info: ["proved", "unknown"] -/
#guard_msgs in #eval [apf, notApf].map verdict

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

end Solidity.Examples.Decision
