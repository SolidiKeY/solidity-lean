import Solidity.Examples.DecisionGapHashes

namespace Solidity.Examples.Decision

open Solidity.Decide

set_option Elab.async false

/-! ### Storage arrays at symbolic indices (M7, plan step 6)

A checked read `xs[i]` halts past the live length; the Theory reads a
formula's `xs[i]` at any slot, the default past every slot.  Update pushing
takes the Theory's reads exactly (`Tm.toLT`), and `arrayReduction?` cuts the
array reads to atoms with what actual arrays make of them
(`Calculus/ArrayCut.lean`), the slot tests a length check settles folded
(`LTm.hasFold`).  A refutation's arrays are rebuilt from the atoms, the
counterassignment first shrunk. -/


def Arrays : Contract := contract!{ uint[] xs; uint[4] row; mapping(uint => uint) owed; }

section

local instance : InContract := ⟨Arrays⟩

/-- An in-range read, its element read again in the postcondition (the
Theory's read), and a false variant. -/
def inRange : Fml Arrays [] := dl!{ ∀ uint i; i < xs.length → [ uint x = xs[i]; ] x == xs[i] }
def inRangeBad : Fml Arrays [] := dl!{ ∀ uint i; i < xs.length → [ uint x = xs[i]; ] x == 0 }
/-- Under the diamond the read must return: past the length it halts. -/
def pastEnd : Fml Arrays [] := dl!{ ∀ uint i; ⟨ uint x = xs[i]; ⟩ true }
def inRangeReturns : Fml Arrays [] := dl!{ ∀ uint i; i < xs.length → ⟨ uint x = xs[i]; ⟩ true }
/-- A write then a read at equal symbolic indices, at different ones (the
read keeps the old word), and at any (refuted). -/
def writeSame : Fml Arrays [] :=
  dl!{ ∀ uint i; ∀ uint j; i == j → [ xs[i] = 5; uint x = xs[j]; ] x == 5 }
def writeKeep : Fml Arrays [] :=
  dl!{ ∀ uint i; ∀ uint j; i != j → j < xs.length → xs[j] == 7 → [ xs[i] = 5; ] xs[j] == 7 }
def writeOther : Fml Arrays [] :=
  dl!{ ∀ uint i; ∀ uint j; [ xs[i] = 5; uint x = xs[j]; ] x == 5 }
def writeRead : Fml Arrays [] := dl!{ ∀ uint i; [ xs[i] = 5; ] xs[i] == 5 }
/-- A fixed array: a write below its length read back, and one past it. -/
def rowWrite : Fml Arrays [] := dl!{ ∀ uint i; i < 4 → [ row[i] = 5; ] row[i] == 5 }
def rowPast : Fml Arrays [] := dl!{ ∀ uint i; ⟨ row[i] = 5; ⟩ true }
/-- Past the live length the Theory reads the slots there, not the default;
past a fixed array's length, the default. -/
def shadowRead : Fml Arrays [] := dl!{ ∀ uint i; i >= xs.length → xs[i] == 0 }
def rowPastRead : Fml Arrays [] := dl!{ ∀ uint i; i >= 4 → row[i] == 0 }
/-- An array read stored in a mapping. -/
def owedRead : Fml Arrays [] :=
  dl!{ ∀ uint i; i < xs.length → [ owed[i] = xs[i]; ] owed[i] == xs[i] }

end

/-- info: "proved" -/
#guard_msgs in #eval verdict inRange
/-- info: "refuted" -/
#guard_msgs in #eval verdict inRangeBad
/-- info: "refuted" -/
#guard_msgs in #eval verdict pastEnd
/-- info: "proved" -/
#guard_msgs in #eval verdict inRangeReturns
/-- info: "proved" -/
#guard_msgs in #eval verdict writeSame
/-- info: "proved" -/
#guard_msgs in #eval verdict writeKeep
/-- info: "refuted" -/
#guard_msgs in #eval verdict writeOther
/-- info: "proved" -/
#guard_msgs in #eval verdict writeRead
/-- info: "proved" -/
#guard_msgs in #eval verdict rowWrite
/-- info: "refuted" -/
#guard_msgs in #eval verdict rowPast
/-- info: "refuted" -/
#guard_msgs in #eval verdict shadowRead
/-- info: "proved" -/
#guard_msgs in #eval verdict rowPastRead
/-- info: "proved" -/
#guard_msgs in #eval verdict owedRead

/-- Kernel-checked coverage: the read past the length, the write then read
at equal indices, and the Theory's read. -/
theorem pastEnd_covered : pastEnd.Covered = true := by decide +kernel
theorem writeSame_covered : writeSame.Covered = true := by decide +kernel
theorem inRange_covered : inRange.Covered = true := by decide +kernel

/-- `decideLeaf_complete`, applied to a read past the length. -/
theorem pastEnd_answers : decideLeaf pastEnd ≠ .unknown := decideLeaf_complete pastEnd_covered

/-- `decideLeaf_proved_iff`, applied: the verdict on an in-range read is exact. -/
theorem inRange_iff : decideLeaf inRange = .proved ↔ Fml.Valid inRange :=
  decideLeaf_proved_iff inRange_covered

/-- `decideGoal_complete`, applied: no hash, so no premise. -/
theorem writeSame_answers : decideGoal writeSame ≠ .unknown :=
  decideGoal_complete writeSame_covered rfl

/-! Two leaves of the named fragment once pinned as counterexamples to
`DecisionTheorem` (`Gaps`): plain storage-array reads, now decided. -/

theorem arrayRead_inTarget : arrayRead.inTarget {} = true := by decide +kernel
theorem fixedRead_inTarget : fixedRead.inTarget {} = true := by decide +kernel
theorem arrayRead_covered : arrayRead.Covered = true := by decide +kernel
theorem fixedRead_covered : fixedRead.Covered = true := by decide +kernel

/-- info: ["proved", "proved"] -/
#guard_msgs in #eval [arrayRead, fixedRead].map verdict


end Solidity.Examples.Decision
