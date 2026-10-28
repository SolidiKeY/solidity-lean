import Solidity.Calculus.MemFloor

/-!
# Primitive-memory reconstruction controls

Compiled object observations, not source/compiler/EVM fixtures. Named
theorems below separately certify representative controls in the kernel.
These controls preserve empty-array halting, strict memory bounds, array
kind, and retained reads. They do not claim negative-block coverage.
-/

namespace Solidity.Examples.MemoryFloor

open Solidity.Decide

private abbrev uintElems (o : MObj [] (.array (.prim .uint))) : List PrimTy.uint.Denote :=
  MObj.elems (H := []) (ArrTy.dyn (E := .prim .uint)) o

private abbrev boolElems (o : MObj [] (.fixed (.prim .bool) 3)) : List PrimTy.bool.Denote :=
  MObj.elems (H := []) (ArrTy.fixed (E := .prim .bool) (n := 3)) o

private theorem uintOk : mxArrOk (ArrTy.dyn (E := .prim .uint)) := by
  change True
  trivial

private theorem bool3Ok : mxArrOk (ArrTy.fixed (E := .prim .bool) (n := 3)) := by
  change 3 < 2 ^ 256
  decide

/-- A two-word fresh-array object; the heap typing is irrelevant to words. -/
def words : MObj [] (.array (.prim .uint)) :=
  ⟨[uintOfNat 7, uintOfNat 9], by decide⟩

/-- The length is a breakpoint, so the nonsampled slot is safely floored. -/
def rebuilt : MObj [] (.array (.prim .uint)) :=
  mxFloorRebuild (H := []) .dyn uintOk words [0, 2]

#guard decide ((uintElems rebuilt).length = 2)
#guard decide ((uintElems rebuilt)[0]? = some (uintOfNat 7))
#guard decide ((uintElems rebuilt)[1]? = some (uintOfNat 7))
#guard decide ((uintElems rebuilt)[1]? ≠ some (uintOfNat 9))
#guard decide ((uintElems rebuilt)[2]? = none)
#guard decide ((uintElems rebuilt)[3]? = none)

/-- Keeping a sample fixes its read, as well as the length. -/
theorem retained_read :
    (uintElems (mxFloorRebuild (H := []) .dyn uintOk words [0, 1, 2]))[1]? =
      (uintElems words)[1]? :=
  mxFloorRebuild_at .dyn uintOk words [0, 1, 2] (by decide +kernel) (by decide)

/-- Empty memory stays empty: the original negative-block gap must retain
this counterexample rather than defaulting its concluding read to zero. -/
def emptyWords : MObj [] (.array (.prim .uint)) := ⟨[], by decide⟩

#guard decide ((uintElems (mxFloorRebuild (H := []) .dyn uintOk emptyWords [0])).length = 0)
#guard decide ((uintElems (mxFloorRebuild (H := []) .dyn uintOk emptyWords [0]))[0]? = none)

/-- Fixed bool arrays retain their shape and use the same read theorem. -/
def flags : MObj [] (.fixed (.prim .bool) 3) := ⟨[true, false, true], rfl⟩

#guard decide ((boolElems (mxFloorRebuild (H := []) .fixed bool3Ok flags [0, 3])).length = 3)
#guard decide ((boolElems (mxFloorRebuild (H := []) .fixed bool3Ok flags [0, 3]))[1]? = some true)
#guard decide ((boolElems (mxFloorRebuild (H := []) .fixed bool3Ok flags [0, 3]))[3]? = none)

/- Negative control: without the length breakpoint, the old floored read
can succeed where the rebuilt array's original-index read halts. -/
#guard decide ((uintElems (mxFloorRebuild (H := []) .dyn uintOk words [0]))[2]? ≠
  (uintElems words)[mxFloorIndex [0] 2]?)

/- Negative control: unrelated guard thresholds are not preserved by a
floor until their operands/successors are retained by preparation. -/
#guard decide (3 < mxFloorIndex [0, 10] 4) ≠ decide (3 < 4)

/-- The empty-array boundary is checked by the kernel as well. -/
theorem empty_read_halts :
    (uintElems (mxFloorRebuild (H := []) .dyn uintOk emptyWords [0]))[0]? = none := by
  decide +kernel

/-- A missing length breakpoint really breaks the optional-read equation. -/
theorem missing_length_changes_definedness :
    (uintElems (mxFloorRebuild (H := []) .dyn uintOk words [0]))[2]? ≠
      (uintElems words)[mxFloorIndex [0] 2]? := by
  decide +kernel

/-- A decreasing floor alone does not transfer an unrelated strict guard. -/
theorem missing_threshold_changes_guard :
    decide (3 < mxFloorIndex [0, 10] 4) ≠ decide (3 < 4) := by
  decide +kernel

#print axioms retained_read
#print axioms empty_read_halts
#print axioms missing_length_changes_definedness
#print axioms missing_threshold_changes_guard

end Solidity.Examples.MemoryFloor
