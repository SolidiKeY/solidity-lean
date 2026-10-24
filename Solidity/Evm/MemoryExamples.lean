import Solidity.Evm.Memory

/-! Concrete positive and negative witnesses for the memory instruction and
array simulation layer. These do not assert whole-program memory coverage. -/
namespace Solidity.Evm.Memory.Examples

private def H : HTy := [.array (.prim .uint)]
private def ref : HRef H (.array (.prim .uint)) := ⟨0, rfl⟩
private def base : Fin W := ⟨16, by decide⟩
private def hp : Heap H :=
  (⟨[indexValue ⟨7, by decide⟩, indexValue ⟨9, by decide⟩], by decide⟩, ())

private def machine : Machine :=
  { Machine.init with mem := fun a =>
      if a = 16 then w[2] else if a = 17 then w[7] else if a = 18 then w[9] else w[0] }

/-- The representation assumptions have an actual populated typed-heap witness. -/
theorem fixture_repr : ArrayRepr hp ref base machine := by
  constructor
  · change 16 + 1 + hp.len ref .dyn ≤ W
    simp only [Heap.len, hp, ref, H, Heap.get, Objs.get, MObj.elems_dyn,
      List.length_cons, List.length_nil]
    decide +kernel
  · change machine.mem 16 = .val (wmod (hp.len ref .dyn))
    simp only [Heap.len, hp, ref, H, Heap.get, Objs.get, MObj.elems_dyn,
      List.length_cons, List.length_nil]
    rfl
  · intro i v hv
    simp only [hp, ref, H, Heap.get, Objs.get, MObj.elems_dyn] at hv
    cases i with
    | zero =>
      cases hv
      exact ⟨⟨7, by decide⟩, rfl, rfl⟩
    | succ i =>
      cases i with
      | zero =>
        cases hv
        exact ⟨⟨9, by decide⟩, rfl, rfl⟩
      | succ i => cases hv

private def top : Out → Option Nat
  | .ok m _ => match m.stack with | .val v :: _ => some v.1 | _ => none
  | _ => none

private def cell (a : Nat) : Out → Option Nat
  | .ok m _ => match m.mem a with | .val v => some v.1 | _ => none
  | _ => none

private def reverted : Out → Bool
  | .revert => true
  | _ => false

/-- Index one reads the second source element, and not the first one. -/
example : top (run (readArrayCode base) (machine.push w[1])) = some 9 := by
  decide +kernel
example : top (run (readArrayCode base) (machine.push w[1])) ≠ some 7 := by
  decide +kernel

/-- The first index outside the live array is rejected before the memory read. -/
example : reverted (run (readArrayCode base) (machine.push w[2])) = true := by
  decide +kernel
example : reverted (run (writeArrayCode base) ((machine.push w[5]).push w[2])) = true := by
  decide +kernel

private def writeThenRead : List Instr :=
  [.push w[5], .push w[0]] ++ writeArrayCode base ++ [.push w[0]] ++ readArrayCode base

/-- Aliases sharing an array base observe the write, and the other element survives. -/
example : top (run writeThenRead machine) = some 5 := by decide +kernel
example : cell 18 (run writeThenRead machine) = some 9 := by decide +kernel
example : cell 16 (run writeThenRead machine) = some 2 := by decide +kernel
example : cell 3 (run writeThenRead machine) = some 0 := by decide +kernel

/-- A populated array cannot satisfy the representation at a wrapping base. -/
example : ¬ ArrayRepr hp ref wMax machine := by
  intro h
  have hs := h.space
  simp only [wMax_def, Heap.len, hp, ref, H, Heap.get, Objs.get, MObj.elems_dyn,
    List.length_cons, List.length_nil] at hs
  have hw : 0 < W := W_pos
  omega

/-- A symbolic storage slot cannot be used as a numeric memory address. -/
example : Instr.mloadAt.step (machine.push (.slot (.root 0))) = .fault := rfl
example : Instr.mstoreAt.step (machine.push w[0]) = .fault := rfl

end Solidity.Evm.Memory.Examples
