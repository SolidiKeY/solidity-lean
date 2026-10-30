import Solidity.Backend.MemoryOps.ObjectFrames

/-! Inhabited published word ownership and reference-array representation.
The old target still represents the framed parent, but cannot represent the
changed child without actual target writes. -/
namespace Solidity.Backend.MemoryOps.ObjectControls
open Solidity.Evm
open Solidity.Evm.Memory.Objects
private abbrev B : RefTy := .array (.prim .bool)
private abbrev P : RefTy := .fixed (.ref B) 2
private abbrev H : HTy := [B, P]
private def child : HRef H B := ⟨0, rfl⟩
private def parent : HRef H P := ⟨1, rfl⟩
private def hp : Heap H := (⟨[true, false], by decide⟩, ⟨[child, child], rfl⟩, ())
private def base (i : Nat) : Fin Evm.W := if i = 0 then ⟨8, by decide⟩ else ⟨16, by decide⟩
private def m : Machine :=
  { Machine.init with
    stack := [Word.val ⟨77, by decide⟩]
    mem := fun a =>
      if a = 8 then Word.val ⟨2, by decide⟩ else
      if a = 9 then Word.val ⟨1, by decide⟩ else
      if a = 10 then Word.val ⟨0, by decide⟩ else Word.val ⟨8, by decide⟩ }
private theorem refs {R : RefTy} (r : HRef H R) :
    (R = B ∧ HEq r child) ∨ (R = P ∧ HEq r parent) := by
  rcases r with ⟨i, hi⟩
  cases i with
  | zero => cases hi; exact .inl ⟨rfl, HEq.rfl⟩
  | succ i => cases i with
    | zero => cases hi; exact .inr ⟨rfl, HEq.rfl⟩
    | succ i => cases hi

/-- Nonempty child and nonprimitive parent have separated positive intervals. -/
theorem initial_ownership : Ownership hp base 4 := by
  refine ⟨?_, ?_, ?_⟩
  · intro R r
    rcases refs r with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ <;> cases hr <;> decide +kernel
  · intro R r
    rcases refs r with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ <;> cases hr
      <;> simp only [cells, Heap.len, MObj.elems_dyn] <;> decide +kernel
  · intro R Q r q hn
    rcases refs r with ⟨rfl, hr⟩ | ⟨rfl, hr⟩ <;> cases hr
      <;> rcases refs q with ⟨rfl, hq⟩ | ⟨rfl, hq⟩ <;> cases hq
      <;> first | exact (hn rfl).elim
                | simp only [cells, Heap.len, MObj.elems_dyn]; decide +kernel

/-- Both repeated reference elements are represented by the actual child base. -/
theorem initial_parent : ArrayRepr hp parent .fixed base m := by
  refine ⟨by decide +kernel, ?_, ?_⟩
  · intro hh
    cases (by simpa only [header] using hh : (0 : Nat) = 1)
  · intro i v hv
    rw [MObj.elems_fixed] at hv
    cases i with
    | zero => cases hv; rfl
    | succ i => cases i with
      | zero => cases hv; rfl
      | succ i => cases hv

/-- The original target also represents the child before its contents change. -/
theorem initial_child : ArrayRepr hp child .dyn base m := by
  refine ⟨by simp only [cells, Heap.len, MObj.elems_dyn]; decide +kernel,
    by intro _; simp only [Heap.len, MObj.elems_dyn]; rfl, ?_⟩
  intro i v hv
  rw [MObj.elems_dyn] at hv
  cases i with
  | zero => cases hv; rfl
  | succ i => cases i with
    | zero => cases hv; rfl
    | succ i => cases hv
private theorem space : 0 + [false].length ≤ hp.len child .dyn := by
  simp only [Heap.len, MObj.elems_dyn]; decide
private def out := overwriteSlice hp child .dyn 0 [false] space

/-- Actual range transport retains ownership and a reference-containing object
representation, without changing the target machine or its stack tail. -/
theorem frame_application :
    Ownership out base 4 ∧ ArrayRepr out parent .fixed base m ∧
      m.stack = [.val ⟨77, by decide⟩] :=
  ⟨overwriteSlice_ownership hp child .dyn 0 [false] space initial_ownership,
    overwriteSlice_other_repr hp child .dyn 0 [false] space parent .fixed (by decide) initial_parent, rfl⟩

/-- The source contents really changed, with length and parent identities intact. -/
theorem changed_child : MObj.elems .dyn (out.get child) = [false, false] ∧
    (MObj.elems .fixed (out.get parent)).map HRef.id = [0, 0] := by
  constructor
  · rw [out, overwriteSlice_elems]
    simp only [MObj.elems_dyn]; rfl
  · rw [out, overwriteSlice_frame hp child parent .dyn 0 [false] space (by decide)]
    simp only [MObj.elems_fixed]; rfl

/-- Merely transporting ownership must not certify stale destination words. -/
theorem stale_target_negative : ¬ ArrayRepr out child .dyn base m := by
  intro ho
  have he := ho.elements 0 false (by rw [changed_child.1]; rfl)
  change (.val (⟨1, by decide⟩ : Fin Evm.W) : Word) = .val ⟨0, by decide⟩ at he
  have hv := Word.val.inj he
  have hn := congrArg Fin.val hv
  cases hn

/-- Removing address separation contradicts the published ownership relation. -/
theorem colliding_base_negative : ¬ Ownership hp (fun _ => ⟨8, by decide⟩) 4 := by
  intro ho
  have he := ho.base_injective child parent rfl
  change 0 = 1 at he
  cases he

/-- info: 'Solidity.Backend.MemoryOps.ObjectControls.initial_ownership' depends on axioms: [propext] -/
#guard_msgs in #print axioms initial_ownership
/-- info: 'Solidity.Backend.MemoryOps.ObjectControls.initial_parent' depends on axioms: [propext] -/
#guard_msgs in #print axioms initial_parent
/-- info: 'Solidity.Backend.MemoryOps.ObjectControls.initial_child' depends on axioms: [propext] -/
#guard_msgs in #print axioms initial_child
/-- info: 'Solidity.Backend.MemoryOps.ObjectControls.frame_application' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms frame_application
/-- info: 'Solidity.Backend.MemoryOps.ObjectControls.changed_child' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms changed_child
/-- info: 'Solidity.Backend.MemoryOps.ObjectControls.stale_target_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms stale_target_negative
/-- info: 'Solidity.Backend.MemoryOps.ObjectControls.colliding_base_negative' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms colliding_base_negative
end Solidity.Backend.MemoryOps.ObjectControls
