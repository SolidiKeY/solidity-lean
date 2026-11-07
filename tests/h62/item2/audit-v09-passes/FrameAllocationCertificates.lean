import Solidity.Yul.Compilation.Allocation

/-! Guard argument/result offset collisions and gaps in the existing arity-indexed
frame footprint, including empty regions and nonzero bases. These generic
certificates extend Frame; no calling convention, runtime-content preservation,
Source adequacy or native execution is inferred. Keep the intrinsic allocation
module unchanged so clients need not elaborate this additive audit companion. -/
namespace Solidity.Yul.Compilation

/-- Every argument occupies its argument interval, including nonzero bases. -/
theorem Frame.arg_bounds {a r l : Nat} (f : Frame a r l) (i : Fin a) :
    f.base ≤ f.arg i ∧ f.arg i < f.base + a :=
  ⟨Nat.le_add_right _ _, Nat.add_lt_add_left i.isLt f.base⟩

/-- Result offsets start after all arguments, not at the frame base. -/
theorem Frame.result_bounds {a r l : Nat} (f : Frame a r l) (i : Fin r) :
    f.base + a ≤ f.result i ∧ f.result i < f.base + a + r :=
  ⟨Nat.le_add_right _ _, Nat.add_lt_add_left i.isLt (f.base + a)⟩

/-- The local interval starts after both argument and result arities. -/
theorem Frame.local_bounds {a r l : Nat} (f : Frame a r l) (i : Fin l) :
    f.base + a + r ≤ f.local i ∧ f.local i < f.limit := by
  exact ⟨Nat.le_add_right _ _, f.local_bound i⟩

theorem Frame.arg_injective {a r l : Nat} (f : Frame a r l) (i j : Fin a)
    (h : f.arg i = f.arg j) : i = j :=
  label_injective f.base i j h

theorem Frame.result_injective {a r l : Nat} (f : Frame a r l) (i j : Fin r)
    (h : f.result i = f.result j) : i = j :=
  label_injective (f.base + a) i j h

theorem Frame.local_injective {a r l : Nat} (f : Frame a r l) (i j : Fin l)
    (h : f.local i = f.local j) : i = j :=
  label_injective (f.base + a + r) i j h

/-- Guard gaps or shifted regions in the frame footprint: every position inside
it is an actual arity-indexed argument, result or local. Empty regions need no
special case and cannot supply a fabricated index. This is allocation only. -/
theorem Frame.covers {a r l : Nat} (f : Frame a r l) (pos : Nat)
    (lower : f.base ≤ pos) (upper : pos < f.limit) :
    (∃ i : Fin a, f.arg i = pos) ∨
    (∃ i : Fin r, f.result i = pos) ∨
    (∃ i : Fin l, f.local i = pos) := by
  simp only [Frame.limit] at upper
  by_cases arg : pos < f.base + a
  · refine Or.inl ⟨⟨pos - f.base, by omega⟩, ?_⟩
    simp only [Frame.arg]
    omega
  · by_cases result : pos < f.base + a + r
    · refine Or.inr (Or.inl ⟨⟨pos - (f.base + a), by omega⟩, ?_⟩)
      simp only [Frame.result]
      omega
    · refine Or.inr (Or.inr ⟨⟨pos - (f.base + a + r), by omega⟩, ?_⟩)
      simp only [Frame.local]
      omega


/-- Nonzero-base combination witness: argument/result offsets coexist with the
last valid local, but the exclusive limit cannot name a local. -/
theorem frame_allocation_witness :
    ((Frame.arg (a := 2) (r := 1) (l := 2) ⟨7⟩ 1 = 8) ∧
      (Frame.result (a := 2) (r := 1) (l := 2) ⟨7⟩ 0 = 9) ∧
      (Frame.local (a := 2) (r := 1) (l := 2) ⟨7⟩ 1 = 11)) ∧
    ¬ ∃ i : Fin 2, Frame.local (a := 2) (r := 1) (l := 2) ⟨7⟩ i = 12 := by
  refine ⟨⟨rfl, rfl, rfl⟩, ?_⟩
  rintro ⟨i, h⟩
  have bound := (Frame.local_bounds (a := 2) (r := 1) (l := 2) ⟨7⟩ i).2
  rw [h] at bound
  exact Nat.lt_irrefl 12 bound

/-- info: 'Solidity.Yul.Compilation.Frame.arg_bounds' does not depend on any axioms -/
#guard_msgs in
#print axioms Frame.arg_bounds
/-- info: 'Solidity.Yul.Compilation.Frame.result_bounds' does not depend on any axioms -/
#guard_msgs in
#print axioms Frame.result_bounds
/-- info: 'Solidity.Yul.Compilation.Frame.local_bounds' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Frame.local_bounds
/-- info: 'Solidity.Yul.Compilation.Frame.arg_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Frame.arg_injective
/-- info: 'Solidity.Yul.Compilation.Frame.result_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Frame.result_injective
/-- info: 'Solidity.Yul.Compilation.Frame.local_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Frame.local_injective
/-- info: 'Solidity.Yul.Compilation.Frame.covers' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms Frame.covers
/-- info: 'Solidity.Yul.Compilation.frame_allocation_witness' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms frame_allocation_witness
end Solidity.Yul.Compilation
