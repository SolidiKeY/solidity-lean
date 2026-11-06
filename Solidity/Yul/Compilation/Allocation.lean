import Init

/-! Independent VY3 allocation arithmetic. Slots are newest-first positions,
not byte-memory addresses or a replacement for G24's representation relation.
No Yul syntax, runtime state or prerequisite-owner machinery is defined here. -/
namespace Solidity.Yul.Compilation

/-- A scope with exactly `n` live word locals, placed above the caller. -/
structure Slots (n : Nat) where
  base : Nat

def Slots.at {n : Nat} (s : Slots n) (i : Fin n) : Nat :=
  s.base + (n - 1 - i.val)

theorem Slots.bounds {n : Nat} (s : Slots n) (i : Fin n) :
    s.base ≤ s.at i ∧ s.at i < s.base + n := by
  have hi : i.val < n := i.isLt
  simp only [Slots.at]
  omega

theorem Slots.injective {n : Nat} (s : Slots n) (i j : Fin n)
    (h : s.at i = s.at j) : i = j := by
  have hi : i.val < n := i.isLt
  have hj : j.val < n := j.isLt
  apply Fin.ext
  simp only [Slots.at] at h
  omega

/-- Add `k` newer binders. Old locals retain their allocated slots. -/
def extend {n : Nat} (k : Nat) (i : Fin n) : Fin (n + k) :=
  ⟨k + i.val, by have hi := i.isLt; omega⟩

theorem Slots.extend_at {n : Nat} (s : Slots n) (k : Nat) (i : Fin n) :
    (Slots.at (n := n + k) ⟨s.base⟩ (extend k i)) = s.at i := by
  have hi : i.val < n := i.isLt
  simp only [Slots.at, extend]
  omega

theorem Slots.relocate {n : Nat} (s : Slots n) (delta : Nat) (i : Fin n) :
    (Slots.at (n := n) ⟨delta + s.base⟩ i) = delta + s.at i := by
  simp only [Slots.at]
  omega

/-- Allocation footprint only. Arguments/results are indexed by arity;
this does not prescribe V12's runtime calling convention. -/
structure Frame (args results locals : Nat) where
  base : Nat

def Frame.arg {a r l : Nat} (f : Frame a r l) (i : Fin a) : Nat := f.base + i.val
def Frame.result {a r l : Nat} (f : Frame a r l) (i : Fin r) : Nat :=
  f.base + a + i.val
def Frame.local {a r l : Nat} (f : Frame a r l) (i : Fin l) : Nat :=
  f.base + a + r + i.val
def Frame.limit {a r l : Nat} (f : Frame a r l) : Nat := f.base + a + r + l

theorem Frame.arg_result_disjoint {a r l : Nat} (f : Frame a r l)
    (i : Fin a) (j : Fin r) : f.arg i ≠ f.result j := by
  have hi := i.isLt
  simp only [Frame.arg, Frame.result]
  omega

theorem Frame.result_local_disjoint {a r l : Nat} (f : Frame a r l)
    (i : Fin r) (j : Fin l) : f.result i ≠ f.local j := by
  have hi := i.isLt
  simp only [Frame.result, Frame.local]
  omega

theorem Frame.arg_local_disjoint {a r l : Nat} (f : Frame a r l)
    (i : Fin a) (j : Fin l) : f.arg i ≠ f.local j := by
  have hi := i.isLt
  simp only [Frame.arg, Frame.local]
  omega

theorem Frame.local_bound {a r l : Nat} (f : Frame a r l) (i : Fin l) :
    f.local i < f.limit := by
  have hi := i.isLt
  simp only [Frame.local, Frame.limit]
  omega

/-- Caller slot positions lie below callee local positions. This is allocation
ordering only, not preservation of runtime contents. -/
theorem Frame.caller_below_locals {a r l n : Nat} (s : Slots n) (i : Fin n)
    (f : Frame a r l) (h : s.base + n ≤ f.base) (j : Fin l) :
    s.at i < f.local j := by
  have hb := s.bounds i
  simp only [Frame.local]
  omega

/-- Arithmetic result-height accounting only. Argument consumption and execution
are separate obligations, expressed for numeric slices in `Slices.lean`. -/
def returnHeight (tail results : Nat) : Nat := tail + results

theorem returnHeight_compose (tail a b : Nat) :
    returnHeight (returnHeight tail a - a) b = tail + b := by
  simp only [returnHeight]
  omega

/-- Distinct allocated label identities remain distinct under placement. -/
def label {n : Nat} (base : Nat) (i : Fin n) : Nat := base + i.val

theorem label_injective {n : Nat} (base : Nat) (i j : Fin n)
    (h : label base i = label base j) : i = j := by
  apply Fin.ext
  simp only [label] at h
  omega

theorem label_relocate {n : Nat} (base delta : Nat) (i : Fin n) :
    label (delta + base) i = delta + label base i := by
  simp only [label]
  omega

#print axioms Slots.injective
#print axioms Slots.extend_at
#print axioms Frame.caller_below_locals
#print axioms label_relocate
end Solidity.Yul.Compilation
