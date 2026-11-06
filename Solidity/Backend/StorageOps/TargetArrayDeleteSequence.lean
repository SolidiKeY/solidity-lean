import Solidity.Backend.StorageOps.TargetArrayClear

/-! Two actual current-header loops, with captured second lvalue and existing
Machine/WordStore semantics. OLD-region premises derive the second header;
no intermediate preservation result is assumed. -/
namespace Solidity.Backend.StorageOps.TargetArrayDeleteSequence

def code (second : Evm.Slot) : List Evm.Instr :=
  TargetArrayClear.code ++ (.push (.slot second) :: TargetArrayClear.code)

def after (machine : Evm.Machine) (tail : List Evm.Word) (first second : Evm.Slot) : Evm.Machine :=
  TargetArrayClear.afterClear (TargetArrayClear.afterClear machine tail first) tail second

/-- Both loop limits are ACTUAL SLOADs, including when slots overlap. -/
theorem run_current (machine : Evm.Machine) (tail : List Evm.Word) (first second : Evm.Slot) :
    Evm.run (code second) {machine with stack := .slot first :: tail} =
      .ok (after machine tail first second) 0 := by
  unfold code
  rw [Evm.run_append_ok (TargetArrayClear.run_current machine tail first)]
  change Evm.run TargetArrayClear.code
    {TargetArrayClear.afterClear machine tail first with stack := .slot second :: tail} = _
  exact TargetArrayClear.run_current (TargetArrayClear.afterClear machine tail first) tail second

/-- Clearing a runtime prefix cannot change an already-zero observation. -/
theorem prefix_zero (store : Evm.WordStore) (slot observer : Evm.Slot) (count : Nat)
    (zero : store observer = 0) : TargetArrayClear.clearPrefix store slot count observer = 0 := by
  induction count with
  | zero => exact zero
  | succ count ih =>
    rw [TargetArrayClear.clearPrefix]
    by_cases same : observer = .data slot count
    · subst observer
      rw [Evm.WordStore.write_same]
      rfl
    · rw [Evm.WordStore.write_other _ _ same]
      exact ih

/-- Includes header/data overlap; this is a concrete zero-writing property. -/
theorem preserves_zero (machine : Evm.Machine) (tail : List Evm.Word) (slot observer : Evm.Slot)
    (zero : machine.store observer = 0) :
    (TargetArrayClear.afterClear machine tail slot).store observer = 0 := by
  unfold TargetArrayClear.afterClear
  by_cases same : observer = slot
  · subst observer
    rw [Evm.WordStore.write_same]
    rfl
  · rw [Evm.WordStore.write_other _ _ same]
    exact prefix_zero machine.store slot observer (machine.store slot) zero

/-- Both headers are zero even without assuming global slot disjointness. -/
theorem headers_zero (machine : Evm.Machine) (tail : List Evm.Word) (first second : Evm.Slot) :
    (after machine tail first second).store first = 0 ∧
    (after machine tail first second).store second = 0 := by
  exact ⟨preserves_zero _ tail second first (TargetArrayClear.after_header machine tail first),
    TargetArrayClear.after_header _ tail second⟩

/-- Selected first-array words after both ACTUAL loops. Second access bounds
are derived from OLD headers and region separation, not supplied as a postfact. -/
theorem first_data (machine : Evm.Machine) (tail : List Evm.Word) (first second : Evm.Slot) (j : Nat)
    (headerApart : second ≠ first)
    (headerDataApart : ∀ k, k < machine.store first → second ≠ .data first k)
    (observerHeaderApart : Evm.Slot.data first j ≠ second)
    (observerDataApart : ∀ k, k < machine.store second → Evm.Slot.data first j ≠ .data second k) :
    (after machine tail first second).store (.data first j) =
      if j < machine.store first then 0 else machine.store (.data first j) := by
  have captured := TargetArrayClear.after_outside machine tail first second headerApart headerDataApart
  unfold after
  rw [TargetArrayClear.after_outside _ tail second (.data first j) observerHeaderApart
    (by intro k inside; rw [captured] at inside; exact observerDataApart k inside)]
  exact TargetArrayClear.after_data machine tail first j

/-- OLD agreement/frame is needed only for an unvisited retained second word. -/
theorem second_data (machine : Evm.Machine) (tail : List Evm.Word) (first second : Evm.Slot) (j : Nat)
    (headerApart : second ≠ first)
    (headerDataApart : ∀ k, k < machine.store first → second ≠ .data first k)
    (unvisited : machine.store second ≤ j →
      Evm.Slot.data second j ≠ first ∧
      ∀ k, k < machine.store first → Evm.Slot.data second j ≠ .data first k) :
    (after machine tail first second).store (.data second j) =
      if j < machine.store second then 0 else machine.store (.data second j) := by
  have captured := TargetArrayClear.after_outside machine tail first second headerApart headerDataApart
  unfold after
  rw [TargetArrayClear.after_data,captured]
  by_cases live : j < machine.store second
  · simp only [if_pos live]
  · simp only [if_neg live]
    exact TargetArrayClear.after_outside machine tail first (.data second j)
      (unvisited (by omega)).1 (unvisited (by omega)).2

/-- Exact observer frame over BOTH OLD generated regions. -/
theorem outside (machine : Evm.Machine) (tail : List Evm.Word) (first second observer : Evm.Slot)
    (headerApart : second ≠ first)
    (headerDataApart : ∀ k, k < machine.store first → second ≠ .data first k)
    (firstHeaderApart : observer ≠ first)
    (firstDataApart : ∀ k, k < machine.store first → observer ≠ .data first k)
    (secondHeaderApart : observer ≠ second)
    (secondDataApart : ∀ k, k < machine.store second → observer ≠ .data second k) :
    (after machine tail first second).store observer = machine.store observer := by
  have captured := TargetArrayClear.after_outside machine tail first second headerApart headerDataApart
  unfold after
  rw [TargetArrayClear.after_outside _ tail second observer secondHeaderApart
    (by intro k inside; rw [captured] at inside; exact secondDataApart k inside)]
  exact TargetArrayClear.after_outside machine tail first observer firstHeaderApart firstDataApart

/-- Fresh indexed target reads after either deletion observe the CURRENT zero
header. Captured raw SLOAD locations are a different operation. -/
theorem fresh_read_reverts (machine : Evm.Machine) (tail : List Evm.Word)
    (first second : Evm.Slot) (j : Nat) (fits : j < Evm.W) :
    Evm.run TargetArrayRead.code
      {after machine tail first second with stack := .val ⟨j,fits⟩ :: .slot first :: tail} = .revert := by
  have zero : (after machine tail first second).store first = 0 := (headers_zero machine tail first second).1
  simpa only [zero,Nat.not_lt_zero,if_false] using
    TargetArrayRead.run_current (after machine tail first second) tail first j fits

/-- info: 'Solidity.Backend.StorageOps.TargetArrayDeleteSequence.run_current' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms run_current

/-- info: 'Solidity.Backend.StorageOps.TargetArrayDeleteSequence.prefix_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms prefix_zero

/-- info: 'Solidity.Backend.StorageOps.TargetArrayDeleteSequence.preserves_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms preserves_zero

/-- info: 'Solidity.Backend.StorageOps.TargetArrayDeleteSequence.headers_zero' depends on axioms: [propext] -/
#guard_msgs in #print axioms headers_zero

/-- info: 'Solidity.Backend.StorageOps.TargetArrayDeleteSequence.first_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms first_data

/-- info: 'Solidity.Backend.StorageOps.TargetArrayDeleteSequence.second_data' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms second_data

/-- info: 'Solidity.Backend.StorageOps.TargetArrayDeleteSequence.outside' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in #print axioms outside

/-- info: 'Solidity.Backend.StorageOps.TargetArrayDeleteSequence.fresh_read_reverts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in #print axioms fresh_read_reverts
end Solidity.Backend.StorageOps.TargetArrayDeleteSequence
