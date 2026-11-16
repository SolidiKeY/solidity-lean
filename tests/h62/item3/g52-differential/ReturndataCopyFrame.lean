import Solidity.Evm.MachineV2

/-! Guarded regression: RETURNDATACOPY memory writes must not change the
caller's storage, balances, return buffer, reply function or ghost call journal.
This general core frame law includes both bounds and memory-write faults.
A fault exposes no post-state; success can change only memory and stack.

copyStep_frame handles supplied operands; returndatacopy_frame also covers
actual core stack dispatch. Neither supplies compiled operand origin, reference
gas/fork agreement, Source execution, an approved domain or full H68 certificate. -/
namespace Solidity.Evm

/-- Every copy either faults or preserves the entire core machine after its
two mutable base fields are restored. No bounds or successful-write premise
excludes either fault branch. -/
theorem copyStep_frame (m : MachineV2) (d o len : Nat) (st : List Word) :
    copyStep m d o len st = .fault ∨
      ∃ next, copyStep m d o len st = .ok next 0 ∧
        {next with base := {next.base with
          stack := m.base.stack, mem := m.base.mem}} = m := by
  by_cases bounds : m.returndata.length < o + len
  · simp only [copyStep, if_pos bounds]
    exact Or.inl (by trivial)
  · simp only [copyStep, if_neg bounds]
    cases written : writeBytes m.base.mem d ((m.returndata.drop o).take len) with
    | none => exact Or.inl (by trivial)
    | some memory => exact Or.inr ⟨_, rfl, rfl⟩

#print axioms copyStep_frame

/-- The actual instruction preserves the same complete frame, including
underflow and slot-valued operand faults. No stack-shape premise removes them. -/
theorem returndatacopy_frame (m : MachineV2) :
    InstrV2.step .returndatacopy m = .fault ∨
      ∃ next, InstrV2.step .returndatacopy m = .ok next 0 ∧
        {next with base := {next.base with
          stack := m.base.stack, mem := m.base.mem}} = m := by
  match stack : m.base.stack with
  | .val d :: .val o :: .val len :: st =>
      simpa only [InstrV2.step, stack] using copyStep_frame m d.val o.val len.val st
  | [] | [_] | [_, _] | .slot _ :: _ | .val _ :: .slot _ :: _
      | .val _ :: .val _ :: .slot _ :: _ =>
      exact Or.inl (by simp only [InstrV2.step, stack])

#print axioms returndatacopy_frame
end Solidity.Evm
