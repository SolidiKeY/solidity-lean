import Solidity.Evm.MachineV2

/-! Guarded regression: RETURNDATACOPY memory writes must not change the
caller's storage, balances, return buffer, reply function or ghost call journal.
This general core frame law includes both bounds and memory-write faults.
A fault exposes no post-state; success can change only memory and stack.

This is copyStep after operands have been supplied. It supplies no operand
origin, reference gas/fork agreement, Source execution, approved native domain
or full H68/P10 certificate. -/
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
end Solidity.Evm
