import Solidity.Source.Types

/-! Isolated source-input feasibility backfill. V07 interface imports still
have independent failing dependencies. These closed proofs are not interface
witness coverage, compiler success, or a gas/fork claim. -/
namespace Solidity.H62.AuditV07

theorem unsigned_implicit_input_fixture :
    ∃ (a b : Source.IntTy) (x : Int),
      a.implicit b = true ∧ a.lo ≤ x ∧ x ≤ a.hi := by
  refine ⟨.u8,.u8,0,rfl,?_,?_⟩
  · decide
  · decide

theorem unsigned_narrowing_guard_negative :
    Source.IntTy.u256.implicit Source.IntTy.u8 = false := by
  rfl

theorem unsigned_u8_boundary_negative :
    ¬ (Source.IntTy.u8.lo ≤ (256 : Int) ∧ (256 : Int) ≤ Source.IntTy.u8.hi) := by
  decide

/-- info: 'Solidity.H62.AuditV07.unsigned_implicit_input_fixture' does not depend on any axioms -/
#guard_msgs in #print axioms unsigned_implicit_input_fixture
/-- info: 'Solidity.H62.AuditV07.unsigned_narrowing_guard_negative' does not depend on any axioms -/
#guard_msgs in #print axioms unsigned_narrowing_guard_negative
/-- info: 'Solidity.H62.AuditV07.unsigned_u8_boundary_negative' does not depend on any axioms -/
#guard_msgs in #print axioms unsigned_u8_boundary_negative
end Solidity.H62.AuditV07
