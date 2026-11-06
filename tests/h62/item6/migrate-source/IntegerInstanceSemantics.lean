import Solidity.Source.Const

/-! A semantic bridge for the changed synthesized Int BEq expression in Q.isInt.
This does not certify unrelated functions, compiler-generated API types, or the
complete migration. The positive control makes the contract nonvacuous. -/
namespace H62Migration

theorem isInt_spec (a : Solidity.Source.Q) :
    a.isInt = true ↔ a.num % (a.den : Int) = 0 := by
  simp only [Solidity.Source.Q.isInt, beq_iff_eq]

theorem isInt_zero :
    (⟨0, 1, by decide⟩ : Solidity.Source.Q).isInt = true := by
  decide

end H62Migration
#print axioms H62Migration.isInt_spec
#print axioms H62Migration.isInt_zero
