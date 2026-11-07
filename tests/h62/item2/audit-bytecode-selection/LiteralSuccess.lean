import Solidity.Backend.Selection.LiteralSelection

/-! Success/totality backfill for actual numeric literal selection and IR.
The machine preserves the whole caller frame. Scalar and IR execution here
are gasless; no external decoder, charged EVM, fork or full compiler claim.
-/
namespace Solidity.H62.BytecodeSelection
open Backend Backend.Selection

/-- An additive audit requirement, separate from the frozen partial interface. -/
def LiteralTotal (select : (i : Evm.Instr) → Option (InstructionCertificate i)) : Prop :=
  ∀ value : Fin Evm.W, ∃ c : InstructionCertificate (.push (.val value)),
    select (.push (.val value)) = some c

theorem selectLiteral_total : LiteralTotal selectLiteral := by
  intro value
  exact ⟨literalCertificate value, rfl⟩

/-- The same selected artifact executes and produces the exact supported result. -/
theorem selected_literal_success (value : Fin Evm.W) (input : Scalar.Stack) :
    ∃ c : InstructionCertificate (.push (.val value)),
      selectLiteral (.push (.val value)) = some c ∧
      Scalar.run c.code input = some (BitVec.ofNat 256 value.val :: input) := by
  refine ⟨literalCertificate value, rfl, ?_⟩
  change Scalar.run [Scalar.pushWord (BitVec.ofNat 256 value.val)] input = _
  simp only [Scalar.run, Scalar.step_pushWord, Option.bind_some]

/-- A reject-all selector fails the explicit supported-program requirement. -/
theorem reject_all_not_total : ¬ LiteralTotal (fun _ => none) := by
  intro total
  obtain ⟨c, bad⟩ := total ⟨0, Evm.W_pos⟩
  cases bad

/-- Every supported nonempty literal IR program succeeds, with exact result. -/
theorem literal_ir_success (value : Fin Evm.W) (m : Evm.Machine) :
    Evm.run [.push (.val value)] m =
      .ok { m with stack := .val value :: m.stack } 0 := rfl

/-- Observable revert is distinct from the required successful outcome. -/
theorem always_revert_fails_literal_success (value : Fin Evm.W) (m : Evm.Machine) :
    Evm.run [.revert] m ≠ .ok { m with stack := .val value :: m.stack } 0 := by
  intro bad
  cases bad

#print axioms selected_literal_success
#print axioms selectLiteral_total
#print axioms reject_all_not_total
#print axioms literal_ir_success
#print axioms always_revert_fails_literal_success
end Solidity.H62.BytecodeSelection
