import Solidity.Backend.StructuredFlow.CoreScopes

/-! Actual core branch followed by a typed continuation. No new syntax or
source evaluator; the fragment checker, representation and capacity stay exact. -/
namespace Solidity.Backend.StructuredFlow.CoreSequence
open Solidity.Evm
variable {C : Solidity.Contract} {Γ Γ₁ Γ₂ Γ₃ : Solidity.Ctx}

def emit (b : Nat) (condition : Solidity.Val C Γ .bool)
    (left : Solidity.Prog C Γ Γ₁) (right : Solidity.Prog C Γ Γ₂)
    (tail : Solidity.Prog C Γ Γ₃) : List Instr :=
  CoreScopes.branch b condition left right ++ compileProg b tail

theorem code (b : Nat) (condition : Solidity.Val C Γ .bool)
    (left : Solidity.Prog C Γ Γ₁) (right : Solidity.Prog C Γ Γ₂)
    (tail : Solidity.Prog C Γ Γ₃) :
    emit b condition left right tail = compileProg b (.cons (.ite condition left right) tail) := by
  rw [emit, CoreScopes.branch_code]
  rfl

/-- The suffix is checked at the branch's actual restricted/merged fragment. -/
theorem admitted {L b : Nat} {F Fbranch : Frag Γ} {Fout : Frag Γ₃}
    {caller : Solidity.State C Γ} {machine : Machine}
    (condition : Solidity.Val C Γ .bool) (left : Solidity.Prog C Γ Γ₁)
    (right : Solidity.Prog C Γ Γ₂) (tail : Solidity.Prog C Γ Γ₃)
    (entry : Sim C L b F caller machine)
    (branchCheck : inFrag F (.ite condition left right) = some Fbranch)
    (tailCheck : inFragP Fbranch tail = some Fout)
    (capacity : L + Prog.pushes (.cons (.ite condition left right) tail) ≤ Lmax) :
    StmtOut C (L + Prog.pushes (.cons (.ite condition left right) tail)) b Fout
      (Prog.shrinks (.cons (.ite condition left right) tail))
      (Prog.pays (.cons (.ite condition left right) tail))
      (Prog.asserts (.cons (.ite condition left right) tail))
      (Solidity.Prog.run caller (.cons (.ite condition left right) tail))
      (run (emit b condition left right tail) machine) machine := by
  rw [code]
  apply prog_sim _ entry _ capacity
  simp only [inFragP, branchCheck]
  exact tailCheck
end Solidity.Backend.StructuredFlow.CoreSequence
