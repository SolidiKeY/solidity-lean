import Solidity.Evm.Correct
import Solidity.Backend.StructuredFlow.BranchSelector

/-! Actual core-compiler scope adapter. These are intrinsic Prog/Stmt inputs,
not Solidity Source lowering. The existing fragment, Sim and capacity premises
remain exact; mixed memory/backend composition is a separate obligation. -/
namespace Solidity.Backend.StructuredFlow.CoreScopes
open Solidity.Evm
variable {C : Solidity.Contract} {Γ Γ₁ Γ₂ : Solidity.Ctx}

def branch (b : Nat) (condition : Solidity.Val C Γ .bool)
    (left : Solidity.Prog C Γ Γ₁) (right : Solidity.Prog C Γ Γ₂) : List Instr :=
  Branch.emit (compileVal b condition) (compileProg b left) (compileProg b right)

theorem branch_code (b : Nat) (condition : Solidity.Val C Γ .bool)
    (left : Solidity.Prog C Γ Γ₁) (right : Solidity.Prog C Γ Γ₂) :
    branch b condition left right = compileStmt b (.ite condition left right) := by
  simp only [branch, Branch.emit, compileStmt, List.append_assoc]

/-- Scoped locals are dropped by the actual typed run and fragment restriction. -/
theorem branch_correct {L L' b : Nat} {F : Frag Γ} {F₁ : Frag Γ₁} {F₂ : Frag Γ₂}
    {caller : Solidity.State C Γ} {machine : Machine}
    (condition : Solidity.Val C Γ .bool) (left : Solidity.Prog C Γ Γ₁)
    (right : Solidity.Prog C Γ Γ₂) (entry : Sim C L b F caller machine)
    (conditionIn : valIn F condition = true)
    (leftRun : StmtOut C L' b F₁ (Prog.shrinks left) (Prog.pays left) (Prog.asserts left)
      (Solidity.Prog.run caller left) (run (compileProg b left) machine) machine)
    (rightRun : StmtOut C L' b F₂ (Prog.shrinks right) (Prog.pays right) (Prog.asserts right)
      (Solidity.Prog.run caller right) (run (compileProg b right) machine) machine) :
    StmtOut C L' b ((F₁.restrict Γ).meet (F₂.restrict Γ))
      (Prog.shrinks left || Prog.shrinks right) (Prog.pays left || Prog.pays right)
      (Prog.asserts left || Prog.asserts right)
      (Solidity.Stmt.run caller (.ite condition left right))
      (run (branch b condition left right) machine) machine := by
  rw [branch_code]
  exact ite_sim condition left right entry conditionIn leftRun rightRun

/-- Discharge body correspondence from the actual published fragment checker. -/
theorem branch_admitted {L b : Nat} {F F' : Frag Γ} {caller : Solidity.State C Γ}
    {machine : Machine} (condition : Solidity.Val C Γ .bool)
    (left : Solidity.Prog C Γ Γ₁) (right : Solidity.Prog C Γ Γ₂)
    (entry : Sim C L b F caller machine)
    (checked : inFrag F (.ite condition left right) = some F')
    (capacity : L + Stmt.pushes (.ite condition left right) ≤ Lmax) :
    StmtOut C (L + Stmt.pushes (.ite condition left right)) b F'
      (Stmt.shrinks (.ite condition left right)) (Stmt.pays (.ite condition left right))
      (Stmt.asserts (.ite condition left right)) (Solidity.Stmt.run caller (.ite condition left right))
      (run (branch b condition left right) machine) machine := by
  rw [branch_code]
  exact stmt_sim _ entry checked capacity

def block (b : Nat) (body : Solidity.Prog C Γ Γ₁) : List Instr := compileProg b body

theorem block_code (b : Nat) (body : Solidity.Prog C Γ Γ₁) :
    block b body = compileStmt b (.block body) := rfl

theorem block_correct {L b : Nat} {F : Frag Γ₁} {caller : Solidity.State C Γ}
    {machine : Machine} {sh pays asserts : Bool} (body : Solidity.Prog C Γ Γ₁)
    (bodyRun : StmtOut C L b F sh pays asserts (Solidity.Prog.run caller body)
      (run (compileProg b body) machine) machine) :
    StmtOut C L b (F.restrict Γ) sh pays asserts (Solidity.Stmt.run caller (.block body))
      (run (block b body) machine) machine := by
  rw [block_code]
  exact block_sim body bodyRun

theorem block_admitted {L b : Nat} {F F' : Frag Γ} {caller : Solidity.State C Γ}
    {machine : Machine} (body : Solidity.Prog C Γ Γ₁)
    (entry : Sim C L b F caller machine)
    (checked : inFrag F (.block body) = some F')
    (capacity : L + Stmt.pushes (.block body) ≤ Lmax) :
    StmtOut C (L + Stmt.pushes (.block body)) b F'
      (Stmt.shrinks (.block body)) (Stmt.pays (.block body)) (Stmt.asserts (.block body))
      (Solidity.Stmt.run caller (.block body)) (run (block b body) machine) machine := by
  rw [block_code]
  exact stmt_sim _ entry checked capacity
end Solidity.Backend.StructuredFlow.CoreScopes
