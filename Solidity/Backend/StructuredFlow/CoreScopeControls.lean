import Solidity.Backend.StructuredFlow.CoreScopes

/-! Inhabited actual fragment/representation and scoped-local controls. -/
namespace Solidity.Backend.StructuredFlow.CoreScopeControls
open Solidity.Evm
private def C : Solidity.Contract := default
private def caller := freshT C 0 W_pos ⟨0,W_pos⟩
private def machine := Machine.init (fun _ => 0) ⟨0,W_pos⟩
private def left : Solidity.Prog C [] [.val .uint] :=
  .cons (.declLocal .uint (.fresh "scoped-local" 0) (some (.simple (.lit 7 rfl)))) .nil
private def right : Solidity.Prog C [] [] := .cons .revert .nil
private def statement (flag : Bool) : Solidity.Stmt C [] [] := .ite (.simple (.bool flag)) left right
private def emitted (flag : Bool) := CoreScopes.branch 0 (.simple (.bool flag)) left right

theorem represented : Sim C 1 0 (Frag.init []) caller machine :=
  Sim.init C 0 W_pos (fun _ => 0) ⟨0,W_pos⟩ rfl

theorem admitted (flag : Bool) : inFrag (Frag.init []) (statement flag) = some (Frag.init []) := rfl

theorem source_true : Solidity.Stmt.run caller (statement true) =
    .ok ⟨caller,List.prefix_refl _⟩ :=
  congrFun (Solidity.Stmt.runR_eq (statement true)) caller

theorem source_false : Solidity.Stmt.run caller (statement false) = .error .revert :=
  congrFun (Solidity.Stmt.runR_eq (statement false)) caller

theorem target_true : run (emitted true) machine =
    .ok {machine with mem := upd machine.mem 0 w[7]} 0 := by rfl

theorem target_false : run (emitted false) machine = .revert := by rfl

theorem checked_agreement (flag : Bool) :
    StmtOut C (1 + Stmt.pushes (statement flag)) 0 (Frag.init [])
      (Stmt.shrinks (statement flag)) (Stmt.pays (statement flag)) (Stmt.asserts (statement flag))
      (Solidity.Stmt.run caller (statement flag)) (run (emitted flag) machine) machine :=
  CoreScopes.branch_admitted _ left right represented (admitted flag) represented.bound

private def machineTail : Machine := {machine with stack := [w[77]]}

theorem represented_tail : Sim C 1 0 (Frag.init []) caller machineTail :=
  represented.stack [w[77]]

theorem target_tail : run (emitted true) machineTail =
    .ok {machineTail with mem := upd machineTail.mem 0 w[7]} 0 := by rfl

theorem checked_tail (flag : Bool) :
    StmtOut C (1 + Stmt.pushes (statement flag)) 0 (Frag.init [])
      (Stmt.shrinks (statement flag)) (Stmt.pays (statement flag)) (Stmt.asserts (statement flag))
      (Solidity.Stmt.run caller (statement flag)) (run (emitted flag) machineTail) machineTail :=
  CoreScopes.branch_admitted _ left right represented_tail (admitted flag) represented_tail.bound

theorem unsupported_refused :
    inFrag (Frag.init [])
      (.ite (.simple (.bool true)) (.cons .assumeFalse .nil) (.nil : Solidity.Prog C [] [])) = none := rfl

theorem block_source : Solidity.Stmt.run caller (.block left) =
    .ok ⟨caller,List.prefix_refl _⟩ :=
  congrFun (Solidity.Stmt.runR_eq (.block left)) caller

theorem block_target : run (CoreScopes.block 0 left) machine =
    .ok {machine with mem := upd machine.mem 0 w[7]} 0 := by rfl
end Solidity.Backend.StructuredFlow.CoreScopeControls
