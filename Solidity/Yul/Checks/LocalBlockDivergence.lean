import Solidity.Yul.LocalBlockLogic
import Solidity.Yul.Checks.LocalBlock
import Solidity.Yul.Checks.ClosedRun
namespace Solidity.Yul.Checks.LocalBlockDivergence
open Solidity.Yul.Closed
namespace Old
export Solidity.Yul.Checks.ClosedRun
  (divergeSig divergeBody divergeBodyD divergeEnv divergeEnvD divergeCall divergeCallD diverge_all)
end Old
export Solidity.Yul.Checks.LocalBlock (ctx initial)

def code : Stmt [] (localExternalTypes ctx) ⟨false,false⟩ 0 :=
  .functions [Old.divergeSig]
    (.cons (.discard (.call .here Fin.elim0)) .nil)
    (.discard (.call .here Fin.elim0))
def policy : Policy.StmtP .A code := (Policy.stmt_iff .A code).mp rfl
def call : Expr [Old.divergeSig] [] 7 0 := .call .here Fin.elim0
def callD : WordExprD call := .call .here (fun i => Fin.elim0 i)
def cache : Stmt [] [] ⟨false,false⟩ 7 :=
  .functions [Old.divergeSig] (.cons Old.divergeBody .nil) (.discard call)
def cacheD : WordStmtD cache := .functions (.cons Old.divergeBodyD .nil) (.discard callD)
theorem lowered : (WordAdapter.program code policy).code = cache := rfl

theorem call_frame (fuel : Nat) (vars : Values 7) :
    evalExpr fuel Old.divergeEnv Old.divergeEnvD.profile call callD.profile vars =
      evalExpr fuel Old.divergeEnv Old.divergeEnvD.profile Old.divergeCall
        Old.divergeCallD.profile Fin.elim0 := by cases fuel <;> rfl

theorem cache_none (fuel : Nat) (vars : Values 7) :
    evalStmt fuel .nil True.intro cache cacheD.profile vars = none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases fuel with
      | zero => rfl
      | succ k =>
          change (evalExpr k Old.divergeEnv Old.divergeEnvD.profile call callD.profile vars).bind _ = none
          rw [call_frame,Old.diverge_all]
          rfl

theorem raw_none (fuel : Nat) (state : WordState (localExternalTypes ctx) 0) :
    WordAdapter.run code policy fuel state = none := by
  change (evalStmt fuel .nil True.intro cache cacheD.profile state.pack).map _ = none
  rw [cache_none]
  rfl

theorem run_none (fuel : Nat) (state : LocalState ctx.env ctx.tys) :
    runLocalBlock ctx code policy fuel state = none := by
  unfold runLocalBlock
  rw [raw_none]
  rfl

theorem box_false (state : LocalState ctx.env ctx.tys) :
    LocalBlockLogic.holds .box code policy (fun _ => False) state := by
  intro fuel result finished
  rw [run_none] at finished
  cases finished

theorem not_diamond_true (state : LocalState ctx.env ctx.tys) :
    ¬ LocalBlockLogic.holds .diamond code policy (fun _ => True) state := by
  rintro ⟨fuel,result,finished,_⟩
  rw [run_none] at finished
  cases finished

def ruleWitness : ∃ premise, Nonempty (Logic.Rule
    (LocalBlockLogic.formula .box code policy (fun _ => False) initial) premise) :=
  LocalBlockLogic.rule_exists .box code policy (fun _ => False) initial
#print axioms run_none
#print axioms box_false
end Solidity.Yul.Checks.LocalBlockDivergence
