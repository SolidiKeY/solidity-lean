import Solidity.Yul.WordSyntax
import Solidity.Yul.Checks.BlockTyping
import Solidity.Yul.Checks.ClosedRun
/-! Universal divergence of an ACTUAL source-derived recursive program.
This is not inferred from a finite timeout, and not a Source state/compiler
theorem. The emitted cache equality is kernel checked. -/
namespace Solidity.Yul.Checks.ExtractDivergence
open Solidity.Source (Syn)
open Solidity.Yul.Closed
open Solidity.Yul.Checks.BlockTyping
namespace Old
export Solidity.Yul.Checks.ClosedRun
  (divergeSig divergeBody divergeBodyD divergeEnv divergeEnvD divergeCall divergeCallD diverge_all)
end Old

def source : Syn (.list .yulStmt) := list [
  fn "spin" [] [] [.yulExprStmt (call "spin" [])],
  .yulExprStmt (call "spin" [])]
def prepared : Solidity.Yul.WordSyntax.Prepared [] source :=
  ((Solidity.Yul.WordSyntax.prepare [] source).toOption).get (by decide)

def cache : Stmt [] [] ClosedSyntax.rootControl 0 :=
  .functions [Old.divergeSig] (.cons Old.divergeBody .nil)
    (.discard (.call .here Fin.elim0))
def cacheD : WordStmtD cache :=
  .functions (.cons Old.divergeBodyD .nil) (.discard Old.divergeCallD)

theorem emitted_cache : prepared.program.code = cache := rfl

theorem run_eq_code {outside body} (p : Solidity.Yul.WordSyntax.Prepared outside body)
    (code : Stmt [] [] ClosedSyntax.rootControl 0) (profile : StmtWordP code)
    (same : p.program.code = code) (fuel : Nat) :
    p.run fuel = evalStmt fuel .nil True.intro code profile Fin.elim0 := by
  cases same
  rfl

theorem run_none (fuel : Nat) : prepared.run fuel = none := by
  rw [run_eq_code prepared cache cacheD.profile emitted_cache]
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases fuel with
      | zero => rfl
      | succ k =>
          change (evalExpr k Old.divergeEnv Old.divergeEnvD.profile
            Old.divergeCall Old.divergeCallD.profile Fin.elim0).bind _ = none
          rw [Old.diverge_all]
          rfl

example : (Logic.Fml.modal .box Solidity.Yul.WordSyntax.emptyModel prepared.program
    (fun _ => .atom fun _ => False)).holds Fin.elim0 := by
  intro fuel result ran
  change prepared.run fuel = some result at ran
  rw [run_none] at ran
  cases ran
example : ¬ (Logic.Fml.modal .diamond Solidity.Yul.WordSyntax.emptyModel prepared.program
    (fun _ => .atom fun _ => True)).holds Fin.elim0 := by
  rintro ⟨fuel,result,ran,_⟩
  change prepared.run fuel = some result at ran
  rw [run_none] at ran
  cases ran

theorem inhabited : Nonempty (Solidity.Yul.WordSyntax.Prepared [] source) := ⟨prepared⟩
end Solidity.Yul.Checks.ExtractDivergence
