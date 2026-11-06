import Solidity.Yul.Checks.WordAdapterCode
import Solidity.Yul.Checks.ClosedRun
import Solidity.Yul.WordAdapterLogic
/-! An actual scoped raw-cell source program diverges at EVERY fuel. The proof
uses its RFL-linked code and the existing no-argument recursive call theorem,
not a finite timeout or a Source/compiler/prefix assumption. -/
namespace Solidity.Yul.Checks.RawDivergence
open Solidity.Source (Syn)
open Solidity.Yul.Closed
open Solidity.Yul.Checks.BlockTyping
namespace Old
export Solidity.Yul.Checks.ClosedRun
  (divergeSig divergeBody divergeBodyD divergeEnv divergeEnvD divergeCall divergeCallD diverge_all)
end Old
namespace Fixture
export Solidity.Yul.Checks.WordAdapter (types scope outside localNames prepare)
end Fixture

def source : List (Syn .yulStmt) := [
  fn "spin" [] [] [.yulExprStmt (call "spin" [])],.yulExprStmt (call "spin" [])]
def prepared := (Fixture.prepare source).toOption.get (by decide)
def call4 : Expr [Old.divergeSig] [] 4 0 := .call .here Fin.elim0
def call4D : WordExprD call4 := .call .here (fun i => Fin.elim0 i)
def code : Stmt [] [] ClosedSyntax.rootControl 4 :=
  .functions [Old.divergeSig] (.cons Old.divergeBody .nil) (.discard call4)
def codeD : WordStmtD code := .functions (.cons Old.divergeBodyD .nil) (.discard call4D)
theorem lowered : prepared.rawProgram.code = code := rfl

theorem call_frame (fuel : Nat) (vars : Values 4) :
    evalExpr fuel Old.divergeEnv Old.divergeEnvD.profile call4 call4D.profile vars =
      evalExpr fuel Old.divergeEnv Old.divergeEnvD.profile Old.divergeCall
        Old.divergeCallD.profile Fin.elim0 := by
  cases fuel <;> rfl

theorem code_none (fuel : Nat) (vars : Values 4) :
    evalStmt fuel .nil True.intro code codeD.profile vars = none := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases fuel with
    | zero => rfl
    | succ k =>
      change (evalExpr k Old.divergeEnv Old.divergeEnvD.profile call4 call4D.profile vars).bind _ = none
      rw [call_frame,Old.diverge_all]
      rfl

theorem raw_cache (body : List (Syn .yulStmt))
    (p : ScopedSyntax.Prepared Fixture.scope .A Fixture.outside Fixture.localNames (list body))
    (cached : Stmt [] [] ClosedSyntax.rootControl 4) (profile : StmtWordP cached)
    (same : p.rawProgram.code = cached) (fuel : Nat) (cells : WordCells Fixture.types) :
    p.rawRun fuel cells =
      (evalStmt fuel .nil True.intro cached profile
        (WordState.pack (X := Fixture.types) (n := 0) ⟨Fin.elim0,cells⟩)).map
          (Solidity.Yul.WordAdapter.Outcome.decode (X := Fixture.types) (n := 0)) := by
  cases same
  rfl

theorem run_none (fuel : Nat) (cells : WordCells Fixture.types) :
    prepared.rawRun fuel cells = none := by
  rw [raw_cache source prepared code codeD.profile lowered,code_none]
  rfl

example (cells : WordCells Fixture.types) :
    Solidity.Yul.WordAdapter.rawHolds .box prepared.typing.code prepared.policy
      (fun _ => False) ⟨Fin.elim0,cells⟩ := by
  intro fuel result done
  change prepared.rawRun fuel cells = some result at done
  rw [run_none] at done
  cases done

example (cells : WordCells Fixture.types) :
    ¬ Solidity.Yul.WordAdapter.rawHolds .diamond prepared.typing.code prepared.policy
      (fun _ => True) ⟨Fin.elim0,cells⟩ := by
  rintro ⟨fuel,result,done,_⟩
  change prepared.rawRun fuel cells = some result at done
  rw [run_none] at done
  cases done

theorem inhabited : Nonempty (ScopedSyntax.Prepared Fixture.scope .A Fixture.outside
    Fixture.localNames (list source)) := ⟨prepared⟩
end Solidity.Yul.Checks.RawDivergence
