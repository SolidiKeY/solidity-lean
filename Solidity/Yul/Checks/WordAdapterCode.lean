
import Solidity.Yul.Checks.WordAdapterFixtures
set_option Elab.async false
namespace Solidity.Yul.Checks.WordAdapter
open Solidity.Source (Syn)

def arg2 {F n} (a b : Expr F [] n 1) : Fin 2 → Expr F [] n 1 :=
  Fin.cases a (Fin.cases b Fin.elim0)
def bin {F n} (op : Pure 2) (a b : Expr F [] n 1) : Expr F [] n 1 :=
  .builtin (.pure op) (arg2 a b)
def set {F c n} (index : Fin n) (value : Expr F [] n 1) : Stmt F [] c n :=
  .assign (Fin.cases (.local index) Fin.elim0) value

/-- Intrinsic caches retain exact arities, scopes, controls and raw-cell locals.
Each is linked by RFL to the ACTUAL checked/adapted program below. -/
def mulDivCode : Stmt [] [] ClosedSyntax.rootControl 4 :=
  .functions [⟨3,1⟩]
    (.cons (.let_ 1 (bin .mul (.local 0) (.local 1))
      (set 4 (bin .div (.local 0) (.local 3)))) .nil)
    (set 0 (.call .here (Fin.cases (.local 0) (Fin.cases (.literal (word 7))
      (Fin.cases (.literal (word 3)) Fin.elim0)))))

def recursiveCode : Stmt [] [] ClosedSyntax.rootControl 4 :=
  .functions [⟨1,1⟩]
    (.cons (.seq
      (.if_ (.local 0) (.seq
        (set 1 (bin .add (.local 0) (.call .here
          (Fin.cases (bin .sub (.local 0) (.literal (word 1))) Fin.elim0)))) .leave))
      (set 1 (.literal (word 7)))) .nil)
    (set 0 (.call .here (Fin.cases (.literal (word 3)) Fin.elim0)))

def loopingCode : Stmt [] [] ClosedSyntax.rootControl 4 :=
  .let_ 1 (.literal (word 0))
    (.for_ .skip (bin .lt (.local 0) (.literal (word 4)))
      (.seq (set 0 (bin .add (.local 0) (.literal (word 1))))
        (set 4 (bin .add (.local 4) (.literal (word 1)))))
      (.seq (.if_ (bin .eq (.local 0) (.literal (word 1))) .continue_)
        (.seq (.if_ (bin .eq (.local 0) (.literal (word 3))) .break_)
          (set 1 (bin .add (.local 1) (.local 0))))))

def mulDivPrepared := (prepare mulDiv).toOption.get (by decide)
def recursivePrepared := (prepare recursive).toOption.get (by decide)
def loopingPrepared := (prepare looping).toOption.get (by decide)

theorem mulDiv_lowered : mulDivPrepared.rawProgram.code = mulDivCode := rfl
theorem recursive_lowered : recursivePrepared.rawProgram.code = recursiveCode := rfl
theorem looping_lowered : loopingPrepared.rawProgram.code = loopingCode := rfl

def recode (original : Logic.Program [] ClosedSyntax.rootControl 4)
    (code : Stmt [] [] ClosedSyntax.rootControl 4) (same : original.code = code) :
    Logic.Program [] ClosedSyntax.rootControl 4 := ⟨code,same ▸ original.words⟩

theorem recode_eq (original : Logic.Program [] ClosedSyntax.rootControl 4)
    (code : Stmt [] [] ClosedSyntax.rootControl 4) (same : original.code = code) :
    recode original code same = original := by
  cases original with
  | mk actual words => cases same; rfl

def execute (program : Logic.Program [] ClosedSyntax.rootControl 4) (fuel : Nat) :
    Option (List Nat) :=
  ((Closed.evalStmt fuel Solidity.Yul.WordAdapter.model.environment
    Solidity.Yul.WordAdapter.model.words program.code program.words
    (WordState.pack (X := types) (n := 0) ⟨Fin.elim0,initial⟩)).map
      (Solidity.Yul.WordAdapter.Outcome.decode (X := types) (n := 0))).map
        (fun result => snapshot result.state.cells)

theorem observe_program (body : List (Syn .yulStmt))
    (p : Solidity.Yul.ScopedSyntax.Prepared scope .A outside localNames
      (Solidity.Yul.Checks.BlockTyping.list body)) (fuel : Nat) :
    observe body fuel = execute p.rawProgram fuel := by
  unfold observe prepare
  rw [p.complete]
  rfl

theorem observe_cache (body : List (Syn .yulStmt))
    (p : Solidity.Yul.ScopedSyntax.Prepared scope .A outside localNames
      (Solidity.Yul.Checks.BlockTyping.list body)) (fuel : Nat)
    (code : Stmt [] [] ClosedSyntax.rootControl 4) (same : p.rawProgram.code = code) :
    observe body fuel = execute (recode p.rawProgram code same) fuel := by
  rw [recode_eq,observe_program body p]

end Solidity.Yul.Checks.WordAdapter
