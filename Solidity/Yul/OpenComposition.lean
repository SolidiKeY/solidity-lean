import Solidity.Yul.OpenExpressionAgreement
import Solidity.Yul.OpenStatementAgreement
import Solidity.Yul.OpenCasesAgreement
import Solidity.Yul.OpenLoopAgreement

/-! Concrete mutual fuel induction constructs every expression/statement/case/
loop field. No Agreement assumption remains in the public composition laws.
This is full tier-A intrinsic AST correspondence, not Source/compiler adequacy. -/
namespace Solidity.Yul.OpenRun
open Closed
open OpenFunctions (PureEnvironment)

theorem agreement (fuel : Nat) : Agreement fuel := by
  induction fuel with
  | zero =>
    constructor <;> intros <;> rfl
  | succ fuel previous =>
    exact ⟨expression_step fuel previous,statement_step fuel previous,
      cases_step fuel previous,loop_step fuel previous⟩

theorem expression_agrees (fuel : Nat) {F X n m r} (coordinates : Coordinates X n m)
    (environment : PureEnvironment F) (code : Expr F X n r)
    (policy : Policy.ExprP .A code) (state : WordState X n) :
    OpenRun.expression fuel environment code policy state =
      Closed.evalExpr fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
        (WordAdapter.expression code policy coordinates.locals coordinates.cells).code
        (WordAdapter.expression code policy coordinates.locals coordinates.cells).words (coordinates.pack state) :=
  (agreement fuel).expression coordinates environment code policy state

theorem statement_agrees (fuel : Nat) {F X c n m} (coordinates : Coordinates X n m)
    (environment : PureEnvironment F) (code : Stmt F X c n)
    (policy : Policy.StmtP .A code) (state : WordState X n) :
    (OpenRun.statement fuel environment code policy state).map (Coordinates.encodeOutcome coordinates) =
      Closed.evalStmt fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
        (WordAdapter.statement code policy coordinates.locals coordinates.cells).code
        (WordAdapter.statement code policy coordinates.locals coordinates.cells).words (coordinates.pack state) :=
  (agreement fuel).statement coordinates environment code policy state

theorem cases_agrees (fuel : Nat) {F X c n m} (coordinates : Coordinates X n m)
    (environment : PureEnvironment F) (code : Cases F X c n)
    (policy : Policy.CasesP .A code) (selector : Word) (state : WordState X n) :
    (OpenRun.casesRun fuel environment code policy selector state).map
        (Option.map (Coordinates.encodeOutcome coordinates)) =
      Closed.evalCases fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
        (WordAdapter.cases code policy coordinates.locals coordinates.cells).code
        (WordAdapter.cases code policy coordinates.locals coordinates.cells).words selector (coordinates.pack state) :=
  (agreement fuel).casesRun coordinates environment code policy selector state

/-- Every actual intrinsic root statement, with the real tier-A policy only.
No Basic/Supported/residual family or callee/body simulation premise remains. -/
theorem run_agrees (fuel : Nat) {X c n} (code : Stmt [] X c n)
    (policy : Policy.StmtP .A code) (state : WordState X n) :
    OpenRun.statement fuel .nil code policy state = WordAdapter.run code policy fuel state := by
  have packed := statement_agrees fuel (Coordinates.canonical X n) .nil code policy state
  have encoding : Coordinates.encodeOutcome (Coordinates.canonical X n) (c := c) =
      WordAdapter.Outcome.encode := by
    funext result
    exact Coordinates.canonical_encode result
  rw [encoding,Coordinates.canonical_pack] at packed
  apply (Option.map_inj_right (f := WordAdapter.Outcome.encode (X := X) (c := c) (n := n))
    (fun one two same => by
      have decoded := congrArg (WordAdapter.Outcome.decode (X := X) (c := c) (n := n)) same
      simpa only [WordAdapter.Outcome.decode_encode] using decoded)).mp
  exact packed.trans (WordAdapter.run_encode code policy fuel state).symm

theorem stable {lo hi : Nat} (bound : lo ≤ hi) {X c n} (code : Stmt [] X c n)
    (policy : Policy.StmtP .A code) (state : WordState X n)
    {result : WordAdapter.Outcome X c n}
    (done : OpenRun.statement lo .nil code policy state = some result) :
    OpenRun.statement hi .nil code policy state = some result := by
  rw [run_agrees] at done ⊢
  exact WordAdapter.run_stable code policy state bound done

theorem completed_unique {lo hi : Nat} {X c n} (code : Stmt [] X c n)
    (policy : Policy.StmtP .A code) (state : WordState X n)
    {first second : WordAdapter.Outcome X c n}
    (one : OpenRun.statement lo .nil code policy state = some first)
    (two : OpenRun.statement hi .nil code policy state = some second) : first = second := by
  rw [run_agrees] at one two
  exact WordAdapter.run_completed_unique code policy state one two

end Solidity.Yul.OpenRun
