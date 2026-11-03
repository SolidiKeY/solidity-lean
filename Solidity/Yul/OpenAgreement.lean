import Solidity.Yul.OpenRun

/-! Exact mutual fuel-induction obligations for the actual direct interpreter.
These are named proof fields, not axioms or an assumed final correspondence.
Concrete step/final composition modules construct every field. -/
namespace Solidity.Yul.OpenRun
open Closed
open OpenFunctions (PureEnvironment)

structure Agreement (fuel : Nat) : Prop where
  expression : ∀ {F X n m r} (coordinates : Coordinates X n m) (environment : PureEnvironment F)
    (code : Expr F X n r) (policy : Policy.ExprP .A code) (state : WordState X n),
    OpenRun.expression fuel environment code policy state =
      Closed.evalExpr fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
        (WordAdapter.expression code policy coordinates.locals coordinates.cells).code
        (WordAdapter.expression code policy coordinates.locals coordinates.cells).words (coordinates.pack state)
  statement : ∀ {F X c n m} (coordinates : Coordinates X n m) (environment : PureEnvironment F)
    (code : Stmt F X c n) (policy : Policy.StmtP .A code) (state : WordState X n),
    (OpenRun.statement fuel environment code policy state).map (Coordinates.encodeOutcome coordinates) =
      Closed.evalStmt fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
        (WordAdapter.statement code policy coordinates.locals coordinates.cells).code
        (WordAdapter.statement code policy coordinates.locals coordinates.cells).words (coordinates.pack state)
  casesRun : ∀ {F X c n m} (coordinates : Coordinates X n m) (environment : PureEnvironment F)
    (code : Cases F X c n) (policy : Policy.CasesP .A code) (selector : Word) (state : WordState X n),
    (OpenRun.casesRun fuel environment code policy selector state).map
        (Option.map (Coordinates.encodeOutcome coordinates)) =
      Closed.evalCases fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
        (WordAdapter.cases code policy coordinates.locals coordinates.cells).code
        (WordAdapter.cases code policy coordinates.locals coordinates.cells).words selector (coordinates.pack state)
  loop : ∀ {F X c n m} (coordinates : Coordinates X n m) (environment : PureEnvironment F)
    (condition : Expr F X n 1) (hc : Policy.ExprP .A condition)
    (post : Stmt F X ⟨c.function,false⟩ n) (hp : Policy.StmtP .A post)
    (body : Stmt F X ⟨c.function,true⟩ n) (hb : Policy.StmtP .A body) (state : WordState X n),
    (OpenRun.loop (c := c) fuel environment condition hc post hp body hb state).map
        (Coordinates.encodeOutcome coordinates) =
      Closed.evalLoop (c := c) fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
        (WordAdapter.expression condition hc coordinates.locals coordinates.cells).code
        (WordAdapter.expression condition hc coordinates.locals coordinates.cells).words
        (WordAdapter.statement post hp coordinates.locals coordinates.cells).code
        (WordAdapter.statement post hp coordinates.locals coordinates.cells).words
        (WordAdapter.statement body hb coordinates.locals coordinates.cells).code
        (WordAdapter.statement body hb coordinates.locals coordinates.cells).words (coordinates.pack state)

end Solidity.Yul.OpenRun
