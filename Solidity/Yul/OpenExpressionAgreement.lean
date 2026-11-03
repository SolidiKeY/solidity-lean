import Solidity.Yul.OpenAgreement

/-! Expression step of the real mutual fuel induction. The previous-horizon
record is discharged by the final induction; calls use actual retained bodies
and the constructed global-only coordinates, not a callee adequacy oracle. -/
namespace Solidity.Yul.OpenRun
open Closed
open OpenFunctions (PureEnvironment)


def closedCall (fuel : Nat) {sig} (closure : Closed.Closure sig)
    (profile : Closed.ClosureWordP closure) (inputs : Values sig.args) : Option (Values sig.rets) := do
  let result ← Closed.evalStmt fuel closure.environment profile.1 closure.body profile.2
    (Closed.extendValues inputs (fun _ : Fin sig.rets => word 0))
  pure (Closed.dropValues sig.args result.vars)

theorem closedCall_congr (fuel : Nat) {sig} {one two : Closed.Closure sig}
    (same : one = two) (first : Closed.ClosureWordP one) (second : Closed.ClosureWordP two)
    (inputs : Values sig.args) :
    closedCall fuel one first inputs = closedCall fuel two second inputs := by
  cases same
  rfl

theorem expression_step (fuel : Nat) (previous : Agreement fuel)
    {F X n m r} (coordinates : Coordinates X n m) (environment : PureEnvironment F)
    (code : Expr F X n r) (policy : Policy.ExprP .A code) (state : WordState X n) :
    OpenRun.expression (fuel+1) environment code policy state =
      Closed.evalExpr (fuel+1) (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
        (WordAdapter.expression code policy coordinates.locals coordinates.cells).code
        (WordAdapter.expression code policy coordinates.locals coordinates.cells).words (coordinates.pack state) := by
  cases code with
  | literal value => rfl
  | «local» index =>
    change some (fun _ => state.locals index) =
      some (fun _ => coordinates.pack state (coordinates.locals index))
    rw [coordinates.pack_local]
  | external ref =>
    change some (fun _ => DirectWords.read (ref.wordRead policy) state.cells) =
      evalExpr (fuel+1) (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
        ((ref.wordRead policy).expression coordinates.cells)
        (WordAdapter.operand_words _ coordinates.cells) (coordinates.pack state)
    generalize operand_eq : ref.wordRead policy = operand
    cases operand with
    | cell cell =>
      change some (fun _ => state.cells cell) =
        some (fun _ => coordinates.pack state (coordinates.cells cell))
      rw [coordinates.pack_cell]
    | literal value => rfl
  | @builtin a r builtin args =>
    rw [OpenRun.expression,WordAdapter.expression,Closed.evalExpr]
    simp only [WordAdapter.tabulate_eq]
    have operands : (fun i : Fin a =>
        (OpenRun.expression fuel environment (args i) (policy.2 i) state).map (fun result : Values 1 => result 0)) =
      (fun i : Fin a =>
        (Closed.evalExpr fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
          (WordAdapter.expression (args i) (policy.2 i) coordinates.locals coordinates.cells).code
          (WordAdapter.expression (args i) (policy.2 i) coordinates.locals coordinates.cells).words
          (coordinates.pack state)).map (fun result : Values 1 => result 0)) := by
      funext i
      rw [previous.expression coordinates environment (args i) (policy.2 i) state]
    rw [operands]
    rfl
  | @call sig function args =>
    let closure := OpenFunctions.lookup environment function
    rw [OpenRun.expression,WordAdapter.expression]
    simp only [WordAdapter.tabulate_eq]
    rw [Closed.evalExpr_call]
    have operands : (fun i : Fin sig.args =>
        (OpenRun.expression fuel environment (args i) (policy i) state).map (fun result : Values 1 => result 0)) =
      (fun i : Fin sig.args =>
        (Closed.evalExpr fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
          (WordAdapter.expression (args i) (policy i) coordinates.locals coordinates.cells).code
          (WordAdapter.expression (args i) (policy i) coordinates.locals coordinates.cells).words
          (coordinates.pack state)).map (fun result : Values 1 => result 0)) := by
      funext i
      rw [previous.expression coordinates environment (args i) (policy i) state]
    rw [operands]
    cases collected : collectValues sig.args (fun i =>
      (Closed.evalExpr fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
        (WordAdapter.expression (args i) (policy i) coordinates.locals coordinates.cells).code
        (WordAdapter.expression (args i) (policy i) coordinates.locals coordinates.cells).words
        (coordinates.pack state)).map (fun result : Values 1 => result 0)) with
    | none => rfl
    | some inputs =>
      let initial : WordState (globals closure.externals) (sig.args+sig.rets) :=
        ⟨Closed.extendValues inputs (fun _ : Fin sig.rets => word 0),
          OpenFunctions.globalCells closure.externals⟩
      have body := previous.statement
        (OpenFunctions.globalCoordinates closure.externals (sig.args+sig.rets))
        closure.environment closure.body closure.policy initial
      change (do
        let result ← OpenRun.statement fuel closure.environment closure.body closure.policy initial
        pure (Closed.dropValues sig.args result.state.locals)) =
        closedCall fuel (Closed.lookup (OpenFunctions.lower environment) function)
          (Closed.lookup_profile (OpenFunctions.lower environment) (OpenFunctions.lower_words environment) function) inputs
      rw [closedCall_congr fuel (OpenFunctions.lookup_lower environment function) _
        (OpenFunctions.lowerClosure_words closure) inputs]
      change (do
        let result ← OpenRun.statement fuel closure.environment closure.body closure.policy initial
        pure (Closed.dropValues sig.args result.state.locals)) =
        (do
          let result ← Closed.evalStmt fuel (OpenFunctions.lower closure.environment)
            (OpenFunctions.lower_words closure.environment)
            (WordAdapter.statement closure.body closure.policy (fun i => i)
              (fun cell => False.elim cell.not_globals)).code
            (WordAdapter.statement closure.body closure.policy (fun i => i)
              (fun cell => False.elim cell.not_globals)).words initial.locals
          pure (Closed.dropValues sig.args result.vars))
      change (OpenRun.statement fuel closure.environment closure.body closure.policy initial).map
        (fun result => (⟨result.state.locals,result.flow⟩ : Closed.Outcome ⟨true,false⟩ (sig.args+sig.rets))) =
          Closed.evalStmt fuel (OpenFunctions.lower closure.environment)
            (OpenFunctions.lower_words closure.environment)
            (WordAdapter.statement closure.body closure.policy (fun i => i)
              (fun cell => False.elim cell.not_globals)).code
            (WordAdapter.statement closure.body closure.policy (fun i => i)
              (fun cell => False.elim cell.not_globals)).words initial.locals at body
      rw [←body]
      cases bodyRun : OpenRun.statement fuel closure.environment closure.body closure.policy initial with
      | none => rfl
      | some result => rfl

end Solidity.Yul.OpenRun
