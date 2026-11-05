import Solidity.Yul.OpenAgreement

namespace Solidity.Yul.OpenRun
open Closed
open OpenFunctions (PureEnvironment)

theorem loop_step (fuel : Nat) (previous : Agreement fuel)
    {F X c n m} (coordinates : Coordinates X n m) (environment : PureEnvironment F)
    (condition : Expr F X n 1) (hc : Policy.ExprP .A condition)
    (post : Stmt F X ⟨c.function,false⟩ n) (hp : Policy.StmtP .A post)
    (body : Stmt F X ⟨c.function,true⟩ n) (hb : Policy.StmtP .A body) (state : WordState X n) :
    (OpenRun.loop (c := c) (fuel+1) environment condition hc post hp body hb state).map
        (Coordinates.encodeOutcome coordinates) =
      Closed.evalLoop (c := c) (fuel+1) (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
        (WordAdapter.expression condition hc coordinates.locals coordinates.cells).code
        (WordAdapter.expression condition hc coordinates.locals coordinates.cells).words
        (WordAdapter.statement post hp coordinates.locals coordinates.cells).code
        (WordAdapter.statement post hp coordinates.locals coordinates.cells).words
        (WordAdapter.statement body hb coordinates.locals coordinates.cells).code
        (WordAdapter.statement body hb coordinates.locals coordinates.cells).words (coordinates.pack state) := by
  let sourceStep : WordState X n → Option (WordAdapter.Outcome X c n) := fun next => do
    let result ← OpenRun.statement fuel environment post hp next
    match result.flow with
    | .normal => OpenRun.loop fuel environment condition hc post hp body hb result.state
    | .leave_ legal => pure ⟨result.state,.leave_ legal⟩
    | .break_ impossible => False.elim (by cases impossible)
    | .continue_ impossible => False.elim (by cases impossible)
  let targetStep : Values m → Option (Closed.Outcome c m) := fun values => do
    let result ← Closed.evalStmt fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
      (WordAdapter.statement post hp coordinates.locals coordinates.cells).code
      (WordAdapter.statement post hp coordinates.locals coordinates.cells).words values
    match result.flow with
    | .normal =>
        Closed.evalLoop fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
          (WordAdapter.expression condition hc coordinates.locals coordinates.cells).code
          (WordAdapter.expression condition hc coordinates.locals coordinates.cells).words
          (WordAdapter.statement post hp coordinates.locals coordinates.cells).code
          (WordAdapter.statement post hp coordinates.locals coordinates.cells).words
          (WordAdapter.statement body hb coordinates.locals coordinates.cells).code
          (WordAdapter.statement body hb coordinates.locals coordinates.cells).words result.vars
    | .leave_ legal => pure ⟨result.vars,.leave_ legal⟩
    | .break_ impossible => False.elim (by cases impossible)
    | .continue_ impossible => False.elim (by cases impossible)
  have stepLaw : ∀ next, (sourceStep next).map (Coordinates.encodeOutcome coordinates) =
      targetStep (coordinates.pack next) := by
    intro next
    dsimp only [sourceStep,targetStep]
    rw [←previous.statement coordinates environment post hp next]
    cases postRun : OpenRun.statement fuel environment post hp next with
    | none => rfl
    | some result =>
      cases result with
      | mk after flow =>
        cases flow with
        | normal => exact previous.loop coordinates environment condition hc post hp body hb after
        | leave_ legal => rfl
        | break_ impossible => cases impossible
        | continue_ impossible => cases impossible
  change (do
    let values ← OpenRun.expression fuel environment condition hc state
    if (values 0).val = 0 then pure (⟨state,.normal⟩ : WordAdapter.Outcome X c n)
    else
      let result ← OpenRun.statement fuel environment body hb state
      match result.flow with
      | .normal => sourceStep result.state
      | .continue_ _ => sourceStep result.state
      | .break_ _ => pure ⟨result.state,.normal⟩
      | .leave_ legal => pure ⟨result.state,.leave_ legal⟩).map (Coordinates.encodeOutcome coordinates) =
    (do
      let values ← Closed.evalExpr fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
        (WordAdapter.expression condition hc coordinates.locals coordinates.cells).code
        (WordAdapter.expression condition hc coordinates.locals coordinates.cells).words (coordinates.pack state)
      if (values 0).val = 0 then pure (⟨coordinates.pack state,.normal⟩ : Closed.Outcome c m)
      else
        let result ← Closed.evalStmt fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
          (WordAdapter.statement body hb coordinates.locals coordinates.cells).code
          (WordAdapter.statement body hb coordinates.locals coordinates.cells).words (coordinates.pack state)
        match result.flow with
        | .normal => targetStep result.vars
        | .continue_ _ => targetStep result.vars
        | .break_ _ => pure ⟨result.vars,.normal⟩
        | .leave_ legal => pure ⟨result.vars,.leave_ legal⟩)
  rw [←previous.expression coordinates environment condition hc state]
  cases conditionRun : OpenRun.expression fuel environment condition hc state with
  | none => rfl
  | some values =>
    change (if (values 0).val = 0
      then some (⟨state,.normal⟩ : WordAdapter.Outcome X c n)
      else (OpenRun.statement fuel environment body hb state).bind (fun result =>
        match result.flow with
        | .normal => sourceStep result.state
        | .continue_ _ => sourceStep result.state
        | .break_ _ => some ⟨result.state,.normal⟩
        | .leave_ legal => some ⟨result.state,.leave_ legal⟩)).map
          (Coordinates.encodeOutcome coordinates) =
      (if (values 0).val = 0
       then some (⟨coordinates.pack state,.normal⟩ : Closed.Outcome c m)
       else (Closed.evalStmt fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
         (WordAdapter.statement body hb coordinates.locals coordinates.cells).code
         (WordAdapter.statement body hb coordinates.locals coordinates.cells).words
         (coordinates.pack state)).bind (fun result =>
           match result.flow with
           | .normal => targetStep result.vars
           | .continue_ _ => targetStep result.vars
           | .break_ _ => some ⟨result.vars,.normal⟩
           | .leave_ legal => some ⟨result.vars,.leave_ legal⟩))
    by_cases zero : (values 0).val = 0
    · rw [if_pos zero,if_pos zero]
      rfl
    · rw [if_neg zero,if_neg zero,←previous.statement coordinates environment body hb state]
      cases bodyRun : OpenRun.statement fuel environment body hb state with
      | none => rfl
      | some result =>
        cases result with
        | mk after flow =>
          cases flow with
          | normal => exact stepLaw after
          | continue_ legal => exact stepLaw after
          | break_ legal => rfl
          | leave_ legal => rfl

end Solidity.Yul.OpenRun
