import Solidity.Yul.OpenAgreement

namespace Solidity.Yul.OpenRun
open Closed
open OpenFunctions (PureEnvironment)

theorem statement_step (fuel : Nat) (previous : Agreement fuel)
    {F X c n m} (coordinates : Coordinates X n m) (environment : PureEnvironment F)
    (code : Stmt F X c n) (policy : Policy.StmtP .A code) (state : WordState X n) :
    (OpenRun.statement (fuel+1) environment code policy state).map (Coordinates.encodeOutcome coordinates) =
      Closed.evalStmt (fuel+1) (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
        (WordAdapter.statement code policy coordinates.locals coordinates.cells).code
        (WordAdapter.statement code policy coordinates.locals coordinates.cells).words (coordinates.pack state) := by
  cases code with
    | skip => rfl
    | assign targets rhs =>
      rw [WordAdapter.statement]
      simp only [WordAdapter.tabulate_eq]
      change (do
        let values ← OpenRun.expression fuel environment rhs policy.2 state
        pure (⟨DirectUpdates.writeValues _ targets policy.1 values state,.normal⟩ : WordAdapter.Outcome X c n)).map
          (Coordinates.encodeOutcome coordinates) =
        (do
          let values ← Closed.evalExpr fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
            (WordAdapter.expression rhs policy.2 coordinates.locals coordinates.cells).code
            (WordAdapter.expression rhs policy.2 coordinates.locals coordinates.cells).words (coordinates.pack state)
          pure (⟨Closed.writeValues _ (fun i =>
            WordAdapter.target (targets i) (policy.1 i) coordinates.locals coordinates.cells)
              values (coordinates.pack state),.normal⟩ : Closed.Outcome c m))
      rw [←previous.expression coordinates environment rhs policy.2 state]
      cases valuesRun : OpenRun.expression fuel environment rhs policy.2 state with
      | none => rfl
      | some values =>
        change some (⟨coordinates.pack (DirectUpdates.writeValues _ targets policy.1 values state),.normal⟩ : Closed.Outcome c m) = _
        rw [Coordinates.pack_writeValues]
        rfl
    | discard rhs =>
      rw [WordAdapter.statement,Closed.evalStmt_discard,←previous.expression coordinates environment rhs policy state]
      change (do
        let _ ← OpenRun.expression fuel environment rhs policy state
        pure (⟨state,.normal⟩ : WordAdapter.Outcome X c n)).map (Coordinates.encodeOutcome coordinates) = _
      cases OpenRun.expression fuel environment rhs policy state <;> rfl
    | seq a b =>
      rw [WordAdapter.statement]
      change (do
        let result ← OpenRun.statement fuel environment a policy.1 state
        match result.flow with
        | .normal => OpenRun.statement fuel environment b policy.2 result.state
        | _ => pure result).map (Coordinates.encodeOutcome coordinates) =
        (do
          let result ← Closed.evalStmt fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
            (WordAdapter.statement a policy.1 coordinates.locals
              coordinates.cells).code
            (WordAdapter.statement a policy.1 coordinates.locals
              coordinates.cells).words (coordinates.pack state)
          match result.flow with
          | .normal =>
              Closed.evalStmt fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
                (WordAdapter.statement b policy.2 coordinates.locals
                  coordinates.cells).code
                (WordAdapter.statement b policy.2 coordinates.locals
                  coordinates.cells).words result.vars
          | _ => pure result)
      rw [←previous.statement coordinates environment a policy.1 state]
      cases firstRun : OpenRun.statement fuel environment a policy.1 state with
      | none => rfl
      | some result =>
        cases result with
        | mk middle flow =>
          cases flow with
          | normal => exact previous.statement coordinates environment b policy.2 middle
          | leave_ legal => rfl
          | break_ legal => rfl
          | continue_ legal => rfl
    | if_ condition body =>
      rw [WordAdapter.statement]
      change (do
        let values ← OpenRun.expression fuel environment condition policy.1 state
        if (values 0).val = 0 then pure (⟨state,.normal⟩ : WordAdapter.Outcome X c n)
        else OpenRun.statement fuel environment body policy.2 state).map (Coordinates.encodeOutcome coordinates) =
        (do
          let values ← Closed.evalExpr fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
            (WordAdapter.expression condition policy.1 coordinates.locals
              coordinates.cells).code
            (WordAdapter.expression condition policy.1 coordinates.locals
              coordinates.cells).words (coordinates.pack state)
          if (values 0).val = 0 then pure (⟨(coordinates.pack state),.normal⟩ : Closed.Outcome c m)
          else
            Closed.evalStmt fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
              (WordAdapter.statement body policy.2 coordinates.locals
                coordinates.cells).code
              (WordAdapter.statement body policy.2 coordinates.locals
                coordinates.cells).words (coordinates.pack state))
      rw [←previous.expression coordinates environment]
      cases conditionRun : OpenRun.expression fuel environment condition policy.1 state with
      | none => rfl
      | some values =>
        change (if (values 0).val = 0
          then some (⟨state,.normal⟩ : WordAdapter.Outcome X c n)
          else OpenRun.statement fuel environment body policy.2 state).map (Coordinates.encodeOutcome coordinates) =
          (if (values 0).val = 0
           then some (⟨(coordinates.pack state),.normal⟩ : Closed.Outcome c m)
           else Closed.evalStmt fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
             (WordAdapter.statement body policy.2 coordinates.locals
               coordinates.cells).code
             (WordAdapter.statement body policy.2 coordinates.locals
               coordinates.cells).words (coordinates.pack state))
        by_cases zero : (values 0).val = 0
        · rw [if_pos zero,if_pos zero]
          rfl
        · rw [if_neg zero,if_neg zero]
          exact previous.statement coordinates environment body policy.2 state
    | let_ r rhs body =>
      let term := WordAdapter.expression rhs policy.1 coordinates.locals coordinates.cells
      let rest := WordAdapter.statement body policy.2
        (coordinates.prepend r).locals (coordinates.prepend r).cells
      rw [WordAdapter.statement]
      change (do
        let values ← OpenRun.expression fuel environment rhs policy.1 state
        let result ← OpenRun.statement fuel environment body policy.2 (state.extend values)
        pure (⟨result.state.drop r,result.flow⟩ : WordAdapter.Outcome X c n)).map
          (Coordinates.encodeOutcome coordinates) =
        (do
          let values ← Closed.evalExpr fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment) term.code term.words (coordinates.pack state)
          let result ← Closed.evalStmt fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment) rest.code rest.words
            (Closed.extendValues values (coordinates.pack state))
          pure (⟨Closed.dropValues r result.vars,result.flow⟩ : Closed.Outcome c m))
      rw [←previous.expression coordinates environment]
      cases rhsRun : OpenRun.expression fuel environment rhs policy.1 state with
      | none => rfl
      | some values =>
        change ((OpenRun.statement fuel environment body policy.2 (state.extend values)).bind (fun result =>
          some (⟨result.state.drop r,result.flow⟩ : WordAdapter.Outcome X c n))).map
            (Coordinates.encodeOutcome coordinates) =
          ((Closed.evalStmt fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment) rest.code rest.words
            (Closed.extendValues values (coordinates.pack state))).bind (fun result =>
              some (⟨Closed.dropValues r result.vars,result.flow⟩ : Closed.Outcome c m)))
        rw [←Coordinates.pack_prefix coordinates values state]
        rw [←previous.statement (coordinates.prepend r) environment body policy.2 (state.extend values)]
        cases bodyRun : OpenRun.statement fuel environment body policy.2 (state.extend values) with
        | none => rfl
        | some result =>
          change some (⟨coordinates.pack (result.state.drop r),result.flow⟩ : Closed.Outcome c m) =
            some ⟨Closed.dropValues r ((coordinates.prepend r).pack result.state),result.flow⟩
          rw [Coordinates.pack_drop]
    | zero r body =>
      let initial : Closed.Values r := fun _ => word 0
      let rest := WordAdapter.statement body policy
        (coordinates.prepend r).locals (coordinates.prepend r).cells
      rw [WordAdapter.statement]
      change ((OpenRun.statement fuel environment body policy (state.extend initial)).bind (fun result =>
        some (⟨result.state.drop r,result.flow⟩ : WordAdapter.Outcome X c n))).map
          (Coordinates.encodeOutcome coordinates) =
        ((Closed.evalStmt fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment) rest.code rest.words
          (Closed.extendValues initial (coordinates.pack state))).bind (fun result =>
            some (⟨Closed.dropValues r result.vars,result.flow⟩ : Closed.Outcome c m)))
      rw [←Coordinates.pack_prefix coordinates initial state]
      rw [←previous.statement (coordinates.prepend r) environment body policy (state.extend initial)]
      cases bodyRun : OpenRun.statement fuel environment body policy (state.extend initial) with
      | none => rfl
      | some result =>
        change some (⟨coordinates.pack (result.state.drop r),result.flow⟩ : Closed.Outcome c m) =
          some ⟨Closed.dropValues r ((coordinates.prepend r).pack result.state),result.flow⟩
        rw [Coordinates.pack_drop]


    | switch selector arms fallback =>
      let term := WordAdapter.expression selector policy.1 coordinates.locals coordinates.cells
      let choices := WordAdapter.cases arms policy.2.1 coordinates.locals coordinates.cells
      let otherwise := WordAdapter.statement fallback policy.2.2 coordinates.locals coordinates.cells
      rw [WordAdapter.statement]
      change (do
        let values ← OpenRun.expression fuel environment selector policy.1 state
        let selected ← OpenRun.casesRun fuel environment arms policy.2.1 (values 0) state
        match selected with
        | some result => pure result
        | none => OpenRun.statement fuel environment fallback policy.2.2 state).map
          (Coordinates.encodeOutcome coordinates) =
        (do
          let values ← Closed.evalExpr fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
            term.code term.words (coordinates.pack state)
          let selected ← Closed.evalCases fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
            choices.code choices.words (values 0) (coordinates.pack state)
          match selected with
          | some result => pure result
          | none =>
              Closed.evalStmt fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
                otherwise.code otherwise.words (coordinates.pack state))
      rw [←previous.expression coordinates environment selector policy.1 state]
      cases valuesRun : OpenRun.expression fuel environment selector policy.1 state with
      | none => rfl
      | some values =>
        change (do
          let selected ← OpenRun.casesRun fuel environment arms policy.2.1 (values 0) state
          match selected with
          | some result => pure result
          | none => OpenRun.statement fuel environment fallback policy.2.2 state).map
            (Coordinates.encodeOutcome coordinates) =
          (do
            let selected ← Closed.evalCases fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
              choices.code choices.words (values 0) (coordinates.pack state)
            match selected with
            | some result => pure result
            | none =>
                Closed.evalStmt fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
                  otherwise.code otherwise.words (coordinates.pack state))
        rw [←previous.casesRun coordinates environment arms policy.2.1 (values 0) state]
        cases selectedRun : OpenRun.casesRun fuel environment arms policy.2.1 (values 0) state with
        | none => rfl
        | some selected =>
          cases selected with
          | none => exact previous.statement coordinates environment fallback policy.2.2 state
          | some result => rfl
    | for_ pre condition post body =>
      let init := WordAdapter.statement pre policy.1 coordinates.locals coordinates.cells
      let test := WordAdapter.expression condition policy.2.1 coordinates.locals coordinates.cells
      let step := WordAdapter.statement post policy.2.2.1 coordinates.locals coordinates.cells
      let work := WordAdapter.statement body policy.2.2.2 coordinates.locals coordinates.cells
      rw [WordAdapter.statement]
      change (do
        let result ← OpenRun.statement fuel environment pre policy.1 state
        match result.flow with
        | .normal => OpenRun.loop fuel environment condition policy.2.1 post policy.2.2.1 body policy.2.2.2 result.state
        | .leave_ legal => pure ⟨result.state,.leave_ legal⟩
        | .break_ impossible => False.elim (by cases impossible)
        | .continue_ impossible => False.elim (by cases impossible)).map
          (Coordinates.encodeOutcome coordinates) =
        (do
          let result ← Closed.evalStmt fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
            init.code init.words (coordinates.pack state)
          match result.flow with
          | .normal =>
              Closed.evalLoop fuel (OpenFunctions.lower environment) (OpenFunctions.lower_words environment)
                test.code test.words step.code step.words work.code work.words result.vars
          | .leave_ legal => pure ⟨result.vars,.leave_ legal⟩
          | .break_ impossible => False.elim (by cases impossible)
          | .continue_ impossible => False.elim (by cases impossible))
      rw [←previous.statement coordinates environment pre policy.1 state]
      cases preRun : OpenRun.statement fuel environment pre policy.1 state with
      | none => rfl
      | some result =>
        cases result with
        | mk next flow =>
          cases flow with
          | normal => exact previous.loop coordinates environment condition policy.2.1 post policy.2.2.1 body policy.2.2.2 next
          | leave_ legal => rfl
          | break_ impossible => cases impossible
          | continue_ impossible => cases impossible
    | leave => rfl
    | break_ => rfl
    | continue_ => rfl
    | functions signatures bodies rest =>
      change (OpenRun.statement fuel (.group signatures environment bodies policy.1)
        rest policy.2 state).map (Coordinates.encodeOutcome coordinates) = _
      exact previous.statement coordinates (.group signatures environment bodies policy.1) rest policy.2 state

end Solidity.Yul.OpenRun
