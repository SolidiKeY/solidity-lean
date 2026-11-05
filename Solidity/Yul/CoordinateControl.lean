import Solidity.Yul.CoordinateUpdates
import Solidity.Yul.DirectControl

/-! Same concrete direct-control interpreter under typed logical coordinates.
All coordinate inverses are explicit and constructed by canonical/prepend.
This theorem supplies real bodies for binder composition; no target stack or
physical-state semantics is introduced. -/
namespace Solidity.Yul.Coordinates
open Closed DirectControl

theorem control_agrees (fuel : Nat) {X c n m} (coordinates : Coordinates X n m) {code : Stmt [] X c n}
    (proof : Basic X code) (policy : Policy.StmtP .A code) (state : WordState X n) :
    (eval fuel proof policy state).map (encodeOutcome coordinates) =
      evalStmt fuel .nil True.intro
        (WordAdapter.statement code policy coordinates.locals
          coordinates.cells).code
        (WordAdapter.statement code policy coordinates.locals
          coordinates.cells).words (coordinates.pack state) := by
  induction fuel generalizing c n m code with
  | zero => rfl
  | succ fuel ih =>
    cases proof with
    | skip => rfl
    | assign targets rhs =>
      change ((DirectUpdates.assign (fuel+1) targets rhs policy state).map
        (fun final => (⟨final,.normal⟩ : WordAdapter.Outcome X c n))).map
          (encodeOutcome coordinates) = _
      simpa only [Option.map_map,Function.comp_def,encodeOutcome] using
        Coordinates.assign_agrees (fuel+1) coordinates targets rhs policy state
    | discard rhs =>
      change (do
        let _ ← DirectWords.eval fuel rhs policy state
        pure (⟨state,.normal⟩ : WordAdapter.Outcome X c n)).map (encodeOutcome coordinates) = _
      rw [WordAdapter.statement,evalStmt_discard,←expression_agrees fuel coordinates]
      cases DirectWords.eval fuel rhs policy state <;> rfl
    | @seq c n a b first second =>
      rw [WordAdapter.statement]
      change (do
        let result ← eval fuel first policy.1 state
        match result.flow with
        | .normal => eval fuel second policy.2 result.state
        | _ => pure result).map (encodeOutcome coordinates) =
        (do
          let result ← evalStmt fuel .nil True.intro
            (WordAdapter.statement a policy.1 coordinates.locals
              coordinates.cells).code
            (WordAdapter.statement a policy.1 coordinates.locals
              coordinates.cells).words (coordinates.pack state)
          match result.flow with
          | .normal =>
              evalStmt fuel .nil True.intro
                (WordAdapter.statement b policy.2 coordinates.locals
                  coordinates.cells).code
                (WordAdapter.statement b policy.2 coordinates.locals
                  coordinates.cells).words result.vars
          | _ => pure result)
      rw [←ih coordinates first policy.1 state]
      cases firstRun : eval fuel first policy.1 state with
      | none => rfl
      | some result =>
        cases result with
        | mk middle flow =>
          cases flow with
          | normal => exact ih coordinates second policy.2 middle
          | leave_ legal => rfl
          | break_ legal => rfl
          | continue_ legal => rfl
    | @if_ c n condition body bodyProof =>
      rw [WordAdapter.statement]
      change (do
        let values ← DirectWords.eval fuel condition policy.1 state
        if (values 0).val = 0 then pure (⟨state,.normal⟩ : WordAdapter.Outcome X c n)
        else eval fuel bodyProof policy.2 state).map (encodeOutcome coordinates) =
        (do
          let values ← evalExpr fuel .nil True.intro
            (WordAdapter.expression condition policy.1 coordinates.locals
              coordinates.cells).code
            (WordAdapter.expression condition policy.1 coordinates.locals
              coordinates.cells).words (coordinates.pack state)
          if (values 0).val = 0 then pure (⟨(coordinates.pack state),.normal⟩ : Closed.Outcome c m)
          else
            evalStmt fuel .nil True.intro
              (WordAdapter.statement body policy.2 coordinates.locals
                coordinates.cells).code
              (WordAdapter.statement body policy.2 coordinates.locals
                coordinates.cells).words (coordinates.pack state))
      rw [←expression_agrees fuel coordinates]
      cases conditionRun : DirectWords.eval fuel condition policy.1 state with
      | none => rfl
      | some values =>
        change (if (values 0).val = 0
          then some (⟨state,.normal⟩ : WordAdapter.Outcome X c n)
          else eval fuel bodyProof policy.2 state).map (encodeOutcome coordinates) =
          (if (values 0).val = 0
           then some (⟨(coordinates.pack state),.normal⟩ : Closed.Outcome c m)
           else evalStmt fuel .nil True.intro
             (WordAdapter.statement body policy.2 coordinates.locals
               coordinates.cells).code
             (WordAdapter.statement body policy.2 coordinates.locals
               coordinates.cells).words (coordinates.pack state))
        by_cases zero : (values 0).val = 0
        · rw [if_pos zero,if_pos zero]
          rfl
        · rw [if_neg zero,if_neg zero]
          exact ih coordinates bodyProof policy.2 state
    | leave => rfl
    | break_ => rfl
    | continue_ => rfl



end Solidity.Yul.Coordinates
